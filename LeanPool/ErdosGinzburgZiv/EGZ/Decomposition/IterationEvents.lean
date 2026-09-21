/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMapLevels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Parameters

/-!
# States and progress certificates for the decomposition iteration

States are minimal and reduced, with a positive constant coordinate radius.
An event records an unsatisfied conclusion. Its color orders completeness
and face events by the represented level, with gap cleanup last.
-/

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

omit [Fact p.Prime] in
theorem isRealizedFace_top (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) :
    Φ.IsRealizedFace x ⊤ := by
  intro q hq
  exact Φ.flag.transition_mem (Φ.faceIndex_le x ⊤) hq

/-- A node equality transports its face without choosing coordinates. -/
def faceAtNode (Φ : FlagDecomposition p d f) {x y : Φ.flag.Node}
    (Γ : (Φ.flag.polytope x).Face) (h : y = x) : (Φ.flag.polytope y).Face := by
  subst y
  exact Γ

omit [Fact p.Prime] in
@[simp]
theorem faceAtNode_rfl (Φ : FlagDecomposition p d f) {x : Φ.flag.Node}
    (Γ : (Φ.flag.polytope x).Face) : Φ.faceAtNode Γ rfl = Γ := rfl

namespace Iteration

/-- A minimal flag decomposition equipped with a positive radius for the iteration. -/
structure State (p d : ℕ) [NeZero p] (f : FpCoord p d → ℕ) where
  /-- The flag decomposition at the current stage. -/
  decomposition : FlagDecomposition p d f
  /-- The positive radius controlling the current decomposition. -/
  radius : ℕ
  radius_pos : 1 ≤ radius
  minimal : decomposition.IsMinimal
  reduced : decomposition.IsReduced
  bounded : decomposition.IsKBounded (fun _ ↦ radius)

namespace State

variable (s : State p d f)

/-- Every node gap exceeds the prescribed scale relative to the total input mass. -/
def GapCondition (δ : ℝ) : Prop :=
  ∀ x, δ ^ 3 * (s.radius : ℝ)⁻¹ ^ d * (natMass f : ℝ) ≤
    (s.decomposition.gap x : ℝ)

/-- The state satisfies the gap bound and the required completeness condition. -/
def Finished (ε δ : ℝ) (g : ℕ → ℕ) : Prop :=
  s.GapCondition δ ∧ s.decomposition.IsComplete (fun _ ↦ g s.radius) ε δ

/-- The three possible reasons for refining a state: a gap, a face, or an incomplete node. -/
inductive Event
  | gap
  | face (x : s.decomposition.flag.Node) (Γ : (s.decomposition.flag.polytope x).Face)
  | complete (x : s.decomposition.flag.Node)

namespace Event

variable {s}

/-- The chosen event witnesses a failure of the corresponding termination condition. -/
def Valid (ε δ : ℝ) (g : ℕ → ℕ) : s.Event → Prop
  | .gap => ¬ s.GapCondition δ
  | .face x Γ => s.decomposition.IsLargeFace ε x Γ ∧ ¬ s.decomposition.IsRealizedFace x Γ
  | .complete x => s.decomposition.IsLargeElement ε x ∧
      ¬ s.decomposition.IsCompleteElement x (g s.radius) δ

/-- The largest level required to remain stable during this event. -/
noncomputable def cutoff : s.Event → ℕ
  | .gap => (d + 1) ^ 2
  | .face x _ => s.decomposition.level x
  | .complete x => s.decomposition.level x

/-- Encode the event type and its level as a natural number for the stopping argument. -/
noncomputable def color : s.Event → ℕ
  | .gap => 2 * (d + 1) ^ 2
  | .face x _ => 2 * s.decomposition.level x + 1
  | .complete x => 2 * s.decomposition.level x

theorem color_lt (E : s.Event) : E.color < 2 * (d + 1) ^ 2 + 1 := by
  cases E with
  | gap => exact Nat.lt_succ_self _
  | face x Γ =>
    have h : s.decomposition.level x < (d + 1) ^ 2 := s.decomposition.representation.level_lt x
    dsimp [color]
    omega
  | complete x =>
    have h : s.decomposition.level x < (d + 1) ^ 2 := s.decomposition.representation.level_lt x
    dsimp [color]
    omega

theorem cutoff_ge_of_color_ge (E : s.Event) {L : ℕ} (h : 2 * L ≤ E.color) :
    L ≤ E.cutoff := by
  cases E <;> dsimp [color, cutoff] at * <;> omega

theorem cutoff_le_square (E : s.Event) : E.cutoff ≤ (d + 1) ^ 2 := by
  cases E with
  | gap => exact le_rfl
  | face x Γ => exact (s.decomposition.representation.level_lt x).le
  | complete x => exact (s.decomposition.representation.level_lt x).le

end Event

omit [Fact (Nat.Prime p)] in
theorem exists_valid_event (ε δ : ℝ) (g : ℕ → ℕ) (h : ¬ s.Finished ε δ g) :
    ∃ E : s.Event, E.Valid ε δ g := by
  classical
  by_cases hgap : s.GapCondition δ
  · by_cases hc : ∀ x, s.decomposition.IsLargeElement ε x →
        s.decomposition.IsCompleteElement x (g s.radius) δ
    · have hf : ¬ ∀ x (Γ : (s.decomposition.flag.polytope x).Face),
          s.decomposition.IsLargeFace ε x Γ → s.decomposition.IsRealizedFace x Γ := by
        intro hf
        exact h ⟨hgap, s.minimal, s.reduced, hc, hf⟩
      push Not at hf
      obtain ⟨x, Γ, hΓ, hn⟩ := hf
      exact ⟨.face x Γ, hΓ, hn⟩
    · push Not at hc
      obtain ⟨x, hx, hn⟩ := hc
      exact ⟨.complete x, hx, hn⟩
  · exact ⟨.gap, hgap⟩

end State

variable {s t : State p d f}

/-- A face event has a surviving node at the same level where its selected
face has become realized. Completeness events kill the selected low-level
lineage. Gap events establish the gap condition at the current scale. -/
def Resolves (S : SubdivisionMap s.decomposition t.decomposition) (δ : ℝ) : s.Event → Prop
  | .gap => t.GapCondition δ
  | .face x Γ => ∃ y : t.decomposition.flag.Node,
      ∃ h : S.node y = x,
      t.decomposition.level y = s.decomposition.level x ∧
      ∀ hne : ((t.decomposition.flag.polytope y).carrier ∩
          S.fibre y ⁻¹' (s.decomposition.faceAtNode Γ h).carrier).Nonempty,
        t.decomposition.IsRealizedFace y
          (S.face y (s.decomposition.faceAtNode Γ h) hne)
  | .complete x => ∀ y : t.decomposition.flag.Node,
      t.decomposition.level y ≤ s.decomposition.level x → S.node y ≠ x

/-- Everything used by the termination argument is certified by a concrete
normalized operation. Stable mass transport is required only below the
event's cutoff. -/
structure Progress (s t : State p d f) (ε δ : ℝ) (g : ℕ → ℕ) where
  /-- The event triggering the transition between the two states. -/
  event : s.Event
  valid : event.Valid ε δ g
  /-- The subdivision map relating the new decomposition to the preceding one. -/
  subdivision : SubdivisionMap s.decomposition t.decomposition
  level_parent : ∀ y, s.decomposition.level (subdivision.node y) ≤ t.decomposition.level y
  /-- Stable node maps for all new nodes at or below the event cutoff. -/
  stable : ∀ y, t.decomposition.level y ≤ event.cutoff →
    StableNodeMap s.decomposition t.decomposition (subdivision.node y) y
  stable_real : ∀ y h, (stable y h).coord.real = subdivision.fibre y
  parent_injective : Set.InjOn subdivision.node {y | t.decomposition.level y ≤ event.cutoff}
  resolves : Resolves subdivision δ event
  radius_le : s.radius ≤ t.radius
  card_le : Fintype.card t.decomposition.flag.Node ≤ 2 * Fintype.card s.decomposition.flag.Node
  mass_le : t.decomposition.retainedMass ≤ s.decomposition.retainedMass
  mass_loss_le : (s.decomposition.retainedMass : ℝ) - t.decomposition.retainedMass ≤
    (ε * δ ^ 2 + (3 : ℝ) ^ (d + 1) * δ) * s.decomposition.retainedMass

end Iteration
end EGZ.FlagDecomposition
