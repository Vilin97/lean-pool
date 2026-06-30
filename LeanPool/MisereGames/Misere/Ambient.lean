/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/

module

public import LeanPool.MisereGames.Misere.Separation

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

variable {G : Type (u + 1)} [Form G]

open Form

attribute [local instance] Classical.propDecidable

public section

namespace Form

open Separation

/-- Ambient predicates closed under the separator and downlink constructions. -/
class Ambient (IsAmbient : outParam (G → Prop)) extends Hereditary IsAmbient,
  ClosedUnderNeg IsAmbient where
  isAmbient_rootedAdjoint {r g : G} : IsAmbient r → IsAmbient g → IsAmbient (rootedAdjoint r g)
  isAmbient_rightSeparatorCandidate {r h x : G} :
    IsAmbient r → IsAmbient h → IsAmbient x → IsAmbient (rightSeparatorCandidate r h x)
  isAmbient_downlinkWitness {r g h : G} {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet r g h y)] [Small (downlinkRightSet r g h x)] :
    IsAmbient r → IsAmbient g → IsAmbient h → (∀ gl, IsAmbient (x gl)) → (∀ hr, IsAmbient (y hr)) →
      IsAmbient (downlinkWitness r g h x y)

/--
The Left separator stays ambient: it is the conjugate of a right one.
-/
theorem Ambient.isAmbient_leftSeparatorCandidate {IsAmbient : G → Prop} [Ambient IsAmbient]
    {r g x : G} (h_root : IsAmbient r) (hg : IsAmbient g) (hx : IsAmbient x) :
    IsAmbient (leftSeparatorCandidate r g x) := by
  rw [leftSeparatorCandidate_eq_neg]
  exact ClosedUnderNeg.neg_of (Ambient.isAmbient_rightSeparatorCandidate
    (ClosedUnderNeg.neg_of h_root) (ClosedUnderNeg.neg_of hg) (ClosedUnderNeg.neg_of hx))

instance : Ambient (IsLong : G → Prop) where
  isAmbient_rootedAdjoint _ _ := isLong _
  isAmbient_rightSeparatorCandidate _ _ _ := isLong _
  isAmbient_downlinkWitness _ _ _ _ _ := isLong _

private lemma rightSeparatorLeftSet_finite {r h : G} (hh : IsShort h) :
    (Separation.rightSeparatorLeftSet r h).Finite := by
  have := Short.finite_moves' Player.right hh
  exact (Set.finite_singleton r).union
    (Set.finite_range (fun hr : moves .right h => rootedAdjoint r (hr : G)))

private lemma rightSeparatorLeftSet_short {r h : G} (h_root_short : IsShort r) (hh : IsShort h) :
    ∀ y ∈ Separation.rightSeparatorLeftSet r h, IsShort y := by
  intro y hy
  simp only [Separation.rightSeparatorLeftSet, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_range] at hy
  rcases hy with rfl | ⟨hr, rfl⟩
  · exact h_root_short
  · exact Adjoint.short_rootedAdjoint h_root_short (Short.of_mem_moves hh hr.prop)

private lemma downlinkZero_finite (r : G) (p : Player) (g h : G) :
    (Separation.downlinkZero r p g h).Finite := by
  unfold Separation.downlinkZero
  by_cases hz : IsEnd (-p) g ∧ IsEnd (-p) h <;> simp [hz]

private lemma downlinkOptions_finite {r : G} {p : Player} {g h : G}
    (hg : IsShort g) (hh : IsShort h) (z : moves (-p) h → G) :
    (Separation.downlinkOptions r p g h z).Finite := by
  have := Short.finite_moves' (-p) hg
  have := Short.finite_moves' (-p) hh
  exact ((Set.finite_range z).union
    (Set.finite_range (fun gp : moves (-p) g => rootedAdjoint r (gp : G)))).union
    (downlinkZero_finite r p g h)

private lemma downlinkOptions_short {r : G} {p : Player} {g h : G} {z : moves (-p) h → G}
    (h_root_short : IsShort r) (hg : IsShort g) (hz : ∀ hp, IsShort (z hp)) :
    ∀ a ∈ Separation.downlinkOptions r p g h z, IsShort a := by
  intro a ha
  simp only [downlinkOptions, downlinkZero, Set.mem_union, Set.mem_range, Subtype.exists,
    exists_prop, Set.mem_ite_empty_right, Set.mem_singleton_iff] at ha
  rcases ha with (⟨hp, hhp, rfl⟩ | ⟨gp, hgp, rfl⟩) | ha0
  · exact hz ⟨hp, hhp⟩
  · exact Adjoint.short_rootedAdjoint h_root_short (Short.of_mem_moves hg hgp)
  · by_cases hend : IsEnd (-p) g ∧ IsEnd (-p) h
    · simpa [hend, ha0] using h_root_short
    · simp [hend] at ha0

instance : Ambient IsShort (G := G) where
  isAmbient_rootedAdjoint h_root_short hg := Adjoint.short_rootedAdjoint h_root_short hg
  isAmbient_rightSeparatorCandidate := fun {r h x} h_root_short h_h h_x => by
    unfold Separation.rightSeparatorCandidate
    apply Short.ofSets
    · exact rightSeparatorLeftSet_finite h_h
    · exact rightSeparatorLeftSet_short h_root_short h_h
    · exact Set.finite_singleton x
    · intro y hy
      rwa [Set.mem_singleton_iff.mp hy]
  isAmbient_downlinkWitness := by
    intro r g h x y _ _ h_root_short h_g h_h hx hy
    let L : Set G := Separation.downlinkLeftSet r g h y
    let R : Set G := Separation.downlinkRightSet r g h x
    change IsShort !{L | R}
    apply Short.ofSets
    · exact downlinkOptions_finite (p := .left) h_g h_h y
    · exact downlinkOptions_short (p := .left) h_root_short h_g hy
    · exact downlinkOptions_finite (p := .right) h_h h_g x
    · exact downlinkOptions_short (p := .right) h_root_short h_h hx

end Form

end

end MisereGames
