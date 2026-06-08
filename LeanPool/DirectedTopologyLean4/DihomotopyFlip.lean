/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.DirectedHomotopy

/-!
# LeanPool.DirectedTopologyLean4.DihomotopyFlip
-/

/-
  If we have a dihomotopy `F` from `f : D(I,X)` to `g : D(I,X)`:
    C----- g -----D
    |             |
    |             |
    |             |
    |             |
    A----- f -----B
  Then we can flip it diagonally to obtain a new homotopy:
    B--- F.evalAtRight 1 -----D
    |                           |
    f                           g
    |                           |
    |                           |
    A----F.evalAtRight 0 -----C

  We then use that to compose two homotopies F
    D----- q₀ -----E
    |              |
    |              |
    |              |
    |              |
    A----- p₀ -----B
  and G
    E----- q₁ -----F
    |              |
    |              |
    |              |
    |              |
    B----- p₁ -----C
  that agree on the common side B ----- E to
    D----- q₀.trans q₁ -----F
    |                       |
    |                       |
    |                       |
    |                       |
    A----- p₀.trans p₁ -----C

  This is a variation of dipath.dihomotopy.hcomp of dihomotopies that are not necessarily dipath
  dihomotopies.
-/

universe u v

open DirectedSpace DirectedUnitInterval unitIAux DirectedMap
open scoped unitInterval

noncomputable section

namespace DirectedMap
namespace Dihomotopy

variable {X : dTopCat} {f g : D(I,X)}

/-- Flip a dihomotopy by swapping its two coordinates. -/
def flip (F : Dihomotopy f g)
    : Dihomotopy (F.evalAtRight 0).toDirectedMap (F.evalAtRight 1).toDirectedMap :=
{
  toFun := fun t => F (t.2, t.1)
  directed_toFun := fun ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ γ ⟨h₁, h₂⟩ => by
      let γ' : Dipath (y₀, x₀) (y₁, x₁) := {
        toFun := fun t => ((γ t).2, (γ t).1)
        source' := by simp
        target' := by simp
        dipath_toPath := ⟨h₂, h₁⟩
      }
      exact F.directed_toFun γ'.toPath γ'.dipath_toPath
  map_zero_left := fun x => rfl
  map_one_left := fun x => rfl
}

lemma flip_apply (F : Dihomotopy f g) (t₀ t₁ : I) :
  F.flip (t₀, t₁) = F (t₁, t₀) := rfl

variable {x₀ x₁ x₂ y₀ y₁ y₂ : X}
variable {p₀ : Dipath x₀ x₁} {p₁ : Dipath x₁ x₂} {q₀ : Dipath y₀ y₁} {q₁ : Dipath y₁ y₂}

/-- Suppose the following are given:
* `p₀ : dipath x₀ x₁`
* `p₁ : dipath x₁ x₂`
* `q₀ : dipath y₀ y₁`
* `q₁ : dipath y₁ y₂`
* `F : dihomotopy p₀.toDirectedMap q₀.toDirectedMap`
* `G : dihomotopy p₁.toDirectedMap p₁.toDirectedMap`
* `h : F.evalAtRight 1 = G.evalAtRight 0`
Then we can compose these horizontally to obtain:
  `dihomotopy (p₀.trans p₁).toDirectedMap (q₀.trans q₁).toDirectedMap`
-/
def hcomp' (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap)
    (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.evalAtRight 1).toDirectedMap = (G.evalAtRight 0).toDirectedMap) :
    Dihomotopy (p₀.trans p₁).toDirectedMap (q₀.trans q₁).toDirectedMap :=
  ((F.flip.cast rfl h).trans G.flip).flip.cast
    (by
      ext t
      change ((F.flip.cast rfl h).trans G.flip) (t, 0) = (p₀.trans p₁) t
      rw [trans_apply, Dipath.trans_apply]
      split_ifs
      · rw [cast_apply, flip_apply]
        exact F.map_zero_left _
      · rw [flip_apply]
        exact G.map_zero_left _
    )
    (by
      ext t
      change ((F.flip.cast rfl h).trans G.flip) (t, 1) = (q₀.trans q₁) t
      rw [trans_apply, Dipath.trans_apply]
      split_ifs
      · rw [cast_apply, flip_apply]
        exact F.map_one_left _
      · rw [flip_apply]
        exact G.map_one_left _
    )

lemma hcomp'_apply (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap)
    (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.evalAtRight 1).toDirectedMap = (G.evalAtRight 0).toDirectedMap) (t₁ t₂ : I) :
    (hcomp' F G h) (t₁, t₂) =
    if h : (t₂ : ℝ) ≤ 1/2 then
      F.evalAtLeft t₁ ⟨2 * t₂, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨t₂.2.1, h⟩⟩
    else
      G.evalAtLeft t₁ ⟨2 * t₂ - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t₂.2.2⟩⟩ := by
  unfold hcomp'
  rw [cast_apply, flip_apply, trans_apply]
  split_ifs
  · rw [cast_apply, flip_apply]
    rfl
  · rw [flip_apply]
    rfl

lemma hcomp'_apply_zero_right (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap)
    (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.evalAtRight 1).toDirectedMap = (G.evalAtRight 0).toDirectedMap) (x : I) :
    (hcomp' F G h) (x, 0) = F (x, 0) := by
  rw [hcomp'_apply]
  split_ifs with h
  · change F (x, _) = F (x, 0)
    apply congr_arg
    ext
    · rfl
    simp
  · exfalso
    apply h
    change (0 : ℝ) ≤ 1/2
    linarith

lemma hcomp'_apply_one_right (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap)
    (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.evalAtRight 1).toDirectedMap = (G.evalAtRight 0).toDirectedMap) (x : I) :
    (hcomp' F G h) (x, 1) = G (x, 1) := by
  rw [hcomp'_apply]
  split_ifs with h
  · exfalso
    have : ¬ ((1 : ℝ) ≤ 1/2) := by linarith
    apply this
    exact h
  · change G (x, _) = G (x, 1)
    apply congr_arg
    ext
    · rfl
    simp
    norm_num

lemma hcomp'_range (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap)
    (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.evalAtRight 1).toDirectedMap = (G.evalAtRight 0).toDirectedMap) :
    Set.range (hcomp' F G h) ⊆ Set.range F ∪ Set.range G := fun z ⟨⟨t₁, t₂⟩, ht⟩ =>  by
  rw [hcomp'_apply] at ht
  split_ifs at ht with h
  · left
    constructor
    exact ht
  · right
    constructor
    exact ht

end Dihomotopy
end DirectedMap
