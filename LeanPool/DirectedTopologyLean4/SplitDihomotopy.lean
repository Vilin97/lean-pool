/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.DirectedPathHomotopy

/-
  This file contains the definitions of splitting a (dipath)
      dihomotopy both vertically and horizontally.

  Take a dihomotopy `F : f ~ g`, with `f g : D(I,X)`:
   *----- g -----*
   |             |
   |             |
   |             |
   |             |
   *----- f -----*

  Splitting vertically at `T : I` gives us:
    *----- g -----*
    |             |
    |             |
    *-- F.eval T -*
  and
    *-- F.eval T -*
    |             |
    |             |
    *----- f -----*

  Splitting horizontally at `T : I` gives us:
   *-- g₁ --*     *-- g₂ --*
   |        |     |        |
   |        | and |        |
   |        |     |        |
   |        |     |        |
   *-- f₁ --*     *-- f₂ --*
  Here f₁, f₂, g₁ and g₂ are obtained from f and g by splitting them at T : I.

  In the case that F is a dipath dihomotopy (it fixes endpoints), then splitting it vertically
  gives two dipath dihomotopies.
-/

open DirectedMap
open scoped unitInterval

namespace SplitDihomotopy


variable {X : dTopCat}

/-- For any `T: I`, we have the directed map `I → I` given by `t ↦ t * T`.
This is an interpolation from 0 to T
-/
abbrev DirectedFst (T : I) : D(I,I) := directed_interpolate_const (unitIAux.zero_le T)

@[simp]
lemma directedFst_apply (T t : I) : DirectedFst T t = ⟨_, unitInterval.mul_mem T.2 t.2⟩ := by
  apply Subtype.coe_inj.mp
  change (σ t : ℝ) * 0 + t * T = T * t
  ring


/-- For any `T : I` we have the directed map `I → I` given by `t ↦ (1 - t) * T + t`.
This is an interpolation from T to 1
-/
abbrev DirectedSnd (T : I) : D(I,I) := directed_interpolate_const (unitIAux.le_one T)

@[simp]
lemma directedSnd_apply (T t : I) : DirectedSnd T t = ⟨_, interp_left_mem_I T t⟩ := by
  apply Subtype.coe_inj.mp
  change (1 - t : ℝ) * T + t * 1 = (1 - T : ℝ) * t + T
  ring

/-- The first part of a dipath-dihomotopy split vertically at `T`: a dihomotopy from `γ₁` to the
slice `F.eval T`. -/
def FirstPartVerticallyDihomotopy {x y : X} {γ₁ γ₂ : Dipath x y} (F : Dipath.Dihomotopy γ₁ γ₂)
    (T : I) :
    Dipath.Dihomotopy γ₁ (F.eval T) where
  toDirectedMap
      := F.toDirectedMap.comp (DirectedMap.prod_map_mk' (DirectedFst T) (DirectedMap.id I))
  map_zero_left := fun x => by change F (DirectedFst T 0, x) = γ₁ x; simp
  map_one_left := fun x => by change F (DirectedFst T 1, x) = F (T, x); simp
  prop' := fun t z hz => F.prop' _ z hz

lemma fpv_apply {x y : X} {γ₁ γ₂ : Dipath x y} (F : Dipath.Dihomotopy γ₁ γ₂) (T s t : I) :
    FirstPartVerticallyDihomotopy F T (s, t) = F (T * s, t) := by
  change F (DirectedFst T s, t) = F (T * s, t)
  rw [directedFst_apply]
  rfl

/-- The second part of a dipath-dihomotopy split vertically at `T`: a dihomotopy from the slice
`F.eval T` to `γ₂`. -/
def SecondPartVerticallyDihomotopy {x y : X} {γ₁ γ₂ : Dipath x y} (F : Dipath.Dihomotopy γ₁ γ₂)
    (T : I) :
    Dipath.Dihomotopy (F.eval T) γ₂ where
  toDirectedMap
      := F.toDirectedMap.comp (DirectedMap.prod_map_mk' (DirectedSnd T) (DirectedMap.id I))

  map_zero_left := fun x => by change F (DirectedSnd T 0, x) = F (T, x); simp
  map_one_left := fun x => by change F (DirectedSnd T 1, x) = γ₂ x; simp
  prop' := fun t z hz => by
      change F (DirectedSnd T t, z) = F (T, z)
      have : F (T, z) = _ := (F.prop' T z hz)
      rw [this]
      exact (F.prop' _ z hz)

lemma spv_apply {x y : X} {γ₁ γ₂ : Dipath x y} (F : Dipath.Dihomotopy γ₁ γ₂) (T s t : I) :
    SecondPartVerticallyDihomotopy F T (s, t) = F (⟨_, interp_left_mem_I T s⟩, t) := by
  change F (DirectedSnd T s, t) = F (_, t)
  rw [directedSnd_apply]

/-- The first part of a dihomotopy split horizontally at `T`: a dihomotopy between the first parts
of `f` and `g` as dipaths. -/
def FirstPartHorizontallyDihomotopy {f g : D(I,X)} (F : Dihomotopy f g) (T : I) :
    Dihomotopy (SplitDipath.FirstPart (Dipath.of_directedMap f) T).toDirectedMap
               (SplitDipath.FirstPart (Dipath.of_directedMap g) T).toDirectedMap where
  toDirectedMap
      := F.toDirectedMap.comp (DirectedMap.prod_map_mk' (DirectedMap.id I) (DirectedFst T))
  map_zero_left := fun x => by
    change F (0, DirectedFst T x) = SplitDipath.FirstPart (Dipath.of_directedMap f) T x
    simp
    rfl
  map_one_left := fun x => by
    change F (1, DirectedFst T x) = SplitDipath.FirstPart (Dipath.of_directedMap g) T x
    simp
    rfl


lemma fph_apply {f g : D(I,X)} (F : Dihomotopy f g) (T s t : I) :
    FirstPartHorizontallyDihomotopy F T (s, t) = F (s, T * t) := by
  change F (s, DirectedFst T t) = F (s, _)
  rw [directedFst_apply]
  rfl

/-- The second part of a dihomotopy split horizontally at `T`: a dihomotopy between the second
parts of `f` and `g` as dipaths. -/
def SecondPartHorizontallyDihomotopy {f g : D(I,X)} (F : Dihomotopy f g) (T : I) :
    Dihomotopy (SplitDipath.SecondPart (Dipath.of_directedMap f) T).toDirectedMap
               (SplitDipath.SecondPart (Dipath.of_directedMap g) T).toDirectedMap where
  toDirectedMap
      := F.toDirectedMap.comp (DirectedMap.prod_map_mk' (DirectedMap.id I) (DirectedSnd T))
  map_zero_left := fun x => by
    change F (0, DirectedSnd T x) = SplitDipath.SecondPart (Dipath.of_directedMap f) T x
    simp
    rfl
  map_one_left := fun x => by
    change F (1, DirectedSnd T x) = SplitDipath.SecondPart (Dipath.of_directedMap g) T x
    simp
    rfl

lemma sph_apply {f g : D(I,X)} (F : Dihomotopy f g) (T s t : I) :
    SecondPartHorizontallyDihomotopy F T (s, t) = F (s, ⟨_, interp_left_mem_I T t⟩) := by
  change F (s, DirectedSnd T t) = F (s, _)
  rw [directedSnd_apply]

lemma fph_eval_0 {f g : D(I,X)} (F : Dihomotopy f g) (T : I) :
    (FirstPartHorizontallyDihomotopy F T).eval_at_right 0 = (F.eval_at_right 0).cast (by simp)
        (by simp) := by
  ext t
  change F (t, DirectedFst T 0) = F (t, 0)
  simp

lemma fph_eval_1 {f g : D(I,X)} (F : Dihomotopy f g) (T : I) :
    (FirstPartHorizontallyDihomotopy F T).eval_at_right 1 =
      (F.eval_at_right T).cast (by { simp; rfl }) (by { simp; rfl }) := by
  ext t
  change F (t, DirectedFst T 1) = F (t, T)
  simp

lemma sph_eval_0 {f g : D(I,X)} (F : Dihomotopy f g) (T : I) :
    (SecondPartHorizontallyDihomotopy F T).eval_at_right 0 =
      (F.eval_at_right T).cast (by { simp; rfl }) (by { simp; rfl }) := by
  ext t
  change F (t, DirectedSnd T 0) = F (t, T)
  simp

lemma sph_eval_1 {f g : D(I,X)} (F : Dihomotopy f g) (T : I) :
    (SecondPartHorizontallyDihomotopy F T).eval_at_right 1 = (F.eval_at_right 1).cast (by simp)
        (by simp) := by
  ext t
  change F (t, DirectedSnd T 1) = F (t, 1)
  simp

end SplitDihomotopy
