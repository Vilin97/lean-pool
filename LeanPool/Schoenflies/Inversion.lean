/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Accessible
public import LeanPool.Schoenflies.Jordan
public import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Inversion in the unit circle, and the density of strongly accessible points

Two consequences of the Jordan curve theorem which have nothing to do with one another beyond
becoming available at the same moment.

## Inversion exchanges the two sides

Inversion about the unit circle centred at `a`,

    I_a(x) = a + (x - a) / ‖x - a‖²,

is the device that turns the *bounded* Schönflies theorem into the unbounded one: it swaps the
two sides of a Jordan curve `C` around any interior point `a`, sending the exterior of `C` onto
the interior of `C^a = I_a(C)` punctured at `a`. So a closed-interior extension for `C^a`,
pushed back through `I_a`, is a closed-*exterior* extension for `C`, which is
`prop:exterior-extension` and the second half of `thm:main`.

The map is Mathlib's `EuclideanGeometry.inversion a 1`, repackaged here as `Schoenflies.invert`
with the three facts the geometry needs: `Schoenflies.dist_invert_center`
(`‖I_a(x) - a‖ = 1/‖x - a‖`), `Schoenflies.invert_involutive`, and continuity away from `a`.
`Schoenflies.invertHomeo` bundles it as a self-homeomorphism of the punctured plane, which is
the form the conjugation `I_b ∘ f ∘ I_a` of `prop:exterior-extension` will want.

The proof of `lem:inversion-sides` is the blueprint's. Put `U = I_a(Ext C) ∪ {a}`. It is

* *open*: away from `a` because `I_a` is a homeomorphism of the punctured plane, and at `a`
  because `C ∪ Int(C)` is bounded, so the complement of a large closed ball `B(a, R)` lies in
  `Ext(C)` and inverts onto `B(a, 1/R) ∖ {a}`;
* *bounded*: a ball `B(a, δ)` lies in `Int(C)`, so exterior points stay at distance `≥ δ` from
  `a` and their inverses at distance `≤ 1/δ`;
* *connected*: the continuous image of `Ext(C)`, together with `a`, which is a limit of it
  because `Ext(C)` is unbounded;
* *bounded by `C^a`*: the third region `I_a(Int(C) ∖ {a})` is open, so the frontier of `U` can
  only be `C^a`, and every point of `C^a` is in it because `C = ∂Ext(C)`.

Being open, connected and with frontier disjoint from `(C^a)ᶜ`, `U` is a component of `(C^a)ᶜ`
(`Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`); being bounded, it is
`Int(C^a)`.

## The closed-exterior extension

`prop:exterior-extension` is the short assembly that sits on top of it, stated parametrically
over `prop:pointed-extension`. `Schoenflies.PointedInteriorExtension` is that interface, written
out: the bounded theorem with a prescribed interior point. `Schoenflies/Endgame.lean` derives
it from the closed-interior extension together with `lem:square-point-mover`, and
`Schoenflies/JordanSchoenflies.lean` supplies the square-extension input.

The assembly needs a name for "restricts to a homeomorphism onto", since it composes four of
them; `Schoenflies.IsHomeoOn` is that, in the unbundled `Schoenflies.Plane.IsSquareMover`
style.

## Density of strongly accessible points

`lem:tangent-dense` is three lines on top of `thm:jordan` and `lem:nearest-strong`: a point of
`C` is a limit of points of the region because `C` is the region's frontier, and the nearest
point of `C` to such a point is strongly accessible and no further from `p` than twice the
distance we started with. It is stated here for either region, since nothing in the argument
distinguishes them.

Everything below inherits the standing hypothesis of `thm:jordan` on `main`,

    harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ

threaded verbatim through every statement that consumes
`Schoenflies.IsJordanCurve.isSeparating`. The two density statements, which are about an
abstract `IsSeparating` curve, do not need it.

## Blueprint

* `Schoenflies.invert` and its algebra — the map `I_a` of §"The closed exteriors".
* `Schoenflies.invertHomeo` — "`I_a` is an involutive homeomorphism of `ℝ² ∖ {a}`".
* `Schoenflies.IsJordanCurve.invert_image` — "`C^a` is a Jordan curve", the first sentence of
  the proof of `lem:inversion-sides`.
* `Schoenflies.invert_image_outside`, `Schoenflies.invert_image_outside_union_singleton`,
  `Schoenflies.invert_image_inside_diff`, `Schoenflies.invert_image_union_outside`,
  `Schoenflies.inversion_sides` — `lem:inversion-sides`.
* `Schoenflies.exists_stronglyAccessible_dist_lt`, `Schoenflies.tangent_dense`,
  `Schoenflies.tangent_dense_inside` — `lem:tangent-dense`.
* `Schoenflies.PointedInteriorExtension` — the `prop:pointed-extension` interface, discharged
  by `Schoenflies.pointed_extension` in `Schoenflies/Endgame.lean`.
* `Schoenflies.exterior_extension` — `prop:exterior-extension`, parametrically on that interface.
* `Schoenflies.IsHomeoOn` — no blueprint statement; the language "restricts to a homeomorphism
  of `S` onto `T`" that `prop:exterior-extension` is phrased in.
-/

@[expose] public section

open Bornology Metric Set

namespace Schoenflies

variable {C Ω : Set Plane} {a p x y : Plane} {ε : ℝ}

/-! ### Inversion about the unit circle centred at a point

`Schoenflies.invert a` is `EuclideanGeometry.inversion a 1`, which Mathlib defines for every
point including the centre, sending `a` to itself. That convention is what makes
`Schoenflies.invert_involutive` hypothesis-free, and it costs nothing: every statement below
that cares about the centre says so. -/

/-- Inversion about the unit circle centred at `a`: `I_a(x) = a + (x - a)/‖x - a‖²`, extended
by `I_a(a) = a` so that it is an involution of the whole plane. -/
noncomputable def invert (a x : Plane) : Plane := EuclideanGeometry.inversion a 1 x

theorem invert_apply (a x : Plane) : invert a x = a + (‖x - a‖ ^ 2)⁻¹ • (x - a) := by
  unfold invert EuclideanGeometry.inversion
  rw [dist_eq_norm]
  simp [add_comm]

@[simp] theorem invert_center (a : Plane) : invert a a = a :=
  EuclideanGeometry.inversion_self a 1

/-- The defining metric identity: inversion inverts the distance to the centre. -/
theorem dist_invert_center (a x : Plane) : dist (invert a x) a = (dist x a)⁻¹ := by
  rw [invert, EuclideanGeometry.dist_inversion_center]
  simp

theorem invert_invert (a x : Plane) : invert a (invert a x) = x :=
  EuclideanGeometry.inversion_inversion a one_ne_zero x

theorem invert_involutive (a : Plane) : Function.Involutive (invert a) := invert_invert a

theorem invert_injective (a : Plane) : Function.Injective (invert a) :=
  (invert_involutive a).injective

/-- Being an involution, inversion has image and preimage the same operation. This is what
makes openness of an image as cheap as openness of a preimage. -/
theorem invert_image_eq_preimage (a : Plane) (S : Set Plane) :
    invert a '' S = invert a ⁻¹' S :=
  congrFun (invert_involutive a).image_eq_preimage_symm S

@[simp] theorem invert_image_invert_image (a : Plane) (S : Set Plane) :
    invert a '' (invert a '' S) = S := by
  simp [← Set.image_comp, invert_invert]

theorem invert_eq_center_iff : invert a x = a ↔ x = a :=
  EuclideanGeometry.inversion_eq_center one_ne_zero

theorem invert_ne_center (h : x ≠ a) : invert a x ≠ a := fun hc => h (invert_eq_center_iff.1 hc)

theorem continuousAt_invert (h : x ≠ a) : ContinuousAt (invert a) x :=
  ContinuousAt.inversion continuousAt_const continuousAt_const continuousAt_id h

theorem continuousOn_invert (a : Plane) : ContinuousOn (invert a) ({a}ᶜ : Set Plane) :=
  fun _ hx => (continuousAt_invert (by simpa using hx)).continuousWithinAt

/-- An open set missing the centre has open image: on the punctured plane, which is itself
open, inversion is a continuous involution, so the image is a preimage. -/
theorem isOpen_invert_image {S : Set Plane} (hS : IsOpen S) (ha : a ∉ S) :
    IsOpen (invert a '' S) := by
  rw [invert_image_eq_preimage]
  refine (continuousOn_invert a).isOpen_preimage isOpen_compl_singleton ?_ hS
  intro z hz
  simp only [mem_compl_iff, mem_singleton_iff]
  rintro rfl
  exact ha (by simpa using hz)

/-- "`I_a` is an involutive homeomorphism of `ℝ² ∖ {a}`", bundled. Its inverse is itself. -/
@[simps! -isSimp apply]
noncomputable def invertHomeo (a : Plane) : ({a}ᶜ : Set Plane) ≃ₜ ({a}ᶜ : Set Plane) where
  toFun z := ⟨invert a z, fun h =>
    z.2 (mem_singleton_iff.2 (invert_eq_center_iff.1 (mem_singleton_iff.1 h)))⟩
  invFun z := ⟨invert a z, fun h =>
    z.2 (mem_singleton_iff.2 (invert_eq_center_iff.1 (mem_singleton_iff.1 h)))⟩
  left_inv z := Subtype.ext (invert_invert a z)
  right_inv z := Subtype.ext (invert_invert a z)
  continuous_toFun := ((continuousOn_invert a).domRestrict).subtype_mk _
  continuous_invFun := ((continuousOn_invert a).domRestrict).subtype_mk _

/-! ### The image of a Jordan curve

Inversion is a homeomorphism on a neighbourhood of a curve avoiding the centre, so it carries
loops to loops. -/

/-- The first sentence of the proof of `lem:inversion-sides`: `C^a = I_a(C)` is a Jordan
curve. -/
theorem IsJordanCurve.invert_image (hC : IsJordanCurve C) (ha : a ∉ C) :
    IsJordanCurve (invert a '' C) := by
  obtain ⟨f, hf, rfl⟩ := hC
  have hmaps : MapsTo f unitInterval ({a}ᶜ : Set Plane) := by
    intro t ht
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact ha ⟨t, ht, rfl⟩
  refine ⟨invert a ∘ f, ⟨(continuousOn_invert a).comp hf.continuousOn hmaps, ?_, ?_⟩, ?_⟩
  · simp only [Function.comp_apply, hf.closes]
  · exact ((invert_injective a).injOn).comp hf.injOn (mapsTo_univ _ _)
  · rw [Set.image_comp]

/-! ### Inversion exchanges the two sides

The whole of `lem:inversion-sides`. The proof is carried in one theorem, because every step
speaks about the same set `U = I_a(Ext C) ∪ {a}`; the consequences that consumers want are
peeled off afterwards. -/

/-- Everything beyond a large enough closed ball about any point is exterior to a separating
curve: the curve and its interior together are bounded. -/
theorem exists_radius_compl_closedBall_subset_outside (hC : IsSeparating C) (a : Plane) :
    ∃ R > 0, (closedBall a R)ᶜ ⊆ outside C := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall a).1
    (hC.isJordanCurve.isCompact.isBounded.union hC.isBounded_inside)
  refine ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
  have hz' : z ∉ C ∪ inside C := fun h =>
    hz (closedBall_subset_closedBall (le_max_left _ _) (hr h))
  have hzc : z ∈ inside C ∪ outside C := by
    rw [inside_union_outside]
    exact fun h => hz' (Or.inl h)
  exact hzc.resolve_left fun h => hz' (Or.inr h)

/-- **`lem:inversion-sides`.** For `a` interior to the Jordan curve `C`, the image of the
exterior of `C` under inversion about `a`, *together with the centre*, is exactly the interior
of `C^a = I_a(C)`.

This is the form the proof produces; `Schoenflies.invert_image_outside` is the blueprint's
statement, obtained by removing `a` from both sides. -/
theorem invert_image_outside_union_singleton
    (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' outside C ∪ {a} = inside (invert a '' C) := by
  have hsep : IsSeparating C := hC.isSeparating harc
  have haC : a ∉ C := ha.1
  have haout : a ∉ outside C := Set.disjoint_left.1 disjoint_inside_outside ha
  have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact haout hz
  -- The three ingredients: a big radius `R`, a small radius `δ`, and the openness of the image.
  obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
  obtain ⟨δ, hδ, hδin⟩ := Metric.isOpen_iff.1 hsep.isOpen_inside a ha
  have hTopen : IsOpen (invert a '' outside C) :=
    isOpen_invert_image hsep.isOpen_outside haout
  -- Exterior points keep their distance from `a`, since a whole ball about `a` is interior.
  have hfar : ∀ z ∈ outside C, δ ≤ dist z a := by
    intro z hz
    by_contra h
    push Not at h
    exact Set.disjoint_left.1 disjoint_inside_outside (hδin (mem_ball.2 h)) hz
  -- (1) `U` is bounded, by `1/δ`.
  have hUbdd : IsBounded (invert a '' outside C ∪ {a}) := by
    refine (isBounded_iff_subset_closedBall a).2 ⟨δ⁻¹, ?_⟩
    rintro z (⟨w, hw, rfl⟩ | rfl)
    · rw [mem_closedBall, dist_invert_center]
      exact inv_anti₀ hδ (hfar w hw)
    · simpa using inv_nonneg.2 hδ.le
  -- (2) `U` is open: it contains the ball `B(a, 1/R)`, whose inverse image is beyond `B(a,R)`.
  have hUball : ball a R⁻¹ ⊆ invert a '' outside C ∪ {a} := by
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · exact Or.inr rfl
    · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
      have hpos : 0 < dist z a := dist_pos.2 hza
      rw [mem_compl_iff, mem_closedBall, dist_invert_center]
      exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
  have hUopen : IsOpen (invert a '' outside C ∪ {a}) := by
    have hrw : invert a '' outside C ∪ {a} = invert a '' outside C ∪ ball a R⁻¹ := by
      refine Subset.antisymm (union_subset subset_union_left ?_)
        (union_subset subset_union_left hUball)
      rintro z rfl
      exact Or.inr (mem_ball_self (by positivity))
    rw [hrw]
    exact hTopen.union isOpen_ball
  -- (3) `U` is connected: `a` is a limit of the image of the (unbounded) exterior.
  have hacl : a ∈ closure (invert a '' outside C) := by
    rw [Metric.mem_closure_iff]
    intro e he
    obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_isBounded_outside
        ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
    refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
    rw [dist_comm, dist_invert_center]
    exact inv_lt_of_inv_lt₀ he hzfar
  have hUconn : IsPreconnected (invert a '' outside C ∪ {a}) :=
    (hsep.isConnected_outside.image _
      ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (by rintro z rfl; exact hacl))
  -- (4) `U` misses `C^a`, since inversion is injective and `a` is not on `C`.
  have hUD : invert a '' outside C ∪ {a} ⊆ (invert a '' C)ᶜ := by
    rintro z (⟨w, hw, rfl⟩ | rfl)
    · rintro ⟨u, hu, huw⟩
      exact hw.1 (invert_injective a huw ▸ hu)
    · rintro ⟨u, hu, hua⟩
      exact haC (invert_eq_center_iff.1 hua ▸ hu)
  -- (5) The third region: the image of the punctured interior is open, and misses `U`.
  have hAopen : IsOpen (invert a '' (inside C \ {a})) :=
    isOpen_invert_image (hsep.isOpen_inside.sdiff isClosed_singleton) (fun h => h.2 rfl)
  have hAU : Disjoint (invert a '' (inside C \ {a})) (invert a '' outside C ∪ {a}) := by
    rw [Set.disjoint_left]
    rintro z ⟨w, ⟨hwin, hwne⟩, rfl⟩ (⟨u, hu, huw⟩ | hza)
    · exact Set.disjoint_left.1 disjoint_inside_outside hwin (invert_injective a huw ▸ hu)
    · exact hwne (mem_singleton_iff.2
        (invert_eq_center_iff.1 (mem_singleton_iff.1 hza)))
  -- The complement of `U` is covered by `C^a` and that third region.
  have hcompl : (invert a '' outside C ∪ {a})ᶜ ⊆
      invert a '' C ∪ invert a '' (inside C \ {a}) := by
    intro z hz
    by_cases hzC : invert a z ∈ C
    · exact Or.inl ⟨invert a z, hzC, invert_invert a z⟩
    · have hmem : invert a z ∈ inside C ∪ outside C := by
        rw [inside_union_outside]; exact hzC
      rcases hmem with hin | hout
      · refine Or.inr ⟨invert a z, ⟨hin, ?_⟩, invert_invert a z⟩
        intro hsing
        have hza : z = a := by
          rw [← invert_invert a z, mem_singleton_iff.1 hsing, invert_center]
        exact hz (Set.mem_union_right _ (mem_singleton_iff.2 hza))
      · exact absurd (show z ∈ invert a '' outside C ∪ {a} from
          Or.inl ⟨invert a z, hout, invert_invert a z⟩) hz
  -- (6) Hence the frontier of `U` is exactly `C^a`.
  have hfrontier : frontier (invert a '' outside C ∪ {a}) = invert a '' C := by
    refine Subset.antisymm (fun z hz => ?_) ?_
    · have hzU : z ∉ invert a '' outside C ∪ {a} := by
        rw [hUopen.frontier_eq] at hz; exact hz.2
      refine (hcompl hzU).resolve_right fun hA => ?_
      exact Set.disjoint_left.1 (hAU.closure_right hAopen) hA (frontier_subset_closure hz)
    · rintro z ⟨w, hwC, rfl⟩
      have hwne : w ≠ a := fun h => haC (h ▸ hwC)
      rw [hUopen.frontier_eq]
      refine ⟨closure_mono subset_union_left
        (mem_closure_image (continuousAt_invert hwne) ?_), fun hmem => hUD hmem ⟨w, hwC, rfl⟩⟩
      rw [← hsep.frontier_outside] at hwC
      exact frontier_subset_closure hwC
  -- (7) `U` is a component of the complement of `C^a`, and it is bounded, so it is the inside.
  have hsepa : IsSeparating (invert a '' C) := (hC.invert_image haC).isSeparating harc
  have haU : a ∈ invert a '' outside C ∪ {a} := Or.inr rfl
  have hcomp : connectedComponentIn (invert a '' C)ᶜ a = invert a '' outside C ∪ {a} :=
    Plane.connectedComponentIn_eq_of_frontier_disjoint hUopen hUconn hUD
      (by rw [hfrontier]; exact Set.inter_compl_self _) haU
  have hain : a ∈ inside (invert a '' C) := ⟨hUD haU, by rw [hcomp]; exact hUbdd⟩
  exact hcomp.symm.trans (hsepa.connectedComponentIn_eq_inside hain)

/-- The centre is never on `C^a`, since it is not on `C`. -/
theorem notMem_invert_image (ha : a ∉ C) : a ∉ invert a '' C := by
  rintro ⟨w, hw, hwa⟩
  exact ha (invert_eq_center_iff.1 hwa ▸ hw)

/-- **`lem:inversion-sides`**, the blueprint's statement:
`I_a(Ext(C)) = Int(C^a) ∖ {a}`. -/
theorem invert_image_outside (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' outside C = inside (invert a '' C) \ {a} := by
  rw [← invert_image_outside_union_singleton harc hC ha]
  refine (Set.union_sdiff_cancel_right ?_).symm
  rintro z ⟨⟨w, hw, rfl⟩, hza⟩
  exact Set.disjoint_left.1 disjoint_inside_outside ha
    (invert_eq_center_iff.1 (mem_singleton_iff.1 hza) ▸ hw)

/-- The other half of the exchange: the punctured *interior* of `C` inverts onto the *exterior*
of `C^a`. Not used by `prop:exterior-extension`, but it is what makes the name of the lemma
true. -/
theorem invert_image_inside_diff (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' (inside C \ {a}) = outside (invert a '' C) := by
  have haC : a ∉ C := ha.1
  have haout : a ∉ outside C := Set.disjoint_left.1 disjoint_inside_outside ha
  have hins := invert_image_outside_union_singleton harc hC ha
  -- Membership in the outside of `C^a` is "off the curve and off the inside".
  have hout : ∀ z : Plane, z ∈ outside (invert a '' C) ↔
      z ∉ invert a '' C ∧ z ∉ inside (invert a '' C) := by
    intro z
    constructor
    · intro hz
      exact ⟨hz.1, Set.disjoint_left.1 disjoint_inside_outside.symm hz⟩
    · rintro ⟨h1, h2⟩
      have hmem : z ∈ inside (invert a '' C) ∪ outside (invert a '' C) := by
        rw [inside_union_outside]; exact h1
      exact hmem.resolve_left h2
  ext z
  rw [hout z]
  constructor
  · rintro ⟨w, ⟨hwin, hwne⟩, rfl⟩
    refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · obtain ⟨u, hu, huw⟩ := hmem
      exact hwin.1 (invert_injective a huw ▸ hu)
    · rw [← hins] at hmem
      rcases hmem with ⟨u, hu, huw⟩ | hza
      · exact Set.disjoint_left.1 disjoint_inside_outside hwin (invert_injective a huw ▸ hu)
      · exact hwne (mem_singleton_iff.2 (invert_eq_center_iff.1 (mem_singleton_iff.1 hza)))
  · rintro ⟨h1, h2⟩
    refine ⟨invert a z, ⟨?_, ?_⟩, invert_invert a z⟩
    · -- `I_a z` is not on `C`, else `z` would be on `C^a`; not exterior, else `z` in `Int(C^a)`.
      have hzC : invert a z ∉ C := fun h => h1 ⟨invert a z, h, invert_invert a z⟩
      have hzout : invert a z ∉ outside C := fun h => h2 (by
        rw [← hins]; exact Set.mem_union_left _ ⟨invert a z, h, invert_invert a z⟩)
      have : invert a z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hzC
      exact this.resolve_right hzout
    · intro hsing
      exact h2 (by
        rw [← hins]
        refine Set.mem_union_right _ (mem_singleton_iff.2 ?_)
        rw [← invert_invert a z, mem_singleton_iff.1 hsing, invert_center])

/-- The closed-exterior form of `lem:inversion-sides`: inversion carries `C ∪ Ext(C)` onto
`(C^a ∪ Int(C^a)) ∖ {a}`. -/
theorem invert_image_union_outside (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' (C ∪ outside C) =
      (invert a '' C ∪ inside (invert a '' C)) \ {a} := by
  rw [Set.image_union, invert_image_outside harc hC ha, Set.union_sdiff_distrib,
    Set.sdiff_singleton_eq_self (notMem_invert_image ha.1)]

/-- **`lem:inversion-sides`, bundled.** `C^a` is a Jordan curve, inversion carries the exterior
of `C` onto the punctured interior of `C^a`, and it *restricts to a homeomorphism* from
`C ∪ Ext(C)` onto `(C^a ∪ Int(C^a)) ∖ {a}`: it is injective and continuous on the source, its
image is the target, and — being an involution — it is its own inverse there, continuous as
well. -/
theorem inversion_sides (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    IsJordanCurve (invert a '' C) ∧
      invert a '' outside C = inside (invert a '' C) \ {a} ∧
      invert a '' (C ∪ outside C) = (invert a '' C ∪ inside (invert a '' C)) \ {a} ∧
      invert a '' ((invert a '' C ∪ inside (invert a '' C)) \ {a}) = C ∪ outside C ∧
      InjOn (invert a) (C ∪ outside C) ∧
      ContinuousOn (invert a) (C ∪ outside C) ∧
      ContinuousOn (invert a) ((invert a '' C ∪ inside (invert a '' C)) \ {a}) := by
  have haC : a ∉ C := ha.1
  have haout : a ∉ outside C := Set.disjoint_left.1 disjoint_inside_outside ha
  have himg := invert_image_union_outside harc hC ha
  have hsrc : C ∪ outside C ⊆ ({a}ᶜ : Set Plane) := by
    rintro z (hz | hz) <;> · simp only [mem_compl_iff, mem_singleton_iff]
                             rintro rfl
                             exact absurd hz (by assumption)
  refine ⟨hC.invert_image haC, invert_image_outside harc hC ha, himg, ?_,
    (invert_injective a).injOn, (continuousOn_invert a).mono hsrc,
    (continuousOn_invert a).mono ?_⟩
  · rw [← himg, invert_image_invert_image]
  · intro z hz
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact hz.2 rfl

/-- The centre of the inversion is interior to the inverted curve. -/
theorem mem_inside_invert_image (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) : a ∈ inside (invert a '' C) := by
  rw [← invert_image_outside_union_singleton harc hC ha]
  exact Or.inr rfl

/-! ### Homeomorphisms between subsets of the plane

`prop:exterior-extension` is a composition of four restricted homeomorphisms, so it needs a
name for "`f` restricts to a homeomorphism of `S` onto `T`". `Schoenflies.IsHomeoOn` is that
name, written the way `Schoenflies.Plane.IsSquareMover` writes the same thing: unbundled, with
the inverse named, so that composing two of them composes two honest functions `Plane → Plane`
instead of producing a subtype-valued `Homeomorph` that must be unwrapped at every use.

**This notion is general and belongs in a lower module.** It is here because
`prop:exterior-extension` is the first statement that needs it; the integrator should hoist it
(and check that no concurrent branch introduced a twin). -/

/-- `IsHomeoOn f g S T`: the maps `f` and `g` restrict to mutually inverse continuous
bijections between `S` and `T`. -/
structure IsHomeoOn (f g : Plane → Plane) (S T : Set Plane) : Prop where
  /-- `f` carries `S` into `T` -/
  mapsTo : MapsTo f S T
  /-- `g` carries `T` into `S` -/
  mapsTo_inv : MapsTo g T S
  /-- `f` is continuous on `S` -/
  continuousOn : ContinuousOn f S
  /-- `g` is continuous on `T` -/
  continuousOn_inv : ContinuousOn g T
  /-- the two are mutually inverse there -/
  invOn : InvOn g f S T

namespace IsHomeoOn

variable {f g f' g' : Plane → Plane} {S T U S' T' : Set Plane}

theorem symm (h : IsHomeoOn f g S T) : IsHomeoOn g f T S where
  mapsTo := h.mapsTo_inv
  mapsTo_inv := h.mapsTo
  continuousOn := h.continuousOn_inv
  continuousOn_inv := h.continuousOn
  invOn := h.invOn.symm

theorem bijOn (h : IsHomeoOn f g S T) : BijOn f S T :=
  h.invOn.bijOn h.mapsTo h.mapsTo_inv

theorem injOn (h : IsHomeoOn f g S T) : InjOn f S := h.bijOn.injOn

theorem image_eq (h : IsHomeoOn f g S T) : f '' S = T := h.bijOn.image_eq

/-- Composing two restricted homeomorphisms. -/
theorem comp (h : IsHomeoOn f g S T) (h' : IsHomeoOn f' g' T U) :
    IsHomeoOn (f' ∘ f) (g ∘ g') S U where
  mapsTo := h'.mapsTo.comp h.mapsTo
  mapsTo_inv := h.mapsTo_inv.comp h'.mapsTo_inv
  continuousOn := h'.continuousOn.comp h.continuousOn h.mapsTo
  continuousOn_inv := h.continuousOn_inv.comp h'.continuousOn_inv h'.mapsTo_inv
  invOn := h.invOn.comp h'.invOn h.mapsTo h'.mapsTo_inv

/-- Restricting to a smaller pair of sets, once the two `MapsTo` clauses are known there. -/
theorem mono (h : IsHomeoOn f g S T) (hS : S' ⊆ S) (hT : T' ⊆ T) (hf : MapsTo f S' T')
    (hg : MapsTo g T' S') : IsHomeoOn f g S' T' where
  mapsTo := hf
  mapsTo_inv := hg
  continuousOn := h.continuousOn.mono hS
  continuousOn_inv := h.continuousOn_inv.mono hT
  invOn := h.invOn.mono hS hT

/-- Deleting a matched pair of points. This is the step "`Φ*` restricts to a homeomorphism
after the two points `a, b` are removed" of `prop:exterior-extension`. -/
theorem sdiff_singleton (h : IsHomeoOn f g S T) {u v : Plane} (hu : u ∈ S) (huv : f u = v) :
    IsHomeoOn f g (S \ {u}) (T \ {v}) := by
  refine h.mono Set.sdiff_subset Set.sdiff_subset (fun z hz => ⟨h.mapsTo hz.1, ?_⟩)
    (fun w hw => ⟨h.mapsTo_inv hw.1, ?_⟩)
  · -- `f z = v = f u` would force `z = u` by injectivity.
    intro hmem
    exact hz.2 (mem_singleton_iff.2
      (h.injOn hz.1 hu ((mem_singleton_iff.1 hmem).trans huv.symm)))
  · -- `g w = u` would force `w = f u = v`.
    intro hmem
    refine hw.2 (mem_singleton_iff.2 ?_)
    rw [← huv, ← mem_singleton_iff.1 hmem, h.invOn.2 hw.1]

end IsHomeoOn

/-- Inversion restricts to a homeomorphism of any set missing the centre onto its image. -/
theorem isHomeoOn_invert {S : Set Plane} (ha : a ∉ S) :
    IsHomeoOn (invert a) (invert a) S (invert a '' S) where
  mapsTo := Set.mapsTo_image _ _
  mapsTo_inv := by
    rintro z ⟨w, hw, rfl⟩
    rwa [invert_invert]
  continuousOn := (continuousOn_invert a).mono (Set.subset_compl_singleton_iff.2 ha)
  continuousOn_inv := (continuousOn_invert a).mono
    (Set.subset_compl_singleton_iff.2 (notMem_invert_image ha))
  invOn := ⟨fun z _ => invert_invert a z, fun z _ => invert_invert a z⟩

/-! ### The closed-exterior extension

`prop:exterior-extension`, assuming `prop:pointed-extension`. That is the blueprint's own
citation, and it is the one statement of the endgame that is not yet available: it rests on
`thm:closed-interior-extension` (open) together with `lem:square-point-mover`
(`Schoenflies.Plane.exists_squareMover`, on `main`) and `lem:jordan-circle`
(`Schoenflies.IsJordanCurve.homeomorph`, on `main`).

Everything that inversion contributes is here; discharging
`Schoenflies.PointedInteriorExtension` finishes the exterior half of `thm:main`. -/

/-- **`prop:pointed-extension`**, as a hypothesis: a boundary homeomorphism between two Jordan
curves extends to a homeomorphism of the closed interiors carrying one prescribed interior
point to another.

This is *not* a restatement of `prop:exterior-extension`: it is about the two **interiors**,
which is the bounded theorem, and it is what the blueprint proves from
`thm:closed-interior-extension` and `lem:square-point-mover`. -/
def PointedInteriorExtension : Prop :=
  ∀ (C C' : Set Plane) (f g : Plane → Plane) (a b : Plane),
    IsJordanCurve C → IsJordanCurve C' → IsHomeoOn f g C C' → a ∈ inside C → b ∈ inside C' →
      ∃ F G : Plane → Plane,
        IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C ∧ F a = b

/-- **`prop:exterior-extension` (closed-exterior extension).** Every homeomorphism between two
Jordan curves extends to a homeomorphism of their closed exteriors.

Assumes `prop:pointed-extension` (`Schoenflies.PointedInteriorExtension`) and the standing
hypothesis `harc` of `thm:jordan`. The proof is the blueprint's: choose `a ∈ Int(C)` and
`b ∈ Int(C')`, invert about each, extend the conjugated boundary map `I_b ∘ f ∘ I_a` over the
interior of `C^a` so that `a ↦ b`, delete the two centres, and conjugate back — the deleted
punctured closed interiors being exactly the closed exteriors, by `lem:inversion-sides`. -/
theorem exterior_extension (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hpt : PointedInteriorExtension) {C C' : Set Plane} {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C') ∧ EqOn F f C := by
  -- Two interior points, from `thm:jordan`.
  obtain ⟨a, ha⟩ := (hC.isSeparating harc).isConnected_inside.nonempty
  obtain ⟨b, hb⟩ := (hC'.isSeparating harc).isConnected_inside.nonempty
  have haC : a ∉ C := ha.1
  have hbC' : b ∉ C' := hb.1
  -- Inversion, on the curves alone …
  have hIa : IsHomeoOn (invert a) (invert a) C (invert a '' C) := isHomeoOn_invert haC
  have hIb : IsHomeoOn (invert b) (invert b) C' (invert b '' C') := isHomeoOn_invert hbC'
  -- … and on the closed exteriors, which is `lem:inversion-sides`.
  have haout : a ∉ C ∪ outside C := by
    rintro (h | h)
    · exact haC h
    · exact Set.disjoint_left.1 disjoint_inside_outside ha h
  have hbout : b ∉ C' ∪ outside C' := by
    rintro (h | h)
    · exact hbC' h
    · exact Set.disjoint_left.1 disjoint_inside_outside hb h
  have hEa : IsHomeoOn (invert a) (invert a) (C ∪ outside C)
      ((invert a '' C ∪ inside (invert a '' C)) \ {a}) := by
    rw [← invert_image_union_outside harc hC ha]
    exact isHomeoOn_invert haout
  have hEb : IsHomeoOn (invert b) (invert b) (C' ∪ outside C')
      ((invert b '' C' ∪ inside (invert b '' C')) \ {b}) := by
    rw [← invert_image_union_outside harc hC' hb]
    exact isHomeoOn_invert hbout
  -- The conjugated boundary homeomorphism `f* = I_b ∘ f ∘ I_a : C^a → (C')^b`.
  have hstar : IsHomeoOn (invert b ∘ f ∘ invert a) (invert a ∘ g ∘ invert b)
      (invert a '' C) (invert b '' C') := by
    have := (hIa.symm.comp hfg).comp hIb
    simpa [Function.comp_assoc] using this
  -- Extend it over the interior of `C^a`, sending `a` to `b`.
  obtain ⟨Φ, Ψ, hΦ, hΦeq, hΦa⟩ := hpt (invert a '' C) (invert b '' C') _ _ a b
    (hC.invert_image haC) (hC'.invert_image hbC') hstar
    (mem_inside_invert_image harc hC ha) (mem_inside_invert_image harc hC' hb)
  -- Delete the two centres, then conjugate back.
  have hΦ' := hΦ.sdiff_singleton
    (Set.mem_union_right _ (mem_inside_invert_image harc hC ha)) hΦa
  refine ⟨invert b ∘ Φ ∘ invert a, invert a ∘ Ψ ∘ invert b, ?_, ?_⟩
  · have := (hEa.comp hΦ').comp hEb.symm
    simpa [Function.comp_assoc] using this
  · -- On `C` the conjugate is `f`, because `I_a` and `I_b` are involutions.
    intro z hz
    have h1 : invert a z ∈ invert a '' C := ⟨z, hz, rfl⟩
    simp only [Function.comp_apply, hΦeq h1, invert_invert]

/-! ### Density of strongly accessible points

`lem:tangent-dense`. Nothing here distinguishes the two regions, so the lemma is proved for
either. The hypotheses are those of `Schoenflies.stronglyAccessible_of_isMinOn`: the region
swallows the component of each of its points, and the curve is in its closure — which for a
separating curve is `C = ∂Ω`. -/

/-- The core estimate. If `C` is compact and every point of `C` is a limit of points of `Ω`,
and `Ω` swallows the component in `Cᶜ` of each of its points, then near any `p ∈ C` there is a
strongly accessible point of `C`: pick `q ∈ Ω` within `ε/2` of `p`, and take the point of `C`
nearest to `q`; it is strongly accessible by `lem:nearest-strong` and within `2‖q - p‖` of
`p`. -/
theorem exists_stronglyAccessible_dist_lt (hCcpt : IsCompact C) (hCne : C.Nonempty)
    (hΩC : Ω ⊆ Cᶜ) (hΩmax : ∀ q ∈ Ω, connectedComponentIn Cᶜ q ⊆ Ω) (hCΩ : C ⊆ closure Ω)
    (hp : p ∈ C) (hε : 0 < ε) :
    ∃ b ∈ C, StronglyAccessible Ω b ∧ dist b p < ε := by
  obtain ⟨q, hqΩ, hqp⟩ := Metric.mem_closure_iff.1 (hCΩ hp) (ε / 2) (by linarith)
  -- A nearest point of `C` to `q`; `C` is compact and nonempty.
  obtain ⟨b, hbC, hbmin⟩ :=
    hCcpt.exists_isMinOn hCne (Continuous.continuousOn (continuous_const.dist continuous_id))
  have hmin : ∀ c ∈ C, dist q b ≤ dist q c := fun c hc => isMinOn_iff.1 hbmin c hc
  refine ⟨b, hbC, stronglyAccessible_of_isMinOn (hΩC hqΩ) hbC hmin (hΩmax q hqΩ), ?_⟩
  -- `‖b - p‖ ≤ ‖b - q‖ + ‖q - p‖ ≤ 2‖q - p‖ < ε`.
  have h1 : dist q b ≤ dist q p := hmin p hp
  have h2 : dist b p ≤ dist b q + dist q p := dist_triangle _ _ _
  rw [dist_comm q b] at h1
  rw [dist_comm p q] at hqp
  linarith

/-- **`lem:tangent-dense` (density of strongly accessible points)**, for either region of a
separating Jordan curve: the points of `C` strongly accessible from `Ω` are dense in `C`. -/
theorem tangent_dense (hC : IsSeparating C) (hΩ : IsRegionOf C Ω) :
    C ⊆ closure {b ∈ C | StronglyAccessible Ω b} := by
  intro p hp
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨b, hbC, hbacc, hbp⟩ := exists_stronglyAccessible_dist_lt
    hC.isJordanCurve.isCompact hC.isJordanCurve.nonempty hΩ.subset_compl
    (fun q hq => (hΩ.connectedComponentIn_eq hC hq).le) (hΩ.subset_closure hC) hp hε
  exact ⟨b, ⟨hbC, hbacc⟩, by rwa [dist_comm]⟩

/-- `lem:tangent-dense` in the blueprint's own setting, `D = Int(C)`. -/
theorem tangent_dense_inside (hC : IsSeparating C) :
    C ⊆ closure {b ∈ C | StronglyAccessible (inside C) b} :=
  tangent_dense hC (IsRegionOf.inside C)

/-- `lem:tangent-dense` for a Jordan curve, threading the standing hypothesis of
`thm:jordan`. -/
theorem IsJordanCurve.tangent_dense (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) :
    C ⊆ closure {b ∈ C | StronglyAccessible (inside C) b} :=
  tangent_dense_inside (hC.isSeparating harc)

end Schoenflies
