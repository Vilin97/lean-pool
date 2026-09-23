/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Inversion
public import LeanPool.Schoenflies.JordanClosed
public import LeanPool.Schoenflies.ModelCurve
public import LeanPool.Schoenflies.SquareMover
public import LeanPool.Schoenflies.Topology

/-!
# The endgame: from the square extension to the relative Jordan–Schönflies theorem

This module carries the whole tail of the manuscript — `prop:square-reduction`,
`thm:closed-interior-extension`, `prop:pointed-extension`, `prop:exterior-extension` and
`thm:main` — parametrically over the square-extension interface.

Every theorem below takes `Schoenflies.SquareExtension` as an explicit hypothesis and assumes
nothing else. In particular the standing hypothesis `harc` that older modules thread is
discharged here at the call site, from `Schoenflies.arc_complement` in
`Schoenflies/JordanClosed.lean`; it no longer appears in any signature. The implication proved
by this module is

    SquareExtension  ⟹  thm:main.

`Schoenflies/JordanSchoenflies.lean` supplies `SquareExtension` from the quantitative
boundary construction and therefore closes this implication without an extra hypothesis.

## What `SquareExtension` says

`Schoenflies.SquareExtension` is `thm:square-extension` written in the `Schoenflies.IsHomeoOn`
style of `Schoenflies/Inversion.lean`: for every Jordan curve `C` and every restricted
homeomorphism `u : C → S` (with named inverse `v`) there are maps `F`, `G` restricting to
mutually inverse homeomorphisms between `C ∪ Int(C)` and `Q`, with `F = u` on `C`. Here
`S = Schoenflies.modelCurve` and `Q = Schoenflies.Plane.closedSquare 0 1`; `S = ∂Q` is
`Schoenflies.modelCurve_eq_frontier`, so this is literally the blueprint's `Q = [-1,1]²`,
`S = ∂Q`.

## The chain

* `prop:square-reduction` is the blueprint's: pick a homeomorphism `h : C' → S`
  (`lem:jordan-circle`), extend `h ∘ f` and `h` to the square, and compose one with the inverse
  of the other. `thm:closed-interior-extension` is the same statement — under the standing
  assumption of `SquareExtension` the reduction *is* the theorem — and is recorded separately
  because everything downstream cites it by that name.
* `prop:pointed-extension` is the interesting one. Given the closed-interior extension `Φ` and
  a square chart `Θ` of the *target* disc, the two points `Θ(Φ(a))` and `Θ(b)` are interior to
  `Q`, because `Θ` carries `C'` onto `∂Q` and hence — being a bijection — `Int(C')` onto
  `Q ∖ ∂Q`. `lem:square-point-mover` then supplies a boundary-fixing self-homeomorphism `M` of
  `Q` moving the first to the second, and `Θ⁻¹ ∘ M ∘ Θ ∘ Φ` is the pointed extension: it agrees
  with `Φ` on `C` because `M` fixes `∂Q` pointwise. This discharges
  `Schoenflies.PointedInteriorExtension`, the last hypothesis of `prop:exterior-extension`.
* `thm:main` is the closed pasting lemma applied twice, once to `F` and once to its inverse.
  The one point the blueprint leaves implicit is that the pasted map is *injective*: the
  interior extension carries `Int(C)` onto `Int(C')` and the exterior extension carries
  `Ext(C)` onto `Ext(C')`, so the two pieces cannot collide. Both facts are instances of
  `Schoenflies.image_eq_diff_of_bijOn_union`, which is the "a bijection matching one part of a
  partition matches the other part" principle.

## The parametric construction interface

Within this deliberately parametric module, every conclusion depends on the *Prop*
`SquareExtension`, so no `def` can produce the maps without an application of choice to that
hypothesis. What is exported as data independently of the interface is
`Schoenflies.paste` (the pasted map itself, with its two evaluation lemmas) and
`Schoenflies.IsHomeoOn.homeomorphOfUniv` (the passage from a global `IsHomeoOn` to a genuine
`Plane ≃ₜ Plane`). The theorems below return the maps in the unbundled `∃ F G, IsHomeoOn F G …`
shape of `Schoenflies.exterior_extension`, which composes.

## Blueprint

* `Schoenflies.SquareExtension` — the **`thm:square-extension`** interface, discharged in
  `Schoenflies/JordanSchoenflies.lean`.
* `Schoenflies.square_reduction` — `prop:square-reduction`.
* `Schoenflies.closed_interior_extension` — **`thm:closed-interior-extension`**.
* `Schoenflies.pointed_extension` — `prop:pointed-extension`; it proves
  `Schoenflies.PointedInteriorExtension` of `Schoenflies/Inversion.lean`.
* `Schoenflies.exterior_extension_of_squareExtension` — `prop:exterior-extension`, restated
  with `harc` discharged and only `SquareExtension` left.
* `Schoenflies.jordan_schoenflies_of_squareExtension`,
  `Schoenflies.jordan_schoenflies_homeomorph_of_squareExtension`,
  `Schoenflies.jordan_schoenflies_of_homeomorph_of_squareExtension` — **`thm:main`**, the relative
  Jordan–Schönflies theorem, in the unbundled, the bundled, and the blueprint's own shape.

Supporting material with no blueprint statement, all general and all candidates for hoisting
into the module that owns `Schoenflies.IsHomeoOn`:
`Schoenflies.exists_isHomeoOn_of_homeomorph`, `Schoenflies.IsHomeoOn.homeomorphOfUniv`,
`Schoenflies.IsHomeoOn.image_inv_eq`, `Schoenflies.image_eq_diff_of_bijOn_union`,
`Schoenflies.paste` and `Schoenflies.Plane.IsSquareMover.isHomeoOn`.
-/

@[expose] public section

open Bornology Metric Set

namespace Schoenflies

/-! ### Restricted homeomorphisms: three general tools

`Schoenflies.IsHomeoOn` (in `Schoenflies/Inversion.lean`) is the unbundled "restricts to a
homeomorphism of `S` onto `T`". Three facts about it are needed below and are not there; they
are general, and the section comment at `IsHomeoOn` already asks for the whole notion to be
hoisted, so these should travel with it. -/

/-- A `Homeomorph` between two subsets of the plane can always be presented as an
`IsHomeoOn` between honest self-maps of the plane: extend both by the identity.

This is the bridge from `lem:jordan-circle`, which produces `Nonempty (↥C ≃ₜ ↥S)`, to the
unbundled language everything downstream is written in. -/
theorem exists_isHomeoOn_of_homeomorph {S T : Set Plane} (e : ↥S ≃ₜ ↥T) :
    ∃ f g : Plane → Plane, IsHomeoOn f g S T ∧ ∀ (z : Plane) (hz : z ∈ S),
      f z = (e ⟨z, hz⟩ : Plane) := by
  classical
  refine ⟨fun z => if hz : z ∈ S then (e ⟨z, hz⟩ : Plane) else z,
    fun w => if hw : w ∈ T then (e.symm ⟨w, hw⟩ : Plane) else w,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun z hz => dite_eq_left hz⟩
  · exact fun z hz => by simp only [dite_eq_left hz]; exact (e ⟨z, hz⟩).2
  · exact fun w hw => by simp only [dite_eq_left hw]; exact (e.symm ⟨w, hw⟩).2
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : (S.domRestrict fun z => if hz : z ∈ S then (e ⟨z, hz⟩ : Plane) else z) =
        fun z : ↥S => (e z : Plane) := by
      funext z
      simp only [Set.domRestrict_apply, dite_eq_left z.2]
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : (T.domRestrict fun w => if hw : w ∈ T then (e.symm ⟨w, hw⟩ : Plane) else w) =
        fun w : ↥T => (e.symm w : Plane) := by
      funext w
      simp only [Set.domRestrict_apply, dite_eq_left w.2]
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  · intro z hz
    simp only [dite_eq_left hz, dite_eq_left (e ⟨z, hz⟩).2]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
  · intro w hw
    simp only [dite_eq_left hw, dite_eq_left (e.symm ⟨w, hw⟩).2]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)

namespace IsHomeoOn

variable {f g : Plane → Plane} {S T : Set Plane}

/-- A restricted homeomorphism of the whole plane onto the whole plane *is* a
homeomorphism. This is the last step of `thm:main`. -/
noncomputable def homeomorphOfUniv (h : IsHomeoOn f g univ univ) : Plane ≃ₜ Plane where
  toFun := f
  invFun := g
  left_inv z := h.invOn.1 (mem_univ z)
  right_inv z := h.invOn.2 (mem_univ z)
  continuous_toFun := continuousOn_univ.1 h.continuousOn
  continuous_invFun := continuousOn_univ.1 h.continuousOn_inv

@[simp] theorem homeomorphOfUniv_apply (h : IsHomeoOn f g univ univ) (z : Plane) :
    h.homeomorphOfUniv z = f z := rfl

/-- The inverse of a restricted homeomorphism undoes it on images: if `f` carries `A ⊆ S` onto
`A'`, then `g` carries `A'` back onto `A`. -/
theorem image_inv_eq (h : IsHomeoOn f g S T) {A A' : Set Plane} (hA : A ⊆ S)
    (hA' : f '' A = A') : g '' A' = A := by
  rw [← hA', Set.image_image]
  exact (Set.EqOn.image_eq (fun z hz => h.invOn.1 (hA hz))).trans (Set.image_id A)

end IsHomeoOn

/-- **Matching one part of a partition matches the other.** If `F` is a bijection of `A ∪ B`
onto `T` carrying the disjoint piece `A` onto `A'`, it carries `B` onto `T ∖ A'`.

Used three times below: `Θ` carries `Int(C')` onto `Q ∖ ∂Q`, and each of the interior and the
exterior extension carries a region onto the corresponding region — which is exactly what makes
the two pasted pieces of `thm:main` injective together. -/
theorem image_eq_diff_of_bijOn_union {F : Plane → Plane} {A B T A' : Set Plane}
    (hF : BijOn F (A ∪ B) T) (hA : F '' A = A') (hdisj : Disjoint A B) :
    F '' B = T \ A' := by
  refine Subset.antisymm ?_ ?_
  · rintro y ⟨z, hzB, rfl⟩
    refine ⟨hF.mapsTo (Or.inr hzB), fun hy => ?_⟩
    rw [← hA] at hy
    obtain ⟨w, hwA, hw⟩ := hy
    exact Set.disjoint_left.1 hdisj hwA (hF.injOn (Or.inl hwA) (Or.inr hzB) hw ▸ hzB)
  · rintro y ⟨hyT, hyA'⟩
    obtain ⟨z, hz, rfl⟩ := hF.surjOn hyT
    have hzB : z ∈ B := hz.resolve_left fun hzA => hyA' (by rw [← hA]; exact ⟨z, hzA, rfl⟩)
    exact ⟨z, hzB, rfl⟩

/-! ### The pasted map

`thm:main` glues the interior and the exterior extension. The glued map is `Set.piecewise`
under a different name, spelled so that the two evaluation lemmas below are the only interface
the proof needs. -/

open Classical in
/-- The map that is `f₁` on `S` and `f₂` off it. The blueprint's "defined by `F_int` on the
closed interior and by `F_ext` on the closed exterior". -/
noncomputable def paste (S : Set Plane) (f₁ f₂ : Plane → Plane) : Plane → Plane :=
  fun z => if z ∈ S then f₁ z else f₂ z

theorem paste_of_mem {S : Set Plane} {f₁ f₂ : Plane → Plane} {z : Plane} (hz : z ∈ S) :
    paste S f₁ f₂ z = f₁ z := by
  classical exact ite_eq_left hz

theorem paste_of_notMem {S : Set Plane} {f₁ f₂ : Plane → Plane} {z : Plane} (hz : z ∉ S) :
    paste S f₁ f₂ z = f₂ z := by
  classical exact ite_eq_right hz

/-! ### The square `Q` and its boundary `S`

The blueprint's `Q = [-1,1]²` is `Plane.closedSquare 0 1` and its boundary `S = ∂Q` is
`modelCurve`, by `modelCurve_eq_frontier`. One consequence is needed: removing the boundary
from the closed square leaves the open square, which is where `lem:square-point-mover` wants
its two points. -/

/-- `Q ∖ S = Q°`. -/
theorem closedSquare_sdiff_modelCurve :
    Plane.closedSquare 0 1 \ modelCurve = Plane.openSquare 0 1 := by
  rw [modelCurve_eq_frontier, Plane.frontier_closedSquare]
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 h2
  · intro h
    have h' : Plane.supDist z 0 < 1 := h
    exact ⟨h'.le, ne_of_lt h'⟩

/-- A mover of the square, read as a restricted homeomorphism. -/
theorem Plane.IsSquareMover.isHomeoOn {c : Plane} {r : ℝ} {M N : Plane → Plane}
    (h : Plane.IsSquareMover c r M N) :
    IsHomeoOn M N (Plane.closedSquare c r) (Plane.closedSquare c r) where
  mapsTo := h.mapsTo
  mapsTo_inv := h.mapsTo_inv
  continuousOn := h.continuousOn
  continuousOn_inv := h.continuousOn_inv
  invOn := h.invOn

/-! ### `thm:square-extension`, assumed

This is the one statement the module assumes, and the only thing standing between the library
and `thm:main`. It is the last big theorem of the manuscript; its proof occupies the whole of
Part II §§"Strongly accessible boundary points"–"Continuity at the Jordan curve". -/

/-- **`thm:square-extension` (square extension)**, as a hypothesis: for every Jordan curve `C`
and every homeomorphism `u : C → S` there is a homeomorphism `C ∪ Int(C) → Q` extending `u`.

Written in the unbundled `Schoenflies.IsHomeoOn` style: `u` comes with its inverse `v`, and the
conclusion produces the extension `F` together with its inverse `G`. `S` is
`Schoenflies.modelCurve` and `Q` is `Schoenflies.Plane.closedSquare 0 1`. -/
def SquareExtension : Prop :=
  ∀ (C : Set Plane) (u v : Plane → Plane), IsJordanCurve C → IsHomeoOn u v C modelCurve →
    ∃ F G : Plane → Plane,
      IsHomeoOn F G (C ∪ inside C) (Plane.closedSquare 0 1) ∧ EqOn F u C

/-! ### Disjointness of a curve from its two regions

A curve is disjoint from either of its two regions, and adding it and removing it again is the
identity. The pastings below use these constantly. -/

variable {C C' : Set Plane}

theorem disjoint_curve_inside (C : Set Plane) : Disjoint C (inside C) :=
  Set.disjoint_left.2 fun _ hzC hz => hz.1 hzC

theorem disjoint_curve_outside (C : Set Plane) : Disjoint C (outside C) :=
  Set.disjoint_left.2 fun _ hzC hz => hz.1 hzC

theorem union_inside_sdiff (C : Set Plane) : (C ∪ inside C) \ C = inside C :=
  Set.union_sdiff_cancel_left (Set.disjoint_iff_inter_eq_empty.1 (disjoint_curve_inside C)).le

theorem union_outside_sdiff (C : Set Plane) : (C ∪ outside C) \ C = outside C :=
  Set.union_sdiff_cancel_left (Set.disjoint_iff_inter_eq_empty.1 (disjoint_curve_outside C)).le

/-- An extension of a boundary homeomorphism to the closed interiors carries the interior onto
the interior. The blueprint never says this; the pointed extension and `thm:main` both need
it. -/
theorem image_inside_eq {F G f : Plane → Plane}
    (hF : IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C')) (hf : EqOn F f C) (hfC : f '' C = C') :
    F '' inside C = inside C' := by
  have hFC : F '' C = C' := (Set.EqOn.image_eq hf).trans hfC
  have := image_eq_diff_of_bijOn_union hF.bijOn hFC (disjoint_curve_inside C)
  rwa [union_inside_sdiff] at this

/-- The same for the closed exteriors. -/
theorem image_outside_eq {F G f : Plane → Plane}
    (hF : IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C')) (hf : EqOn F f C)
    (hfC : f '' C = C') : F '' outside C = outside C' := by
  have hFC : F '' C = C' := (Set.EqOn.image_eq hf).trans hfC
  have := image_eq_diff_of_bijOn_union hF.bijOn hFC (disjoint_curve_outside C)
  rwa [union_outside_sdiff] at this

/-! ### `prop:square-reduction` and `thm:closed-interior-extension`

The blueprint's proof verbatim: choose `h : C' → S` by `lem:jordan-circle`, extend `h ∘ f` and
`h` over the two closed discs by `thm:square-extension`, and take `Ψ⁻¹ ∘ Φ`. -/

/-- **`prop:square-reduction` (reduction to the square).** If every boundary homeomorphism from
a Jordan curve to `S` has a closed-interior extension, then every homeomorphism `f : C → C'`
between Jordan curves extends to a homeomorphism `C ∪ Int(C) → C' ∪ Int(C')`. -/
theorem square_reduction (hsq : SquareExtension) {f g : Plane → Plane} (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C := by
  obtain ⟨e⟩ := hC'.homeomorph_modelCurve
  obtain ⟨h, k, hhk, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨Φ, Φ', hΦ, hΦeq⟩ := hsq C (h ∘ f) (g ∘ k) hC (hfg.comp hhk)
  obtain ⟨Ψ, Ψ', hΨ, hΨeq⟩ := hsq C' h k hC' hhk
  refine ⟨Ψ' ∘ Φ, Φ' ∘ Ψ, hΦ.comp hΨ.symm, fun z hz => ?_⟩
  have h1 : f z ∈ C' := hfg.mapsTo hz
  change Ψ' (Φ z) = f z
  rw [hΦeq hz]
  change Ψ' (h (f z)) = f z
  rw [← hΨeq h1]
  exact hΨ.invOn.1 (Set.mem_union_left _ h1)

/-- **`thm:closed-interior-extension` (closed-interior extension).** Every homeomorphism
`f : C → C'` between Jordan curves extends to a homeomorphism of the closed interiors.

Under the standing assumption `SquareExtension` this is literally `prop:square-reduction`; it
is recorded under its own name because everything downstream cites it by that name. -/
theorem closed_interior_extension (hsq : SquareExtension) {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C :=
  square_reduction hsq hC hC' hfg

/-! ### `prop:pointed-extension`

The blueprint's proof, with one step made explicit: the square chart `Θ` of the *target* disc
carries `Int(C')` onto `Q ∖ ∂Q = Q°`, because it carries `C'` onto `∂Q` and is a bijection of
the closed disc onto `Q`. That is what puts the two points `Θ(Φ(a))` and `Θ(b)` in the open
square, where `lem:square-point-mover` lives. -/

/-- **`prop:pointed-extension` (pointed closed-interior extension).** A boundary homeomorphism
`f : C → C'` and prescribed points `a ∈ Int(C)`, `b ∈ Int(C')` admit a closed-interior
extension `H` with `H(a) = b`.

This is `Schoenflies.PointedInteriorExtension`, the hypothesis of
`Schoenflies.exterior_extension`, discharged. -/
theorem pointed_extension (hsq : SquareExtension) : PointedInteriorExtension := by
  intro C C' f g a b hC hC' hfg ha hb
  -- The unpointed extension, and a square chart of the target disc.
  obtain ⟨Φ, Φ', hΦ, hΦeq⟩ := square_reduction hsq hC hC' hfg
  obtain ⟨e⟩ := hC'.homeomorph_modelCurve
  obtain ⟨h, k, hhk, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨Θ, Θ', hΘ, hΘeq⟩ := hsq C' h k hC' hhk
  -- `Θ` carries the boundary onto `∂Q`, hence the interior onto `Q ∖ ∂Q = Q°`.
  have hΘC : Θ '' C' = modelCurve := (Set.EqOn.image_eq hΘeq).trans hhk.image_eq
  have hΘin : Θ '' inside C' = Plane.openSquare 0 1 := by
    rw [← closedSquare_sdiff_modelCurve]
    exact image_eq_diff_of_bijOn_union hΘ.bijOn hΘC (disjoint_curve_inside C')
  -- `Φ` carries `Int(C)` onto `Int(C')`, so `Φ a` is an interior point of the target.
  have hΦin : Φ '' inside C = inside C' := image_inside_eq hΦ hΦeq hfg.image_eq
  have haΦ : Φ a ∈ inside C' := by rw [← hΦin]; exact ⟨a, ha, rfl⟩
  have hx : Θ (Φ a) ∈ Plane.openSquare 0 1 := by rw [← hΘin]; exact ⟨Φ a, haΦ, rfl⟩
  have hy : Θ b ∈ Plane.openSquare 0 1 := by rw [← hΘin]; exact ⟨b, hb, rfl⟩
  -- `lem:square-point-mover`: a boundary-fixing self-homeomorphism of `Q` moving one to the
  -- other. Conjugating it by `Θ` and composing with `Φ` is the pointed extension.
  obtain ⟨M, N, hM, hMx, -⟩ := Plane.exists_squareMover hx hy
  refine ⟨_, _, ((hΦ.comp hΘ).comp hM.isHomeoOn).comp hΘ.symm, fun z hz => ?_, ?_⟩
  · have h1 : f z ∈ C' := hfg.mapsTo hz
    change Θ' (M (Θ (Φ z))) = f z
    rw [hΦeq hz]
    -- `M` is the identity on `∂Q`, and `Θ (f z)` lies there.
    have h2 : Θ (f z) ∈ frontier (Plane.closedSquare 0 1) := by
      rw [← modelCurve_eq_frontier, ← hΘC]
      exact ⟨f z, h1, rfl⟩
    rw [hM.eqOn_frontier h2]
    exact hΘ.invOn.1 (Set.mem_union_left _ h1)
  · change Θ' (M (Θ (Φ a))) = b
    rw [hMx]
    exact hΘ.invOn.1 (Set.mem_union_right _ hb)

/-! ### `prop:exterior-extension`, from the square extension

`Schoenflies.exterior_extension` in `Schoenflies/Inversion.lean` is proved already; it carries
two hypotheses, the standing `harc` of `thm:jordan` and `PointedInteriorExtension`. Part I
discharges the first (`Schoenflies.arc_complement`) and the previous theorem discharges the
second, so only `SquareExtension` survives. -/

/-- **`prop:exterior-extension` (closed-exterior extension)**, with everything discharged but
the square extension: every homeomorphism between two Jordan curves extends to a homeomorphism
of their closed exteriors. -/
theorem exterior_extension_of_squareExtension (hsq : SquareExtension) {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C') ∧ EqOn F f C :=
  exterior_extension (fun _ hA => arc_complement hA) (pointed_extension hsq) hC hC' hfg

/-! ### `thm:main`

The closed pasting lemma, twice. The blueprint's proof is three sentences; the two facts it
leaves implicit are that the closed interior and the closed exterior are *closed* (they are the
closures of the two regions, `IsRegionOf.closure_eq`) and that the pasted map is injective,
which is `image_inside_eq` and `image_outside_eq`. -/

/-- The closed interior of a Jordan curve is closed: it is the closure of the interior. -/
theorem isClosed_union_inside (hC : IsSeparating C) : IsClosed (C ∪ inside C) := by
  rw [Set.union_comm, ← (IsRegionOf.inside C).closure_eq hC]
  exact isClosed_closure

/-- The closed exterior of a Jordan curve is closed. -/
theorem isClosed_union_outside (hC : IsSeparating C) : IsClosed (C ∪ outside C) := by
  rw [Set.union_comm, ← (IsRegionOf.outside C).closure_eq hC]
  exact isClosed_closure

/-- The two closed sides cover the plane. -/
theorem union_inside_union_outside (C : Set Plane) :
    (C ∪ inside C) ∪ (C ∪ outside C) = univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  by_cases hz : z ∈ C
  · exact Or.inl (Or.inl hz)
  · have hz' : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hz
    exact hz'.imp Or.inr Or.inr

/-- A point outside the closed interior is exterior. -/
theorem mem_outside_of_notMem_union_inside {z : Plane} (hz : z ∉ C ∪ inside C) :
    z ∈ outside C := by
  have hzC : z ∉ C := fun h => hz (Or.inl h)
  have : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hzC
  exact this.resolve_left fun h => hz (Or.inr h)

/-- **`thm:main`, the relative Jordan–Schönflies theorem.** Every homeomorphism between two
Jordan curves extends to a homeomorphism of the whole plane.

This form takes `Schoenflies.SquareExtension` as its sole auxiliary theorem. It is the unbundled
form; `Schoenflies.jordan_schoenflies_homeomorph_of_squareExtension` packages the result as a
self-homeomorphism of the plane. -/
theorem jordan_schoenflies_of_squareExtension (hsq : SquareExtension)
    {f g : Plane → Plane} (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G univ univ ∧ EqOn F f C := by
  have hsC : IsSeparating C := jordan_curve_theorem hC
  have hsC' : IsSeparating C' := jordan_curve_theorem hC'
  obtain ⟨Fi, Gi, hFi, hFieq⟩ := closed_interior_extension hsq hC hC' hfg
  obtain ⟨Fe, Ge, hFe, hFeeq⟩ := exterior_extension_of_squareExtension hsq hC hC' hfg
  -- The four "region onto region" facts that make the paste injective.
  have hFiin : Fi '' inside C = inside C' := image_inside_eq hFi hFieq hfg.image_eq
  have hFeout : Fe '' outside C = outside C' := image_outside_eq hFe hFeeq hfg.image_eq
  have hGiin : Gi '' inside C' = inside C := hFi.image_inv_eq Set.subset_union_right hFiin
  have hGeout : Ge '' outside C' = outside C := hFe.image_inv_eq Set.subset_union_right hFeout
  -- The inverse maps agree on `C'`, where both are `g`.
  have hGieq : EqOn Gi g C' := by
    intro w hw
    have hgw : g w ∈ C := hfg.mapsTo_inv hw
    have hFw : Fi (g w) = w := by rw [hFieq hgw]; exact hfg.invOn.2 hw
    calc Gi w = Gi (Fi (g w)) := by rw [hFw]
      _ = g w := hFi.invOn.1 (Set.mem_union_left _ hgw)
  have hGeeq : EqOn Ge g C' := by
    intro w hw
    have hgw : g w ∈ C := hfg.mapsTo_inv hw
    have hFw : Fe (g w) = w := by rw [hFeeq hgw]; exact hfg.invOn.2 hw
    calc Ge w = Ge (Fe (g w)) := by rw [hFw]
      _ = g w := hFe.invOn.1 (Set.mem_union_left _ hgw)
  -- Evaluation of the two pasted maps on each of the two closed pieces. Off the closed
  -- interior the paste is `Fe` by definition; *on* the closed interior it is `Fi`, and the two
  -- agree on the overlap `C`, where both are `f`.
  have hFint : EqOn (paste (C ∪ inside C) Fi Fe) Fi (C ∪ inside C) := fun _ hz => paste_of_mem hz
  have hFext : EqOn (paste (C ∪ inside C) Fi Fe) Fe (C ∪ outside C) := by
    rintro z (hzC | hzout)
    · rw [paste_of_mem (Set.mem_union_left _ hzC), hFieq hzC, hFeeq hzC]
    · refine paste_of_notMem fun hz => ?_
      exact Set.disjoint_left.1 disjoint_inside_outside
        (hz.resolve_left fun h => Set.disjoint_left.1 (disjoint_curve_outside C) h hzout) hzout
  have hGint : EqOn (paste (C' ∪ inside C') Gi Ge) Gi (C' ∪ inside C') :=
    fun _ hw => paste_of_mem hw
  have hGext : EqOn (paste (C' ∪ inside C') Gi Ge) Ge (C' ∪ outside C') := by
    rintro w (hwC | hwout)
    · rw [paste_of_mem (Set.mem_union_left _ hwC), hGieq hwC, hGeeq hwC]
    · refine paste_of_notMem fun hw => ?_
      exact Set.disjoint_left.1 disjoint_inside_outside
        (hw.resolve_left fun h => Set.disjoint_left.1 (disjoint_curve_outside C') h hwout) hwout
  refine ⟨paste (C ∪ inside C) Fi Fe, paste (C' ∪ inside C') Gi Ge,
    ⟨mapsTo_univ _ _, mapsTo_univ _ _, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- continuity of `F`: the closed pasting lemma on the two closed sides
    rw [← union_inside_union_outside C]
    exact Plane.continuousOn_union_of_isClosed (isClosed_union_inside hsC)
      (isClosed_union_outside hsC) (hFi.continuousOn.congr hFint)
      (hFe.continuousOn.congr hFext)
  · rw [← union_inside_union_outside C']
    exact Plane.continuousOn_union_of_isClosed (isClosed_union_inside hsC')
      (isClosed_union_outside hsC') (hFi.continuousOn_inv.congr hGint)
      (hFe.continuousOn_inv.congr hGext)
  · -- `G ∘ F = id`. The exterior case is where injectivity lives: `Fe z` is *exterior*, so the
    -- paste for `G` reads it with `Ge` and not with `Gi`.
    intro z _
    by_cases hz : z ∈ C ∪ inside C
    · rw [hFint hz, hGint (hFi.mapsTo hz), hFi.invOn.1 hz]
    · have hzout : z ∈ outside C := mem_outside_of_notMem_union_inside hz
      have hzL : z ∈ C ∪ outside C := Or.inr hzout
      have hFz : Fe z ∈ outside C' := by rw [← hFeout]; exact ⟨z, hzout, rfl⟩
      rw [hFext hzL, hGext (Or.inr hFz), hFe.invOn.1 hzL]
  · -- `F ∘ G = id`
    intro w _
    by_cases hw : w ∈ C' ∪ inside C'
    · rw [hGint hw, hFint (hFi.mapsTo_inv hw), hFi.invOn.2 hw]
    · have hwout : w ∈ outside C' := mem_outside_of_notMem_union_inside hw
      have hwL : w ∈ C' ∪ outside C' := Or.inr hwout
      have hGw : Ge w ∈ outside C := by rw [← hGeout]; exact ⟨w, hwout, rfl⟩
      rw [hGext hwL, hFext (Or.inr hGw), hFe.invOn.2 hwL]
  · exact fun z hz => (hFint (Set.mem_union_left _ hz)).trans (hFieq hz)

/-- **`thm:main`**, with the extension packaged as a self-homeomorphism of the plane. This is
the blueprint's statement: *there is a homeomorphism `F : ℝ² → ℝ²` whose restriction to `C` is
`f`*. -/
theorem jordan_schoenflies_homeomorph_of_squareExtension (hsq : SquareExtension)
    {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F : Plane ≃ₜ Plane, EqOn F f C := by
  obtain ⟨F, G, hFG, hFeq⟩ := jordan_schoenflies_of_squareExtension hsq hC hC' hfg
  exact ⟨hFG.homeomorphOfUniv, hFeq⟩

/-- **`thm:main`**, taking the boundary homeomorphism in bundled form, which is how the
blueprint states it: `f : C → C'` a homeomorphism of subspaces. -/
theorem jordan_schoenflies_of_homeomorph_of_squareExtension (hsq : SquareExtension)
    (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z := by
  obtain ⟨f, g, hfg, hfe⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, hF⟩ := jordan_schoenflies_homeomorph_of_squareExtension hsq hC hC' hfg
  exact ⟨F, fun z => (hF z.2).trans (hfe z z.2)⟩

end Schoenflies
