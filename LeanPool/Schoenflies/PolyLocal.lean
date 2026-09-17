/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.LocallyPolygonal
import LeanPool.Schoenflies.PolygonalCarrier

/-!
# Local polygonal connectedness, in the form brick B7 consumes

`Schoenflies/LocallyPolygonal.lean` (brick B5) and `Schoenflies/PolygonalCarrier.lean`
(brick B6) were written independently and each carries its own "joined by a polygonal path
inside a set" relation — `PolyConnIn` as an existential over vertex lists, `PolyReaches` as
an inductive relation — with its own local form. This module makes them one, and then fixes
the shape problem that stops B5 from feeding B7.

## The shape problem

Both local forms ask only that the connecting path lie in `S`:

```
IsLocallyPolyConnAt S p  :  ∃ U open ∋ p, ∀ x y ∈ U ∩ S, PolyConnIn S x y
IsLocallyPolyConnected C :  ∀ w ∈ C, ∃ V open ∋ w, ∀ z ∈ V ∩ C, PolyReaches C w z
```

That is enough for B6 — the clopen argument only needs *some* path — but it is a property
with **no local content whatsoever**: any polygonally connected `S` satisfies it with
`U = univ`. In particular it does not survive intersection with an open set, and that is
exactly what B7 needs: `U_e` is a component of a relatively open piece of `M`, and a
replacement arc has to stay inside the thin tube, not merely inside `M`.

The fix is `IsLocallyPolyConnAt'`: *arbitrarily small* neighbourhoods `U` of `p` such that
any two points of `U ∩ S` are joined **inside `U ∩ S`**. B5's proof already produces this —
its paths are two segments inside convex pieces of the small square about `p`, and the
square's radius may be shrunk freely — so nothing geometric is lost, only misstated.
`isLocallyPolyConn'_compl_openSquare` and `isLocallyPolyConn'_compl_biUnion` are B5 in the
strengthened form, and `IsLocallyPolyConn'.weaken` recovers the original statements.

## Blueprint

Brick B5 ↔ brick B6 of `lem:polygonal-redrawing` (H6), and the interface B7 uses.

* `polyConnIn_iff_polyReaches` — the two relations agree.
* `IsLocallyPolyConn.isLocallyPolyConnected`, `IsLocallyPolyConnected.isLocallyPolyConn` —
  the two weak local forms agree, so B5 as originally stated does feed B6.
* `IsLocallyPolyConnAt'`, `IsLocallyPolyConn'` — the strengthened local form.
* `isLocallyPolyConnAt'_of_convex_cover` — the strengthened star lemma: a square about `p`
  cut by convex pieces, each of which contains `p` as soon as it is nonempty.
* `isLocallyPolyConnAt'_compl_openSquare`, `isLocallyPolyConn'_compl_biUnion` — **brick B5**,
  strengthened.
* `IsLocallyPolyConn'.inter_isOpen` — shrinkability: a relatively open piece of a locally
  polygonally connected set is locally polygonally connected.
* `IsRelOpenIn`, `isRelOpenIn_connectedComponentIn` — components of relatively open subsets
  are relatively open, the fact B7 quotes for `U_e`.
* `polyReaches_of_isPreconnected_of_isRelOpenIn`, `polyReaches_connectedComponentIn` — the
  payoff: two points of a connected relatively open piece are joined *inside that piece*.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {S T A B C W : Set Plane} {p x y z : Plane}

/-! ### The two weak local forms agree

`IsLocallyPolyConn` quantifies over *pairs* of points of the neighbourhood,
`IsLocallyPolyConnected` only over paths *from the centre*; symmetry and transitivity of the
relation make the two equivalent. -/

/-- Brick B5's conclusion, read as brick B6's hypothesis. -/
theorem IsLocallyPolyConn.isLocallyPolyConnected (h : IsLocallyPolyConn S) :
    IsLocallyPolyConnected S := by
  intro w hw
  obtain ⟨U, hU, hwU, hconn⟩ := h w hw
  exact ⟨U, hU, hwU, fun z hz => (hconn w ⟨hwU, hw⟩ z hz).polyReaches⟩

/-- The converse: a path from the centre to each of two points, run backwards and forwards. -/
theorem IsLocallyPolyConnected.isLocallyPolyConn (h : IsLocallyPolyConnected S) :
    IsLocallyPolyConn S := by
  intro p hp
  obtain ⟨V, hV, hpV, hreach⟩ := h p hp
  exact ⟨V, hV, hpV, fun x hx y hy => ((hreach x hx).symm.trans (hreach y hy)).polyConnIn⟩

/-! ### Squares are a neighbourhood basis

B5 builds its neighbourhoods as axis-parallel squares, and the strengthened local form needs
them arbitrarily small inside a given open set. -/

namespace Plane

/-- A square of half a radius sits inside the ball of that radius, because `√2 < 2`. The open
counterpart of `Plane.closedSquare_subset_ball`, restated here so that this module does not
have to import the graph layer. No sign condition on the radius: for `ε ≤ 0` the square is
already empty. -/
theorem openSquare_subset_ball (p : Plane) (ε : ℝ) : openSquare p (ε / 2) ⊆ ball p ε := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x p < ε / 2 := hx
  have hnorm : ‖x - p‖ ≤ Real.sqrt 2 * supDist x p := norm_le_sqrt_two_mul_supNorm _
  rw [mem_ball, dist_eq_norm]
  nlinarith [supDist_nonneg x p]

/-- Inside any open set around `p` there is a square about `p`, of radius at most any
prescribed positive bound. -/
theorem exists_openSquare_subset {W : Set Plane} {p : Plane} (hW : IsOpen W) (hp : p ∈ W)
    {s₀ : ℝ} (hs₀ : 0 < s₀) : ∃ s, 0 < s ∧ s ≤ s₀ ∧ openSquare p s ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW p hp
  exact ⟨min s₀ (ε / 2), lt_min hs₀ (by linarith), min_le_left _ _,
    (openSquare_mono (min_le_right _ _)).trans ((openSquare_subset_ball p ε).trans hball)⟩

end Plane

/-! ### The strengthened local form -/

/-- `S` is polygonally connected near `p` **inside arbitrarily small neighbourhoods**: for
every open `W` containing `p` there is an open `U ⊆ W` containing `p` such that any two points
of `U ∩ S` are joined by a polygonal path lying in `U ∩ S`.

Two strengthenings over `IsLocallyPolyConnAt`, and both are needed by brick B7. The path is
confined to the neighbourhood, not merely to `S`, because a replacement arc has to stay in its
tube; and the neighbourhoods run through a basis at `p`, because otherwise the property does
not survive intersecting `S` with an open set (`IsLocallyPolyConn'.inter_isOpen`). -/
def IsLocallyPolyConnAt' (S : Set Plane) (p : Plane) : Prop :=
  ∀ W : Set Plane, IsOpen W → p ∈ W →
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyReaches (U ∩ S) x y

/-- `S` is locally polygonally connected in the strengthened sense. -/
def IsLocallyPolyConn' (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt' S p

theorem IsLocallyPolyConnAt'.weaken (h : IsLocallyPolyConnAt' S p) :
    IsLocallyPolyConnAt S p := by
  obtain ⟨U, hU, hpU, -, hpath⟩ := h univ isOpen_univ (mem_univ p)
  exact ⟨U, hU, hpU, fun x hx y hy => ((hpath x hx y hy).mono inter_subset_right).polyConnIn⟩

/-- The strengthened form implies the original brick B5 statement, so nothing is lost by
replacing one with the other. -/
theorem IsLocallyPolyConn'.weaken (h : IsLocallyPolyConn' S) : IsLocallyPolyConn S :=
  fun p hp => (h p hp).weaken

/-- What brick B6 consumes. -/
theorem IsLocallyPolyConn'.isLocallyPolyConnected (h : IsLocallyPolyConn' S) :
    IsLocallyPolyConnected S := h.weaken.isLocallyPolyConnected

/-- The property is local: only the trace of `S` on a neighbourhood of `p` matters. This is
what reduces "finitely many squares" to "one square". -/
theorem IsLocallyPolyConnAt'.congr_nhds {V : Set Plane} (h : IsLocallyPolyConnAt' T p)
    (hV : IsOpen V) (hpV : p ∈ V) (heq : S ∩ V = T ∩ V) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ V) (hW.inter hV) ⟨hpW, hpV⟩
  have hUV : U ⊆ V := hUsub.trans inter_subset_right
  have hUST : U ∩ S = U ∩ T := by
    ext x
    constructor
    · rintro ⟨hxU, hxS⟩
      exact ⟨hxU, (heq.subset ⟨hxS, hUV hxU⟩).1⟩
    · rintro ⟨hxU, hxT⟩
      exact ⟨hxU, (heq.symm.subset ⟨hxT, hUV hxU⟩).1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_left, ?_⟩
  rw [hUST]
  exact hpath

/-- A neighbourhood of `p` already inside `S` settles the point: shrink it to a square, which
is convex, so a single segment joins any two of its points. -/
theorem isLocallyPolyConnAt'_of_nbhd_subset {V : Set Plane} (hV : IsOpen V) (hpV : p ∈ V)
    (hVS : V ⊆ S) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, -, hsub⟩ := Plane.exists_openSquare_subset (hV.inter hW) ⟨hpV, hpW⟩ one_pos
  refine ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs,
    hsub.trans inter_subset_right, fun x hx y hy => PolyReaches.of_segment ?_⟩
  exact ((convex_openSquare p s).segment_subset hx.1 hy.1).trans
    fun w hw => ⟨hw, hVS (hsub hw).1⟩

/-- An open set is locally polygonally connected in the strengthened sense. -/
theorem isLocallyPolyConn'_of_isOpen (hS : IsOpen S) : IsLocallyPolyConn' S :=
  fun _ hp => isLocallyPolyConnAt'_of_nbhd_subset hS hp Subset.rfl

/-- **The strengthened star lemma**, and the whole geometric content of brick B5's three
shapes. Suppose that inside one square about `p` the trace of `S` is covered by convex sets
`H i`, that each `H i` meets that square only inside `S`, and that each `H i` which meets the
square contains `p`. Then `S` is locally polygonally connected at `p` in the strengthened
sense.

Two points of a small square about `p` are then joined by two segments through `p`, each
inside one convex piece of that *small* square — which is why the path never leaves the
neighbourhood. No piece is required to be nonempty and none is named, so the disk, the
half-disk and the three-quarter disk are all this statement. -/
theorem isLocallyPolyConnAt'_of_convex_cover {ι : Type*} {H : ι → Set Plane} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hconv : ∀ i, Convex ℝ (H i))
    (hsub : ∀ i, openSquare p s₀ ∩ H i ⊆ S)
    (hcover : openSquare p s₀ ∩ S ⊆ ⋃ i, H i)
    (hstar : ∀ i, ∀ z ∈ openSquare p s₀ ∩ H i, p ∈ H i) :
    IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, hss₀, hsW⟩ := Plane.exists_openSquare_subset hW hpW hs₀
  have hmono : openSquare p s ⊆ openSquare p s₀ := openSquare_mono hss₀
  have hpiece : ∀ i, openSquare p s ∩ H i ⊆ openSquare p s ∩ S :=
    fun i _ hx => ⟨hx.1, hsub i ⟨hmono hx.1, hx.2⟩⟩
  -- Every point of the small relative square is joined to the centre by one segment.
  have hto : ∀ x ∈ openSquare p s ∩ S, PolyReaches (openSquare p s ∩ S) x p := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover ⟨hmono hx.1, hx.2⟩)
    refine PolyReaches.of_segment (Subset.trans ?_ (hpiece i))
    exact ((convex_openSquare p s).inter (hconv i)).segment_subset ⟨hx.1, hxi⟩
      ⟨mem_openSquare_self hs, hstar i x ⟨hmono hx.1, hxi⟩⟩
  exact ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs, hsW,
    fun x hx y hy => (hto x hx).trans (hto y hy).symm⟩

/-! ### Brick B5, strengthened

The two theorems of `LocallyPolygonal.lean`, reproved in the strengthened form. The geometry
is unchanged — `Plane.exists_radius_sides` still does all the work — because the pieces the
old proof used were already inside the neighbourhood; only the statement moves. -/

/-- **The one-square case of brick B5, strengthened.** The complement of an open axis-parallel
square is polygonally connected near every point of the plane, by paths confined to the
neighbourhood. -/
theorem isLocallyPolyConnAt'_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt' (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt'_of_convex_cover
    (H := fun ib : Fin 2 × Bool => sideHalfPlane c r ib.1 ib.2) hs
    (fun ib => convex_sideHalfPlane c r ib.1 ib.2)
    (fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2))
    (fun x hx => compl_openSquare_subset_iUnion c r hx.2)
    (fun ib z hz => (hstar ib z hz).2)

/-- **Brick B5, strengthened.** The plane minus finitely many open axis-parallel squares whose
closed squares are pairwise disjoint is locally polygonally connected, with the connecting
paths confined to the neighbourhood.

The two cases are unchanged. Away from all the closed squares a small square about `p` lies
inside `M` outright. Otherwise `p` lies in exactly one closed square, and a small enough square
about `p` misses all the others, so near `p` the set `M` *is* the complement of that one open
square — which is what `IsLocallyPolyConnAt'.congr_nhds` says suffices. -/
theorem isLocallyPolyConn'_compl_biUnion {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn' ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) := by
  intro p _
  -- The room between `p` and a square it is outside of, as a radius bound.
  have room : ∀ c : Plane, ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ Q, p ∈ closedSquare c₀ (ρ c₀)
  · -- `p` is in the closed square about `c₀`, hence outside every other closed square.
    obtain ⟨c₀, hc₀Q, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ Q \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcQ, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀Q c hcQ fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, Set.mem_ofPred_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite (hQ.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    refine (isLocallyPolyConnAt'_compl_openSquare c₀ (ρ c₀) p).congr_nhds
      (isOpen_openSquare p s) (mem_openSquare_self hs) ?_
    ext x
    constructor
    · rintro ⟨hxM, hxU⟩
      exact ⟨fun hcon => hxM (mem_biUnion hc₀Q hcon), hxU⟩
    · rintro ⟨hx₀, hxU⟩
      refine ⟨fun hcon => ?_, hxU⟩
      obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c s (hsle c ⟨hcQ, hcne⟩) x hxU hxc
  · -- `p` is outside every closed square, so a small square about `p` lies wholly in `M`.
    push Not at hnear
    have hfar : ∀ c ∈ Q, 0 < supDist p c - ρ c := by
      intro c hcQ
      have := hnear c hcQ
      simp only [closedSquare, Set.mem_ofPred_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hQ (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt'_of_nbhd_subset (isOpen_openSquare p s) (mem_openSquare_self hs)
      fun x hx hcon => ?_
    obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c s (hsle c hcQ) x hx hxc

-- A machine check that the strengthened form subsumes the original brick B5: this typechecks
-- only if the two statements line up on the nose.
example {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) :=
  (isLocallyPolyConn'_compl_biUnion hQ ρ hdisj).weaken

example (c : Plane) (r : ℝ) (p : Plane) : IsLocallyPolyConnAt (openSquare c r)ᶜ p :=
  (isLocallyPolyConnAt'_compl_openSquare c r p).weaken

/-! ### Shrinkability

The point of the strengthening. `IsLocallyPolyConn` does **not** have this property: it holds
for any polygonally connected `S` with `U = univ`, and the comb space — the segments
`{0} × [0,1]`, `{1/n} × [0,1]` and `[0,1] × {0}` — is polygonally connected while its
intersection with a thin open strip about `y = 1` is not locally polygonally connected at
`(0,1)`. -/

/-- **Shrinkability.** A relatively open piece of a locally polygonally connected set is
locally polygonally connected. Taking the neighbourhood inside `W` is what makes this work,
and it is the reason `IsLocallyPolyConnAt'` quantifies over all open `W ∋ p`. -/
theorem IsLocallyPolyConnAt'.inter_isOpen (h : IsLocallyPolyConnAt' S p) (hW : IsOpen W)
    (hpW : p ∈ W) : IsLocallyPolyConnAt' (S ∩ W) p := by
  intro W' hW' hpW'
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ W') (hW.inter hW') ⟨hpW, hpW'⟩
  have hUW : U ⊆ W := hUsub.trans inter_subset_left
  have hUS : U ∩ (S ∩ W) = U ∩ S :=
    Subset.antisymm (fun _ hx => ⟨hx.1, hx.2.1⟩) fun _ hx => ⟨hx.1, hx.2, hUW hx.1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_right, ?_⟩
  rw [hUS]
  exact hpath

theorem IsLocallyPolyConn'.inter_isOpen (h : IsLocallyPolyConn' S) (hW : IsOpen W) :
    IsLocallyPolyConn' (S ∩ W) :=
  fun _ hp => (h _ hp.1).inter_isOpen hW hp.2

/-! ### Relatively open subsets and their components -/

/-- `A` is relatively open in `S`: cut out of `S` by an ambient open set. -/
def IsRelOpenIn (S A : Set Plane) : Prop := ∃ W : Set Plane, IsOpen W ∧ A = S ∩ W

theorem IsRelOpenIn.subset (h : IsRelOpenIn S A) : A ⊆ S := by
  obtain ⟨W, -, rfl⟩ := h
  exact inter_subset_left

theorem isRelOpenIn_self (S : Set Plane) : IsRelOpenIn S S :=
  ⟨univ, isOpen_univ, (inter_univ S).symm⟩

theorem IsOpen.isRelOpenIn (hA : IsOpen A) (hAS : A ⊆ S) : IsRelOpenIn S A :=
  ⟨A, hA, (inter_eq_self_of_subset_right hAS).symm⟩

/-- The shape `isRelOpen_of_polyReaches_stable` delivers, read as relative openness. -/
theorem isRelOpenIn_of_exists (hAS : A ⊆ S) (h : ∃ U : Set Plane, IsOpen U ∧ A ⊆ U ∧ U ∩ S ⊆ A) :
    IsRelOpenIn S A := by
  obtain ⟨U, hU, hAU, hUA⟩ := h
  exact ⟨U, hU, Subset.antisymm (fun _ hx => ⟨hAS hx, hAU hx⟩) fun _ hx => hUA ⟨hx.2, hx.1⟩⟩

/-- Relative openness is transitive, which is how a component of a relatively open piece is
seen to be relatively open in the ambient set. -/
theorem IsRelOpenIn.trans (hA : IsRelOpenIn S A) (hB : IsRelOpenIn A B) : IsRelOpenIn S B := by
  obtain ⟨W, hW, rfl⟩ := hA
  obtain ⟨W', hW', rfl⟩ := hB
  exact ⟨W ∩ W', hW.inter hW', by rw [inter_assoc]⟩

/-- Shrinkability, phrased for a relatively open piece. -/
theorem IsLocallyPolyConn'.of_isRelOpenIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A) :
    IsLocallyPolyConn' A := by
  obtain ⟨W, hW, rfl⟩ := hA
  exact h.inter_isOpen hW

/-- **Components of relatively open subsets are relatively open.** For `S` locally polygonally
connected and `A` relatively open in `S`, each connected component of `A` is relatively open
in `S`.

The proof is `isRelOpen_of_polyReaches_stable`: a polygonal path inside `A` is a connected
subset of `A`, so it cannot leave the component it starts in, which is exactly the stability
that lemma asks for. -/
theorem isRelOpenIn_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsRelOpenIn S (connectedComponentIn A x) := by
  refine hA.trans (isRelOpenIn_of_exists (connectedComponentIn_subset A x) ?_)
  refine isRelOpen_of_polyReaches_stable (h.of_isRelOpenIn hA).isLocallyPolyConnected
    (connectedComponentIn_subset A x) fun w hw z _ hreach => ?_
  -- The polygon carrying the path is connected, lies in `A` and starts at `w`.
  obtain ⟨vs, hne, hsubA, hhead, hlast⟩ := hreach.exists_poly
  have hpoly : poly vs ⊆ connectedComponentIn A x := by
    rw [connectedComponentIn_eq hw]
    exact (isConnected_poly hne).isPreconnected.subset_connectedComponentIn
      (hhead ▸ head_mem_poly hne) hsubA
  exact hpoly (hlast ▸ getLast_mem_poly hne)

/-- A component of a relatively open piece is itself locally polygonally connected, so the
whole interface applies again one level down. -/
theorem isLocallyPolyConn'_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsLocallyPolyConn' (connectedComponentIn A x) :=
  h.of_isRelOpenIn (isRelOpenIn_connectedComponentIn h hA x)

/-! ### The payoff -/

/-- **What brick B7 uses.** In a locally polygonally connected `S`, any two points of a
connected relatively open subset are joined by a polygonal path *inside that subset*. -/
theorem polyReaches_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    PolyReaches C x y :=
  PolyReaches.of_isPreconnected (h.of_isRelOpenIn hC).isLocallyPolyConnected hconn hx hy

/-- The same, as a vertex list. -/
theorem exists_poly_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y :=
  (polyReaches_of_isPreconnected_of_isRelOpenIn h hC hconn hx hy).exists_poly

/-- The component form, which is how `U_e` arises: a component of a relatively open piece is
both relatively open and polygonally connected in itself. -/
theorem polyReaches_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    {w : Plane} (hx : x ∈ connectedComponentIn A w) (hy : y ∈ connectedComponentIn A w) :
    PolyReaches (connectedComponentIn A w) x y :=
  polyReaches_of_isPreconnected_of_isRelOpenIn h (isRelOpenIn_connectedComponentIn h hA w)
    isPreconnected_connectedComponentIn hx hy

end Schoenflies
