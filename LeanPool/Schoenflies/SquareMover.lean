/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Square

/-!
# Moving an interior point of the square

The pointed form of the bounded theorem needs a self-homeomorphism of the closed square that
fixes the boundary pointwise and carries one prescribed interior point to another. The
blueprint builds it by coning: the four triangles `conv {x, vᵢ, vᵢ₊₁}` triangulate the square,
and the affine map of each onto `conv {y, vᵢ, vᵢ₊₁}` fixing the two corners pastes with its
neighbours along the radial edges.

The construction here is the same map in different coordinates, and it is written so that no
pasting of four affine pieces is needed. It is the composite of two *shears*. A shear bends
one coordinate by the piecewise-linear self-map of `[-r, r]` that fixes the two endpoints and
moves a chosen breakpoint (`bend`), with a displacement that is scaled by a tent function of
the *other* coordinate (`tent`), so that it dies away to zero on the two transverse sides of
the square. The first shear moves the first coordinate of `x` to that of `y`, the second moves
the second coordinate.

Two features make this cheap. Writing the tent as a minimum of two affine functions makes it
continuous with no case split at all. And the family of shears is closed under inversion: the
shear with displacement parameters `k, k'` is undone by the shear with parameters `k + k',
-k'`, so bijectivity and the continuity of the inverse come from one composition identity
(`bend_bend`) instead of from a compactness argument, and no map has to be inverted by hand.

## Blueprint

* `Plane.exists_squareMover` — Lemma (Moving an interior point of the square): for interior
  points `x`, `y` of the square there are mutually inverse boundary-fixing self-maps `M`, `N`
  of the closed square with `M x = y`. `Plane.IsSquareMover` bundles the properties that make
  `M` a homeomorphism of the square onto itself, `Plane.IsSquareMover.homeomorph` repackages
  it as a `Homeomorph`, and `Plane.IsSquareMover.eqOn_frontier` states the boundary condition
  against the topological frontier, which `Plane.frontier_closedSquare` identifies with the
  blueprint's boundary square `S`.
* `Plane.iInter_eq_singleton_of_mem_tail` — the point-set kernel of Proposition (Skeleton
  agreement). The proposition itself is not statable in the present development; see the
  section comment at that lemma for exactly what is and is not proved.

Supporting material, of independent use: `Plane.tent` and `Plane.bend` with their algebra,
`Plane.continuousOn_bend`, the coordinate lemmas `Plane.abs_sub_le_supDist`,
`Plane.supDist_le_of_forall`, `Plane.exists_abs_sub_eq_of_supDist_eq`,
and `Plane.interior_closedSquare`.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### The tent function -/

/-- The tent of height `1` on `[-r, r]` with peak at `p`: it vanishes at the two endpoints,
takes the value `1` at `p`, and is linear on either side. Written as a minimum of two affine
functions rather than as a case split, which makes its continuity immediate. -/
noncomputable def tent (r p u : ℝ) : ℝ := min ((u + r) / (p + r)) ((r - u) / (r - p))

variable {r p q u : ℝ}

theorem continuous_tent (r p : ℝ) : Continuous (tent r p) := by
  unfold tent; fun_prop

theorem pos_of_lt_lt (h₁ : -r < p) (h₂ : p < r) : 0 < r := by linarith

theorem tent_le_one (h₁ : -r < p) (h₂ : p < r) (u : ℝ) : tent r p u ≤ 1 := by
  rcases le_total u p with h | h
  · exact le_trans (min_le_left _ _) (by rw [div_le_one (by linarith)]; linarith)
  · exact le_trans (min_le_right _ _) (by rw [div_le_one (by linarith)]; linarith)

theorem tent_nonneg (h₁ : -r < p) (h₂ : p < r) (hu : -r ≤ u) (hu' : u ≤ r) :
    0 ≤ tent r p u :=
  le_min (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith))

@[simp] theorem tent_self (h₁ : -r < p) (h₂ : p < r) : tent r p p = 1 := by
  rw [tent, div_self (by linarith), div_self (by linarith), min_self]

theorem tent_left (h₁ : -r < p) (h₂ : p < r) : tent r p (-r) = 0 := by
  have hr : 0 < r := pos_of_lt_lt h₁ h₂
  rw [tent, show -r + r = 0 by ring, zero_div]
  exact min_eq_left (div_nonneg (by linarith) (by linarith))

theorem tent_right (h₁ : -r < p) (h₂ : p < r) : tent r p r = 0 := by
  have hr : 0 < r := pos_of_lt_lt h₁ h₂
  rw [tent, show r - r = 0 by ring, zero_div]
  exact min_eq_right (div_nonneg (by linarith) (by linarith))

/-! ### Bending an interval -/

/-- The piecewise-linear self-map of `[-r, r]` that fixes both endpoints and carries `p` to
`q`, linearly on `[-r, p]` and on `[p, r]`. -/
noncomputable def bend (r p q u : ℝ) : ℝ :=
  if u ≤ p then -r + (u + r) * (q + r) / (p + r) else r - (r - u) * (r - q) / (r - p)

theorem bend_of_le (h : u ≤ p) : bend r p q u = -r + (u + r) * (q + r) / (p + r) := ite_eq_left h

theorem bend_of_gt (h : p < u) : bend r p q u = r - (r - u) * (r - q) / (r - p) :=
  ite_eq_right (not_le.2 h)

theorem bend_left (h : -r ≤ p) : bend r p q (-r) = -r := by
  rw [bend_of_le h]; simp

theorem bend_right (h : p < r) : bend r p q r = r := by
  rw [bend_of_gt h]; simp

theorem bend_self (h : -r < p) : bend r p q p = q := by
  have hp : p + r ≠ 0 := by linarith
  rw [bend_of_le le_rfl, mul_comm, mul_div_assoc, div_self hp, mul_one]; ring

theorem bend_refl (h₁ : -r < p) (h₂ : p < r) (u : ℝ) : bend r p p u = u := by
  rcases le_or_gt u p with h | h
  · rw [bend_of_le h, mul_div_assoc, div_self (by linarith : p + r ≠ 0), mul_one]; ring
  · rw [bend_of_gt h, mul_div_assoc, div_self (by linarith : r - p ≠ 0), mul_one]; ring

/-- On the left half, the bend does not go past the image `q` of the peak. -/
theorem bend_le_of_le (h₁ : -r < p) (h₂ : -r < q) (h : u ≤ p) : bend r p q u ≤ q := by
  rw [bend_of_le h]
  have : (u + r) * (q + r) / (p + r) ≤ q + r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- On the right half, the bend stays past the image `q` of the peak. -/
theorem lt_bend_of_lt (h₁ : p < r) (h₂ : q < r) (h : p < u) : q < bend r p q u := by
  rw [bend_of_gt h]
  have : (r - u) * (r - q) / (r - p) < r - q := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The bend maps `[-r, r]` into itself. -/
theorem bend_mem (h₁ : -r < p) (h₂ : p < r) (h₃ : -r < q) (h₄ : q < r) (hu : -r ≤ u)
    (hu' : u ≤ r) : -r ≤ bend r p q u ∧ bend r p q u ≤ r := by
  rcases le_or_gt u p with h | h
  · refine ⟨?_, le_of_lt (lt_of_le_of_lt (bend_le_of_le h₁ h₃ h) h₄)⟩
    rw [bend_of_le h]
    have : 0 ≤ (u + r) * (q + r) / (p + r) := div_nonneg (by nlinarith) (by linarith)
    linarith
  · refine ⟨le_of_lt (lt_trans h₃ (lt_bend_of_lt h₂ h₄ h)), ?_⟩
    rw [bend_of_gt h]
    have : 0 ≤ (r - u) * (r - q) / (r - p) := div_nonneg (by nlinarith) (by linarith)
    linarith

/-- Bending from `p` to `q` and back from `q` to `p` is the identity. -/
theorem bend_bend (h₁ : -r < p) (h₂ : p < r) (h₃ : -r < q) (h₄ : q < r) (u : ℝ) :
    bend r q p (bend r p q u) = u := by
  rcases le_or_gt u p with h | h
  · have hp : p + r ≠ 0 := by linarith
    have hq : q + r ≠ 0 := by linarith
    rw [bend_of_le (bend_le_of_le h₁ h₃ h), bend_of_le h]
    field_simp
    ring
  · have hp : r - p ≠ 0 := by linarith
    have hq : r - q ≠ 0 := by linarith
    rw [bend_of_gt (lt_bend_of_lt h₂ h₄ h), bend_of_gt h]
    field_simp
    ring

/-- Past the peak the right-hand branch of the bend is valid, including at the peak itself,
where the two branches agree. -/
theorem bend_eq_right (h₁ : p + r ≠ 0) (h₂ : r - p ≠ 0) (h : p ≤ u) :
    bend r p q u = r - (r - u) * (r - q) / (r - p) := by
  rcases eq_or_lt_of_le h with rfl | h'
  · rw [bend_of_le le_rfl]
    field_simp
    ring
  · exact bend_of_gt h'

/-- Continuity of a bend whose three arguments vary continuously, on a closed set where the
peak stays away from the two endpoints. The two branches are pasted along the closed sets
where the argument is on one or the other side of the peak. -/
theorem continuousOn_bend (r : ℝ) {s : Set Plane} {P Q U : Plane → ℝ} (hs : IsClosed s)
    (hP : Continuous P) (hQ : Continuous Q) (hU : Continuous U)
    (h1 : ∀ z ∈ s, P z + r ≠ 0) (h2 : ∀ z ∈ s, r - P z ≠ 0) :
    ContinuousOn (fun z => bend r (P z) (Q z) (U z)) s := by
  have hcover : s = (s ∩ {z | U z ≤ P z}) ∪ (s ∩ {z | P z ≤ U z}) := by
    ext z
    constructor
    · intro hz
      rcases le_total (U z) (P z) with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
  rw [hcover]
  refine (continuousOn_union_iff_of_isClosed (hs.inter (isClosed_le hU hP))
    (hs.inter (isClosed_le hP hU))).2 ⟨?_, ?_⟩
  · refine ContinuousOn.congr (f := fun z => -r + (U z + r) * (Q z + r) / (P z + r)) ?_ ?_
    · exact continuousOn_const.add
        (((hU.continuousOn.add continuousOn_const).mul
          (hQ.continuousOn.add continuousOn_const)).div
            (hP.continuousOn.add continuousOn_const) fun z hz => h1 z hz.1)
    · exact fun z hz => bend_of_le hz.2
  · refine ContinuousOn.congr (f := fun z => r - (r - U z) * (r - Q z) / (r - P z)) ?_ ?_
    · exact continuousOn_const.sub
        (((continuousOn_const.sub hU.continuousOn).mul
          (continuousOn_const.sub hQ.continuousOn)).div
            (continuousOn_const.sub hP.continuousOn) fun z hz => h2 z hz.1)
    · exact fun z hz => bend_eq_right (h1 z hz.1) (h2 z hz.1) hz.2

/-! ### Coordinates of the square -/

/-- Each coordinate difference is bounded by the sup distance. -/
theorem abs_sub_le_supDist (z c : Plane) (l : Fin 2) : |z l - c l| ≤ supDist z c := by
  fin_cases l
  · exact abs_sub_zero_le_supDist z c
  · exact abs_sub_one_le_supDist z c

/-- Conversely, a bound on both coordinate differences bounds the sup distance. -/
theorem supDist_le_of_forall {z c : Plane} {r : ℝ} (h : ∀ l : Fin 2, |z l - c l| ≤ r) :
    supDist z c ≤ r :=
  max_le (h 0) (h 1)

/-- The sup distance is attained at one of the two coordinates. -/
theorem exists_abs_sub_eq_of_supDist_eq {z c : Plane} {r : ℝ} (h : supDist z c = r) :
    ∃ l : Fin 2, |z l - c l| = r := by
  rcases max_choice |z 0 - c 0| |z 1 - c 1| with hm | hm
  · exact ⟨0, by rw [← h]; exact hm.symm⟩
  · exact ⟨1, by rw [← h]; exact hm.symm⟩

theorem abs_sub_lt_of_mem_openSquare {z c : Plane} {r : ℝ} (hz : z ∈ openSquare c r)
    (l : Fin 2) : |z l - c l| < r :=
  lt_of_le_of_lt (abs_sub_le_supDist z c l) hz

/-- The coordinate of a point of the open square, as a member of the open interval. -/
theorem mem_Ioo_of_mem_openSquare {z c : Plane} {r : ℝ} (hz : z ∈ openSquare c r) (l : Fin 2) :
    z l - c l ∈ Ioo (-r) r := by
  have := abs_sub_lt_of_mem_openSquare hz l
  rw [abs_lt] at this
  exact ⟨this.1, this.2⟩

/-- In `Fin 2`, two indices distinct from a third are equal. -/
theorem fin2_eq_of_ne_of_ne {i j l : Fin 2} (h₁ : j ≠ i) (h₂ : l ≠ i) : l = j := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

/-! ### Shearing the square along one coordinate -/

/-- The weight of the level line of `z` transverse to the `i`-th coordinate: it is `1` on the
level `b` and dies away to `0` at the two sides `z j - c j = ±r` of the square. -/
noncomputable def shearWeight (c : Plane) (r b : ℝ) (j : Fin 2) (z : Plane) : ℝ :=
  tent r b (z j - c j)

/-- The shear of the square about `c` of radius `r` in the direction of the `i`-th coordinate.
On the level line indexed by `w = shearWeight`, the `i`-th coordinate is bent by the
piecewise-linear map carrying `a + k * w` to `a + (k + k') * w` and fixing the two sides
`z i - c i = ±r`. Both the map with parameters `k, k'` and its inverse, which has parameters
`k + k', -k'`, belong to this two-parameter family — that is what the second parameter is
for. -/
noncomputable def shear (c : Plane) (r a b k k' : ℝ) (i j : Fin 2) (z : Plane) : Plane :=
  z + (bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
    (z i - c i) - (z i - c i)) • EuclideanSpace.single i (1 : ℝ)

/-- The parameters of a shear are admissible when the peak of the level weight and the peak of
every bend it performs stay strictly inside the square. -/
structure IsShear (r a b k k' : ℝ) : Prop where
  /-- the level of maximal displacement is interior -/
  peak : b ∈ Ioo (-r) r
  /-- the point that is moved is interior -/
  base : a ∈ Ioo (-r) r
  /-- the breakpoints of the bends are interior -/
  mid : a + k ∈ Ioo (-r) r
  /-- the images of the breakpoints are interior -/
  top : a + (k + k') ∈ Ioo (-r) r

variable {c : Plane} {a b k k' : ℝ} {i j l : Fin 2} {z : Plane}

/-- The inverse shear has admissible parameters as well. -/
theorem IsShear.inv (h : IsShear r a b k k') : IsShear r a b (k + k') (-k') where
  peak := h.peak
  base := h.base
  mid := h.top
  top := by rw [show k + k' + -k' = k by ring]; exact h.mid

theorem shear_apply_same :
    shear c r a b k k' i j z i =
      c i + bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z i - c i) := by
  simp only [shear, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    ite_true, mul_one]
  ring

theorem shear_apply_ne (h : l ≠ i) : shear c r a b k k' i j z l = z l := by
  simp [shear, h]

/-- A convex combination of two interior points of `(-r, r)` is interior. -/
theorem mem_Ioo_of_weight {w : ℝ} (ha : a ∈ Ioo (-r) r) (hak : a + k ∈ Ioo (-r) r)
    (hw : w ∈ Icc (0 : ℝ) 1) : a + k * w ∈ Ioo (-r) r := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hak
  obtain ⟨h5, h6⟩ := hw
  rcases eq_or_lt_of_le h5 with rfl | hw0
  · simpa using ⟨h1, h2⟩
  · constructor
    · nlinarith [mul_pos hw0 (show (0:ℝ) < a + k + r by linarith),
        mul_nonneg (show (0:ℝ) ≤ 1 - w by linarith) (show (0:ℝ) ≤ a + r by linarith)]
    · nlinarith [mul_pos hw0 (show (0:ℝ) < r - a - k by linarith),
        mul_nonneg (show (0:ℝ) ≤ 1 - w by linarith) (show (0:ℝ) ≤ r - a by linarith)]

/-- On the square, the level weight is a weight. -/
theorem shearWeight_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    shearWeight c r b j z ∈ Icc (0 : ℝ) 1 := by
  have hb := abs_sub_le_supDist z c j
  have : |z j - c j| ≤ r := le_trans hb hz
  rw [abs_le] at this
  exact ⟨tent_nonneg h.peak.1 h.peak.2 this.1 this.2, tent_le_one h.peak.1 h.peak.2 _⟩

/-- On the square, the breakpoint of the bend performed by the shear is interior. -/
theorem shear_mid_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    a + k * shearWeight c r b j z ∈ Ioo (-r) r :=
  mem_Ioo_of_weight h.base h.mid (shearWeight_mem h hz)

/-- On the square, the image of the breakpoint is interior. -/
theorem shear_top_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    a + (k + k') * shearWeight c r b j z ∈ Ioo (-r) r :=
  mem_Ioo_of_weight h.base h.top (shearWeight_mem h hz)

/-- The shear maps the closed square to itself. -/
theorem shear_mapsTo (h : IsShear r a b k k') (i j : Fin 2) :
    MapsTo (shear c r a b k k' i j) (closedSquare c r) (closedSquare c r) := by
  intro z hz
  refine supDist_le_of_forall fun l => ?_
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same]
    have hu : |z l - c l| ≤ r := le_trans (abs_sub_le_supDist z c l) hz
    rw [abs_le] at hu
    have := bend_mem (shear_mid_mem (j := j) h hz).1 (shear_mid_mem (j := j) h hz).2
      (shear_top_mem (j := j) h hz).1 (shear_top_mem (j := j) h hz).2 hu.1 hu.2
    rw [show c l + bend r (a + k * shearWeight c r b j z)
      (a + (k + k') * shearWeight c r b j z) (z l - c l) - c l
      = bend r (a + k * shearWeight c r b j z)
        (a + (k + k') * shearWeight c r b j z) (z l - c l) by ring, abs_le]
    exact this
  · rw [shear_apply_ne hl]
    exact le_trans (abs_sub_le_supDist z c l) hz

/-- The shear with parameters `k + k', -k'` undoes the shear with parameters `k, k'`. -/
theorem shear_shear (h : IsShear r a b k k') (hij : j ≠ i) (hz : z ∈ closedSquare c r) :
    shear c r a b (k + k') (-k') i j (shear c r a b k k' i j z) = z := by
  have hweight : shearWeight c r b j (shear c r a b k k' i j z) = shearWeight c r b j z := by
    rw [shearWeight, shearWeight, shear_apply_ne hij]
  ext l
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same, hweight, shear_apply_same, show
      c l + bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z l - c l) - c l
      = bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z l - c l) by ring, show k + k' + -k' = k by ring]
    rw [bend_bend (shear_mid_mem (j := j) h hz).1 (shear_mid_mem (j := j) h hz).2
      (shear_top_mem (j := j) h hz).1 (shear_top_mem (j := j) h hz).2]
    ring
  · rw [shear_apply_ne hl, shear_apply_ne hl]

/-- The shear fixes the boundary of the square pointwise. -/
theorem shear_eq_self_of_boundary (h : IsShear r a b k k') (hij : j ≠ i)
    (hz : z ∈ closedSquare c r) (hbd : supDist z c = r) : shear c r a b k k' i j z = z := by
  have hr : 0 < r := pos_of_lt_lt h.peak.1 h.peak.2
  obtain ⟨m, hm⟩ := exists_abs_sub_eq_of_supDist_eq hbd
  ext l
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same]
    by_cases hml : m = l
    · -- the extreme coordinate is the bent one, and the bend fixes the two endpoints
      subst hml
      rcases (abs_eq hr.le).1 hm with he | he
      · rw [he, bend_right (shear_mid_mem (j := j) h hz).2]
        linarith
      · rw [he, bend_left (shear_mid_mem (j := j) h hz).1.le]
        linarith
    · -- the extreme coordinate is the transverse one: the level weight there is zero
      have hmj : m = j := fin2_eq_of_ne_of_ne hij hml
      subst hmj
      have hw : shearWeight c r b m z = 0 := by
        rcases (abs_eq hr.le).1 hm with he | he
        · rw [shearWeight, he]; exact tent_right h.peak.1 h.peak.2
        · rw [shearWeight, show z m - c m = -r by linarith [he]]
          exact tent_left h.peak.1 h.peak.2
      rw [hw]
      simp only [mul_zero, add_zero]
      rw [bend_refl h.base.1 h.base.2]
      ring
  · rw [shear_apply_ne hl]

/-- The shear is continuous on the square. -/
theorem shear_continuousOn (h : IsShear r a b k k') (i j : Fin 2) :
    ContinuousOn (shear c r a b k k' i j) (closedSquare c r) := by
  have hW : Continuous fun z : Plane => shearWeight c r b j z :=
    (continuous_tent r b).comp ((continuous_coord j).sub continuous_const)
  have hU : Continuous fun z : Plane => z i - c i := (continuous_coord i).sub continuous_const
  have hP : Continuous fun z : Plane => a + k * shearWeight c r b j z :=
    continuous_const.add (continuous_const.mul hW)
  have hQ : Continuous fun z : Plane => a + (k + k') * shearWeight c r b j z :=
    continuous_const.add (continuous_const.mul hW)
  have hbend := continuousOn_bend r (s := closedSquare c r) (isClosed_closedSquare c r) hP hQ hU
    (fun z hz => by linarith [(shear_mid_mem (j := j) h hz).1])
    (fun z hz => by linarith [(shear_mid_mem (j := j) h hz).2])
  exact continuous_id.continuousOn.add ((hbend.sub hU.continuousOn).smul continuousOn_const)

/-! ### Movers of the square -/

/-- `M` and `N` are mutually inverse self-homeomorphisms of the closed square about `c` of
radius `r`, each fixing its boundary pointwise. This is the "homeomorphism of `Q` fixing `S`"
of the blueprint, written without the `Homeomorph` bundle; `IsSquareMover.homeomorph`
repackages it as one. -/
structure IsSquareMover (c : Plane) (r : ℝ) (M N : Plane → Plane) : Prop where
  /-- `M` maps the square to itself -/
  mapsTo : MapsTo M (closedSquare c r) (closedSquare c r)
  /-- `N` maps the square to itself -/
  mapsTo_inv : MapsTo N (closedSquare c r) (closedSquare c r)
  /-- `M` is continuous on the square -/
  continuousOn : ContinuousOn M (closedSquare c r)
  /-- `N` is continuous on the square -/
  continuousOn_inv : ContinuousOn N (closedSquare c r)
  /-- the two are mutually inverse there -/
  invOn : InvOn N M (closedSquare c r) (closedSquare c r)
  /-- `M` fixes the boundary pointwise -/
  fixes : ∀ z ∈ closedSquare c r, supDist z c = r → M z = z
  /-- `N` fixes the boundary pointwise -/
  fixes_inv : ∀ z ∈ closedSquare c r, supDist z c = r → N z = z

namespace IsSquareMover

variable {M N M' N' : Plane → Plane}

theorem symm (h : IsSquareMover c r M N) : IsSquareMover c r N M where
  mapsTo := h.mapsTo_inv
  mapsTo_inv := h.mapsTo
  continuousOn := h.continuousOn_inv
  continuousOn_inv := h.continuousOn
  invOn := h.invOn.symm
  fixes := h.fixes_inv
  fixes_inv := h.fixes

theorem bijOn (h : IsSquareMover c r M N) :
    BijOn M (closedSquare c r) (closedSquare c r) :=
  h.invOn.bijOn h.mapsTo h.mapsTo_inv

theorem image_eq (h : IsSquareMover c r M N) :
    M '' closedSquare c r = closedSquare c r := h.bijOn.image_eq

/-- Movers compose: `M'` after `M`, undone by `N` after `N'`. -/
theorem comp (h : IsSquareMover c r M N) (h' : IsSquareMover c r M' N') :
    IsSquareMover c r (M' ∘ M) (N ∘ N') where
  mapsTo := h'.mapsTo.comp h.mapsTo
  mapsTo_inv := h.mapsTo_inv.comp h'.mapsTo_inv
  continuousOn := h'.continuousOn.comp h.continuousOn h.mapsTo
  continuousOn_inv := h.continuousOn_inv.comp h'.continuousOn_inv h'.mapsTo_inv
  invOn := by
    constructor
    · intro z hz
      simp only [Function.comp_apply]
      rw [h'.invOn.1 (h.mapsTo hz), h.invOn.1 hz]
    · intro z hz
      simp only [Function.comp_apply]
      rw [h.invOn.2 (h'.mapsTo_inv hz), h'.invOn.2 hz]
  fixes := fun z hz hbd => by
    simp only [Function.comp_apply, h.fixes z hz hbd, h'.fixes z hz hbd]
  fixes_inv := fun z hz hbd => by
    simp only [Function.comp_apply, h'.fixes_inv z hz hbd, h.fixes_inv z hz hbd]

end IsSquareMover

/-- A shear, together with the shear that undoes it, is a mover of the square. -/
theorem isSquareMover_shear (h : IsShear r a b k k') (hij : j ≠ i) :
    IsSquareMover c r (shear c r a b k k' i j) (shear c r a b (k + k') (-k') i j) where
  mapsTo := shear_mapsTo h i j
  mapsTo_inv := shear_mapsTo h.inv i j
  continuousOn := shear_continuousOn h i j
  continuousOn_inv := shear_continuousOn h.inv i j
  invOn := by
    refine ⟨fun z hz => shear_shear h hij hz, fun z hz => ?_⟩
    have hz' := shear_shear h.inv hij hz
    rwa [show k + k' + -k' = k by ring, neg_neg] at hz'
  fixes := fun z hz hbd => shear_eq_self_of_boundary h hij hz hbd
  fixes_inv := fun z hz hbd => shear_eq_self_of_boundary h.inv hij hz hbd

/-! ### Moving an interior point -/

/-- Blueprint Lemma (Moving an interior point of the square). For any two interior points `x`
and `y` of the closed square about `c` of radius `r` there is a self-homeomorphism of the
square carrying `x` to `y` and fixing the boundary pointwise.

The map is built as two shears: the first moves the first coordinate of `x` to that of `y`
along the level line of `x`, the second moves the second coordinate along the level line of
the result. Each shear bends one coordinate by a piecewise-linear map whose displacement dies
away to zero at the two transverse sides, which is exactly the piecewise-affine cone
construction of the blueprint, written in coordinates. -/
theorem exists_squareMover {c x y : Plane} {r : ℝ} (hx : x ∈ openSquare c r)
    (hy : y ∈ openSquare c r) :
    ∃ M N : Plane → Plane, IsSquareMover c r M N ∧ M x = y ∧ N y = x := by
  have hx0 := mem_Ioo_of_mem_openSquare hx 0
  have hx1 := mem_Ioo_of_mem_openSquare hx 1
  have hy0 := mem_Ioo_of_mem_openSquare hy 0
  have hy1 := mem_Ioo_of_mem_openSquare hy 1
  have hne : (1 : Fin 2) ≠ 0 := by decide
  have hne' : (0 : Fin 2) ≠ 1 := by decide
  -- the first shear moves the first coordinate, along the level line of `x`
  have h₁ : IsShear r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) := by
    refine ⟨hx1, hx0, by simpa using hx0, ?_⟩
    rw [show x 0 - c 0 + (0 + (y 0 - x 0)) = y 0 - c 0 by ring]
    exact hy0
  -- the second shear moves the second coordinate, along the level line of the result
  have h₂ : IsShear r (x 1 - c 1) (y 0 - c 0) 0 (y 1 - x 1) := by
    refine ⟨hy0, hx1, by simpa using hx1, ?_⟩
    rw [show x 1 - c 1 + (0 + (y 1 - x 1)) = y 1 - c 1 by ring]
    exact hy1
  have hmover := (isSquareMover_shear (c := c) h₁ hne).comp (isSquareMover_shear (c := c) h₂ hne')
  have hMx : (shear c r (x 1 - c 1) (y 0 - c 0) 0 (y 1 - x 1) 1 0 ∘
      shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1) x = y := by
    -- the composite carries `x` to `y`
    have hW₁ : shearWeight c r (x 1 - c 1) 1 x = 1 := by
      rw [shearWeight, tent_self hx1.1 hx1.2]
    have hfirst0 : shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x 0 = y 0 := by
      rw [shear_apply_same, hW₁]
      simp only [add_zero, zero_add, mul_one]
      rw [bend_self hx0.1]
      ring
    have hfirst1 : shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x 1 = x 1 :=
      shear_apply_ne hne
    have hW₂ : shearWeight c r (y 0 - c 0) 0
        (shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x) = 1 := by
      rw [shearWeight, hfirst0, tent_self hy0.1 hy0.2]
    simp only [Function.comp_apply]
    ext l
    revert l
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [shear_apply_ne hne', hfirst0]
    · rw [shear_apply_same, hW₂, hfirst1]
      simp only [add_zero, zero_add, mul_one]
      rw [bend_self hx1.1]
      ring
  refine ⟨_, _, hmover, hMx, ?_⟩
  have hinv := hmover.invOn.1 (show supDist x c ≤ r from hx.le)
  rwa [hMx] at hinv

/-! ### The boundary of the square -/

theorem add_smul_single_apply (z : Plane) (t : ℝ) (l : Fin 2) :
    (z + t • EuclideanSpace.single l (1 : ℝ)) l = z l + t := by
  simp [PiLp.add_apply, PiLp.smul_apply]

theorem dist_add_smul_single (z : Plane) (t : ℝ) (l : Fin 2) :
    dist (z + t • EuclideanSpace.single l (1 : ℝ)) z = |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single]
  simp

/-- The interior of the closed square is the open square: a point with a coordinate at
distance exactly `r` from the centre can be pushed further out along that coordinate. -/
theorem interior_closedSquare (c : Plane) (r : ℝ) :
    interior (closedSquare c r) = openSquare c r := by
  have hsub : openSquare c r ⊆ closedSquare c r := fun z hz => show supDist z c ≤ r from hz.le
  refine Subset.antisymm (fun z hz => ?_) (interior_maximal hsub (isOpen_openSquare c r))
  by_contra hzo
  have hzc : z ∈ closedSquare c r := interior_subset hz
  have heq : supDist z c = r := le_antisymm hzc (not_lt.1 hzo)
  obtain ⟨l, hl⟩ := exists_abs_sub_eq_of_supDist_eq heq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have hr : 0 ≤ r := hl ▸ abs_nonneg _
  have key : ∀ t : ℝ, |t| < ε → |(z l - c l) + t| ≤ r := by
    intro t ht
    have hmem : z + t • EuclideanSpace.single l (1 : ℝ) ∈ closedSquare c r :=
      interior_subset (hball (by rw [Metric.mem_ball, dist_add_smul_single]; exact ht))
    have := le_trans (abs_sub_le_supDist (z + t • EuclideanSpace.single l (1 : ℝ)) c l) hmem
    rwa [add_smul_single_apply, show z l + t - c l = z l - c l + t by ring] at this
  rcases (abs_eq hr).1 hl with he | he
  · have := (abs_le.1 (key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))).2
    rw [he] at this
    linarith
  · have := (abs_le.1 (key (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith))).1
    rw [he] at this
    linarith

/-- The boundary of the closed square is the sup-distance sphere: the blueprint's `S`. -/
theorem frontier_closedSquare (c : Plane) (r : ℝ) :
    frontier (closedSquare c r) = {z | supDist z c = r} := by
  rw [(isClosed_closedSquare c r).frontier_eq, interior_closedSquare]
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 (not_lt.1 h2)
  · intro h
    exact ⟨le_of_eq h, by rw [openSquare, Set.mem_ofPred_eq, h]; exact lt_irrefl r⟩

/-- A mover is the identity on the boundary square `S`. -/
theorem IsSquareMover.eqOn_frontier {M N : Plane → Plane} (h : IsSquareMover c r M N) :
    EqOn M id (frontier (closedSquare c r)) := by
  intro z hz
  rw [frontier_closedSquare, Set.mem_ofPred_eq] at hz
  exact h.fixes z (le_of_eq hz) hz

/-! ### The mover as a homeomorphism -/

/-- A mover of the square, packaged as a self-homeomorphism of the closed square. -/
noncomputable def IsSquareMover.homeomorph {M N : Plane → Plane} (h : IsSquareMover c r M N) :
    closedSquare c r ≃ₜ closedSquare c r where
  toFun z := ⟨M z, h.mapsTo z.2⟩
  invFun z := ⟨N z, h.mapsTo_inv z.2⟩
  left_inv z := Subtype.ext (h.invOn.1 z.2)
  right_inv z := Subtype.ext (h.invOn.2 z.2)
  continuous_toFun := h.continuousOn.domRestrict.subtype_mk _
  continuous_invFun := h.continuousOn_inv.domRestrict.subtype_mk _

@[simp] theorem IsSquareMover.homeomorph_apply {M N : Plane → Plane}
    (h : IsSquareMover c r M N) (z : closedSquare c r) :
    (h.homeomorph z : Plane) = M z := rfl

@[simp] theorem IsSquareMover.homeomorph_symm_apply {M N : Plane → Plane}
    (h : IsSquareMover c r M N) (z : closedSquare c r) :
    (h.homeomorph.symm z : Plane) = N z := rfl

/-! ### The point-set kernel of skeleton agreement

The blueprint's Proposition (Skeleton agreement) says that the limit map `F`, defined at `x`
as the unique point of the nested intersection `⋂ n, T n x` of closed target stars, agrees
with every finite skeleton map: if `x ∈ G_N ∩ D` then `F x = g_N x`. Its proof is one line of
point-set topology once the combinatorics is in place — the value `g_N x` lies in `T n x` for
every `n ≥ N`, hence in the intersection, hence is *the* point of the intersection.

That one line is what follows. The proposition itself cannot be stated in this development
yet: matched cell structures, carriers, stars, the skeleton homeomorphisms `g_n` and the limit
map `F` do not exist here. What is proved is exactly the implication the proposition rests on,
with the nested stars as an abstract antitone sequence of shrinking compacta and `g_N x` as an
abstract point of all late terms. -/

/-- If the terms of an antitone sequence of nonempty compacta have diameters tending to zero,
and a point lies in every term from some index on, then that point is the unique point of the
intersection. Blueprint Proposition (Skeleton agreement), stripped of the cell apparatus:
read `K n` as the closed target star `T n x` and `v` as the skeleton value `g_N x`. -/
theorem iInter_eq_singleton_of_mem_tail {K : ℕ → Set Plane} {v : Plane} {N : ℕ}
    (hne : ∀ n, (K n).Nonempty) (hK : ∀ n, IsCompact (K n)) (hmono : Antitone K)
    (hdiam : Filter.Tendsto (fun n => diam (K n)) Filter.atTop (nhds 0))
    (hv : ∀ n, N ≤ n → v ∈ K n) : ⋂ n, K n = {v} := by
  obtain ⟨p, hp⟩ := eq_singleton_iInter_of_diam_tendsto_zero hne hK hmono hdiam
  have hvmem : v ∈ ⋂ n, K n := by
    refine mem_iInter.2 fun n => ?_
    rcases le_total N n with h | h
    · exact hv n h
    · exact hmono h (hv N le_rfl)
  rw [hp] at hvmem
  rw [hp, mem_singleton_iff.1 hvmem]

end Plane

end Schoenflies
