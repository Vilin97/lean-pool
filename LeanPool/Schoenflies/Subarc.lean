/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Curve

/-!
# Subarcs, open arcs, and the subarc basis

A subarc is the arc restricted to a subinterval of the parameter interval — but an arc is
carried by a map *on* `[0, 1]`, so the restriction has to be reparametrised back onto it.
That reparametrisation is `reparam a b : t ↦ a + t * (b - a)`: pure arithmetic, with no
inverse to construct and no choice to make. With it a subarc is a composition, and the two
things an arc must be — continuous and injective — are the two things a composition inherits.

Injectivity is required only on `uIcc a b`, the parameter interval actually traversed, not on
all of `[0, 1]`. That is what lets the two arcs of a Jordan curve be cut out of a loop, whose
parametrisation is injective on `[0, 1)` only.

The substance of the file is the last two sections. A parametrisation is an **open map onto
its arc**: the image of a relatively open piece of the parameter interval is relatively open
in the arc. This is where the continuity of the inverse earns its keep, and it is proved
without ever constructing that inverse — a continuous injection on a compact set is a closed
map onto its image, and a closed injective map is open onto its image, by complements.
Together with `basic_piece_inside_ball`, which puts such a piece inside any prescribed ball,
these images are a basis of the arc's subspace topology.

Relative openness is stated in the ambient form `∃ V, IsOpen V ∧ W = V ∩ A` rather than
through the subtype `↥A`, since every consumer here works with subsets of the plane.

## Blueprint

The blueprint uses subarcs throughout §1 without a numbered statement of their own; they are
the tool behind, among others, the model-curve parametrization (`lem:jordan-circle`), where
"the relatively open subarcs of `C`" are exactly the images produced by `image_isRelOpen`, and
the density arguments of `lem:accessible-dense`, which need `basic_piece_inside_ball`.

* `subarc`, `isArcBetween_subarc` — a piece of an arc is again an arc.
* `IsArc.exists_isArcBetween_subset` — the set-level reading: two points of an arc bound a
  subarc of it.
* `openArc` — the blueprint's `P°`, an arc without its two endpoints.
* `image_isRelOpen` — a parametrisation is an open map onto its arc; `openArc_isRelOpen` and
  `openArc_subarc_isRelOpen` are the "relatively open subarcs" of `lem:jordan-circle`.
* `basic_piece_inside_ball` — the subarc basis.
-/

@[expose] public section

open Set unitInterval

namespace Schoenflies

/-! ### Reparametrising `[0, 1]` onto a subinterval -/

/-- The affine map carrying `[0, 1]` onto the parameter interval between `a` and `b`,
running from `a` to `b`. -/
def reparam (a b : ℝ) : ℝ → ℝ := fun t => a + t * (b - a)

variable {a b : ℝ}

@[simp] theorem reparam_zero : reparam a b 0 = a := by simp [reparam]

@[simp] theorem reparam_one : reparam a b 1 = b := by simp [reparam]

theorem continuous_reparam : Continuous (reparam a b) := by unfold reparam; fun_prop

/-- The reparametrisation is injective as soon as it is not constant. -/
theorem reparam_injective (hab : a ≠ b) : Function.Injective (reparam a b) := by
  intro s t hst
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have : s * (b - a) = t * (b - a) := by
    have := hst
    simp only [reparam] at this
    linarith
  exact mul_right_cancel₀ hba this

/-- `reparam a b` carries the unit interval exactly onto `uIcc a b`. This is `segment_eq_image'`
read through the identification of a real segment with an unordered closed interval. -/
theorem image_reparam_I : reparam a b '' I = uIcc a b := by
  change (fun θ : ℝ => a + θ * (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b
  have h : (fun θ : ℝ => a + θ • (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
    rw [← segment_eq_image' ℝ a b, segment_eq_uIcc]
  simpa [reparam, smul_eq_mul] using h

theorem mapsTo_reparam : MapsTo (reparam a b) I (uIcc a b) :=
  mapsTo_iff_image_subset.mpr image_reparam_I.subset

/-- A subinterval of the unit interval stays inside it: `uIcc` is the convex hull of its two
endpoints, and the unit interval is convex. -/
theorem uIcc_subset_I (ha : a ∈ I) (hb : b ∈ I) : uIcc a b ⊆ I :=
  uIcc_subset_Icc ha hb

/-! ### Subarcs -/

/-- The subarc of `f` between the parameters `a` and `b`: the arc traversed from `f a` to
`f b`, reparametrised so that it is again a map on `[0, 1]`. -/
def subarc (f : ℝ → Plane) (a b : ℝ) : ℝ → Plane := fun t => f (reparam a b t)

variable {f : ℝ → Plane}

@[simp] theorem subarc_zero : subarc f a b 0 = f a := by simp [subarc]

@[simp] theorem subarc_one : subarc f a b 1 = f b := by simp [subarc]

/-- The image of a subarc is the arc restricted to the subinterval — which is what "sub"
means, and the form every consumer wants. -/
theorem subarc_image : subarc f a b '' I = f '' uIcc a b := by
  rw [show subarc f a b = f ∘ reparam a b from rfl, image_comp, image_reparam_I]

theorem subarc_image_subset (ha : a ∈ I) (hb : b ∈ I) : subarc f a b '' I ⊆ f '' I := by
  rw [subarc_image]
  exact image_mono (uIcc_subset_I ha hb)

theorem continuousOn_subarc (hc : ContinuousOn f I) (ha : a ∈ I) (hb : b ∈ I) :
    ContinuousOn (subarc f a b) I :=
  hc.comp continuous_reparam.continuousOn
    (mapsTo_reparam.mono_right (uIcc_subset_I ha hb))

/-- Injectivity of the subarc needs injectivity of `f` only where the subarc runs. -/
theorem injOn_subarc (hi : InjOn f (uIcc a b)) (hab : a ≠ b) : InjOn (subarc f a b) I := by
  intro s hs t ht hst
  exact reparam_injective hab (hi (mapsTo_reparam hs) (mapsTo_reparam ht) hst)

/-- A subarc between two distinct parameters is an arc between the two values there. The
injectivity hypothesis is confined to the traversed interval, so this applies to a piece of a
Jordan curve as well as to a piece of an arc. -/
theorem isArcBetween_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  ⟨subarc f a b, continuousOn_subarc hc ha hb, injOn_subarc hi hab,
    subarc_image, subarc_zero, subarc_one⟩

theorem isArc_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) : IsArc (f '' uIcc a b) :=
  (isArcBetween_subarc hc hi ha hb hab).isArc

/-- The version for an arc, whose parametrisation is injective everywhere. -/
theorem isArcBetween_subarc_of_injOn_I (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  isArcBetween_subarc hc (hi.mono (uIcc_subset_I ha hb)) ha hb hab

/-- Any two distinct points of an arc are the endpoints of a subarc of it. The set-level
form, for the consumers that never see a parametrisation. -/
theorem IsArc.exists_isArcBetween_subset {A : Set Plane} (h : IsArc A) {p q : Plane}
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) : ∃ B ⊆ A, IsArcBetween B p q := by
  obtain ⟨f, hc, hi, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  refine ⟨f '' uIcc s t, image_mono (uIcc_subset_I hs ht), ?_⟩
  exact isArcBetween_subarc_of_injOn_I hc hi hs ht (fun h => hpq (by rw [h]))

/-! ### The arc without its endpoints -/

/-- The open arc — the blueprint's `P°`: an arc with its two endpoints removed.

Taken on the parameter side, as the image of the open unit interval, because that is the form
the subarc basis argument needs: an open subarc is the image of an open subinterval.
Injectivity then says it is also the arc minus the two endpoint *values*, which is how the
blueprint reads it (`openArc_eq_diff`). -/
def openArc (f : ℝ → Plane) : Set Plane := f '' Ioo 0 1

theorem Ioo_subset_I : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self

theorem openArc_subset : openArc f ⊆ f '' I := image_mono Ioo_subset_I

/-- On an arc the two readings of "without its endpoints" agree: dropping the endpoints of the
parameter interval drops exactly the two endpoint values, since injectivity means no other
parameter shares them. -/
theorem openArc_eq_diff (hi : InjOn f I) : openArc f = f '' I \ {f 0, f 1} := by
  have hIoo : Ioo (0 : ℝ) 1 = I \ {0, 1} := by
    ext t
    simp only [mem_Ioo, mem_sdiff, mem_Icc, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1.le⟩, h0.ne', h1.ne⟩
    · rintro ⟨⟨h0, h1⟩, hne0, hne1⟩; exact ⟨h0.lt_of_ne' hne0, h1.lt_of_ne hne1⟩
  have hpair : f '' ({0, 1} : Set ℝ) = {f 0, f 1} := image_pair f 0 1
  rw [openArc, hIoo, hi.image_sdiff_subset (by
        rintro t (rfl | rfl); exacts [zero_mem_I, one_mem_I]), hpair]

/-- The open arc of a subarc is the arc restricted to the *open* subinterval. -/
theorem openArc_subarc (hab : a ≠ b) : openArc (subarc f a b) = f '' uIoo a b := by
  have h : reparam a b '' Ioo 0 1 = uIoo a b := by
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · -- Increasing: the witness for `x` is the fraction of the way from `a` to `b`.
      rw [uIoo_of_lt hlt]
      ext x
      simp only [mem_image, mem_Ioo, reparam]
      refine ⟨?_, fun hx => ⟨(x - a) / (b - a), ⟨?_, ?_⟩, by field_simp; ring⟩⟩
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · exact div_pos (by linarith [hx.1]) (by linarith)
      · exact (div_lt_one (by linarith)).mpr (by linarith [hx.2])
    · exact absurd rfl hab
    · -- Decreasing: the same fraction, written with both signs flipped.
      rw [uIoo_of_gt hgt]
      ext x
      simp only [mem_image, mem_Ioo, reparam]
      refine ⟨?_, fun hx => ⟨(a - x) / (a - b), ⟨?_, ?_⟩, by field_simp; ring⟩⟩
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · exact div_pos (by linarith [hx.2]) (by linarith)
      · exact (div_lt_one (by linarith)).mpr (by linarith [hx.1])
  rw [openArc, show subarc f a b = f ∘ reparam a b from rfl, image_comp, h]

/-! ### The interior of an arc, set-level

`openArc` is stated for a parametrisation. Three separate modules needed the same facts stated
for the *set* — `IsArcBetween A p q` gives `A ∖ {p, q}` connected, nonempty, and having both
endpoints in its closure — and each proved them again from scratch, one of them twice under two
names. Two of those copies were literally the same statement in modules that do not import each
other, so the build never noticed: alpha-equivalent `Prop`s are defeq under proof irrelevance,
and Lean's import checker accepts them. They live here now. -/

/-- The two ends of an arc are distinct: they are the images of `0` and `1`. -/
theorem IsArcBetween.ne {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) : p ≠ q := by
  obtain ⟨f, -, hinj, -, hf0, hf1⟩ := h
  intro he
  have h01 : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (by rw [hf0, hf1, he])
  norm_num at h01

/-- **The interior of an arc is the image of the open parameter interval.** The bridge from
`IsArcBetween`, which is about the set, to `openArc`, which is about a parametrisation. -/
theorem IsArcBetween.diff_eq_openArc {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    ∃ f : ℝ → Plane, ContinuousOn f I ∧ A \ {p, q} = f '' Ioo 0 1 := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  exact ⟨f, hc, by rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]⟩

/-- **The interior of an arc is connected.** It is the continuous image of `Ioo 0 1`. -/
theorem IsArcBetween.isPreconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) := by
  obtain ⟨f, hc, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact isPreconnected_Ioo.image _ (hc.mono Ioo_subset_I)

/-- The interior of an arc is nonempty: `Ioo 0 1` is. -/
theorem IsArcBetween.nonempty_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    (A \ {p, q}).Nonempty := by
  obtain ⟨f, -, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact ⟨f (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- The interior of an arc is connected in the nonempty sense. -/
theorem IsArcBetween.isConnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsConnected (A \ {p, q}) :=
  ⟨h.nonempty_diff, h.isPreconnected_diff⟩

/-- **An endpoint of an arc is a limit of its interior.** This is what turns "the closure of a
cell meets the curve in one arc only" into a statement about the *endpoints* of a crosscut, and
it is what says an ear's two ends lie on the boundary of the face its interior lies in. -/
theorem IsArcBetween.left_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : p ∈ closure (A \ {p, q}) := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  have hEq : A \ {p, q} = f '' Ioo 0 1 := by
    rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]
  -- The endpoint is the limit of the interior as the parameter tends to `0`.
  rw [hEq, ← h0]
  refine ((hc 0 zero_mem_I).mono Ioo_subset_I).mem_closure_image ?_
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact zero_mem_I

theorem IsArcBetween.right_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : q ∈ closure (A \ {p, q}) := by
  rw [Set.pair_comm]
  exact h.reverse.left_mem_closure_diff

/-- **An arc is the closure of its interior.** The arc is compact, hence closed, so the closure
of the interior is inside it; conversely the interior is inside its own closure and each of the
two endpoints is a limit of it. -/
theorem IsArcBetween.closure_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    closure (A \ {p, q}) = A := by
  refine Subset.antisymm (h.isArc.isClosed.closure_subset_iff.2 sdiff_subset) fun z hz => ?_
  by_cases hzp : z = p
  · exact hzp ▸ h.left_mem_closure_diff
  by_cases hzq : z = q
  · exact hzq ▸ h.right_mem_closure_diff
  exact subset_closure ⟨hz, by rintro (rfl | rfl) <;> simp_all⟩

/-! ### A parametrisation is an open map onto its arc -/

/-- **The parametrisation is an open map onto its arc.** The image of a relatively open piece
of the parameter interval is relatively open in the arc.

No inverse is constructed. The complement piece `I \ U` is compact, so its image is compact,
so it is closed; and by injectivity the image of `U ∩ I` is exactly the arc minus that closed
set. Stated for a relatively open *piece* `U ∩ I` rather than for a subarc, because at an
endpoint the basic neighbourhood is half-open — `openArc` of a subarc is the interior case,
and this covers both. -/
theorem image_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) {U : Set ℝ} (hU : IsOpen U) :
    ∃ V : Set Plane, IsOpen V ∧ f '' (U ∩ I) = V ∩ f '' I := by
  refine ⟨(f '' (I \ U))ᶜ, ?_, ?_⟩
  · -- The discarded piece is compact, hence closed, so its complement is open.
    exact (isCompact_image_of_subset_I hc sdiff_subset
      (isClosed_Icc.sdiff hU)).isClosed.isOpen_compl
  · -- Injectivity turns "remove the image" into "image of the removal".
    have hdiff : f '' (I \ (I \ U)) = f '' I \ f '' (I \ U) :=
      hi.image_sdiff_subset sdiff_subset
    rw [sdiff_sdiff_right_self, inter_comm I U] at hdiff
    rw [hdiff, sdiff_eq, inter_comm]

/-- The pointwise reading of the previous theorem, and the one consumers use: around every
point of the image of a relatively open piece there is a ball meeting the arc only inside that
image. This is precisely the continuity of the inverse parametrisation. -/
theorem exists_ball_inter_subset_image (hc : ContinuousOn f I) (hi : InjOn f I)
    {U : Set ℝ} (hU : IsOpen U) {x : Plane} (hx : x ∈ f '' (U ∩ I)) :
    ∃ ε > 0, Metric.ball x ε ∩ f '' I ⊆ f '' (U ∩ I) := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi hU
  have hxV : x ∈ V := (hV ▸ hx).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen x hxV
  exact ⟨ε, hε, fun y hy => hV ▸ ⟨hball hy.1, hy.2⟩⟩

/-- The open arc is relatively open in the arc: the blueprint's `P°` is a relatively open
subarc. -/
theorem openArc_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) :
    ∃ V : Set Plane, IsOpen V ∧ openArc f = V ∩ f '' I := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi (isOpen_Ioo (a := (0 : ℝ)) (b := 1))
  exact ⟨V, hVopen, by rwa [inter_eq_self_of_subset_left Ioo_subset_I] at hV⟩

/-- A subarc without its endpoints is relatively open in the arc. These are the "relatively
open subarcs" the blueprint speaks of. -/
theorem openArc_subarc_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) :
    ∃ V : Set Plane, IsOpen V ∧ f '' uIoo a b = V ∩ f '' I := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi (U := uIoo a b) isOpen_Ioo
  refine ⟨V, hVopen, ?_⟩
  rwa [inter_eq_self_of_subset_left
    (uIoo_subset_uIcc_self.trans (uIcc_subset_I ha hb))] at hV

/-! ### The subarc basis -/

/-- **Every neighbourhood of a point of the arc contains the image of an open subinterval
around its parameter.** With `image_isRelOpen`, which says those images are relatively open,
this makes them a basis of the arc's subspace topology.

The piece is the parameter interval cut by an interval around the parameter, which is
half-open exactly when the point is an endpoint. -/
theorem basic_piece_inside_ball (hc : ContinuousOn f I) {x : Plane} (hx : x ∈ f '' I)
    {r : ℝ} (hr : 0 < r) :
    ∃ c d : ℝ, x ∈ f '' (Ioo c d ∩ I) ∧ f '' (Ioo c d ∩ I) ⊆ Metric.ball x r := by
  obtain ⟨s, hs, rfl⟩ := hx
  -- Continuity at the parameter turns the prescribed radius into a parameter radius.
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hc s hs) r hr
  refine ⟨s - δ, s + δ, ⟨s, ⟨⟨by linarith, by linarith⟩, hs⟩, rfl⟩, ?_⟩
  rintro y ⟨t, ⟨ht, htI⟩, rfl⟩
  have : dist t s < δ := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact Metric.mem_ball.mpr (hclose htI this)

end Schoenflies
