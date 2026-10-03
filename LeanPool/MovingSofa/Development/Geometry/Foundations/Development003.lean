/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.Isoperimetric.BrunnMinkowski
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001


public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.SetSemiring
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff
/-!
# Moving sofa: related mathematical developments

* `Infrastructure.Topology.Foundations.Development001`.
* `Infrastructure.Curves.Foundations.Development002`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `JordanPick.JordanCurve.Arcs`.
* `JordanPick.JordanCurve.Brouwer`.
* `JordanPick.JordanCurve.Counting`.
* `JordanPick.JordanCurve`.
* `TauCeti.Analysis.Calculus.MetricVariation`.
* `TauCeti.Analysis.Normed.Module.Ball.Exterior`.
* `TauCeti.Analysis.Normed.Module.HalfSpace`.
* `TauCeti.Topology.EMetricSpace.BoundedVariation`.
* `External`.
* `TauCeti.Topology.Frontier`.
* `TauCeti.Topology.FilledHull`.
* `TauCeti.Analysis.Normed.Module.FilledHull`.
* `TauCeti.Topology.LocallyConnected`.
* `TauCeti.Topology.JordanCurve.Basic`.
* `TauCeti.Topology.JordanCurve.Path`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
/-!
# Arc scaffolding for the (continuous) Jordan curve theorem

Reusable topology lemmas that split a topological circle into closed arcs, each
homeomorphic to the unit interval.  These feed Maehara's proof of the Jordan
curve theorem.

`Plane := EuclideanSpace ℝ (Fin 2)` and the circle is `Metric.sphere (0:Plane) 1`.

Main deliverables:
* `circleHomeoSphere` / `spherePlaneHomeoCircle` — the bridge between Mathlib's
  `Circle` (unit circle in `ℂ`) and `sphere (0:Plane) 1`.
* `param` — the angle parametrization `ℝ → sphere (0:Plane) 1`, continuous,
  `2π`-periodic, with explicit fibers and surjective.
* `arcHomeoUnitInterval` — a closed arc `param '' Icc a b` (with `a < b`,
  `b - a < 2π`) is homeomorphic to `unitInterval`.
* `sphere_split` — two distinct points cut the circle into two closed arcs, each
  `≃ₜ unitInterval`, with union the whole circle and intersection the two points.
* `jordanCurve_split` — transport of `sphere_split` across a homeomorphism
  `sphere (0:Plane) 1 ≃ₜ K`.
* `exists_proper_arc` — a proper closed subset of the circle sits inside a proper
  closed arc `≃ₜ unitInterval`.
-/

public section

namespace JordanCurve.Arcs

open Metric Set Function Real

/-- The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## 1. The circle model bridge -/

/-- A linear isometry equivalence `ℂ ≃ₗᵢ[ℝ] Plane`, from the standard orthonormal
basis of `EuclideanSpace ℝ (Fin 2)`. -/
@[expose]
noncomputable def complexLIE : ℂ ≃ₗᵢ[ℝ] Plane :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- The underlying `Equiv` between Mathlib's `Circle` and the unit sphere of the
plane, induced by `complexLIE`. -/
@[expose]
noncomputable def circleEquivSphere : Circle ≃ sphere (0 : Plane) 1 where
  toFun z := ⟨complexLIE z, by
    rw [mem_sphere_zero_iff_norm, complexLIE.norm_map]; exact z.norm_coe⟩
  invFun w := ⟨complexLIE.symm w, by
    change complexLIE.symm w ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, complexLIE.symm.norm_map, ← mem_sphere_zero_iff_norm]
    exact w.2⟩
  left_inv z := by ext; simp [complexLIE.symm_apply_apply]
  right_inv w := by ext; simp [complexLIE.apply_symm_apply]

/-- **Circle model bridge.** `Circle ≃ₜ sphere (0:Plane) 1`. -/
@[expose]
noncomputable def circleHomeoSphere : Circle ≃ₜ sphere (0 : Plane) 1 :=
  Continuous.homeoOfEquivCompactToT2 (f := circleEquivSphere) <| by
    apply Continuous.subtype_mk
    exact complexLIE.continuous.comp continuous_subtype_val

/-- **Circle model bridge** (as requested): `sphere (0:Plane) 1 ≃ₜ Circle`. -/
noncomputable def spherePlaneHomeoCircle : sphere (0 : Plane) 1 ≃ₜ Circle :=
  circleHomeoSphere.symm

@[simp] lemma circleHomeoSphere_coe (z : Circle) :
    (circleHomeoSphere z : Plane) = complexLIE z := rfl

/-! ## 2. The angle parametrization -/

/-- The angle parametrization `ℝ → sphere (0:Plane) 1`, `θ ↦` the plane point at
angle `θ` on the unit circle. -/
noncomputable def param (θ : ℝ) : sphere (0 : Plane) 1 := circleHomeoSphere (Circle.exp θ)

@[continuity, fun_prop]
lemma continuous_param : Continuous param :=
  circleHomeoSphere.continuous.comp Circle.exp.continuous

/-- Two angles give the same point iff they differ by an integer multiple of `2π`. -/
lemma param_eq_iff {s t : ℝ} : param s = param t ↔ ∃ m : ℤ, s = t + m * (2 * π) := by
  unfold param
  rw [circleHomeoSphere.injective.eq_iff, Circle.exp_eq_exp]

/-- The parametrization is surjective. -/
lemma param_surjective : Surjective param :=
  circleHomeoSphere.surjective.comp Circle.exp_surjective

/-- The parametrization is `2π`-periodic. -/
lemma param_periodic : Function.Periodic param (2 * π) := by
  intro θ
  rw [param_eq_iff]
  exact ⟨1, by push_cast; ring⟩

/-! ## 2. Closed arc ≃ₜ unitInterval -/

/-- On a closed interval shorter than a full turn, `param` is injective. -/
lemma param_injOn {a b : ℝ} (h : b - a < 2 * π) : InjOn param (Icc a b) := by
  intro s hs t ht hst
  obtain ⟨m, hm⟩ := param_eq_iff.1 hst
  have hp : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨hαs, hsβ⟩ := hs
  obtain ⟨hat, htb⟩ := ht
  have e : s - t = (m : ℝ) * (2 * π) := by linarith
  have hlt : (m : ℝ) * (2 * π) < 1 * (2 * π) := by rw [one_mul, ← e]; linarith
  have hgt : (-1 : ℝ) * (2 * π) < (m : ℝ) * (2 * π) := by rw [neg_one_mul, ← e]; linarith
  have u1 : (m : ℝ) < 1 := lt_of_mul_lt_mul_right hlt hp.le
  have u2 : (-1 : ℝ) < (m : ℝ) := lt_of_mul_lt_mul_right hgt hp.le
  have hm0 : m = 0 := by
    have b1 : m < (1 : ℤ) := by exact_mod_cast u1
    have b2 : (-1 : ℤ) < m := by exact_mod_cast u2
    omega
  rw [hm0] at hm; push_cast at hm; linarith

/-- Image of a closed interval of angles under `param` (a "closed arc"). -/
lemma isClosed_arc (a b : ℝ) : IsClosed (param '' Icc a b) :=
  (isCompact_Icc.image continuous_param).isClosed

/-- On a short closed interval `param` restricts to a homeomorphism onto its
image (the arc). -/
noncomputable def arcHomeoIcc {a b : ℝ} (h : b - a < 2 * π) :
    (Icc a b) ≃ₜ (param '' Icc a b) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn param (Icc a b) (param_injOn h))
    (continuous_induced_rng.2 (continuous_param.comp continuous_subtype_val))

/-- **Closed arc ≃ₜ unitInterval.** A closed arc `param '' Icc a b` with
`a < b` and `b - a < 2π` is homeomorphic to the unit interval. -/
noncomputable def arcHomeoUnitInterval {a b : ℝ} (hab : a < b) (h : b - a < 2 * π) :
    (param '' Icc a b) ≃ₜ unitInterval :=
  (arcHomeoIcc h).symm.trans (iccHomeoI a b hab)

/-- The left endpoint `param a` of the arc maps to `0` under `arcHomeoUnitInterval`. -/
lemma arcHomeoUnitInterval_apply_left {a b : ℝ} (hab : a < b) (h : b - a < 2 * π)
    (hmem : param a ∈ param '' Icc a b) :
    arcHomeoUnitInterval hab h ⟨param a, hmem⟩ = 0 := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have key : (arcHomeoIcc h) ⟨a, ha⟩ = ⟨param a, hmem⟩ := Subtype.ext rfl
  have hsymm : (arcHomeoIcc h).symm ⟨param a, hmem⟩ = ⟨a, ha⟩ := by
    rw [← key, Homeomorph.symm_apply_apply]
  apply Subtype.ext
  change ((arcHomeoIcc h).symm.trans (iccHomeoI a b hab) ⟨param a, hmem⟩ : ℝ)
      = ((0 : unitInterval) : ℝ)
  rw [Homeomorph.trans_apply, hsymm, iccHomeoI_apply_coe, Set.Icc.coe_zero]
  change (a - a) / (b - a) = 0
  rw [sub_self, zero_div]

/-- The right endpoint `param b` of the arc maps to `1` under `arcHomeoUnitInterval`. -/
lemma arcHomeoUnitInterval_apply_right {a b : ℝ} (hab : a < b) (h : b - a < 2 * π)
    (hmem : param b ∈ param '' Icc a b) :
    arcHomeoUnitInterval hab h ⟨param b, hmem⟩ = 1 := by
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  have key : (arcHomeoIcc h) ⟨b, hb⟩ = ⟨param b, hmem⟩ := Subtype.ext rfl
  have hsymm : (arcHomeoIcc h).symm ⟨param b, hmem⟩ = ⟨b, hb⟩ := by
    rw [← key, Homeomorph.symm_apply_apply]
  apply Subtype.ext
  change ((arcHomeoIcc h).symm.trans (iccHomeoI a b hab) ⟨param b, hmem⟩ : ℝ)
      = ((1 : unitInterval) : ℝ)
  rw [Homeomorph.trans_apply, hsymm, iccHomeoI_apply_coe, Set.Icc.coe_one]
  change (b - a) / (b - a) = 1
  rw [div_self (by linarith : b - a ≠ 0)]

/-! ## 2b. Interior of an arc is path-connected -/

/-- **Interior of an arc is path-connected.** If `A ≃ₜ unitInterval` via `e` and two
points `x, y ∈ A` are the endpoints (`{e x, e y} = {0, 1}`), then `A \ {x, y}` — the
arc with its endpoints removed — is path-connected. -/
theorem arc_interior_isPathConnected {X : Type*} [TopologicalSpace X] {A : Set X}
    (e : A ≃ₜ unitInterval) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (he : ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) = {0, 1}) :
    IsPathConnected (A \ {x, y}) := by
  -- endpoint values, extracted from the set equality
  have hmx : e ⟨x, hx⟩ ∈ ({0, 1} : Set unitInterval) := by
    rw [← he]; exact Set.mem_insert _ _
  have hmy : e ⟨y, hy⟩ ∈ ({0, 1} : Set unitInterval) := by
    rw [← he]; exact Set.mem_insert_of_mem _ rfl
  have h0 : (0 : unitInterval) ∈ ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) := by
    rw [he]; exact Set.mem_insert _ _
  have h1 : (1 : unitInterval) ∈ ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) := by
    rw [he]; exact Set.mem_insert_of_mem _ rfl
  -- the parametrizing map from `Ioo 0 1 ⊆ ℝ`
  set g : ℝ → X := fun s => ((e.symm (Set.projIcc 0 1 (by norm_num) s) : A) : X) with hg
  have hgcont : Continuous g :=
    continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc)
  have hIoo : IsPathConnected (Set.Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num⟩
  have himg : g '' Set.Ioo (0 : ℝ) 1 = A \ {x, y} := by
    ext p
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
      have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) s = ⟨s, hsI⟩ :=
        Set.projIcc_of_mem _ hsI
      refine ⟨(e.symm _).2, ?_⟩
      rintro (hgx | hgy)
      · -- g s = x is impossible
        have heq : e.symm (Set.projIcc (0 : ℝ) 1 (by norm_num) s) = ⟨x, hx⟩ :=
          Subtype.ext hgx
        have hval : Set.projIcc (0 : ℝ) 1 (by norm_num) s = e ⟨x, hx⟩ := by
          rw [← heq, Homeomorph.apply_symm_apply]
        rw [hproj] at hval
        rcases hmx with hxe | hxe
        · rw [hxe] at hval
          exact absurd (congrArg Subtype.val hval) (by simpa using hs.1.ne')
        · rw [Set.mem_singleton_iff] at hxe; rw [hxe] at hval
          exact absurd (congrArg Subtype.val hval) (by simpa using hs.2.ne)
      · -- g s = y is impossible
        have heq : e.symm (Set.projIcc (0 : ℝ) 1 (by norm_num) s) = ⟨y, hy⟩ :=
          Subtype.ext hgy
        have hval : Set.projIcc (0 : ℝ) 1 (by norm_num) s = e ⟨y, hy⟩ := by
          rw [← heq, Homeomorph.apply_symm_apply]
        rw [hproj] at hval
        rcases hmy with hye | hye
        · rw [hye] at hval
          exact absurd (congrArg Subtype.val hval) (by simpa using hs.1.ne')
        · rw [Set.mem_singleton_iff] at hye; rw [hye] at hval
          exact absurd (congrArg Subtype.val hval) (by simpa using hs.2.ne)
    · rintro ⟨hpA, hpxy⟩
      have hpx : p ≠ x := fun h => hpxy (Or.inl h)
      have hpy : p ≠ y := fun h => hpxy (Or.inr h)
      set t : unitInterval := e ⟨p, hpA⟩ with ht
      have htne0 : t ≠ 0 := by
        intro h; apply hpx
        rcases h0 with h0e | h0e
        · have : e ⟨p, hpA⟩ = e ⟨x, hx⟩ := by rw [← ht, h, h0e]
          exact congrArg Subtype.val (e.injective this)
        · rw [Set.mem_singleton_iff] at h0e
          have : e ⟨p, hpA⟩ = e ⟨y, hy⟩ := by rw [← ht, h, h0e]
          exact absurd (congrArg Subtype.val (e.injective this)) hpy
      have htne1 : t ≠ 1 := by
        intro h; apply hpx
        rcases h1 with h1e | h1e
        · have : e ⟨p, hpA⟩ = e ⟨x, hx⟩ := by rw [← ht, h, h1e]
          exact congrArg Subtype.val (e.injective this)
        · rw [Set.mem_singleton_iff] at h1e
          have : e ⟨p, hpA⟩ = e ⟨y, hy⟩ := by rw [← ht, h, h1e]
          exact absurd (congrArg Subtype.val (e.injective this)) hpy
      have htmem : (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        refine ⟨lt_of_le_of_ne t.2.1 ?_, lt_of_le_of_ne t.2.2 ?_⟩
        · intro h; exact htne0 (Subtype.ext h.symm)
        · intro h; exact htne1 (Subtype.ext h)
      refine ⟨(t : ℝ), htmem, ?_⟩
      have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) (t : ℝ) = t :=
        Set.projIcc_val _ t
      change ((e.symm (Set.projIcc (0 : ℝ) 1 (by norm_num) (t : ℝ)) : A) : X) = p
      rw [hproj, ht, Homeomorph.symm_apply_apply]
  rw [← himg]
  exact hIoo.image hgcont

/-- **`arc_interior_joinedIn`.** For an arc `A ≃ₜ unitInterval` via `e` whose two
endpoints are `x, y` (`{e x, e y} = {0, 1}`), any two interior points `u, v ∈ A`
(neither equal to `x` nor `y`) are joined by a path inside `A \ {x, y}`. -/
theorem arc_interior_joinedIn {X : Type*} [TopologicalSpace X] {A : Set X}
    (e : A ≃ₜ unitInterval) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (he : ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) = {0, 1})
    {u v : X} (hu : u ∈ A) (hv : v ∈ A)
    (hux : u ∉ ({x, y} : Set X)) (hvx : v ∉ ({x, y} : Set X)) :
    JoinedIn (A \ {x, y}) u v :=
  (arc_interior_isPathConnected e hx hy he).joinedIn u ⟨hu, hux⟩ v ⟨hv, hvx⟩

/-! ## 3. The two-point split -/

/-- **Two-point split.** Two distinct points `x`, `y` on the circle cut it into
two closed arcs `A₁`, `A₂`, each homeomorphic to the unit interval, whose union
is the whole circle and whose intersection is exactly `{x, y}`. -/
theorem sphere_split {x y : sphere (0 : Plane) 1} (hxy : x ≠ y) :
    ∃ A₁ A₂ : Set (sphere (0 : Plane) 1),
      IsClosed A₁ ∧ IsClosed A₂ ∧ A₁ ∪ A₂ = univ ∧ A₁ ∩ A₂ = {x, y} ∧
      Nonempty (A₁ ≃ₜ unitInterval) ∧ Nonempty (A₂ ≃ₜ unitInterval) ∧
      IsPathConnected (A₁ \ {x, y}) ∧ IsPathConnected (A₂ \ {x, y}) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨α, hα⟩ := param_surjective x
  obtain ⟨β₀, hβ₀⟩ := param_surjective y
  set β := toIocMod hp α β₀ with hβdef
  have hmemβ : β ∈ Ioc α (α + 2 * π) := toIocMod_mem_Ioc hp α β₀
  -- `param β = y`
  have hpar_β : param β = y := by
    have hz : β₀ - β = (toIocDiv hp α β₀ : ℤ) • (2 * π) := self_sub_toIocMod hp α β₀
    rw [zsmul_eq_mul] at hz
    have hpp : param β = param β₀ := by
      rw [param_eq_iff]; exact ⟨-(toIocDiv hp α β₀), by push_cast; linarith⟩
    rw [hpp, hβ₀]
  -- `β < α + 2π` (else `y = x`)
  have hβlt : β < α + 2 * π := by
    rcases lt_or_eq_of_le hmemβ.2 with h | h
    · exact h
    · exact absurd (by rw [← hpar_β, h, param_periodic, hα] : y = x).symm hxy
  have hlen1 : β - α < 2 * π := by linarith [hβlt]
  have hlen2 : (α + 2 * π) - β < 2 * π := by linarith [hmemβ.1]
  -- union is everything
  have hunion : (param '' Icc α β) ∪ (param '' Icc β (α + 2 * π)) = univ := by
    rw [← image_union, Icc_union_Icc_eq_Icc hmemβ.1.le hβlt.le,
      param_periodic.image_Icc hp α, param_surjective.range_eq]
  -- intersection is `{x, y}`
  have hinter : (param '' Icc α β) ∩ (param '' Icc β (α + 2 * π)) = {x, y} := by
    ext z
    simp only [mem_inter_iff, mem_image, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩
      have hst : param s = param t := hsz.trans htz.symm
      obtain ⟨m, hm⟩ := param_eq_iff.1 hst
      obtain ⟨hαs, hsβ⟩ := hs
      obtain ⟨hβt, htα⟩ := ht
      have e : s - t = (m : ℝ) * (2 * π) := by linarith
      have hm_ub : (m : ℝ) ≤ 0 := by
        have h2 : (m : ℝ) * (2 * π) ≤ 0 * (2 * π) := by rw [zero_mul, ← e]; linarith
        exact le_of_mul_le_mul_right h2 hp
      have hm_lb : (-1 : ℝ) ≤ (m : ℝ) := by
        have h2 : (-1 : ℝ) * (2 * π) ≤ (m : ℝ) * (2 * π) := by
          rw [neg_one_mul, ← e]; linarith
        exact le_of_mul_le_mul_right h2 hp
      have hcase : m = 0 ∨ m = -1 := by
        have a0 : m ≤ (0 : ℤ) := by exact_mod_cast hm_ub
        have a1 : (-1 : ℤ) ≤ m := by exact_mod_cast hm_lb
        omega
      rcases hcase with h0 | h1
      · right
        have hst2 : s = t := by rw [h0] at hm; push_cast at hm; linarith
        have hsβeq : s = β := le_antisymm hsβ (by rw [hst2]; exact hβt)
        rw [← hsz, hsβeq]; exact hpar_β
      · left
        have hst2 : s = t - 2 * π := by rw [h1] at hm; push_cast at hm; linarith
        have hsαeq : s = α := le_antisymm (by rw [hst2]; linarith) hαs
        rw [← hsz, hsαeq]; exact hα
    · rintro (rfl | rfl)
      · exact ⟨⟨α, ⟨le_refl α, hmemβ.1.le⟩, hα⟩,
          ⟨α + 2 * π, ⟨hβlt.le, le_refl _⟩, by rw [param_periodic]; exact hα⟩⟩
      · exact ⟨⟨β, ⟨hmemβ.1.le, le_refl β⟩, hpar_β⟩,
          ⟨β, ⟨le_refl β, hβlt.le⟩, hpar_β⟩⟩
  -- path-connectedness of the two arcs with their shared endpoints removed
  have hmem_α₁ : param α ∈ param '' Icc α β := ⟨α, left_mem_Icc.2 hmemβ.1.le, rfl⟩
  have hmem_β₁ : param β ∈ param '' Icc α β := ⟨β, right_mem_Icc.2 hmemβ.1.le, rfl⟩
  have hxA1 : x ∈ param '' Icc α β := hα ▸ hmem_α₁
  have hyA1 : y ∈ param '' Icc α β := hpar_β ▸ hmem_β₁
  have hpc1 : IsPathConnected (param '' Icc α β \ {x, y}) := by
    refine arc_interior_isPathConnected (arcHomeoUnitInterval hmemβ.1 hlen1) hxA1 hyA1 ?_
    have hex : arcHomeoUnitInterval hmemβ.1 hlen1 ⟨x, hxA1⟩ = 0 := by
      rw [show (⟨x, hxA1⟩ : ↥(param '' Icc α β)) = ⟨param α, hmem_α₁⟩ from
        Subtype.ext hα.symm]
      exact arcHomeoUnitInterval_apply_left hmemβ.1 hlen1 hmem_α₁
    have hey : arcHomeoUnitInterval hmemβ.1 hlen1 ⟨y, hyA1⟩ = 1 := by
      rw [show (⟨y, hyA1⟩ : ↥(param '' Icc α β)) = ⟨param β, hmem_β₁⟩ from
        Subtype.ext hpar_β.symm]
      exact arcHomeoUnitInterval_apply_right hmemβ.1 hlen1 hmem_β₁
    rw [hex, hey]
  have hmem_β₂ : param β ∈ param '' Icc β (α + 2 * π) :=
    ⟨β, left_mem_Icc.2 hβlt.le, rfl⟩
  have hmem_α₂ : param (α + 2 * π) ∈ param '' Icc β (α + 2 * π) :=
    ⟨α + 2 * π, right_mem_Icc.2 hβlt.le, rfl⟩
  have hxeq : param (α + 2 * π) = x := by rw [param_periodic]; exact hα
  have hxA2 : x ∈ param '' Icc β (α + 2 * π) := hxeq ▸ hmem_α₂
  have hyA2 : y ∈ param '' Icc β (α + 2 * π) := hpar_β ▸ hmem_β₂
  have hpc2 : IsPathConnected (param '' Icc β (α + 2 * π) \ {x, y}) := by
    refine arc_interior_isPathConnected (arcHomeoUnitInterval hβlt hlen2) hxA2 hyA2 ?_
    have hex : arcHomeoUnitInterval hβlt hlen2 ⟨x, hxA2⟩ = 1 := by
      rw [show (⟨x, hxA2⟩ : ↥(param '' Icc β (α + 2 * π))) = ⟨param (α + 2 * π), hmem_α₂⟩
        from Subtype.ext hxeq.symm]
      exact arcHomeoUnitInterval_apply_right hβlt hlen2 hmem_α₂
    have hey : arcHomeoUnitInterval hβlt hlen2 ⟨y, hyA2⟩ = 0 := by
      rw [show (⟨y, hyA2⟩ : ↥(param '' Icc β (α + 2 * π))) = ⟨param β, hmem_β₂⟩ from
        Subtype.ext hpar_β.symm]
      exact arcHomeoUnitInterval_apply_left hβlt hlen2 hmem_β₂
    rw [hex, hey]; exact Set.pair_comm 1 0
  exact ⟨param '' Icc α β, param '' Icc β (α + 2 * π),
    isClosed_arc α β, isClosed_arc β (α + 2 * π), hunion, hinter,
    ⟨arcHomeoUnitInterval hmemβ.1 hlen1⟩, ⟨arcHomeoUnitInterval hβlt hlen2⟩, hpc1, hpc2⟩

/-! ## 4. Transport across a homeomorphism to a Jordan curve -/

/-- **Transport to a Jordan curve.** Given a homeomorphism `f` from the circle to
a space `K` and two distinct points, the images of the two arcs split `K` into two
closed arcs `≃ₜ unitInterval` meeting exactly at `{f x, f y}`. -/
theorem jordanCurve_split {K : Type*} [TopologicalSpace K]
    (f : sphere (0 : Plane) 1 ≃ₜ K) {x y : sphere (0 : Plane) 1} (hxy : x ≠ y) :
    ∃ A₁ A₂ : Set K,
      IsClosed A₁ ∧ IsClosed A₂ ∧ A₁ ∪ A₂ = univ ∧ A₁ ∩ A₂ = {f x, f y} ∧
      Nonempty (A₁ ≃ₜ unitInterval) ∧ Nonempty (A₂ ≃ₜ unitInterval) ∧
      IsPathConnected (A₁ \ {f x, f y}) ∧ IsPathConnected (A₂ \ {f x, f y}) := by
  obtain ⟨A₁, A₂, hc1, hc2, hu, hi, ⟨e1⟩, ⟨e2⟩, hpc1, hpc2⟩ := sphere_split hxy
  have himg1 : f '' (A₁ \ {x, y}) = f '' A₁ \ {f x, f y} := by
    rw [Set.image_sdiff f.injective, Set.image_insert_eq, Set.image_singleton]
  have himg2 : f '' (A₂ \ {x, y}) = f '' A₂ \ {f x, f y} := by
    rw [Set.image_sdiff f.injective, Set.image_insert_eq, Set.image_singleton]
  refine ⟨f '' A₁, f '' A₂, f.isClosedMap _ hc1, f.isClosedMap _ hc2, ?_, ?_,
    ⟨(f.image A₁).symm.trans e1⟩, ⟨(f.image A₂).symm.trans e2⟩,
    himg1 ▸ hpc1.image f.continuous, himg2 ▸ hpc2.image f.continuous⟩
  · rw [← image_union, hu, image_univ, f.surjective.range_eq]
  · rw [← Set.image_inter f.injective, hi, Set.image_insert_eq, Set.image_singleton]

/-! ## 5. A proper closed arc containing a proper closed set -/

/-- **Proper arc containing a set.** A proper closed subset `C` of the circle is
contained in a proper closed arc `A` (homeomorphic to the unit interval). -/
theorem exists_proper_arc {C : Set (sphere (0 : Plane) 1)}
    (hC : IsClosed C) (hCne : C ≠ univ) :
    ∃ A : Set (sphere (0 : Plane) 1),
      C ⊆ A ∧ A ≠ univ ∧ IsClosed A ∧ Nonempty (A ≃ₜ unitInterval) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem C).1 hCne
  obtain ⟨γ, hγ⟩ := param_surjective z
  have hopen : IsOpen (param ⁻¹' Cᶜ) := hC.isOpen_compl.preimage continuous_param
  have hmemγ : γ ∈ param ⁻¹' Cᶜ := by rw [mem_preimage, hγ]; exact hz
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.1 hopen γ hmemγ
  set δ := min (ε / 2) (π / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδπ : δ < π := lt_of_le_of_lt (min_le_right _ _) (by linarith [pi_pos])
  have hδε : δ ≤ ε := le_trans (min_le_left _ _) (by linarith)
  have hsub : Ioo (γ - δ) (γ + δ) ⊆ param ⁻¹' Cᶜ := by
    intro w hw
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    obtain ⟨hw1, hw2⟩ := hw
    constructor <;> linarith
  -- `z ∉ A`, so `A ≠ univ`
  have hzA : z ∉ param '' Icc (γ + δ) (γ + 2 * π - δ) := by
    rintro ⟨θ, hθ, hθz⟩
    have hpe : param θ = param γ := by rw [hθz, hγ]
    obtain ⟨m, hm⟩ := param_eq_iff.1 hpe
    obtain ⟨hθ1, hθ2⟩ := hθ
    have e : (m : ℝ) * (2 * π) = θ - γ := by linarith
    have hpos : (0 : ℝ) < (m : ℝ) * (2 * π) := by rw [e]; linarith
    have hlt : (m : ℝ) * (2 * π) < 2 * π := by rw [e]; linarith
    have m1 : (0 : ℝ) < (m : ℝ) :=
      lt_of_mul_lt_mul_right (by rw [zero_mul]; exact hpos) hp.le
    have m2 : (m : ℝ) < 1 :=
      lt_of_mul_lt_mul_right (by rw [one_mul]; exact hlt) hp.le
    have a0 : (0 : ℤ) < m := by exact_mod_cast m1
    have a1 : m < (1 : ℤ) := by exact_mod_cast m2
    omega
  refine ⟨param '' Icc (γ + δ) (γ + 2 * π - δ), ?_,
    (Set.ne_univ_iff_exists_notMem _).2 ⟨z, hzA⟩, isClosed_arc _ _,
    ⟨arcHomeoUnitInterval (by linarith) (by linarith)⟩⟩
  -- `C ⊆ A`
  intro c hc
  obtain ⟨θc, hθc⟩ := param_surjective c
  set θ' := toIcoMod hp (γ + δ) θc with hθ'def
  have hmem' : θ' ∈ Ico (γ + δ) (γ + δ + 2 * π) := toIcoMod_mem_Ico hp (γ + δ) θc
  have hpar' : param θ' = c := by
    have hz2 : θc - θ' = (toIcoDiv hp (γ + δ) θc : ℤ) • (2 * π) :=
      self_sub_toIcoMod hp (γ + δ) θc
    rw [zsmul_eq_mul] at hz2
    have : param θ' = param θc := by
      rw [param_eq_iff]; exact ⟨-(toIcoDiv hp (γ + δ) θc), by push_cast; linarith⟩
    rw [this, hθc]
  have hθ'ub : θ' ≤ γ + 2 * π - δ := by
    by_contra h
    rw [not_le] at h
    have hmem2 : θ' - 2 * π ∈ Ioo (γ - δ) (γ + δ) := by
      constructor
      · linarith
      · linarith [hmem'.2]
    have hpre : (θ' - 2 * π) ∈ param ⁻¹' Cᶜ := hsub hmem2
    rw [mem_preimage] at hpre
    have hpc : param (θ' - 2 * π) = c := by
      rw [show θ' = (θ' - 2 * π) + 2 * π by ring, param_periodic] at hpar'
      exact hpar'
    rw [hpc] at hpre
    exact hpre hc
  exact ⟨θ', ⟨hmem'.1, hθ'ub⟩, hpar'⟩

end JordanCurve.Arcs

end

end

section

/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
/-!
# Toward the 2D Brouwer fixed point theorem

We build the classical topological proof of the two-dimensional Brouwer fixed
point theorem, in four phases:

* **Phase 1** — the once-around loop on `AddCircle 1` is not homotopic (rel
  endpoints) to the constant loop.  This is the mathematical heart: it is proved
  from the covering `ℝ → AddCircle 1` via unique path lifting
  (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`).
* **Phase 1.5** — transport of Phase 1 across `AddCircle 1 ≃ₜ Circle ≃ₜ
  sphere (0 : ℝ²) 1` to obtain a non-nullhomotopic loop on the geometric circle.
* **Phase 2** — no retraction of the disk onto its boundary circle: a retraction
  would give a null-homotopy of the Phase 1.5 loop.
* **Phase 3** — Brouwer for the closed unit disk (`brouwer_disk`): a
  fixed-point-free self-map yields a retraction (ray construction).
* **Phase 4** — the general convex/compact/nonempty statement `brouwerFPT`.
-/

public section

namespace JordanCurve.Brouwer

open Metric Set Function unitInterval Topology
open scoped RealInnerProductSpace

/-- The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## Phase 1 — the once-around loop on `AddCircle 1` is not nullhomotopic -/

/-- The covering map `ℝ → AddCircle 1`. -/
theorem cover : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1

/-- The once-around loop `t ↦ ↑t` in `AddCircle 1`. -/
@[expose]
noncomputable def acLoop : C(I, AddCircle (1 : ℝ)) :=
  ⟨fun t => ((t : ℝ) : AddCircle (1 : ℝ)), cover.continuous.comp continuous_subtype_val⟩

/-- The lift of `acLoop` to `ℝ` starting at `0`: the identity `t ↦ ↑t`. -/
@[expose]
noncomputable def idLift : C(I, ℝ) := ⟨fun t => (t : ℝ), continuous_subtype_val⟩

@[simp] lemma acLoop_apply (t : I) : acLoop t = ((t : ℝ) : AddCircle (1 : ℝ)) := rfl
@[simp] lemma idLift_apply (t : I) : idLift t = (t : ℝ) := rfl

/-- **Phase 1.** The once-around loop is not homotopic rel endpoints to the
constant loop. -/
theorem acLoop_not_homotopic :
    ¬ acLoop.HomotopicRel (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) {0, 1} := by
  intro h
  have h0 : acLoop 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by simp
  have h1 : (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
    simp
  have key := cover.liftPath_apply_one_eq_of_homotopicRel h (0 : ℝ) h0 h1
  -- Identify the two lifts.
  have e1 : cover.liftPath acLoop (0 : ℝ) h0 = idLift := by
    refine ((cover.eq_liftPath_iff' h0).mpr ⟨?_, ?_⟩).symm
    · ext t; simp
    · simp
  have e2 : cover.liftPath (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) (0 : ℝ) h1
      = ContinuousMap.const I (0 : ℝ) := cover.liftPath_const h1
  rw [e1, e2] at key
  simp at key

/-! ## Phase 1.5 — transport to the geometric circle `sphere (0 : ℝ²) 1` -/

/-- The homeomorphism `AddCircle 1 ≃ₜ sphere (0 : ℝ²) 1`, via `Circle`. -/
@[expose]
noncomputable def acToSphere : AddCircle (1 : ℝ) ≃ₜ sphere (0 : Plane) 1 :=
  (AddCircle.homeomorphCircle (one_ne_zero)).trans Arcs.circleHomeoSphere

/-- The base point of the sphere loop. -/
noncomputable def sBase : sphere (0 : Plane) 1 := acToSphere 0

/-- The once-around loop on the geometric circle `sphere (0 : ℝ²) 1`. -/
@[expose]
noncomputable def sLoop : C(I, sphere (0 : Plane) 1) :=
  (⟨acToSphere, acToSphere.continuous⟩ : C(AddCircle (1 : ℝ), sphere (0 : Plane) 1)).comp acLoop

@[simp] lemma sLoop_apply (t : I) : sLoop t = acToSphere (acLoop t) := rfl

lemma sLoop_zero : sLoop 0 = sBase := by simp [sBase]

/-- **Phase 1.5.** The once-around loop on the geometric circle is not homotopic
rel endpoints to the constant loop. -/
theorem sLoop_not_homotopic :
    ¬ sLoop.HomotopicRel (ContinuousMap.const I sBase) {0, 1} := by
  intro h
  apply acLoop_not_homotopic
  have hh := h.comp_continuousMap
    (⟨acToSphere.symm, acToSphere.symm.continuous⟩ : C(sphere (0 : Plane) 1, AddCircle (1 : ℝ)))
  have e1 : (⟨acToSphere.symm, acToSphere.symm.continuous⟩ :
      C(sphere (0 : Plane) 1, AddCircle (1 : ℝ))).comp sLoop = acLoop := by
    ext t; simp [sLoop, acToSphere.symm_apply_apply]
  have e2 : (⟨acToSphere.symm, acToSphere.symm.continuous⟩ :
      C(sphere (0 : Plane) 1, AddCircle (1 : ℝ))).comp (ContinuousMap.const I sBase)
      = ContinuousMap.const I (0 : AddCircle (1 : ℝ)) := by
    ext t; simp [sBase, acToSphere.symm_apply_apply]
  rwa [e1, e2] at hh

lemma sLoop_one : sLoop 1 = sBase := by
  have : acLoop 1 = (0 : AddCircle (1 : ℝ)) := by
    simp only [acLoop_apply]
    have : ((1 : I) : ℝ) = (1 : ℝ) := rfl
    rw [this]; exact AddCircle.coe_period 1
  simp [sBase, this]

/-! ## Phase 2 — no retraction of the disk onto its boundary circle -/

/-- The straight-line contraction point `(1-t)·(loop s) + t·base` in the disk. -/
noncomputable def diskPt (t s : I) : Plane :=
  (1 - (t : ℝ)) • (sLoop s : Plane) + (t : ℝ) • (sBase : Plane)

lemma diskPt_mem (t s : I) : diskPt t s ∈ closedBall (0 : Plane) 1 := by
  have hv : (sLoop s : Plane) ∈ closedBall (0 : Plane) 1 :=
    sphere_subset_closedBall (sLoop s).2
  have hw : (sBase : Plane) ∈ closedBall (0 : Plane) 1 :=
    sphere_subset_closedBall sBase.2
  exact convex_closedBall 0 1 hv hw (by unit_interval) (by unit_interval) (by ring)

lemma continuous_diskPt : Continuous (fun p : I × I => diskPt p.1 p.2) := by
  unfold diskPt
  fun_prop

/-- The contraction as a continuous map into the disk. -/
noncomputable def diskMap : C(I × I, closedBall (0 : Plane) 1) :=
  ⟨fun p => ⟨diskPt p.1 p.2, diskPt_mem p.1 p.2⟩,
    (continuous_diskPt).subtype_mk _⟩

/-- **Phase 2.** There is no retraction of the closed disk onto its boundary
circle. -/
theorem no_retraction (ρ : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1))
    (hrange : ∀ x, (ρ x : Plane) ∈ sphere (0 : Plane) 1)
    (hid : ∀ x : closedBall (0 : Plane) 1,
      (x : Plane) ∈ sphere (0 : Plane) 1 → (ρ x : Plane) = (x : Plane)) :
    False := by
  apply sLoop_not_homotopic
  -- The homotopy `H t s = ρ ((1-t)·loop s + t·base)`, valued in the sphere.
  set H : C(I × I, sphere (0 : Plane) 1) :=
    ⟨fun p => ⟨(ρ (diskMap p) : Plane), hrange _⟩,
      (map_continuous ρ |>.comp (map_continuous diskMap)).subtype_val.subtype_mk _⟩ with hH
  refine ⟨{
    toContinuousMap := H
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · -- H (0, s) = sLoop s
    intro s
    have hmem : (diskMap (0, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskPt 0 s ∈ _
      simp only [diskPt, Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
      exact (sLoop s).2
    apply Subtype.ext
    change (ρ (diskMap (0, s)) : Plane) = (sLoop s : Plane)
    rw [hid _ hmem]
    show (diskMap (0, s) : Plane) = (sLoop s : Plane)
    change diskPt 0 s = (sLoop s : Plane)
    simp [diskPt]
  · -- H (1, s) = base
    intro s
    have hmem : (diskMap (1, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskPt 1 s ∈ _
      simp only [diskPt, Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]
      exact sBase.2
    apply Subtype.ext
    change (ρ (diskMap (1, s)) : Plane) = (sBase : Plane)
    rw [hid _ hmem]
    show (diskMap (1, s) : Plane) = (sBase : Plane)
    change diskPt 1 s = (sBase : Plane)
    simp [diskPt]
  · -- rel endpoints: for s ∈ {0,1}, H t s = sLoop s = base
    intro t s hs
    have hs' : (sLoop s : Plane) = (sBase : Plane) := by
      rcases hs with h | h
      · rw [show s = (0 : I) from h, sLoop_zero]
      · rw [show s = (1 : I) from h, sLoop_one]
    have hmem : (diskMap (t, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskPt t s ∈ _
      simp only [diskPt, hs', ← add_smul, sub_add_cancel, one_smul]
      exact sBase.2
    apply Subtype.ext
    change (ρ (diskMap (t, s)) : Plane) = (sLoop s : Plane)
    rw [hid _ hmem, hs']
    show (diskMap (t, s) : Plane) = (sBase : Plane)
    change diskPt t s = (sBase : Plane)
    simp only [diskPt, hs', ← add_smul, sub_add_cancel, one_smul]

/-! ## Phase 3 — Brouwer for the closed unit disk

Given a fixed-point-free self-map `f` of the disk, the ray from `f x` through `x`
exits the boundary circle at a point `ρ x`; this `ρ` is a retraction, forbidden
by Phase 2. -/

section Disk

variable (f : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1))

/-- The direction vector `x - f x` of the ray. -/
noncomputable def dvec (x : closedBall (0 : Plane) 1) : Plane := (x : Plane) - (f x : Plane)

/-- Quadratic coefficient `A = ‖x - f x‖²`. -/
noncomputable def Acoef (x : closedBall (0 : Plane) 1) : ℝ := ⟪dvec f x, dvec f x⟫
/-- Coefficient `B = ⟪f x, x - f x⟫`. -/
noncomputable def Bcoef (x : closedBall (0 : Plane) 1) : ℝ := ⟪(f x : Plane), dvec f x⟫
/-- Coefficient `C = ‖f x‖² - 1 ≤ 0`. -/
noncomputable def Ccoef (x : closedBall (0 : Plane) 1) : ℝ := ‖(f x : Plane)‖ ^ 2 - 1
/-- Discriminant `B² - A·C ≥ 0`. -/
noncomputable def discr (x : closedBall (0 : Plane) 1) : ℝ := (Bcoef f x) ^ 2 - Acoef f x * Ccoef
  f x
/-- The (larger) root parameter `t = (-B + √disc)/A`. -/
noncomputable def tparam (x : closedBall (0 : Plane) 1) : ℝ :=
  (- Bcoef f x + Real.sqrt (discr f x)) / Acoef f x
/-- The exit point `ρ x = f x + t·(x - f x)` on the boundary circle. -/
noncomputable def rhoPt (x : closedBall (0 : Plane) 1) : Plane :=
  (f x : Plane) + tparam f x • dvec f x

variable (hf : ∀ x, (f x : Plane) ≠ (x : Plane))
include hf

lemma dvec_ne (x) : dvec f x ≠ 0 := by
  simp only [dvec, sub_ne_zero]; exact fun h => hf x h.symm

lemma Acoef_pos (x) : 0 < Acoef f x := by
  rw [Acoef, real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr (dvec_ne f hf x)) 2

omit hf in
lemma Ccoef_nonpos (x) : Ccoef f x ≤ 0 := by
  rw [Ccoef, sub_nonpos]
  have : ‖(f x : Plane)‖ ≤ 1 := by
    have := (f x).2; rw [mem_closedBall, dist_zero_right] at this; exact this
  nlinarith [norm_nonneg (f x : Plane)]

lemma discr_nonneg (x) : 0 ≤ discr f x := by
  have hA := (Acoef_pos f hf x).le
  have hC := Ccoef_nonpos f x
  have : 0 ≤ Acoef f x * (- Ccoef f x) := mul_nonneg hA (by linarith)
  rw [discr]; nlinarith [sq_nonneg (Bcoef f x)]

/-- The exit point lies on the unit circle. -/
lemma norm_rhoPt (x) : ‖rhoPt f x‖ = 1 := by
  have hA := Acoef_pos f hf x
  have hsq : (Real.sqrt (discr f x)) ^ 2 = discr f x :=
    Real.sq_sqrt (discr_nonneg f hf x)
  have hnormsq : ‖rhoPt f x‖ ^ 2 = 1 := by
    rw [rhoPt, norm_add_sq_real, norm_smul, real_inner_smul_right]
    have hAe : ⟪dvec f x, dvec f x⟫ = Acoef f x := rfl
    have hBe : ⟪(f x : Plane), dvec f x⟫ = Bcoef f x := rfl
    have hCe : ‖(f x : Plane)‖ ^ 2 = Ccoef f x + 1 := by rw [Ccoef]; ring
    rw [hBe, hCe]
    have hnd : ‖dvec f x‖ ^ 2 = Acoef f x := by
      rw [← real_inner_self_eq_norm_sq]; rfl
    rw [Real.norm_eq_abs, mul_pow, sq_abs, hnd]
    -- Now: (C+1) + 2*(t*B) + t^2 * A = 1, with t = (-B+√disc)/A
    rw [tparam]
    field_simp
    rw [discr] at hsq ⊢
    nlinarith [hsq, hA]
  have := norm_nonneg (rhoPt f x)
  nlinarith [hnormsq, this]

/-- On the boundary circle, `ρ` is the identity. -/
lemma rhoPt_of_mem_sphere (x : closedBall (0 : Plane) 1)
    (hx : (x : Plane) ∈ sphere (0 : Plane) 1) :
    rhoPt f x = (x : Plane) := by
  have hxn : ‖(x : Plane)‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hx
  have hA := Acoef_pos f hf x
  have eA : Acoef f x = ‖dvec f x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have eC : Ccoef f x = ‖(f x : Plane)‖ ^ 2 - 1 := rfl
  have hAdd : dvec f x + (f x : Plane) = (x : Plane) := by rw [dvec]; abel
  have hcomm : ⟪dvec f x, (f x : Plane)⟫ = Bcoef f x := by rw [Bcoef, real_inner_comm]
  have hexp : ‖(x : Plane)‖ ^ 2
      = ‖dvec f x‖ ^ 2 + 2 * ⟪dvec f x, (f x : Plane)⟫ + ‖(f x : Plane)‖ ^ 2 := by
    rw [← hAdd, norm_add_sq_real]
  rw [hxn, hcomm] at hexp
  -- A + 2B + C = 0
  have hkey : Acoef f x + 2 * Bcoef f x + Ccoef f x = 0 := by
    rw [eA, eC]; linear_combination -hexp
  -- A + B = ⟪x, x - f x⟫ = 1 - ⟪x, f x⟫ ≥ 0
  have hApB : Acoef f x + Bcoef f x = ⟪(x : Plane), dvec f x⟫ := by
    rw [Acoef, Bcoef, ← inner_add_left, hAdd]
  have hxd : ⟪(x : Plane), dvec f x⟫ = 1 - ⟪(x : Plane), (f x : Plane)⟫ := by
    rw [dvec, inner_sub_right, real_inner_self_eq_norm_sq, hxn]; norm_num
  have hcs : ⟪(x : Plane), (f x : Plane)⟫ ≤ 1 := by
    have hfn : ‖(f x : Plane)‖ ≤ 1 := by
      have := (f x).2; rwa [mem_closedBall, dist_zero_right] at this
    calc ⟪(x : Plane), (f x : Plane)⟫ ≤ ‖(x : Plane)‖ * ‖(f x : Plane)‖ := real_inner_le_norm _ _
      _ ≤ 1 * 1 := by rw [hxn]; exact mul_le_mul le_rfl hfn (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hAB : 0 ≤ Acoef f x + Bcoef f x := by rw [hApB, hxd]; linarith
  -- disc = (A+B)², so √disc = A+B, t = 1
  have hdisc : discr f x = (Acoef f x + Bcoef f x) ^ 2 := by
    rw [discr]; linear_combination (-Acoef f x) * hkey
  have hsqrt : Real.sqrt (discr f x) = Acoef f x + Bcoef f x := by
    rw [hdisc, Real.sqrt_sq hAB]
  have ht1 : tparam f x = 1 := by
    have hnum : -Bcoef f x + (Acoef f x + Bcoef f x) = Acoef f x := by ring
    rw [tparam, hsqrt, hnum, div_self hA.ne']
  rw [rhoPt, ht1, one_smul, dvec]; abel

/-! ### Continuity of the retraction -/

omit hf in
lemma continuous_fval : Continuous fun x : closedBall (0 : Plane) 1 => (f x : Plane) :=
  continuous_subtype_val.comp (map_continuous f)

omit hf in
lemma continuous_dvec : Continuous (dvec f) :=
  continuous_subtype_val.sub (continuous_fval f)

omit hf in
lemma continuous_Acoef : Continuous (Acoef f) :=
  (continuous_dvec f).inner (continuous_dvec f)

omit hf in
lemma continuous_Bcoef : Continuous (Bcoef f) :=
  (continuous_fval f).inner (continuous_dvec f)

omit hf in
lemma continuous_Ccoef : Continuous (Ccoef f) :=
  ((continuous_fval f).norm.pow 2).sub continuous_const

omit hf in
lemma continuous_discr : Continuous (discr f) :=
  ((continuous_Bcoef f).pow 2).sub ((continuous_Acoef f).mul (continuous_Ccoef f))

lemma continuous_tparam : Continuous (tparam f) :=
  Continuous.div (((continuous_Bcoef f).neg).add (continuous_discr f).sqrt)
    (continuous_Acoef f) (fun x => (Acoef_pos f hf x).ne')

lemma continuous_rhoPt : Continuous (rhoPt f) :=
  (continuous_fval f).add ((continuous_tparam f hf).smul (continuous_dvec f))

end Disk

/-- **Phase 3.** Brouwer's fixed point theorem for the closed unit disk. -/
theorem brouwer_disk (f : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1)) :
    ∃ x, f x = x := by
  by_contra hcon
  push Not at hcon
  have hf : ∀ x, (f x : Plane) ≠ (x : Plane) := fun x h => hcon x (Subtype.ext h)
  have hρmem : ∀ x, rhoPt f x ∈ closedBall (0 : Plane) 1 := fun x => by
    rw [mem_closedBall, dist_zero_right, norm_rhoPt f hf x]
  refine no_retraction ⟨fun x => ⟨rhoPt f x, hρmem x⟩, (continuous_rhoPt f hf).subtype_mk _⟩
    (fun x => ?_) (fun x hx => ?_)
  · change rhoPt f x ∈ sphere (0 : Plane) 1
    rw [mem_sphere_zero_iff_norm]; exact norm_rhoPt f hf x
  · change rhoPt f x = (x : Plane)
    exact rhoPt_of_mem_sphere f hf x hx

/-! ## Phase 4 — general nonempty compact convex sets -/

/-- Transfer of the fixed-point property along a homeomorphism. -/
theorem fixedPoint_transfer {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (hY : ∀ g : C(Y, Y), ∃ y, g y = y) (f : C(X, X)) : ∃ x, f x = x := by
  obtain ⟨y, hy⟩ := hY ((⟨φ, φ.continuous⟩ : C(X, Y)).comp
      (f.comp (⟨φ.symm, φ.symm.continuous⟩ : C(Y, X))))
  refine ⟨φ.symm y, ?_⟩
  have hfy : φ (f (φ.symm y)) = y := hy
  calc f (φ.symm y) = φ.symm (φ (f (φ.symm y))) := (φ.symm_apply_apply _).symm
    _ = φ.symm y := by rw [hfy]

/-! ### Brouwer on an arbitrary closed ball (by rescaling) -/

/-- Rescaling homeomorphism `closedBall 0 R ≃ₜ closedBall 0 1` (`x ↦ R⁻¹ • x`). -/
noncomputable def ballScale (R : ℝ) (hR : 0 < R) :
    closedBall (0 : Plane) R ≃ₜ closedBall (0 : Plane) 1 where
  toFun x := ⟨R⁻¹ • (x : Plane), by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hx : ‖(x : Plane)‖ ≤ R := by have := x.2; rwa [mem_closedBall, dist_zero_right] at this
    rw [inv_mul_le_iff₀ hR]; simpa using hx⟩
  invFun y := ⟨R • (y : Plane), by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hy : ‖(y : Plane)‖ ≤ 1 := by have := y.2; rwa [mem_closedBall, dist_zero_right] at this
    nlinarith [norm_nonneg (y : Plane)]⟩
  left_inv x := by ext; simp [smul_smul, mul_inv_cancel₀ hR.ne']
  right_inv y := by ext; simp [smul_smul, inv_mul_cancel₀ hR.ne']
  -- `fun_prop` rather than term-mode `Continuous.subtype_mk`: since Mathlib
  -- `905b9581`, unifying `Continuous.subtype_mk _ ?hp` against the `continuous_invFun`
  -- field of this `where` block diverges (it exhausts even a 1M heartbeat budget in
  -- `isDefEq`). Not a proof-size problem — hoisting the membership obligations into
  -- standalone lemmas does not help; only avoiding that unification does.
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Brouwer for a closed ball of arbitrary positive radius.** -/
theorem brouwer_ball (R : ℝ) (hR : 0 < R)
    (f : C(closedBall (0 : Plane) R, closedBall (0 : Plane) R)) : ∃ x, f x = x :=
  fixedPoint_transfer (ballScale R hR) (fun g => brouwer_disk g) f

/-! ### Nearest-point projection onto a nonempty compact convex set

Any nonempty compact convex set `s ⊆ ℝ²` is a retract of any closed ball
containing it, via the (nonexpansive, hence continuous) nearest-point
projection.  This yields Brouwer for all such `s` uniformly — in particular the
degenerate empty-interior case is handled without any dimension reduction. -/

section Projection

variable {s : Set Plane} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)

/-- Nearest-point projection of `u` onto the nonempty compact convex set `s`. -/
noncomputable def projFun (u : Plane) : Plane :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose

lemma projFun_mem (u : Plane) : projFun hconv hcomp hne u ∈ s :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose_spec.1

/-- The variational characterization of the projection. -/
lemma projFun_inner_le (u : Plane) {w : Plane} (hw : w ∈ s) :
    ⟪u - projFun hconv hcomp hne u, w - projFun hconv hcomp hne u⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv (projFun_mem hconv hcomp hne u)).mp
    (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose_spec.2 w hw

/-- The projection fixes the points of `s`. -/
lemma projFun_eq_self {u : Plane} (hu : u ∈ s) : projFun hconv hcomp hne u = u := by
  have h := projFun_inner_le hconv hcomp hne u hu
  rw [real_inner_self_eq_norm_sq] at h
  have hz : u - projFun hconv hcomp hne u = 0 := by
    have hn := norm_nonneg (u - projFun hconv hcomp hne u)
    have : ‖u - projFun hconv hcomp hne u‖ = 0 := by nlinarith
    rwa [norm_eq_zero] at this
  rw [sub_eq_zero] at hz; exact hz.symm

/-- The projection is nonexpansive. -/
lemma projFun_dist_le (u₁ u₂ : Plane) :
    ‖projFun hconv hcomp hne u₁ - projFun hconv hcomp hne u₂‖ ≤ ‖u₁ - u₂‖ := by
  set v₁ := projFun hconv hcomp hne u₁
  set v₂ := projFun hconv hcomp hne u₂
  have hb1 : 0 ≤ ⟪u₁ - v₁, v₁ - v₂⟫ := by
    have h := projFun_inner_le hconv hcomp hne u₁ (projFun_mem hconv hcomp hne u₂)
    rw [show v₂ - v₁ = -(v₁ - v₂) by abel, inner_neg_right] at h
    linarith
  have hb2 : ⟪u₂ - v₂, v₁ - v₂⟫ ≤ 0 :=
    projFun_inner_le hconv hcomp hne u₂ (projFun_mem hconv hcomp hne u₁)
  have decomp : ⟪u₁ - u₂, v₁ - v₂⟫
      = ⟪u₁ - v₁, v₁ - v₂⟫ - ⟪u₂ - v₂, v₁ - v₂⟫ + ⟪v₁ - v₂, v₁ - v₂⟫ := by
    have hsum : u₁ - u₂ = (u₁ - v₁ - (u₂ - v₂)) + (v₁ - v₂) := by abel
    rw [← inner_sub_left, ← inner_add_left, ← hsum]
  have key : ‖v₁ - v₂‖ ^ 2 ≤ ⟪u₁ - u₂, v₁ - v₂⟫ := by
    rw [decomp, ← real_inner_self_eq_norm_sq]; linarith
  have hcs : ⟪u₁ - u₂, v₁ - v₂⟫ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := real_inner_le_norm _ _
  rcases (norm_nonneg (v₁ - v₂)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · have hsq : ‖v₁ - v₂‖ * ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := by
      rw [← pow_two]; exact le_trans key hcs
    exact le_of_mul_le_mul_right hsq hpos

lemma continuous_projFun : Continuous (projFun hconv hcomp hne) :=
  (LipschitzWith.mk_one (fun u₁ u₂ => by
    rw [dist_eq_norm, dist_eq_norm]; exact projFun_dist_le hconv hcomp hne u₁ u₂)).continuous

end Projection

/-- **The 2D Brouwer fixed point theorem.** Every continuous self-map of a
nonempty compact convex subset of `ℝ²` has a fixed point.  This matches the
`JordanCurve.BrouwerFPT` interface used to discharge the Jordan curve theorem.

The set `s` is contained in a closed ball `closedBall 0 R`; the nearest-point
projection `r : closedBall 0 R → s` is a continuous retraction, so the self-map
`incl ∘ f ∘ r` of the ball has (by `brouwer_ball`) a fixed point `x`, whose
coordinates lie in `s`, whence `r x` is a fixed point of `f`. -/
theorem brouwerFPT : ∀ s : Set Plane, Convex ℝ s → IsCompact s → s.Nonempty →
    ∀ f : C(s, s), ∃ x, f x = x := by
  intro s hconv hcomp hne f
  obtain ⟨R, hR, hsub⟩ := hcomp.isBounded.subset_closedBall_lt 0 0
  let incl : C(s, closedBall (0 : Plane) R) :=
    ⟨fun y => ⟨(y : Plane), hsub y.2⟩, continuous_subtype_val.subtype_mk _⟩
  let r : C(closedBall (0 : Plane) R, s) :=
    ⟨fun x => ⟨projFun hconv hcomp hne (x : Plane), projFun_mem hconv hcomp hne (x : Plane)⟩,
      ((continuous_projFun hconv hcomp hne).comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := brouwer_ball R hR (incl.comp (f.comp r))
  refine ⟨r x, ?_⟩
  apply Subtype.ext
  have hval : (f (r x) : Plane) = (x : Plane) := congrArg Subtype.val hx
  have hxs : (x : Plane) ∈ s := by rw [← hval]; exact (f (r x)).2
  have hrx : ((r x : s) : Plane) = (x : Plane) := projFun_eq_self hconv hcomp hne hxs
  change (f (r x) : Plane) = ((r x : s) : Plane)
  rw [hval, hrx]

end Brouwer

end JordanCurve

end

section

/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
/-!
# Counting plumbing for the Jordan curve theorem

Pure-topology lemmas, independent of any geometry, used to turn the statement
"the complement of the curve has exactly two connected components" into the
numerical fact `Nat.card (ConnectedComponents …) = 2`.

The geometry side works with `connectedComponentIn S x` for `S : Set Plane` the
(open, nonempty) complement of the curve, and with two distinguished points in
the two components.  This file provides:

* `nat_card_connectedComponents_eq_two` — from two points in distinct components
  together covering everything, conclude `Nat.card (ConnectedComponents X) = 2`.
* `connectedComponents_subtype_eq_iff` — the bridge identifying equality of
  classes of subtype points with equality of `connectedComponentIn`.
-/

public section

namespace JordanCurve.Counting

open Set

variable {X : Type*} [TopologicalSpace X]

/-- If a space `X` has two points `a`, `b` lying in distinct connected components
and every point's component is one of those two, then `X` has exactly two
connected components. -/
theorem nat_card_connectedComponents_eq_two
    (a b : X) (hab : ConnectedComponents.mk a ≠ ConnectedComponents.mk b)
    (hcover : ∀ x : X, ConnectedComponents.mk x = ConnectedComponents.mk a
                     ∨ ConnectedComponents.mk x = ConnectedComponents.mk b) :
    Nat.card (ConnectedComponents X) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk a, ConnectedComponents.mk b, hab, ?_⟩
  rw [eq_univ_iff_forall]
  intro z
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
  rcases hcover x with h | h
  · exact mem_insert_iff.mpr (Or.inl h)
  · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr h))

/-- Bridge lemma.  For two points `x`, `y` of a subset `S`, the connected
components of the corresponding subtype points agree iff their
`connectedComponentIn S` subsets agree.  This lets the geometry side, which
phrases things via `connectedComponentIn S`, feed
`nat_card_connectedComponents_eq_two`. -/
theorem connectedComponents_subtype_eq_iff {S : Set X} {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) :
    ConnectedComponents.mk (⟨x, hx⟩ : S) = ConnectedComponents.mk (⟨y, hy⟩ : S)
      ↔ connectedComponentIn S x = connectedComponentIn S y := by
  rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image hy,
    (image_injective.mpr Subtype.coe_injective).eq_iff,
    ← ConnectedComponents.coe_eq_coe]

end JordanCurve.Counting

end

end

section

/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
/-!
# The (continuous) Jordan Curve Theorem, via Brouwer — Maehara's proof

Target (lean-eval `jordan_curve`, pure Mathlib): a continuous injection
`r : S¹ → ℝ²` has a complement with exactly two connected components.

**Strategy (Maehara, *The Jordan curve theorem via the Brouwer fixed point
theorem*, Amer. Math. Monthly 1984).** Reduce to the Brouwer fixed point theorem,
taken here as an explicit interface `BrouwerFPT` (to be discharged from upstream
Mathlib — PR #36770 is landing Brouwer — or built separately). The reduction uses:

* **Lemma 2 (crossing)** — two transversal paths in a rectangle must meet; proved
  directly from Brouwer via an explicit map of the square to its boundary.
* **Lemma 1** — if `ℝ²∖J` is disconnected, each component has `J` as its
  boundary; via the Tietze extension theorem + Brouwer.
* **Main construction** — using the farthest pair `a,b ∈ J` and the points
  `l,m,p,q` on a vertical segment, show `ℝ²∖J` has exactly one bounded component;
  with the unique unbounded component that gives exactly two.

This file is imported by the top-level `JordanPick` module and is complete:
sorry-free, with `#print axioms JordanCurve.jordan_curve` reporting only
`[propext, Classical.choice, Quot.sound]`.
-/

public section

namespace JordanCurve

open Metric Set Function Bornology

/-- The plane `ℝ²` as used by the eval problem. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Brouwer fixed point theorem** (interface). Every continuous self-map of a
nonempty convex compact subset of the plane has a fixed point. Discharged
separately (upstream Mathlib PR #36770, or a standalone build). All of Maehara's
argument is `BrouwerFPT → …`. -/
def BrouwerFPT : Prop :=
  ∀ s : Set Plane, Convex ℝ s → IsCompact s → s.Nonempty →
    ∀ f : C(s, s), ∃ x, f x = x

/-- **Lemma 2 (crossing lemma, Maehara).** Two continuous paths in a rectangle
`[a,b]×[c,d]`, one running from the left edge to the right edge (`h`), the other
from the bottom edge to the top edge (`v`), must meet. Proved directly from
Brouwer: if they were disjoint, the explicit normalized map
`F(s,t) = ((v₁ t − h₁ s)/N, (h₂ s − v₂ t)/N)` (with `N` the sup-norm of
`h s − v t`) sends the parameter square `[-1,1]²` to its boundary with no fixed
point. Coordinates are `p 0`, `p 1` of `p : Plane`. -/
theorem crossing (hbr : BrouwerFPT) {a b c d : ℝ} (_hab : a ≤ b) (_hcd : c ≤ d)
    (h v : ℝ → Plane)
    (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
    (hhE : ∀ t ∈ Icc (-1 : ℝ) 1, h t 0 ∈ Icc a b ∧ h t 1 ∈ Icc c d)
    (hvE : ∀ t ∈ Icc (-1 : ℝ) 1, v t 0 ∈ Icc a b ∧ v t 1 ∈ Icc c d)
    (hh1 : h (-1) 0 = a) (hh2 : h 1 0 = b)
    (hv1 : v (-1) 1 = c) (hv2 : v 1 1 = d) :
    ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, h s = v t := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ s ∈ Icc (-1) 1, ∀ t ∈ Icc (-1) 1, h s ≠ v t`
  -- The parameter square `Q = [-1,1]²`.
  set Q : Set Plane := {p | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-1 : ℝ) 1} with hQdef
  have hQ0 : ∀ p ∈ Q, p 0 ∈ Icc (-1 : ℝ) 1 := fun p hp => hp.1
  have hQ1 : ∀ p ∈ Q, p 1 ∈ Icc (-1 : ℝ) 1 := fun p hp => hp.2
  -- `Q` is convex.
  have hconv : Convex ℝ Q := by
    have c0 : Convex ℝ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1} := by
      exact (convex_Icc (-1 : ℝ) 1).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
    have c1 : Convex ℝ {p : Plane | p 1 ∈ Icc (-1 : ℝ) 1} := by
      exact (convex_Icc (-1 : ℝ) 1).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
    exact c0.inter c1
  -- `Q` is compact (closed and bounded in a finite-dimensional space).
  have hcomp : IsCompact Q := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have d0 : IsClosed {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1} :=
        isClosed_Icc.preimage (EuclideanSpace.proj (0:Fin 2)).continuous
      have d1 : IsClosed {p : Plane | p 1 ∈ Icc (-1 : ℝ) 1} :=
        isClosed_Icc.preimage (EuclideanSpace.proj (1:Fin 2)).continuous
      exact d0.inter d1
    · apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 2)).subset
      intro p hp
      simp only [mem_closedBall, dist_zero_right]
      have h0 : |p 0| ≤ 1 := abs_le.2 ⟨hp.1.1, hp.1.2⟩
      have h1 : |p 1| ≤ 1 := abs_le.2 ⟨hp.2.1, hp.2.2⟩
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
        show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by ring, Real.sqrt_sq]; norm_num]
      apply Real.sqrt_le_sqrt
      nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]
  have hne0 : Q.Nonempty := by
    refine ⟨0, ?_, ?_⟩ <;>
      · simp only [mem_Icc, show (0:Plane) 0 = 0 from rfl, show (0:Plane) 1 = 0 from rfl]
        norm_num
  -- The sup-norm distance and the normalized boundary map.
  let N : Plane → ℝ := fun p => max |h (p 0) 0 - v (p 1) 0| |h (p 0) 1 - v (p 1) 1|
  let n0 : Plane → ℝ := fun p => (v (p 1) 0 - h (p 0) 0) / N p
  let n1 : Plane → ℝ := fun p => (h (p 0) 1 - v (p 1) 1) / N p
  let F : Plane → Plane := fun p => !₂[n0 p, n1 p]
  have hNnn : ∀ p, 0 ≤ N p := fun p => le_trans (abs_nonneg _) (le_max_left _ _)
  -- `N > 0` on `Q`: otherwise `h (p 0) = v (p 1)`, contradicting `hcon`.
  have hNpos : ∀ p ∈ Q, 0 < N p := by
    intro p hp
    rcases (hNnn p).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hNz : N p = 0 := heq.symm
      have hA0 : |h (p 0) 0 - v (p 1) 0| ≤ N p := le_max_left _ _
      have hB0 : |h (p 0) 1 - v (p 1) 1| ≤ N p := le_max_right _ _
      rw [hNz] at hA0 hB0
      have eA : h (p 0) 0 = v (p 1) 0 := by
        have := le_antisymm hA0 (abs_nonneg _); rwa [abs_eq_zero, sub_eq_zero] at this
      have eB : h (p 0) 1 = v (p 1) 1 := by
        have := le_antisymm hB0 (abs_nonneg _); rwa [abs_eq_zero, sub_eq_zero] at this
      refine hcon (p 0) (hQ0 p hp) (p 1) (hQ1 p hp) ?_
      ext i; fin_cases i
      · exact eA
      · exact eB
  -- Continuity ingredients.
  have hc0 : Continuous (fun p : Plane => p 0) := by fun_prop
  have hc1 : Continuous (fun p : Plane => p 1) := by fun_prop
  have mt0 : MapsTo (fun p : Plane => p 0) Q (Icc (-1 : ℝ) 1) := fun p hp => hQ0 p hp
  have mt1 : MapsTo (fun p : Plane => p 1) Q (Icc (-1 : ℝ) 1) := fun p hp => hQ1 p hp
  have hHx0 : ContinuousOn (fun p : Plane => h (p 0) 0) Q :=
    (hc0.comp_continuousOn hh).comp hc0.continuousOn mt0
  have hHx1 : ContinuousOn (fun p : Plane => h (p 0) 1) Q :=
    (hc1.comp_continuousOn hh).comp hc0.continuousOn mt0
  have hVx0 : ContinuousOn (fun p : Plane => v (p 1) 0) Q :=
    (hc0.comp_continuousOn hv).comp hc1.continuousOn mt1
  have hVx1 : ContinuousOn (fun p : Plane => v (p 1) 1) Q :=
    (hc1.comp_continuousOn hv).comp hc1.continuousOn mt1
  have hNcont : ContinuousOn N Q :=
    ContinuousOn.sup ((hHx0.sub hVx0).abs) ((hHx1.sub hVx1).abs)
  have hn0c : ContinuousOn n0 Q :=
    (hVx0.sub hHx0).div hNcont (fun p hp => (hNpos p hp).ne')
  have hn1c : ContinuousOn n1 Q :=
    (hHx1.sub hVx1).div hNcont (fun p hp => (hNpos p hp).ne')
  have hFcont : ContinuousOn F Q := by
    have hG : ContinuousOn (fun p : Plane => (![n0 p, n1 p] : Fin 2 → ℝ)) Q := by
      rw [continuousOn_pi]
      intro i; fin_cases i
      · simpa using hn0c
      · simpa using hn1c
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn hG
  -- `F` maps `Q` into `Q`: each coordinate has absolute value `≤ 1`.
  have hbound : ∀ p ∈ Q, |n0 p| ≤ 1 ∧ |n1 p| ≤ 1 := by
    intro p hp
    have hN := hNpos p hp
    refine ⟨?_, ?_⟩
    · change |(v (p 1) 0 - h (p 0) 0) / N p| ≤ 1
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      calc |v (p 1) 0 - h (p 0) 0| = |h (p 0) 0 - v (p 1) 0| := abs_sub_comm _ _
        _ ≤ N p := le_max_left _ _
    · change |(h (p 0) 1 - v (p 1) 1) / N p| ≤ 1
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      exact le_max_right _ _
  have hmaps : MapsTo F Q Q := by
    intro p hp
    obtain ⟨hb0, hb1⟩ := hbound p hp
    exact ⟨mem_Icc.2 (abs_le.1 hb0), mem_Icc.2 (abs_le.1 hb1)⟩
  -- Package as a self-map of `Q` and apply Brouwer.
  let f : C(Q, Q) := ⟨fun p => ⟨F p.1, hmaps p.2⟩, by
    apply Continuous.subtype_mk; exact hFcont.domRestrict⟩
  obtain ⟨x, hx⟩ := hbr Q hconv hcomp hne0 f
  set p₀ : Plane := (x : Plane) with hp0def
  have hp0Q : p₀ ∈ Q := x.2
  have hN := hNpos p₀ hp0Q
  have hfix : F p₀ = p₀ := congrArg Subtype.val hx
  have hfix0 : p₀ 0 = (v (p₀ 1) 0 - h (p₀ 0) 0) / N p₀ := by
    have e : (F p₀) 0 = (v (p₀ 1) 0 - h (p₀ 0) 0) / N p₀ := rfl
    rw [← e, hfix]
  have hfix1 : p₀ 1 = (h (p₀ 0) 1 - v (p₀ 1) 1) / N p₀ := by
    have e : (F p₀) 1 = (h (p₀ 0) 1 - v (p₀ 1) 1) / N p₀ := rfl
    rw [← e, hfix]
  -- The fixed point lies on the boundary: `|p₀ 0| = 1` or `|p₀ 1| = 1`.
  have a0 : |p₀ 0| = |h (p₀ 0) 0 - v (p₀ 1) 0| / N p₀ := by
    conv_lhs => rw [hfix0]
    rw [abs_div, abs_of_pos hN, abs_sub_comm]
  have a1 : |p₀ 1| = |h (p₀ 0) 1 - v (p₀ 1) 1| / N p₀ := by
    conv_lhs => rw [hfix1]
    rw [abs_div, abs_of_pos hN]
  have hbdry : |p₀ 0| = 1 ∨ |p₀ 1| = 1 := by
    rcases le_total |h (p₀ 0) 1 - v (p₀ 1) 1| |h (p₀ 0) 0 - v (p₀ 1) 0| with hle | hle
    · left
      have hNA : N p₀ = |h (p₀ 0) 0 - v (p₀ 1) 0| := max_eq_left hle
      rw [a0, hNA]; exact div_self (by rw [← hNA]; exact hN.ne')
    · right
      have hNB : N p₀ = |h (p₀ 0) 1 - v (p₀ 1) 1| := max_eq_right hle
      rw [a1, hNB]; exact div_self (by rw [← hNB]; exact hN.ne')
  -- Boundary contradiction in each of the four cases.
  rcases hbdry with hb | hb
  · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 hb with hpos | hneg
    · -- `p₀ 0 = 1`: then `h (p₀ 0) 0 = b ≥ v (p₀ 1) 0`, so `p₀ 0 ≤ 0`.
      have hh0b : h (p₀ 0) 0 = b := by rw [hpos]; exact hh2
      have hvle : v (p₀ 1) 0 ≤ b := (hvE (p₀ 1) (hQ1 p₀ hp0Q)).1.2
      have : p₀ 0 ≤ 0 := by
        rw [hfix0]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      linarith
    · -- `p₀ 0 = -1`: then `h (p₀ 0) 0 = a ≤ v (p₀ 1) 0`, so `p₀ 0 ≥ 0`.
      have hh0a : h (p₀ 0) 0 = a := by rw [hneg]; exact hh1
      have hvge : a ≤ v (p₀ 1) 0 := (hvE (p₀ 1) (hQ1 p₀ hp0Q)).1.1
      have : 0 ≤ p₀ 0 := by rw [hfix0]; exact div_nonneg (by linarith) hN.le
      linarith
  · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 hb with hpos | hneg
    · -- `p₀ 1 = 1`: then `v (p₀ 1) 1 = d ≥ h (p₀ 0) 1`, so `p₀ 1 ≤ 0`.
      have hv1d : v (p₀ 1) 1 = d := by rw [hpos]; exact hv2
      have hhle : h (p₀ 0) 1 ≤ d := (hhE (p₀ 0) (hQ0 p₀ hp0Q)).2.2
      have : p₀ 1 ≤ 0 := by
        rw [hfix1]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      linarith
    · -- `p₀ 1 = -1`: then `v (p₀ 1) 1 = c ≤ h (p₀ 0) 1`, so `p₀ 1 ≥ 0`.
      have hv1c : v (p₀ 1) 1 = c := by rw [hneg]; exact hv1
      have hhge : c ≤ h (p₀ 0) 1 := (hhE (p₀ 0) (hQ0 p₀ hp0Q)).2.1
      have : 0 ≤ p₀ 1 := by rw [hfix1]; exact div_nonneg (by linarith) hN.le
      linarith

/-! ### Foundational topology of a Jordan curve `J = range r`

A Jordan curve is `J = range r` for `r : S¹ → ℝ²` continuous and injective. Here we
collect the purely topological facts about `J` and its complement that Maehara's
argument needs, independent of Brouwer:

* `J` is compact and closed, its complement `Jᶜ` is open (tasks 1-2);
* `r` is a (closed) embedding, so `J ≃ₜ S¹` (task 3);
* `Jᶜ` has exactly one unbounded connected component (PRELIM (a));
* each connected component of `Jᶜ` is open and path-connected (PRELIM (b)).
-/

/-- The plane has rank `2 > 1`; the engine for connectivity of ball-complements. -/
theorem one_lt_rank_plane : 1 < Module.rank ℝ Plane := by
  have h : Module.rank ℝ Plane = 2 := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num
  rw [h]; norm_num

/-- The exterior `{x | R < ‖x‖}` of a closed ball is connected in the plane
(dimension `2 > 1`). Proved as the continuous image of the connected set
`sphere 0 1 ×ˢ Ioi R` under `(s, t) ↦ t • s`. -/
theorem isConnected_compl_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsConnected {x : Plane | R < ‖x‖} := by
  have hconn : IsConnected ((sphere (0 : Plane) 1) ×ˢ (Ioi R)) :=
    (isConnected_sphere one_lt_rank_plane 0 zero_le_one).prod isConnected_Ioi
  have himg := hconn.image (fun p : Plane × ℝ => p.2 • p.1)
    (continuous_snd.smul continuous_fst).continuousOn
  have hset : {x : Plane | R < ‖x‖}
      = (fun p : Plane × ℝ => p.2 • p.1) '' ((sphere (0 : Plane) 1) ×ˢ (Ioi R)) := by
    ext x
    simp only [mem_ofPred_eq, mem_image, mem_prod, mem_Ioi, Prod.exists]
    constructor
    · intro hx
      have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx
      refine ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (ne_of_gt hxpos)]
      · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos), one_smul]
    · rintro ⟨s, t, ⟨hs, ht⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hs
      rw [norm_smul, hs, mul_one, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR ht)]
      exact ht
  rw [hset]; exact himg

section JordanCurveData

variable (r : sphere (0 : Plane) 1 → Plane)

/-- **Task 1.** The Jordan curve `J = range r` is compact (continuous image of the
compact circle `S¹`). -/
theorem jordanCurve_isCompact (hcont : Continuous r) : IsCompact (range r) :=
  isCompact_range hcont

/-- **Task 1.** The Jordan curve `J = range r` is closed (compact in a Hausdorff
space). -/
theorem jordanCurve_isClosed (hcont : Continuous r) : IsClosed (range r) :=
  (jordanCurve_isCompact r hcont).isClosed

/-- **Task 2.** The complement of the Jordan curve is open. -/
theorem isOpen_compl_jordanCurve (hcont : Continuous r) : IsOpen (range r)ᶜ :=
  (jordanCurve_isClosed r hcont).isOpen_compl

/-- **Task 3.** A continuous injection of the compact circle into the plane is a
closed embedding. -/
theorem r_isClosedEmbedding (hcont : Continuous r) (hinj : Injective r) :
    Topology.IsClosedEmbedding r :=
  hcont.isClosedEmbedding hinj

/-- **Task 3.** `r` is a topological embedding. -/
theorem r_isEmbedding (hcont : Continuous r) (hinj : Injective r) :
    Topology.IsEmbedding r :=
  (r_isClosedEmbedding r hcont hinj).isEmbedding

/-- **Task 3.** The Jordan curve `J = range r` is homeomorphic to the circle `S¹`. -/
noncomputable def jordanCurveHomeo (hcont : Continuous r) (hinj : Injective r) :
    sphere (0 : Plane) 1 ≃ₜ (range r) :=
  (r_isEmbedding r hcont hinj).toHomeomorph

/-- A radius `R ≥ 0` with `range r ⊆ closedBall 0 R` (compact ⇒ bounded). -/
private theorem exists_jordanCurve_bound (hcont : Continuous r) :
    ∃ R : ℝ, 0 ≤ R ∧ range r ⊆ closedBall (0 : Plane) R := by
  obtain ⟨R, hR⟩ := (jordanCurve_isCompact r hcont).isBounded.subset_closedBall 0
  exact ⟨max R 0, le_max_right R 0,
    hR.trans (closedBall_subset_closedBall (le_max_left R 0))⟩

/-- **PRELIM (a).** `Jᶜ` has an unbounded connected component: pick any point in the
cobounded exterior `{x | R < ‖x‖}` of a ball containing `J`; that exterior is
connected, lies in `Jᶜ`, and is unbounded, so the component containing it is
unbounded. -/
theorem exists_unbounded_component (hcont : Continuous r) :
    ∃ x ∈ (range r)ᶜ, ¬ IsBounded (connectedComponentIn (range r)ᶜ x) := by
  obtain ⟨R, hR0, hsub⟩ := exists_jordanCurve_bound r hcont
  have hEconn : IsConnected {z : Plane | R < ‖z‖} := isConnected_compl_closedBall hR0
  have hEsub : {z : Plane | R < ‖z‖} ⊆ (range r)ᶜ := by
    intro z hz hzr
    have := hsub hzr
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  have hEnb : ¬ IsBounded {z : Plane | R < ‖z‖} := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    obtain ⟨z, hz⟩ := NormedSpace.exists_lt_norm ℝ Plane (max M R)
    have hzE : z ∈ {z : Plane | R < ‖z‖} := lt_of_le_of_lt (le_max_right M R) hz
    have hzM := hM hzE
    rw [mem_closedBall_zero_iff] at hzM
    exact absurd (le_max_left M R) (not_le.2 (lt_of_lt_of_le hz hzM))
  obtain ⟨x, hxE⟩ := hEconn.nonempty
  refine ⟨x, hEsub hxE, ?_⟩
  have hEcomp : {z : Plane | R < ‖z‖} ⊆ connectedComponentIn (range r)ᶜ x :=
    hEconn.isPreconnected.subset_connectedComponentIn hxE hEsub
  exact fun hbdd => hEnb (hbdd.subset hEcomp)

/-- **PRELIM (a).** Any two unbounded components of `Jᶜ` coincide: each unbounded
component must meet the connected cobounded exterior `{x | R < ‖x‖}`, which therefore
lies in a single component. -/
theorem unbounded_component_unique (hcont : Continuous r) {x y : Plane}
    (hxu : ¬ IsBounded (connectedComponentIn (range r)ᶜ x))
    (hyu : ¬ IsBounded (connectedComponentIn (range r)ᶜ y)) :
    connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  obtain ⟨R, hR0, hsub⟩ := exists_jordanCurve_bound r hcont
  set E : Set Plane := {z : Plane | R < ‖z‖} with hE
  have hEconn : IsConnected E := isConnected_compl_closedBall hR0
  have hEsub : E ⊆ (range r)ᶜ := by
    intro z hz hzr
    have := hsub hzr
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  -- An unbounded component meets `E`.
  have meetsE : ∀ z : Plane,
      ¬ IsBounded (connectedComponentIn (range r)ᶜ z) →
      ∃ w ∈ E, w ∈ connectedComponentIn (range r)ᶜ z := by
    intro z hz
    by_contra hcon
    push Not at hcon
    apply hz
    have hsubBall : connectedComponentIn (range r)ᶜ z ⊆ closedBall (0 : Plane) R := by
      intro w hw
      rw [mem_closedBall_zero_iff]
      by_contra hwn
      exact hcon w (not_le.1 hwn) hw
    exact isBounded_closedBall.subset hsubBall
  obtain ⟨p, hpE⟩ := hEconn.nonempty
  have hEcomp : E ⊆ connectedComponentIn (range r)ᶜ p :=
    hEconn.isPreconnected.subset_connectedComponentIn hpE hEsub
  -- Both components equal the component of `p`.
  obtain ⟨wx, hwxE, hwxc⟩ := meetsE x hxu
  obtain ⟨wy, hwyE, hwyc⟩ := meetsE y hyu
  have hx : connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ p := by
    rw [connectedComponentIn_eq hwxc, ← connectedComponentIn_eq (hEcomp hwxE)]
  have hy : connectedComponentIn (range r)ᶜ y = connectedComponentIn (range r)ᶜ p := by
    rw [connectedComponentIn_eq hwyc, ← connectedComponentIn_eq (hEcomp hwyE)]
  rw [hx, hy]

/-- **PRELIM (b).** Each connected component of `Jᶜ` is open (`Jᶜ` is open and the
plane is locally connected). -/
theorem isOpen_component (hcont : Continuous r) (x : Plane) :
    IsOpen (connectedComponentIn (range r)ᶜ x) :=
  (isOpen_compl_jordanCurve r hcont).connectedComponentIn

/-- **PRELIM (b).** Each connected component of `Jᶜ` is path-connected (it is open
and connected in the locally path-connected plane). -/
theorem isPathConnected_component (hcont : Continuous r) {x : Plane}
    (hx : x ∈ (range r)ᶜ) :
    IsPathConnected (connectedComponentIn (range r)ᶜ x) :=
  ((isOpen_component r hcont x).isConnected_iff_isPathConnected).mp
    (isConnected_connectedComponentIn_iff.mpr hx)

end JordanCurveData

/-- **Maehara's Lemma 1 core: "an arc does not separate the plane".** If `A ⊆ ℝ²`
is an arc (homeomorphic to the unit interval `[0,1]`) then its complement `Aᶜ` is
connected.

Proof (Brouwer + Tietze). If `Aᶜ` were disconnected it would have a bounded
component (there is a unique unbounded one, containing the cobounded exterior of a
disc through `A`); pick a point `o` in it. Since `A ≃ₜ [0,1]` and `[0,1]` is an
absolute retract (`TietzeExtension`), the identity `A → A` extends to a retraction
`ρ : ℝ² → A`. Glue `ρ` on the component `K ∋ o` with the identity elsewhere: the two
pieces agree on `frontier K ⊆ A` where `ρ = id`, giving a continuous
`Q : ℝ² → ℝ²∖{o}` that is the identity outside `K`. On a large disc `D = closedBall o R`
containing `A` and `K`, the map `z ↦ o - R·(Q z - o)/‖Q z - o‖` (antipodal radial
projection about `o`) is a fixed-point-free continuous self-map of `D`, contradicting
Brouwer. -/
theorem arc_not_separates (hbr : BrouwerFPT) {A : Set Plane}
    (φ : A ≃ₜ unitInterval) : IsConnected Aᶜ := by
  classical
  -- `A` is compact, hence closed, bounded, and `Aᶜ` is open.
  have : CompactSpace ↥unitInterval := inferInstance
  have hcsA : CompactSpace ↥A := φ.symm.compactSpace
  have hAcpt : IsCompact A := isCompact_iff_compactSpace.mpr hcsA
  have hAcl : IsClosed A := hAcpt.isClosed
  have hAbd : IsBounded A := hAcpt.isBounded
  have hAopen : IsOpen Aᶜ := hAcl.isOpen_compl
  -- Tietze retraction `ρ : ℝ² → ℝ²`, `range ρ ⊆ A`, `ρ = id` on `A`.
  have : TietzeExtension ↥A := TietzeExtension.of_homeo φ
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hAcl (ContinuousMap.id ↥A)
  set ρ : Plane → Plane := fun x => (g x : Plane) with hρdef
  have hρcont : Continuous ρ := continuous_subtype_val.comp g.continuous
  have hρmem : ∀ x, ρ x ∈ A := fun x => (g x).2
  have hρid : ∀ a ∈ A, ρ a = a := by
    intro a ha
    have h1 := DFunLike.congr_fun hg ⟨a, ha⟩
    simp only [ContinuousMap.restrict_apply, ContinuousMap.id_apply] at h1
    change (g a : Plane) = a
    exact congrArg Subtype.val h1
  -- A radius `R0 ≥ 0` with `A ⊆ closedBall 0 R0`; the cobounded exterior `E`.
  obtain ⟨R0, hR0, hAsub⟩ : ∃ R0 : ℝ, 0 ≤ R0 ∧ A ⊆ closedBall (0 : Plane) R0 := by
    obtain ⟨R, hR⟩ := hAbd.subset_closedBall (0 : Plane)
    exact ⟨max R 0, le_max_right R 0,
      hR.trans (closedBall_subset_closedBall (le_max_left R 0))⟩
  set E : Set Plane := {z : Plane | R0 < ‖z‖} with hEdef
  have hEconn : IsConnected E := isConnected_compl_closedBall hR0
  have hEsub : E ⊆ Aᶜ := by
    intro z hz hzA
    have := hAsub hzA
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  obtain ⟨p, hpE⟩ := hEconn.nonempty
  have hpAc : p ∈ Aᶜ := hEsub hpE
  have hEcomp : E ⊆ connectedComponentIn Aᶜ p :=
    hEconn.isPreconnected.subset_connectedComponentIn hpE hEsub
  -- An unbounded component meets `E`.
  have meetsE : ∀ z, z ∈ Aᶜ → ¬ IsBounded (connectedComponentIn Aᶜ z) →
      ∃ w ∈ E, w ∈ connectedComponentIn Aᶜ z := by
    intro z _ hzu
    by_contra hcon
    push Not at hcon
    apply hzu
    have hsubBall : connectedComponentIn Aᶜ z ⊆ closedBall (0 : Plane) R0 := by
      intro w hw
      rw [mem_closedBall_zero_iff]
      by_contra hwn
      exact hcon w (not_le.1 hwn) hw
    exact isBounded_closedBall.subset hsubBall
  refine ⟨⟨p, hpAc⟩, ?_⟩
  -- `IsPreconnected Aᶜ`: either every component is unbounded (⇒ connected), or a
  -- bounded one exists (⇒ Brouwer contradiction).
  by_cases hbdd : ∃ o ∈ Aᶜ, IsBounded (connectedComponentIn Aᶜ o)
  · -- Bounded component: derive a contradiction via Brouwer.
    exfalso
    obtain ⟨o, hoAc, hKbd⟩ := hbdd
    set K : Set Plane := connectedComponentIn Aᶜ o with hKdef
    have hoK : o ∈ K := mem_connectedComponentIn hoAc
    have hKopen : IsOpen K := hAopen.connectedComponentIn
    have hoA : o ∉ A := hoAc
    -- `frontier K ⊆ A`.
    have hfrontier : frontier K ⊆ A := by
      intro x hx
      by_contra hxA
      have hxAc : x ∈ Aᶜ := hxA
      have hxcl : x ∈ closure K := frontier_subset_closure hx
      have hxnK : x ∉ K := by
        intro hxK
        have : x ∈ K ∩ frontier K := ⟨hxK, hx⟩
        rw [hKopen.inter_frontier_eq] at this
        exact absurd this (Set.notMem_empty x)
      have hCxopen : IsOpen (connectedComponentIn Aᶜ x) := hAopen.connectedComponentIn
      have hxCx : x ∈ connectedComponentIn Aᶜ x := mem_connectedComponentIn hxAc
      rw [_root_.mem_closure_iff] at hxcl
      obtain ⟨w, hwCx, hwK⟩ := hxcl _ hCxopen hxCx
      have e1 : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwCx
      rw [hKdef] at hwK
      have e2 : connectedComponentIn Aᶜ o = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwK
      rw [e1, ← e2] at hxCx
      rw [← hKdef] at hxCx
      exact hxnK hxCx
    -- A radius `R > 0` with `A ⊆ ball o R` and `K ⊆ ball o R`.
    obtain ⟨R, hRpos, hAR, hKR⟩ :
        ∃ R : ℝ, 0 < R ∧ A ⊆ ball o R ∧ K ⊆ ball o R := by
      obtain ⟨rA, hrA⟩ := hAbd.subset_closedBall o
      obtain ⟨rK, hrK⟩ := hKbd.subset_closedBall o
      refine ⟨max (max rA rK) 0 + 1, by positivity, ?_, ?_⟩
      · exact hrA.trans (closedBall_subset_ball
          (lt_of_le_of_lt ((le_max_left rA rK).trans (le_max_left _ 0)) (lt_add_one _)))
      · exact hrK.trans (closedBall_subset_ball
          (lt_of_le_of_lt ((le_max_right rA rK).trans (le_max_left _ 0)) (lt_add_one _)))
    -- The glued map `Q` and its properties.
    set Q : Plane → Plane := K.piecewise ρ id with hQdef
    have hQcont : Continuous Q := by
      refine Continuous.piecewise ?_ hρcont continuous_id
      intro a ha
      show ρ a = id a
      simpa using hρid a (hfrontier ha)
    have hQA : ∀ z ∈ K, Q z = ρ z := fun z hz => by
      rw [hQdef]; exact Set.piecewise_eq_of_mem _ _ _ hz
    have hQid : ∀ z, z ∉ K → Q z = z := fun z hz => by
      rw [hQdef]; exact Set.piecewise_eq_of_notMem _ _ _ hz
    have hQne : ∀ z, Q z ≠ o := by
      intro z
      by_cases hz : z ∈ K
      · rw [hQA z hz]; intro h; exact hoA (h ▸ hρmem z)
      · rw [hQid z hz]; intro h; apply hz; rw [h]; exact hoK
    -- The antipodal radial projection about `o`.
    set Φ : Plane → Plane := fun z => o - R • (‖Q z - o‖⁻¹ • (Q z - o)) with hΦdef
    have hΦcont : Continuous Φ := by
      have h1 : Continuous (fun z => Q z - o) := hQcont.sub continuous_const
      have h2 : Continuous (fun z => (‖Q z - o‖)⁻¹) :=
        h1.norm.inv₀ (fun z => by
          simp only [ne_eq, norm_eq_zero, sub_eq_zero]; exact hQne z)
      -- Each step is ascribed explicitly, and the scalar is passed to `const_smul`
      -- rather than inferred: since Mathlib `905b9581`, `continuous_const.smul _`
      -- leaves the scalar an undetermined metavariable, because unifying the `Pi`-level
      -- `f • g` of `Continuous.smul` against `fun z ↦ R • …` no longer solves for it.
      have h3 : Continuous (fun z => (‖Q z - o‖)⁻¹ • (Q z - o)) := h2.smul h1
      have h4 : Continuous (fun z => R • ((‖Q z - o‖)⁻¹ • (Q z - o))) := h3.const_smul R
      exact continuous_const.sub h4
    have hΦsphere : ∀ z, ‖Φ z - o‖ = R := by
      intro z
      have hne : Q z - o ≠ 0 := sub_ne_zero.mpr (hQne z)
      have hw1 : ‖‖Q z - o‖⁻¹ • (Q z - o)‖ = 1 := norm_smul_inv_norm hne
      have he : Φ z - o = -(R • (‖Q z - o‖⁻¹ • (Q z - o))) := by
        simp only [hΦdef]; abel
      rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hRpos.le, hw1,
        mul_one]
    -- `Φ` maps `D = closedBall o R` into `D`.
    set D : Set Plane := closedBall o R with hDdef
    have hΦD : ∀ z ∈ D, Φ z ∈ D := by
      intro z _
      rw [hDdef, mem_closedBall]
      exact le_of_eq (by rw [dist_eq_norm]; exact hΦsphere z)
    have hDconv : Convex ℝ D := convex_closedBall o R
    have hDcomp : IsCompact D := isCompact_closedBall o R
    have hDne : D.Nonempty := ⟨o, by rw [hDdef]; exact mem_closedBall_self hRpos.le⟩
    -- Package as a self-map of `D` and apply Brouwer.
    let F : C(↥D, ↥D) :=
      ⟨fun z => ⟨Φ z.1, hΦD z.1 z.2⟩,
        Continuous.subtype_mk (hΦcont.comp continuous_subtype_val) _⟩
    obtain ⟨x, hx⟩ := hbr D hDconv hDcomp hDne F
    set x0 : Plane := (x : Plane) with hx0
    have hfix : Φ x0 = x0 := congrArg Subtype.val hx
    have hx0R : ‖x0 - o‖ = R := by rw [← hfix]; exact hΦsphere x0
    have hx0nK : x0 ∉ K := by
      intro hk
      have hin := hKR hk
      rw [mem_ball, dist_eq_norm, hx0R] at hin
      exact lt_irrefl R hin
    have hQx0 : Q x0 = x0 := hQid x0 hx0nK
    have hcompute : Φ x0 = o - (x0 - o) := by
      simp only [hΦdef]
      rw [hQx0, hx0R, smul_smul, mul_inv_cancel₀ hRpos.ne', one_smul]
    rw [hcompute] at hfix
    have hz : x0 - o = 0 := by
      have e : (2 : ℝ) • (x0 - o) = x0 - (o - (x0 - o)) := by rw [two_smul]; abel
      have h20 : (2 : ℝ) • (x0 - o) = 0 := by rw [e, hfix]; abel
      exact (smul_eq_zero.mp h20).resolve_left (by norm_num)
    rw [hz, norm_zero] at hx0R
    exact absurd hx0R.symm hRpos.ne'
  · -- No bounded component: every point's component equals that of `p`.
    push Not at hbdd
    have hAeq : Aᶜ ⊆ connectedComponentIn Aᶜ p := by
      intro x hx
      obtain ⟨w, hwE, hwx⟩ := meetsE x hx (hbdd x hx)
      have e1 : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwx
      have e2 : connectedComponentIn Aᶜ p = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq (hEcomp hwE)
      have hxc : x ∈ connectedComponentIn Aᶜ x := mem_connectedComponentIn hx
      rw [e1, ← e2] at hxc
      exact hxc
    have hsup : connectedComponentIn Aᶜ p ⊆ Aᶜ := connectedComponentIn_subset Aᶜ p
    rw [Set.Subset.antisymm hAeq hsup]
    exact (isConnected_connectedComponentIn_iff.mpr hpAc).isPreconnected

/-- **Maehara's Lemma 1.** If `ℝ²∖J` is disconnected, each component has the whole
Jordan curve `J = range r` as its boundary. We state (and prove) the sharper
unconditional form: for any `x` in the complement, the frontier of its connected
component equals `range r`.

Proof (arc argument, via `arc_not_separates`). Write `U` for the component of `x`.
Always `frontier U ⊆ range r` (a boundary point outside the curve would lie in some
component of the open complement, forcing it into `U` — impossible for a frontier
point). If `frontier U ⊊ range r`, transport the proper closed set
`C = r⁻¹(frontier U) ⊊ S¹` to a proper closed arc `A₀` (via `exists_proper_arc`) and
push forward to `A = r '' A₀`, a proper arc with `frontier U ⊆ A ⊊ range r`. Then
`Aᶜ` is connected (`arc_not_separates`), yet `U` and `(closure U)ᶜ` split it into two
nonempty relatively open pieces (`x ∈ U`; a point of `range r ∖ A` lies in
`(closure U)ᶜ`) — contradicting connectedness. -/
theorem component_boundary_eq (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    {x : Plane} (hx : x ∈ (range r)ᶜ)
    (_hy : ∃ y ∈ (range r)ᶜ,
      connectedComponentIn (range r)ᶜ y ≠ connectedComponentIn (range r)ᶜ x) :
    frontier (connectedComponentIn (range r)ᶜ x) = range r := by
  classical
  set U := connectedComponentIn (range r)ᶜ x with hUdef
  have hUopen : IsOpen U := isOpen_component r hcont x
  have hxU : x ∈ U := mem_connectedComponentIn hx
  -- **Step 1: `frontier U ⊆ range r`.**
  have hsub : frontier U ⊆ range r := by
    intro w hw
    by_contra hwr
    have hwc : w ∈ (range r)ᶜ := hwr
    have hwcl : w ∈ closure U := frontier_subset_closure hw
    have hWopen : IsOpen (connectedComponentIn (range r)ᶜ w) :=
      isOpen_component r hcont w
    have hwW : w ∈ connectedComponentIn (range r)ᶜ w := mem_connectedComponentIn hwc
    rw [_root_.mem_closure_iff] at hwcl
    obtain ⟨v, hvW, hvU⟩ := hwcl _ hWopen hwW
    have e1 : connectedComponentIn (range r)ᶜ w = connectedComponentIn (range r)ᶜ v :=
      connectedComponentIn_eq hvW
    have e2 : U = connectedComponentIn (range r)ᶜ v := connectedComponentIn_eq hvU
    have hwU : w ∈ U := by rw [e2, ← e1]; exact hwW
    have : w ∈ U ∩ frontier U := ⟨hwU, hw⟩
    rw [hUopen.inter_frontier_eq] at this
    exact absurd this (Set.notMem_empty w)
  -- **Step 2: `frontier U = range r`.**
  by_contra hne
  have hssub : frontier U ⊂ range r := hsub.ssubset_of_ne hne
  -- Pull `frontier U` back to a proper closed subset `C ⊊ S¹`.
  set C : Set (sphere (0 : Plane) 1) := r ⁻¹' frontier U with hCdef
  have hCclosed : IsClosed C := isClosed_frontier.preimage hcont
  have hCne : C ≠ univ := by
    intro h
    apply hne
    refine Set.Subset.antisymm hsub ?_
    intro w hw
    obtain ⟨s, rfl⟩ := hw
    have hsC : s ∈ C := h.symm ▸ mem_univ s
    exact hsC
  obtain ⟨A₀, hCA0, hA0ne, hA0closed, ⟨e0⟩⟩ :=
    JordanCurve.Arcs.exists_proper_arc hCclosed hCne
  set A : Set Plane := r '' A₀ with hAdef
  -- Compactness of the sphere subtype ⇒ of `A₀`, giving `A ≃ₜ unitInterval`.
  have hcsSphere : CompactSpace (sphere (0 : Plane) 1) :=
    JordanCurve.Arcs.circleHomeoSphere.compactSpace
  have hcsA0 : CompactSpace ↥A₀ := isCompact_iff_compactSpace.mp hA0closed.isCompact
  have eImg : (↥A₀) ≃ₜ (↥A) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.image r A₀ hinj)
      (continuous_induced_rng.2 (hcont.comp continuous_subtype_val))
  have eA : A ≃ₜ unitInterval := eImg.symm.trans e0
  -- `A ⊆ range r`, `frontier U ⊆ A`, and a point of `range r ∖ A`.
  have hAr : A ⊆ range r := by
    rw [hAdef]; rintro _ ⟨s, _, rfl⟩; exact ⟨s, rfl⟩
  have hfrA : frontier U ⊆ A := by
    rw [hAdef]
    intro w hw
    obtain ⟨s, rfl⟩ := hsub hw
    exact ⟨s, hCA0 hw, rfl⟩
  obtain ⟨s₀, hs₀⟩ := (Set.ne_univ_iff_exists_notMem A₀).1 hA0ne
  have hq'r : r s₀ ∈ range r := ⟨s₀, rfl⟩
  have hq'A : r s₀ ∉ A := by
    rw [hAdef]
    rintro ⟨s, hsA, hss⟩
    exact hs₀ (hinj hss ▸ hsA)
  -- `Aᶜ` is connected (an arc does not separate the plane).
  have hAconn : IsConnected Aᶜ := arc_not_separates hbr eA
  -- The clopen (preconnectedness) contradiction.
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset (range r)ᶜ x
  have hUAc : U ⊆ Aᶜ := hUsub.trans (compl_subset_compl.mpr hAr)
  have hxAc : x ∈ Aᶜ := hUAc hxU
  have hVopen : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  have hcover : Aᶜ ⊆ U ∪ (closure U)ᶜ := by
    intro w hwAc
    by_cases hwcl : w ∈ closure U
    · left
      by_contra hwU
      have hfr : w ∈ frontier U := by
        refine ⟨hwcl, ?_⟩
        rw [hUopen.interior_eq]; exact hwU
      exact hwAc (hfrA hfr)
    · right; exact hwcl
  have hqV : r s₀ ∈ (closure U)ᶜ := by
    intro hcl
    have hnU : r s₀ ∉ U := fun h => (hUsub h) hq'r
    have hfr : r s₀ ∈ frontier U := by
      refine ⟨hcl, ?_⟩
      rw [hUopen.interior_eq]; exact hnU
    exact hq'A (hfrA hfr)
  obtain ⟨w, _, hwU, hwV⟩ :=
    hAconn.isPreconnected U (closure U)ᶜ hUopen hVopen hcover
      ⟨x, hxAc, hxU⟩ ⟨r s₀, hq'A, hqV⟩
  exact hwV (subset_closure hwU)

/-! ## Normalization foundation (Maehara farthest-pair setup)

We prepare Maehara's WLOG normalization: the diameter of `J = range r` is realized
by a farthest pair `a, b`, and a similarity homeomorphism `T` moves `a ↦ !₂[-1,0]`,
`b ↦ !₂[1,0]`, scaling every distance by the fixed factor `2 / dist a b`.  This
reduces the geometric core (`step_A`, `step_B`) to *normalized* statements in which
the farthest pair sits at `(±1, 0)`. -/

/-- `complexLIE 1 = !₂[1,0]`. -/
private lemma complexLIE_one : Arcs.complexLIE (1 : ℂ) = !₂[(1 : ℝ), 0] := by
  have h := Complex.isometryOfOrthonormal_apply (EuclideanSpace.basisFun (Fin 2) ℝ) (1 : ℂ)
  rw [show Arcs.complexLIE
        = Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) from rfl, h]
  simp only [Complex.one_re, Complex.one_im, one_smul, zero_smul, add_zero,
    EuclideanSpace.basisFun_apply]
  ext i; fin_cases i <;>
    simp

/-- `complexLIE (-1) = !₂[-1,0]`. -/
private lemma complexLIE_negOne : Arcs.complexLIE (-1 : ℂ) = !₂[(-1 : ℝ), 0] := by
  have h := Complex.isometryOfOrthonormal_apply (EuclideanSpace.basisFun (Fin 2) ℝ) (-1 : ℂ)
  rw [show Arcs.complexLIE
        = Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) from rfl, h]
  simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero,
    zero_smul, add_zero, EuclideanSpace.basisFun_apply]
  ext i; fin_cases i <;>
    simp

/-- **Task 1 (farthest pair).** The compact curve `range r` contains a pair `a, b`
realizing the diameter of `J`, and `a ≠ b` (as `r` is injective on the sphere, which
has at least two points). -/
theorem exists_farthest_pair {r : sphere (0 : Plane) 1 → Plane}
    (hcont : Continuous r) (hinj : Injective r) :
    ∃ a ∈ range r, ∃ b ∈ range r,
      (∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ dist a b) ∧ a ≠ b := by
  have hcpt : IsCompact (range r) := jordanCurve_isCompact r hcont
  -- two explicit distinct points on the sphere, hence in `range r`
  have hs1 : (!₂[(1 : ℝ), 0] : Plane) ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  have hs2 : (!₂[(-1 : ℝ), 0] : Plane) ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  set s1 : sphere (0 : Plane) 1 := ⟨!₂[(1 : ℝ), 0], hs1⟩ with hs1def
  set s2 : sphere (0 : Plane) 1 := ⟨!₂[(-1 : ℝ), 0], hs2⟩ with hs2def
  have hs12 : s1 ≠ s2 := by
    intro h
    rw [hs1def, hs2def, Subtype.mk_eq_mk] at h
    have hh : (!₂[(1 : ℝ), 0] : Plane) 0 = (!₂[(-1 : ℝ), 0] : Plane) 0 := by rw [h]
    norm_num [PiLp.toLp_apply] at hh
  have hne : (range r).Nonempty := ⟨r s1, mem_range_self _⟩
  have hprod : IsCompact ((range r) ×ˢ (range r)) := hcpt.prod hcpt
  have hpne : ((range r) ×ˢ (range r)).Nonempty := hne.prod hne
  obtain ⟨⟨a, b⟩, hmem, hmax⟩ :=
    hprod.exists_isMaxOn hpne
      (continuous_dist.continuousOn (s := (range r) ×ˢ (range r)))
  rw [mem_prod] at hmem
  refine ⟨a, hmem.1, b, hmem.2, ?_, ?_⟩
  · intro z hz w hw
    exact isMaxOn_iff.mp hmax (z, w) (mem_prod.mpr ⟨hz, hw⟩)
  · intro hEq
    have hd0 : dist a b = 0 := by rw [hEq, dist_self]
    have hle : dist (r s1) (r s2) ≤ dist a b :=
      isMaxOn_iff.mp hmax (r s1, r s2) (mem_prod.mpr ⟨mem_range_self _, mem_range_self _⟩)
    rw [hd0] at hle
    exact hs12 (hinj (eq_of_dist_eq_zero (le_antisymm hle dist_nonneg)))

/-- **Task 2 (similarity normalization).** Given `a ≠ b` on the plane there is a
similarity homeomorphism `T : Plane ≃ₜ Plane` scaling every distance by the fixed
positive factor `2 / dist a b`, with `T a = !₂[-1,0]` and `T b = !₂[1,0]`. -/
theorem exists_similarity {a b : Plane} (hab : a ≠ b) :
    ∃ T : Plane ≃ₜ Plane,
      (∀ z w, dist (T z) (T w) = (2 / dist a b) * dist z w) ∧
        T a = !₂[(-1 : ℝ), 0] ∧ T b = !₂[(1 : ℝ), 0] := by
  set L := Arcs.complexLIE with hL
  set A : ℂ := L.symm a with hA
  set B : ℂ := L.symm b with hB
  have hBAne : B ≠ A := by
    intro h; exact hab (L.symm.injective h).symm
  have hABne : B - A ≠ 0 := sub_ne_zero.mpr hBAne
  set α : ℂ := 2 / (B - A) with hα
  have hαne : α ≠ 0 := by rw [hα]; exact div_ne_zero two_ne_zero hABne
  set β : ℂ := -(A + B) / (B - A) with hβ
  set e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ α hαne).trans (Homeomorph.addRight β) with he
  have he_apply : ∀ w : ℂ, e w = α * w + β := by
    intro w
    rw [he]
    simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀, Homeomorph.coe_addRight]
  set T : Plane ≃ₜ Plane := (L.symm.toHomeomorph).trans (e.trans L.toHomeomorph) with hT
  have hT_apply : ∀ w : Plane, T w = L (α * L.symm w + β) := by
    intro w
    rw [hT]
    simp only [Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, he_apply]
  refine ⟨T, ?_, ?_, ?_⟩
  · -- distance scaling
    intro z w
    rw [hT_apply, hT_apply, L.dist_map, dist_eq_norm,
      show (α * L.symm z + β) - (α * L.symm w + β) = α * (L.symm z - L.symm w) by ring,
      norm_mul, ← dist_eq_norm, L.symm.dist_map]
    have hαnorm : ‖α‖ = 2 / dist a b := by
      rw [hα, norm_div]
      rw [show ‖(2:ℂ)‖ = 2 by norm_num]
      congr 1
      rw [hB, hA, ← dist_eq_norm, L.symm.dist_map, dist_comm]
    rw [hαnorm]
  · -- T a = !₂[-1,0]
    have hval : α * A + β = -1 := by rw [hα, hβ]; field_simp; ring
    rw [hT_apply, ← hA, hval, hL]; exact complexLIE_negOne
  · -- T b = !₂[1,0]
    have hval : α * B + β = 1 := by rw [hα, hβ]; field_simp; ring
    rw [hT_apply, ← hB, hval, hL]; exact complexLIE_one

/-- Boundedness is preserved and reflected by a map scaling all distances by a fixed
positive factor. -/
theorem isBounded_image_scaling {T : Plane → Plane} {c : ℝ} (hc : 0 < c)
    (hscale : ∀ z w, dist (T z) (T w) = c * dist z w) (K : Set Plane) :
    IsBounded (T '' K) ↔ IsBounded K := by
  simp only [Metric.isBounded_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / c, fun x hx y hy => ?_⟩
    have h := hC (mem_image_of_mem T hx) (mem_image_of_mem T hy)
    rw [hscale] at h
    rw [le_div_iff₀ hc, mul_comm]; exact h
  · rintro ⟨C, hC⟩
    refine ⟨c * C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hC hx hy) hc.le

/-! ### Setup lemmas for the normalized frame (Steps A, B) -/

/-- Squared Euclidean distance in `Plane` expanded in coordinates. -/
private lemma dist_sq_coord (z w : Plane) :
    dist z w ^ 2 = (z 0 - w 0) ^ 2 + (z 1 - w 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- **Setup 1 (the "lens").** In the normalized frame with the farthest pair at
`a = !₂[-1,0]`, `b = !₂[1,0]` and diameter `2` (`hfar`), the whole curve lies in
the rectangle `[-1,1] × [-2,2]`.  For `z ∈ range r`, both `dist z a ≤ 2` and
`dist z b ≤ 2`, i.e. `(z 0+1)²+(z 1)² ≤ 4` and `(z 0-1)²+(z 1)² ≤ 4`; these force
`z 0 ∈ [-1,1]` and (adding them) `(z 0)²+(z 1)² ≤ 3`, hence `z 1 ∈ [-2,2]`. -/
theorem normalized_subset_rectangle
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    range r ⊆ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} := by
  intro z hz
  have hza : dist z (!₂[(-1 : ℝ), 0]) ≤ 2 := hfar z hz _ hm
  have hzb : dist z (!₂[(1 : ℝ), 0]) ≤ 2 := hfar z hz _ hp
  have hza2 : dist z (!₂[(-1 : ℝ), 0]) ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := (!₂[(-1 : ℝ), 0] : Plane))]
  have hzb2 : dist z (!₂[(1 : ℝ), 0]) ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := (!₂[(1 : ℝ), 0] : Plane))]
  rw [dist_sq_coord] at hza2 hzb2
  have ea0 : (!₂[(-1 : ℝ), 0] : Plane) 0 = -1 := by simp
  have ea1 : (!₂[(-1 : ℝ), 0] : Plane) 1 = 0 := by simp
  have eb0 : (!₂[(1 : ℝ), 0] : Plane) 0 = 1 := by simp
  have eb1 : (!₂[(1 : ℝ), 0] : Plane) 1 = 0 := by simp
  rw [ea0, ea1] at hza2
  rw [eb0, eb1] at hzb2
  simp only [mem_ofPred_eq, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [sq_nonneg (z 1)]
  · nlinarith [sq_nonneg (z 1)]
  · nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - 2), sq_nonneg (z 1 + 2)]
  · nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - 2), sq_nonneg (z 1 + 2)]

/-- **`arc_path` (reusable reparametrization).** A path in a set `S ⊆ Plane`
joining `a` to `b` can be reparametrized to a map `h : ℝ → Plane` on the interval
`[-1,1]`, with `h (-1) = a`, `h 1 = b`, continuous on `[-1,1]`, and staying in `S`.
This is exactly the shape required by the `crossing` lemma for the horizontal path
(endpoints on the left/right edges of a rectangle). -/
theorem arc_path {S : Set Plane} {a b : Plane} (hj : JoinedIn S a b) :
    ∃ h : ℝ → Plane, ContinuousOn h (Icc (-1 : ℝ) 1) ∧ h (-1) = a ∧ h 1 = b ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, h t ∈ S := by
  refine ⟨fun t => hj.somePath (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)),
    ?_, ?_, ?_, ?_⟩
  · exact (hj.somePath.continuous.comp
      (continuous_projIcc.comp (by fun_prop))).continuousOn
  · change hj.somePath _ = a
    rw [show Set.projIcc (0 : ℝ) 1 (by norm_num) (((-1 : ℝ) + 1) / 2) = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hj.somePath.source
  · change hj.somePath _ = b
    rw [show Set.projIcc (0 : ℝ) 1 (by norm_num) (((1 : ℝ) + 1) / 2) = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hj.somePath.target
  · intro t _; exact hj.somePath_mem _

/-- **Setup 2 (segment meets curve).** The vertical segment from `s = !₂[0,-2]` to
`n = !₂[0,2]` meets the curve.  Proof via the `crossing` lemma with horizontal path
`h` a curve-path from `a = !₂[-1,0]` to `b = !₂[1,0]` (the curve is path-connected,
reparametrized by `arc_path`) staying in the rectangle `[-1,1]×[-2,2]`
(`normalized_subset_rectangle`), and vertical path `v t = !₂[0, 2t]` running from the
bottom edge `y=-2` to the top edge `y=2`.  Delivers a curve point on the vertical
axis. -/
theorem segment_meets_curve (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (_hinj : Injective r)
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ p ∈ range r, p 0 = 0 ∧ p 1 ∈ Icc (-2 : ℝ) 2 := by
  -- the curve is path-connected (continuous image of the path-connected circle)
  have hsp : IsPathConnected (sphere (0:Plane) 1) :=
    isPathConnected_sphere one_lt_rank_plane 0 (by norm_num)
  have : PathConnectedSpace ↥(sphere (0:Plane) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hsp
  have h1 : IsPathConnected (univ : Set ↥(sphere (0:Plane) 1)) :=
    pathConnectedSpace_iff_univ.mp ‹_›
  have hpc : IsPathConnected (range r) := by
    have := h1.image hcont; rwa [image_univ] at this
  have hjoin : JoinedIn (range r) (!₂[(-1 : ℝ), 0]) (!₂[(1 : ℝ), 0]) :=
    hpc.joinedIn _ hm _ hp
  obtain ⟨h, hcontOn, hh1, hh2, hhmem⟩ := arc_path hjoin
  have hrect := normalized_subset_rectangle hm hp hfar
  -- vertical path `v t = !₂[0, 2t]`
  set v : ℝ → Plane := fun t => !₂[(0 : ℝ), 2 * t] with hvdef
  have hvcont : ContinuousOn v (Icc (-1 : ℝ) 1) := by
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]<;> fun_prop
  have hv0 : ∀ t : ℝ, v t 0 = 0 := by intro t; simp [hvdef]
  have hv1 : ∀ t : ℝ, v t 1 = 2 * t := by intro t; simp [hvdef]
  -- edge/rectangle conditions
  have hhE : ∀ t ∈ Icc (-1 : ℝ) 1, h t 0 ∈ Icc (-1 : ℝ) 1 ∧ h t 1 ∈ Icc (-2 : ℝ) 2 :=
    fun t ht => hrect (hhmem t ht)
  have hvE : ∀ t ∈ Icc (-1 : ℝ) 1, v t 0 ∈ Icc (-1 : ℝ) 1 ∧ v t 1 ∈ Icc (-2 : ℝ) 2 := by
    intro t ht
    rw [mem_Icc] at ht
    refine ⟨?_, ?_⟩
    · rw [hv0]; simp
    · rw [hv1, mem_Icc]; constructor <;> nlinarith [ht.1, ht.2]
  have hh1' : h (-1) 0 = -1 := by rw [hh1]; simp
  have hh2' : h 1 0 = 1 := by rw [hh2]; simp
  have hv1e : v (-1) 1 = -2 := by rw [hv1]; norm_num
  have hv2e : v 1 1 = 2 := by rw [hv1]; norm_num
  obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1 : ℝ) ≤ 1)
    (by norm_num : (-2 : ℝ) ≤ 2) h v hcontOn hvcont hhE hvE hh1' hh2' hv1e hv2e
  refine ⟨h s, hhmem s hs, ?_, ?_⟩
  · rw [heq, hv0]
  · rw [heq]; exact (hvE t ht).2

/-- **Setup 3 (top of the axis).** The intersection of the curve with the vertical
axis `Jax = {p ∈ range r | p 0 = 0}` is compact (closed subset of the compact
curve) and nonempty (`segment_meets_curve`), hence attains its `y`-maximum at some
point `l ∈ range r` with `l 0 = 0`. -/
theorem exists_ymax_on_axis (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ l ∈ range r, l 0 = 0 ∧ ∀ p ∈ range r, p 0 = 0 → p 1 ≤ l 1 := by
  set Jax : Set Plane := {p ∈ range r | p 0 = 0} with hJax
  have hsub : Jax ⊆ range r := fun p hp => hp.1
  have hJaxcl : IsClosed Jax :=
    (jordanCurve_isClosed r hcont).inter (isClosed_eq (by fun_prop) continuous_const)
  have hJaxcpt : IsCompact Jax :=
    (jordanCurve_isCompact r hcont).of_isClosed_subset hJaxcl hsub
  have hne : Jax.Nonempty := by
    obtain ⟨p, hpr, hp0, _⟩ := segment_meets_curve hbr hcont hinj hm hp hfar
    exact ⟨p, hpr, hp0⟩
  have hcy : Continuous (fun p : Plane => p 1) := by fun_prop
  obtain ⟨l, hlJax, hlmax⟩ :=
    hJaxcpt.exists_isMaxOn hne (f := fun p : Plane => p 1) hcy.continuousOn
  refine ⟨l, hlJax.1, hlJax.2, ?_⟩
  intro p hpr hp0
  exact hlmax (show p ∈ Jax from ⟨hpr, hp0⟩)

/-- **Image of an arc under the subtype coercion is again an arc.** If `A ⊆ ↥K`
(a subset of a subtype of `Plane`) is homeomorphic to `unitInterval`, then its image
`(↑) '' A ⊆ Plane` is homeomorphic to `unitInterval`.  The composite coercion
`↥A → Plane` is a continuous injection from a compact space to a Hausdorff space,
hence a (closed) embedding, so `↥A ≃ₜ ↥(range …) = ↥((↑) '' A)`. -/
private lemma planar_arc_homeo {K : Set Plane} {A : Set ↥K}
    (e : A ≃ₜ unitInterval) : Nonempty (((↑) '' A : Set Plane) ≃ₜ unitInterval) := by
  have : CompactSpace ↥A := e.symm.compactSpace
  let k : ↥A → Plane := fun a => ((a : ↥K) : Plane)
  have hkc : Continuous k := continuous_subtype_val.comp continuous_subtype_val
  have hki : Injective k := Subtype.coe_injective.comp Subtype.coe_injective
  have hemb : Topology.IsEmbedding k := (hkc.isClosedEmbedding hki).isEmbedding
  have hrange : Set.range k = ((↑) '' A : Set Plane) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨((Homeomorph.setCongr hrange).symm.trans hemb.toHomeomorph.symm).trans e⟩

/-- **Setup 4 (arc split at `a`, `b`).** The curve `range r` splits at the farthest
pair `a = !₂[-1,0]`, `b = !₂[1,0]` into two closed arcs `J_n`, `J_s ⊆ Plane`, each
`≃ₜ unitInterval`, with `J_n ∪ J_s = range r` and `J_n ∩ J_s = {a, b}`, labelled so
that the `y`-topmost axis point `l` lies in `J_n`. -/
theorem jordan_arcs (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ J_n J_s : Set Plane,
      IsClosed J_n ∧ IsClosed J_s ∧
      J_n ∪ J_s = range r ∧
      J_n ∩ J_s = {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} ∧
      Nonempty (J_n ≃ₜ unitInterval) ∧ Nonempty (J_s ≃ₜ unitInterval) ∧
      IsPathConnected (J_n \ {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]}) ∧
      IsPathConnected (J_s \ {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]}) ∧
      ∃ l ∈ range r, l 0 = 0 ∧ (∀ p ∈ range r, p 0 = 0 → p 1 ≤ l 1) ∧ l ∈ J_n := by
  obtain ⟨l, hlr, hl0, hlmax⟩ := exists_ymax_on_axis hbr hcont hinj hm hp hfar
  set J := jordanCurveHomeo r hcont hinj with hJdef
  have hab : (!₂[(-1 : ℝ), 0] : Plane) ≠ !₂[(1 : ℝ), 0] := by
    intro h
    have h0 : (!₂[(-1 : ℝ), 0] : Plane) 0 = (!₂[(1 : ℝ), 0] : Plane) 0 := by rw [h]
    rw [show (!₂[(-1 : ℝ), 0] : Plane) 0 = -1 from by simp,
        show (!₂[(1 : ℝ), 0] : Plane) 0 = 1 from by simp] at h0
    norm_num at h0
  set x : sphere (0 : Plane) 1 := J.symm ⟨_, hm⟩ with hxdef
  set y : sphere (0 : Plane) 1 := J.symm ⟨_, hp⟩ with hydef
  have hxy : x ≠ y := by
    intro h
    exact hab (Subtype.ext_iff.mp (J.symm.injective h))
  obtain ⟨A₁, A₂, hc1, hc2, hu, hi, ⟨e1⟩, ⟨e2⟩, hpcA1, hpcA2⟩ := Arcs.jordanCurve_split J hxy
  -- transported endpoints: `J x = ⟨a,hm⟩`, `J y = ⟨b,hp⟩`
  have hJx : J x = ⟨_, hm⟩ := J.apply_symm_apply _
  have hJy : J y = ⟨_, hp⟩ := J.apply_symm_apply _
  -- planar images of the two arcs
  set B₁ : Set Plane := (↑) '' A₁ with hB1
  set B₂ : Set Plane := (↑) '' A₂ with hB2
  have hBu : B₁ ∪ B₂ = range r := by
    rw [hB1, hB2, ← Set.image_union, hu, Set.image_univ, Subtype.range_coe]
  have hBi : B₁ ∩ B₂ = {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} := by
    rw [hB1, hB2, ← Set.image_inter Subtype.coe_injective, hi, hJx, hJy,
      Set.image_pair]
  have hn1 : Nonempty (B₁ ≃ₜ unitInterval) := planar_arc_homeo e1
  have hn2 : Nonempty (B₂ ≃ₜ unitInterval) := planar_arc_homeo e2
  have hcl1 : IsClosed B₁ :=
    (isCompact_iff_compactSpace.mpr hn1.some.symm.compactSpace).isClosed
  have hcl2 : IsClosed B₂ :=
    (isCompact_iff_compactSpace.mpr hn2.some.symm.compactSpace).isClosed
  -- transport path-connectedness of the arc interiors down to the plane
  have hpcB1 : IsPathConnected (B₁ \ {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]}) := by
    have h := hpcA1.image (continuous_subtype_val (p := fun z => z ∈ range r))
    rwa [Set.image_sdiff Subtype.coe_injective, Set.image_insert_eq, Set.image_singleton,
      hJx, hJy] at h
  have hpcB2 : IsPathConnected (B₂ \ {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]}) := by
    have h := hpcA2.image (continuous_subtype_val (p := fun z => z ∈ range r))
    rwa [Set.image_sdiff Subtype.coe_injective, Set.image_insert_eq, Set.image_singleton,
      hJx, hJy] at h
  -- `l` lies in `range r = B₁ ∪ B₂`; label the containing arc `J_n`
  have hlB : l ∈ B₁ ∪ B₂ := by rw [hBu]; exact hlr
  rcases hlB with hl | hl
  · exact ⟨B₁, B₂, hcl1, hcl2, hBu, hBi, hn1, hn2, hpcB1, hpcB2, l, hlr, hl0, hlmax, hl⟩
  · refine ⟨B₂, B₁, hcl2, hcl1, ?_, ?_, hn2, hn1, hpcB2, hpcB1, l, hlr, hl0, hlmax, hl⟩
    · rw [Set.union_comm]; exact hBu
    · rw [Set.inter_comm]; exact hBi

/-! ### Path-concatenation infrastructure and Maehara's interior points

The tools below package repeated use of the `crossing` lemma: any bottom-to-top
path in the normalized rectangle meets each arc (`vertical_meets_arc`), together with
the plumbing (`concatPath2`, `concatPath3`) that glues path pieces into one
continuous path on `[-1,1]` whose image is the union of the pieces. -/

/-- An arc `J ⊆ Plane` homeomorphic to `unitInterval` is path-connected. -/
theorem arc_isPathConnected {J : Set Plane} (e : ↥J ≃ₜ unitInterval) :
    IsPathConnected J := by
  have : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected (Set.nonempty_Icc.mpr (by norm_num)))
  have h1 : IsPathConnected (univ : Set unitInterval) := isPathConnected_univ
  have h2 := h1.image
    (show Continuous (fun x : unitInterval => ((e.symm x : ↥J) : Plane)) from
      continuous_subtype_val.comp e.symm.continuous)
  rw [Set.image_univ] at h2
  have hrange : (Set.range fun x : unitInterval => ((e.symm x : ↥J) : Plane)) = J := by
    ext p
    simp only [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩; exact (e.symm x).2
    · intro hp; exact ⟨e ⟨p, hp⟩, by simp⟩
  rwa [hrange] at h2

/-- An arc `J ≃ₜ unitInterval` joins any two of its points inside `J`. -/
theorem arc_joinedIn {J : Set Plane} (e : ↥J ≃ₜ unitInterval)
    {a b : Plane} (ha : a ∈ J) (hb : b ∈ J) : JoinedIn J a b :=
  (arc_isPathConnected e).joinedIn a ha b hb

/-- **Key reusable tool.** Any path `v` running from the bottom edge (`v (-1) 1 = -2`)
to the top edge (`v 1 1 = 2`) of the normalized rectangle `[-1,1]×[-2,2]` must meet an
arc `J` that joins the left point `a = !₂[-1,0]` to the right point `b = !₂[1,0]` inside
the rectangle.  Immediate from `crossing`, using `arc_path` for the horizontal path. -/
theorem vertical_meets_arc (hbr : BrouwerFPT) {J : Set Plane}
    (hJsub : J ⊆ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2})
    (hJoin : JoinedIn J (!₂[(-1 : ℝ), 0]) (!₂[(1 : ℝ), 0]))
    {v : ℝ → Plane} (hvcont : ContinuousOn v (Icc (-1 : ℝ) 1))
    (hvE : ∀ t ∈ Icc (-1 : ℝ) 1, v t 0 ∈ Icc (-1 : ℝ) 1 ∧ v t 1 ∈ Icc (-2 : ℝ) 2)
    (hv1 : v (-1) 1 = -2) (hv2 : v 1 1 = 2) :
    ∃ t ∈ Icc (-1 : ℝ) 1, v t ∈ J := by
  obtain ⟨h, hcontOn, hh1, hh2, hhmem⟩ := arc_path hJoin
  have hhE : ∀ t ∈ Icc (-1 : ℝ) 1, h t 0 ∈ Icc (-1 : ℝ) 1 ∧ h t 1 ∈ Icc (-2 : ℝ) 2 :=
    fun t ht => hJsub (hhmem t ht)
  have hh1' : h (-1) 0 = -1 := by rw [hh1]; simp
  have hh2' : h 1 0 = 1 := by rw [hh2]; simp
  obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1 : ℝ) ≤ 1)
    (by norm_num : (-2 : ℝ) ≤ 2) h v hcontOn hvcont hhE hvE hh1' hh2' hv1 hv2
  exact ⟨t, ht, heq ▸ hhmem s hs⟩

/-- A path piece `f : ℝ → Plane`, continuous on `[-1,1]`, as a `Path (f (-1)) (f 1)`
over `unitInterval` (reparametrized by `s ↦ 2s-1`). -/
private noncomputable def pathOfPiece {f : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) : Path (f (-1)) (f 1) :=
  Path.mk ⟨fun s : unitInterval => f (2 * (s : ℝ) - 1), by
      refine hf.comp_continuous (by fun_prop) (fun s => ?_)
      have hs := s.2; rw [Set.mem_Icc] at hs ⊢
      constructor <;> [linarith [hs.1]; linarith [hs.2]]⟩
    (by norm_num [Set.Icc.coe_zero]) (by norm_num [Set.Icc.coe_one])

private lemma pathOfPiece_range {f : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Set.range (pathOfPiece hf) = f '' Icc (-1 : ℝ) 1 := by
  ext p
  simp only [Set.mem_range, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨s, rfl⟩
    have hs := s.2; rw [Set.mem_Icc] at hs
    exact ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨⟨(y + 1) / 2, by rw [Set.mem_Icc]; constructor <;> linarith⟩, ?_⟩
    change f (2 * ((y + 1) / 2) - 1) = f y
    congr 1; ring

/-- **Path concatenation (2 pieces).** Two path pieces on `[-1,1]` that chain up
(`f 1 = g (-1)`) glue to one path `c` on `[-1,1]` from `f (-1)` to `g 1`, whose image
is contained in the union of the pieces' images. -/
theorem concatPath2 {f g : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hg : ContinuousOn g (Icc (-1 : ℝ) 1))
    (hchain : f 1 = g (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1 : ℝ) 1) ∧ c (-1) = f (-1) ∧ c 1 = g 1 ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, c t ∈ f '' Icc (-1 : ℝ) 1 ∪ g '' Icc (-1 : ℝ) 1 := by
  set P : Path (f (-1)) (g 1) :=
    (pathOfPiece hf).trans ((pathOfPiece hg).cast hchain rfl) with hP
  refine ⟨fun t => P (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)), ?_, ?_, ?_, ?_⟩
  · exact (P.continuous.comp (continuous_projIcc.comp (by fun_prop))).continuousOn
  · change P _ = f (-1)
    rw [show Set.projIcc (0 : ℝ) 1 (by norm_num) (((-1 : ℝ) + 1) / 2) = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact P.source
  · change P _ = g 1
    rw [show Set.projIcc (0 : ℝ) 1 (by norm_num) (((1 : ℝ) + 1) / 2) = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact P.target
  · intro t _
    have hmem : P (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)) ∈ Set.range P := ⟨_, rfl⟩
    rw [hP, Path.trans_range] at hmem
    have hr1 : Set.range (pathOfPiece hf) = f '' Icc (-1 : ℝ) 1 := pathOfPiece_range hf
    have hr2 : Set.range ((pathOfPiece hg).cast hchain rfl) = g '' Icc (-1 : ℝ) 1 := by
      simp only [Path.cast_coe]; exact pathOfPiece_range hg
    rw [hr1, hr2] at hmem
    exact hmem

/-- **Path concatenation (3 pieces).** Three chained path pieces on `[-1,1]` glue to
one path `c` on `[-1,1]` from `f (-1)` to `h 1`, with image in the union of the three
pieces' images. -/
theorem concatPath3 {f g h : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hg : ContinuousOn g (Icc (-1 : ℝ) 1))
    (hh : ContinuousOn h (Icc (-1 : ℝ) 1))
    (hfg : f 1 = g (-1)) (hgh : g 1 = h (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1 : ℝ) 1) ∧ c (-1) = f (-1) ∧ c 1 = h 1 ∧
      ∀ t ∈ Icc (-1 : ℝ) 1,
        c t ∈ f '' Icc (-1 : ℝ) 1 ∪ g '' Icc (-1 : ℝ) 1 ∪ h '' Icc (-1 : ℝ) 1 := by
  obtain ⟨c2, hc2cont, hc2a, hc2b, hc2mem⟩ := concatPath2 hf hg hfg
  obtain ⟨c3, hc3cont, hc3a, hc3b, hc3mem⟩ :=
    concatPath2 hc2cont hh (by rw [hc2b]; exact hgh)
  refine ⟨c3, hc3cont, by rw [hc3a, hc2a], hc3b, fun t ht => ?_⟩
  rcases hc3mem t ht with hin | hin
  · obtain ⟨u, hu, huc⟩ := hin
    exact Set.mem_union_left _ (huc ▸ hc2mem u hu)
  · exact Set.mem_union_right _ hin

/-- **Path concatenation (5 pieces).** Five chained path pieces on `[-1,1]` glue to one
path `c` on `[-1,1]` from `f1 (-1)` to `f5 1`, with image in the union of the five
pieces' images. -/
theorem concatPath5 {f1 f2 f3 f4 f5 : ℝ → Plane}
    (h1 : ContinuousOn f1 (Icc (-1 : ℝ) 1)) (h2 : ContinuousOn f2 (Icc (-1 : ℝ) 1))
    (h3 : ContinuousOn f3 (Icc (-1 : ℝ) 1)) (h4 : ContinuousOn f4 (Icc (-1 : ℝ) 1))
    (h5 : ContinuousOn f5 (Icc (-1 : ℝ) 1))
    (c12 : f1 1 = f2 (-1)) (c23 : f2 1 = f3 (-1)) (c34 : f3 1 = f4 (-1))
    (c45 : f4 1 = f5 (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1 : ℝ) 1) ∧ c (-1) = f1 (-1) ∧ c 1 = f5 1 ∧
      ∀ t ∈ Icc (-1 : ℝ) 1,
        c t ∈ ((((f1 '' Icc (-1 : ℝ) 1 ∪ f2 '' Icc (-1 : ℝ) 1) ∪ f3 '' Icc (-1 : ℝ) 1)
          ∪ f4 '' Icc (-1 : ℝ) 1) ∪ f5 '' Icc (-1 : ℝ) 1) := by
  obtain ⟨c123, hc123cont, hc123a, hc123b, hc123mem⟩ := concatPath3 h1 h2 h3 c12 c23
  obtain ⟨c45, hc45cont, hc45a, hc45b, hc45mem⟩ := concatPath2 h4 h5 c45
  obtain ⟨c, hccont, hca, hcb, hcmem⟩ :=
    concatPath2 hc123cont hc45cont (by rw [hc123b, hc45a]; exact c34)
  refine ⟨c, hccont, by rw [hca, hc123a], by rw [hcb, hc45b], fun t ht => ?_⟩
  rcases hcmem t ht with hin | hin
  · obtain ⟨u, hu, hue⟩ := hin
    have hmem := hc123mem u hu
    rw [hue] at hmem
    exact Or.inl (Or.inl hmem)
  · obtain ⟨u, hu, hue⟩ := hin
    have hmem := hc45mem u hu
    rw [hue] at hmem
    rcases hmem with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- **Interior point `m`.** The intersection `J_n ∩ axis` (`axis = {p | p 0 = 0}`) is
compact and nonempty (it contains `l`), hence attains its `y`-minimum at a point `m`. -/
theorem exists_ymin_Jn_axis {J_n : Set Plane} (hJncl : IsClosed J_n)
    (hcpt : IsCompact J_n) {l : Plane} (hlJn : l ∈ J_n) (hl0 : l 0 = 0) :
    ∃ m ∈ J_n, m 0 = 0 ∧ ∀ p ∈ J_n, p 0 = 0 → m 1 ≤ p 1 := by
  set Jm : Set Plane := {p ∈ J_n | p 0 = 0} with hJm
  have hsub : Jm ⊆ J_n := fun p hp => hp.1
  have hcl : IsClosed Jm :=
    hJncl.inter (isClosed_eq (by fun_prop) continuous_const)
  have hJmcpt : IsCompact Jm := hcpt.of_isClosed_subset hcl hsub
  have hne : Jm.Nonempty := ⟨l, hlJn, hl0⟩
  have hcy : Continuous (fun p : Plane => p 1) := by fun_prop
  obtain ⟨m, hmJm, hmmin⟩ :=
    hJmcpt.exists_isMinOn hne (f := fun p : Plane => p 1) hcy.continuousOn
  exact ⟨m, hmJm.1, hmJm.2, fun p hpJn hp0 => hmmin (show p ∈ Jm from ⟨hpJn, hp0⟩)⟩

/-- **The vertical segment `m → s` meets `J_s`.** With `s = !₂[0,-2]` (below the
rectangle's bottom edge), the axis segment from the interior point `m ∈ J_n` down to
`s` must cross the southern arc `J_s`.  Proof by contradiction: were it disjoint from
`J_s`, the concatenation `s → m` (axis), `m → l` (a path inside `J_n \ {a,b}`),
`l → n` (axis, `n = !₂[0,2]`) would give a bottom-to-top path in the rectangle
avoiding `J_s`, contradicting `vertical_meets_arc` (`J_s` joins `a` to `b`).  The
crossing point lies on the segment, so it sits on the axis at height `≤ m 1`. -/
theorem ms_meets_Js (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (_hcont : Continuous r) (_hinj : Injective r)
    (hmr : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hpr : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane}
    (hUnion : J_n ∪ J_s = range r)
    (hInter : J_n ∩ J_s = {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]})
    (eJs : ↥J_s ≃ₜ unitInterval)
    (hpcJn : IsPathConnected (J_n \ {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]}))
    {l : Plane} (hlJn : l ∈ J_n) (hl0 : l 0 = 0)
    (hlmax : ∀ q ∈ range r, q 0 = 0 → q 1 ≤ l 1)
    {m : Plane} (hmJn : m ∈ J_n) (hm0 : m 0 = 0) :
    ∃ w ∈ J_s, w 0 = 0 ∧ w 1 ≤ m 1 := by
  set a : Plane := !₂[(-1 : ℝ), 0] with ha_def
  set b : Plane := !₂[(1 : ℝ), 0] with hb_def
  -- opaque bottom / top axis points (avoid unfolding `!₂` in later arithmetic)
  obtain ⟨s, hs0, hs1⟩ : ∃ s : Plane, s 0 = 0 ∧ s 1 = -2 :=
    ⟨!₂[(0 : ℝ), -2], by simp, by simp⟩
  obtain ⟨nn, hn0, hn1⟩ : ∃ nn : Plane, nn 0 = 0 ∧ nn 1 = 2 :=
    ⟨!₂[(0 : ℝ), 2], by simp, by simp⟩
  have ha0 : a 0 = -1 := by simp [ha_def]
  have hb0 : b 0 = 1 := by simp [hb_def]
  -- basic containments and the rectangle bound
  have hJnr : J_n ⊆ range r := by rw [← hUnion]; exact subset_union_left
  have hJsr : J_s ⊆ range r := by rw [← hUnion]; exact subset_union_right
  have hrect := normalized_subset_rectangle hmr hpr hfar
  have hmrange : m ∈ range r := hJnr hmJn
  have hlrange : l ∈ range r := hJnr hlJn
  have hm1lb : (-2 : ℝ) ≤ m 1 := (hrect hmrange).2.1
  have hm1ub : m 1 ≤ 2 := (hrect hmrange).2.2
  have hl1lb : (-2 : ℝ) ≤ l 1 := (hrect hlrange).2.1
  have hl1ub : l 1 ≤ 2 := (hrect hlrange).2.2
  -- `a, b ∈ J_s`; `J_s` joins them
  have haJs : a ∈ J_s := by
    have : a ∈ J_n ∩ J_s := by rw [hInter]; exact Set.mem_insert _ _
    exact this.2
  have hbJs : b ∈ J_s := by
    have : b ∈ J_n ∩ J_s := by rw [hInter]; exact Set.mem_insert_of_mem _ rfl
    exact this.2
  have hJoinJs : JoinedIn J_s a b := arc_joinedIn eJs haJs hbJs
  have hJsrect : J_s ⊆ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} :=
    hJsr.trans hrect
  -- `m, l ∉ {a,b}` (they are on the axis `x = 0`, while `a 0 = -1`, `b 0 = 1`)
  have hmab : m ∉ ({a, b} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun p : Plane => p 0) h;
       simp only [hm0, ha0, hb0] at hc; norm_num at hc)
  have hlab : l ∉ ({a, b} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun p : Plane => p 0) h;
       simp only [hl0, ha0, hb0] at hc; norm_num at hc)
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ w ∈ J_s, w 0 = 0 → m 1 < w 1`
  -- three path pieces on `[-1,1]`
  set f1 : ℝ → Plane := fun t => s + ((t + 1) / 2) • (m - s) with hf1def
  set f3 : ℝ → Plane := fun t => l + ((t + 1) / 2) • (nn - l) with hf3def
  obtain ⟨f2, hf2cont, hf2m, hf2l, hf2mem⟩ :=
    arc_path (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
  have hf1cont : ContinuousOn f1 (Icc (-1 : ℝ) 1) := (by fun_prop : Continuous f1).continuousOn
  have hf3cont : ContinuousOn f3 (Icc (-1 : ℝ) 1) := (by fun_prop : Continuous f3).continuousOn
  have hf1_1 : f1 1 = m := by simp [hf1def]
  have hf1_m1 : f1 (-1) = s := by simp [hf1def]
  have hf3_1 : f3 1 = nn := by simp [hf3def]
  have hf3_m1 : f3 (-1) = l := by simp [hf3def]
  have hf1f2 : f1 1 = f2 (-1) := by rw [hf1_1, hf2m]
  have hf2f3 : f2 1 = f3 (-1) := by rw [hf2l, hf3_m1]
  obtain ⟨c, hccont, hcs, hcn, hcmem⟩ := concatPath3 hf1cont hf2cont hf3cont hf1f2 hf2f3
  -- endpoints of the concatenation are on the bottom / top edges
  have hcm1 : c (-1) 1 = -2 := by rw [hcs, hf1_m1]; exact hs1
  have hcn1 : c 1 1 = 2 := by rw [hcn, hf3_1]; exact hn1
  -- the three pieces stay in the rectangle
  have hf1x : ∀ t, f1 t 0 = 0 := fun t => by simp [hf1def, hs0, hm0]
  have hf3x : ∀ t, f3 t 0 = 0 := fun t => by simp [hf3def, hl0, hn0]
  have hf1y_le : ∀ t ∈ Icc (-1 : ℝ) 1, f1 t 1 ≤ m 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hs1]
    nlinarith [ht.1, ht.2, hm1lb]
  have hf1y_ge : ∀ t ∈ Icc (-1 : ℝ) 1, (-2 : ℝ) ≤ f1 t 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hs1]
    nlinarith [ht.1, ht.2, hm1lb]
  have hf3y_ge : ∀ t ∈ Icc (-1 : ℝ) 1, l 1 ≤ f3 t 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hn1]
    nlinarith [ht.1, ht.2, hl1ub]
  have hf3y_le : ∀ t ∈ Icc (-1 : ℝ) 1, f3 t 1 ≤ 2 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hn1]
    nlinarith [ht.1, ht.2, hl1lb, hl1ub]
  have hbound : ∀ z ∈ (f1 '' Icc (-1 : ℝ) 1 ∪ f2 '' Icc (-1 : ℝ) 1) ∪ f3 '' Icc (-1 : ℝ) 1,
      z 0 ∈ Icc (-1 : ℝ) 1 ∧ z 1 ∈ Icc (-2 : ℝ) 2 := by
    rintro z ((⟨t1, ht1, rfl⟩ | ⟨t2, ht2, rfl⟩) | ⟨t3, ht3, rfl⟩)
    · exact ⟨by rw [hf1x]; norm_num,
        mem_Icc.2 ⟨hf1y_ge t1 ht1, le_trans (hf1y_le t1 ht1) hm1ub⟩⟩
    · exact hrect (hJnr (hf2mem t2 ht2).1)
    · exact ⟨by rw [hf3x]; norm_num,
        mem_Icc.2 ⟨le_trans hl1lb (hf3y_ge t3 ht3), hf3y_le t3 ht3⟩⟩
  have hcE : ∀ t ∈ Icc (-1 : ℝ) 1, c t 0 ∈ Icc (-1 : ℝ) 1 ∧ c t 1 ∈ Icc (-2 : ℝ) 2 :=
    fun t ht => hbound (c t) (hcmem t ht)
  -- the concatenation is a bottom-to-top path, so it must meet `J_s`
  obtain ⟨t, ht, hctJs⟩ :=
    vertical_meets_arc hbr hJsrect hJoinJs hccont hcE hcm1 hcn1
  rcases hcmem t ht with (⟨t1, ht1, ht1e⟩ | ⟨t2, ht2, ht2e⟩) | ⟨t3, ht3, ht3e⟩
  · -- on the lower axis segment: contradicts `hcon` (height `≤ m 1`)
    have hct0 : c t 0 = 0 := by rw [← ht1e]; exact hf1x t1
    have hcty : c t 1 ≤ m 1 := by rw [← ht1e]; exact hf1y_le t1 ht1
    exact absurd (hcon (c t) hctJs hct0) (not_lt.2 hcty)
  · -- on the middle piece: lands in `J_n \ {a,b}`, disjoint from `J_s`
    have hctJn : c t ∈ J_n := ht2e ▸ (hf2mem t2 ht2).1
    have hctnab : c t ∉ ({a, b} : Set Plane) := ht2e ▸ (hf2mem t2 ht2).2
    have : c t ∈ J_n ∩ J_s := ⟨hctJn, hctJs⟩
    rw [hInter] at this
    exact hctnab this
  · -- on the upper axis segment: forced to equal `l`, but `l ∉ J_s`
    have hct0 : c t 0 = 0 := by rw [← ht3e]; exact hf3x t3
    have hcty_ge : l 1 ≤ c t 1 := by rw [← ht3e]; exact hf3y_ge t3 ht3
    have hcty_le : c t 1 ≤ l 1 := hlmax (c t) (hJsr hctJs) hct0
    have hcty : c t 1 = l 1 := le_antisymm hcty_le hcty_ge
    have hctl : c t = l := by ext i; fin_cases i <;> simp [hct0, hl0, hcty]
    have hlnJs : l ∉ J_s := by
      intro h
      have : l ∈ J_n ∩ J_s := ⟨hlJn, h⟩
      rw [hInter] at this; exact hlab this
    exact hlnJs (hctl ▸ hctJs)

/-- **Maehara's construction points.** Bundles the five points of Maehara's figure
on the vertical axis `x = 0`:
* `l` — the topmost intersection of the axis with the curve (in `J_n`);
* `m` — the lowest point of `J_n` on the axis;
* `p` — the highest point of `J_s` on the axis lying at or below `m` (the top of the
  southern arc on the segment `m → s`, via `ms_meets_Js`);
* `q` — the lowest point of `J_s` on the axis;
* `z₀` — the midpoint `!₂[0,(m 1 + p 1)/2]` of `m` and `p`.

The established `y`-ordering is `q 1 ≤ p 1 ≤ z₀ 1 ≤ m 1 ≤ l 1`.  (Note `p` is the
`J_s`-max **restricted to heights `≤ m 1`**; this is what makes `p 1 ≤ m 1` — hence
the placement of `z₀` between `p` and `m` — provable at this stage.) -/
theorem exists_construction_points (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ (J_n J_s : Set Plane) (l m p q z₀ : Plane),
      J_n ∪ J_s = range r ∧
      J_n ∩ J_s = {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} ∧
      IsPathConnected (J_n \ {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]}) ∧
      (l ∈ J_n ∧ l 0 = 0 ∧ ∀ w ∈ range r, w 0 = 0 → w 1 ≤ l 1) ∧
      (m ∈ J_n ∧ m 0 = 0 ∧ ∀ w ∈ J_n, w 0 = 0 → m 1 ≤ w 1) ∧
      (p ∈ J_s ∧ p 0 = 0 ∧ p 1 ≤ m 1 ∧ ∀ w ∈ J_s, w 0 = 0 → w 1 ≤ m 1 → w 1 ≤ p 1) ∧
      (q ∈ J_s ∧ q 0 = 0 ∧ ∀ w ∈ J_s, w 0 = 0 → q 1 ≤ w 1) ∧
      z₀ = !₂[(0 : ℝ), (m 1 + p 1) / 2] ∧
      m 1 ≤ l 1 ∧ q 1 ≤ p 1 ∧ p 1 ≤ z₀ 1 ∧ z₀ 1 ≤ m 1 ∧
      IsPathConnected (J_s \ {!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]}) ∧
      JoinedIn J_n (!₂[(-1 : ℝ), 0]) (!₂[(1 : ℝ), 0]) ∧
      JoinedIn J_s (!₂[(-1 : ℝ), 0]) (!₂[(1 : ℝ), 0]) := by
  obtain ⟨J_n, J_s, hJncl, hJscl, hUnion, hInter, ⟨eJn⟩, ⟨eJs⟩, hpcJn, hpcJs,
    l, hlr, hl0, hlmax, hlJn⟩ := jordan_arcs hbr hcont hinj hm hp hfar
  have hcptr : IsCompact (range r) := jordanCurve_isCompact r hcont
  have hJnr : J_n ⊆ range r := by rw [← hUnion]; exact subset_union_left
  have hJsr : J_s ⊆ range r := by rw [← hUnion]; exact subset_union_right
  have hJncpt : IsCompact J_n := hcptr.of_isClosed_subset hJncl hJnr
  have hJscpt : IsCompact J_s := hcptr.of_isClosed_subset hJscl hJsr
  -- `m` : lowest point of `J_n` on the axis
  obtain ⟨m, hmJn, hm0, hmmin⟩ := exists_ymin_Jn_axis hJncl hJncpt hlJn hl0
  -- `J_s` meets the axis below `m`
  obtain ⟨w₀, hw₀Js, hw₀0, hw₀m⟩ :=
    ms_meets_Js hbr hcont hinj hm hp hfar hUnion hInter eJs hpcJn hlJn hl0 hlmax hmJn hm0
  -- `p` : highest point of `J_s` on the axis at or below `m`
  set Sp : Set Plane := {w ∈ J_s | w 0 = 0 ∧ w 1 ≤ m 1} with hSpdef
  have hSpcl : IsClosed Sp := by
    have hEq : Sp = (J_s ∩ {w : Plane | w 0 = 0}) ∩ {w : Plane | w 1 ≤ m 1} := by
      ext w
      constructor
      · rintro ⟨hJ, h0, hle⟩; exact ⟨⟨hJ, h0⟩, hle⟩
      · rintro ⟨⟨hJ, h0⟩, hle⟩; exact ⟨hJ, h0, hle⟩
    rw [hEq]
    exact (hJscl.inter (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hSpcpt : IsCompact Sp := hJscpt.of_isClosed_subset hSpcl (fun w hw => hw.1)
  obtain ⟨p, hpSp, hpmax⟩ := hSpcpt.exists_isMaxOn ⟨w₀, hw₀Js, hw₀0, hw₀m⟩
    (f := fun w : Plane => w 1) (by fun_prop : Continuous (fun w : Plane => w 1)).continuousOn
  -- `q` : lowest point of `J_s` on the axis
  set Sq : Set Plane := {w ∈ J_s | w 0 = 0} with hSqdef
  have hSqcl : IsClosed Sq :=
    hJscl.inter (isClosed_eq (by fun_prop) continuous_const)
  have hSqcpt : IsCompact Sq := hJscpt.of_isClosed_subset hSqcl (fun w hw => hw.1)
  obtain ⟨q, hqSq, hqmin⟩ := hSqcpt.exists_isMinOn ⟨w₀, hw₀Js, hw₀0⟩
    (f := fun w : Plane => w 1) (by fun_prop : Continuous (fun w : Plane => w 1)).continuousOn
  -- extract the packaged facts
  have hpm : p 1 ≤ m 1 := hpSp.2.2
  have hml : m 1 ≤ l 1 := hlmax m (hJnr hmJn) hm0
  have hqp : q 1 ≤ p 1 := hqmin ⟨hpSp.1, hpSp.2.1⟩
  have haJn : (!₂[(-1 : ℝ), 0] : Plane) ∈ J_n := by
    have : (!₂[(-1 : ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert _ _
    exact this.1
  have hbJn : (!₂[(1 : ℝ), 0] : Plane) ∈ J_n := by
    have : (!₂[(1 : ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert_of_mem _ rfl
    exact this.1
  have haJs : (!₂[(-1 : ℝ), 0] : Plane) ∈ J_s := by
    have : (!₂[(-1 : ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert _ _
    exact this.2
  have hbJs : (!₂[(1 : ℝ), 0] : Plane) ∈ J_s := by
    have : (!₂[(1 : ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert_of_mem _ rfl
    exact this.2
  have hJoinJn : JoinedIn J_n (!₂[(-1 : ℝ), 0]) (!₂[(1 : ℝ), 0]) := arc_joinedIn eJn haJn hbJn
  have hJoinJs : JoinedIn J_s (!₂[(-1 : ℝ), 0]) (!₂[(1 : ℝ), 0]) := arc_joinedIn eJs haJs hbJs
  refine ⟨J_n, J_s, l, m, p, q, !₂[(0 : ℝ), (m 1 + p 1) / 2], hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩,
    ⟨hpSp.1, hpSp.2.1, hpm, fun w hwJs hw0 hwm => hpmax ⟨hwJs, hw0, hwm⟩⟩,
    ⟨hqSq.1, hqSq.2, fun w hwJs hw0 => hqmin ⟨hwJs, hw0⟩⟩, rfl, hml, hqp, ?_, ?_,
    hpcJs, hJoinJn, hJoinJs⟩
  · rw [show (!₂[(0 : ℝ), (m 1 + p 1) / 2] : Plane) 1 = (m 1 + p 1) / 2 from by simp]
    linarith [hpm]
  · rw [show (!₂[(0 : ℝ), (m 1 + p 1) / 2] : Plane) 1 = (m 1 + p 1) / 2 from by simp]
    linarith [hpm]

/-- **First-exit lemma (A.1).** A path `α` on `[0,1]` starting inside an open set `O`
and ending outside a closed superset `C ⊇ O` has a *first exit time* `tw ∈ (0,1]`:
`α tw` lies in the frontier layer `C \ O`, and `α u ∈ O` for all `u < tw`. -/
theorem exists_first_exit {α : ℝ → Plane} {O C : Set Plane}
    (hO : IsOpen O) (hC : IsClosed C) (hOC : O ⊆ C)
    (hcont : ContinuousOn α (Icc (0 : ℝ) 1))
    (h0 : α 0 ∈ O) (h1 : α 1 ∉ C) :
    ∃ tw ∈ Ioc (0 : ℝ) 1, α tw ∈ C ∧ α tw ∉ O ∧ ∀ u ∈ Ico (0 : ℝ) tw, α u ∈ O := by
  set S : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | α t ∉ O} with hSdef
  -- `S` is closed: it is `Icc 0 1 ∩ α⁻¹(Oᶜ)`
  have hScl : IsClosed S := by
    have hEq : S = Icc (0 : ℝ) 1 ∩ α ⁻¹' Oᶜ := by
      ext t; simp only [hSdef, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff]
    rw [hEq]; exact hcont.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hSne : S.Nonempty :=
    ⟨1, ⟨by norm_num, fun h => h1 (hOC h)⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set tw := sInf S with htw
  have htwS : tw ∈ S := hScl.csInf_mem hSne hSbdd
  have htw01 : tw ∈ Icc (0 : ℝ) 1 := htwS.1
  have htwO : α tw ∉ O := htwS.2
  -- `tw > 0` (since `0 ∉ S`)
  have h0S : (0 : ℝ) ∉ S := fun h => h.2 h0
  have htwpos : 0 < tw := lt_of_le_of_ne htw01.1 (fun h => h0S (h ▸ htwS))
  -- points strictly below `tw` are still in `O`
  have hbelow : ∀ u ∈ Ico (0 : ℝ) tw, α u ∈ O := by
    intro u hu
    by_contra hnot
    have huS : u ∈ S := ⟨⟨hu.1, le_trans hu.2.le htw01.2⟩, hnot⟩
    exact absurd (csInf_le hSbdd huS) (not_le.2 hu.2)
  -- `α tw ∈ C` by closure of the pre-exit segment
  have htwC : α tw ∈ C := by
    have hT : IsClosed (Icc (0 : ℝ) 1 ∩ α ⁻¹' C) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc hC
    have hsub : Ico (0 : ℝ) tw ⊆ Icc (0 : ℝ) 1 ∩ α ⁻¹' C := by
      intro u hu
      exact ⟨⟨hu.1, le_trans hu.2.le htw01.2⟩, hOC (hbelow u hu)⟩
    have : tw ∈ Icc (0 : ℝ) 1 ∩ α ⁻¹' C := by
      apply hT.closure_subset_iff.mpr hsub
      rw [closure_Ico (ne_of_lt htwpos)]
      exact ⟨htwpos.le, le_refl tw⟩
    exact this.2
  exact ⟨tw, ⟨htwpos, htw01.2⟩, htwC, htwO, hbelow⟩

/-- A vertical segment `{p | p 0 = c ∧ p 1 ∈ T}` (with `T` path-connected) is
path-connected: it is the image of `T` under `y ↦ !₂[c, y]`. -/
theorem isPathConnected_vertSeg (c : ℝ) {T : Set ℝ} (hT : IsPathConnected T) :
    IsPathConnected {p : Plane | p 0 = c ∧ p 1 ∈ T} := by
  have hfcont : Continuous (fun y : ℝ => (!₂[c, y] : Plane)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]<;> fun_prop
  have himg := hT.image hfcont
  have hEq : (fun y : ℝ => (!₂[c, y] : Plane)) '' T = {p : Plane | p 0 = c ∧ p 1 ∈ T} := by
    ext p
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by simp, by simpa using hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨p 1, h1, by ext i; fin_cases i <;> simp [h0]⟩
  rwa [hEq] at himg

/-- A horizontal segment `{p | p 1 = c ∧ p 0 ∈ T}` is path-connected. -/
theorem isPathConnected_horizSeg (c : ℝ) {T : Set ℝ} (hT : IsPathConnected T) :
    IsPathConnected {p : Plane | p 1 = c ∧ p 0 ∈ T} := by
  have hfcont : Continuous (fun x : ℝ => (!₂[x, c] : Plane)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]<;> fun_prop
  have himg := hT.image hfcont
  have hEq : (fun x : ℝ => (!₂[x, c] : Plane)) '' T = {p : Plane | p 1 = c ∧ p 0 ∈ T} := by
    ext p
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by simp, by simpa using hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨p 0, h1, by ext i; fin_cases i <;> simp [h0]⟩
  rwa [hEq] at himg

/-- **Curve meets the rectangle boundary only on the axis (A.2).** Any curve point on
the frontier of the normalized rectangle `[-1,1]×[-2,2]` has `y = 0` (so it is `a` or
`b`).  The "lens" bound `(p 0±1)²+(p 1)² ≤ 4` rules out the top/bottom edges outright
and pins the left/right edges to `y = 0`. -/
theorem curve_boundary_axis
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ p ∈ range r, (p 0 = -1 ∨ p 0 = 1 ∨ p 1 = -2 ∨ p 1 = 2) → p 1 = 0 := by
  intro p hp' hbdry
  have hza : dist p (!₂[(-1 : ℝ), 0]) ^ 2 ≤ 4 := by
    have := hfar p hp' _ hm; nlinarith [dist_nonneg (x := p) (y := (!₂[(-1 : ℝ),0] : Plane))]
  have hzb : dist p (!₂[(1 : ℝ), 0]) ^ 2 ≤ 4 := by
    have := hfar p hp' _ hp; nlinarith [dist_nonneg (x := p) (y := (!₂[(1 : ℝ),0] : Plane))]
  rw [dist_sq_coord] at hza hzb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hza hzb
  rcases hbdry with h | h | h | h
  · have h2 : (p 1)^2 = 0 := le_antisymm (by nlinarith [hzb]) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · have h2 : (p 1)^2 = 0 := le_antisymm (by nlinarith [hza]) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · exfalso; nlinarith [hza, hzb, sq_nonneg (p 0 + 1), sq_nonneg (p 0 - 1), h, sq_nonneg (p 1 + 2)]
  · exfalso; nlinarith [hza, hzb, sq_nonneg (p 0 + 1), sq_nonneg (p 0 - 1), h, sq_nonneg (p 1 - 2)]

/-- **Lower boundary arc (A.2).** The part of the rectangle frontier with `y < 0` is
path-connected, contains the bottom axis point `!₂[0,-2]`, lies in the rectangle, and
avoids the curve; moreover any frontier point with `y < 0` lies in it. -/
theorem exists_lower_boundary_path
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ G : Set Plane,
      IsPathConnected G ∧
      (!₂[(0 : ℝ), -2] : Plane) ∈ G ∧
      G ⊆ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} ∧
      (∀ p ∈ G, p ∉ range r) ∧
      (∀ p : Plane, p 0 ∈ Icc (-1 : ℝ) 1 → p 1 ∈ Icc (-2 : ℝ) 2 →
        ¬(p 0 ∈ Ioo (-1 : ℝ) 1 ∧ p 1 ∈ Ioo (-2 : ℝ) 2) → p 1 < 0 → p ∈ G) := by
  set L : Set Plane := {p : Plane | p 0 = -1 ∧ p 1 ∈ Ico (-2 : ℝ) 0} with hLdef
  set Rt : Set Plane := {p : Plane | p 0 = 1 ∧ p 1 ∈ Ico (-2 : ℝ) 0} with hRdef
  set Bot : Set Plane := {p : Plane | p 1 = -2 ∧ p 0 ∈ Icc (-1 : ℝ) 1} with hBdef
  have hLpc : IsPathConnected L :=
    isPathConnected_vertSeg (-1) ((convex_Ico _ _).isPathConnected (nonempty_Ico.mpr (by norm_num)))
  have hRpc : IsPathConnected Rt :=
    isPathConnected_vertSeg 1 ((convex_Ico _ _).isPathConnected (nonempty_Ico.mpr (by norm_num)))
  have hBpc : IsPathConnected Bot :=
    isPathConnected_horizSeg (-2) ((convex_Icc _ _).isPathConnected (nonempty_Icc.mpr
      (by norm_num)))
  have memL : (!₂[(-1 : ℝ), -2] : Plane) ∈ L := ⟨by simp, by rw [mem_Ico]; exact ⟨by simp, by
    norm_num⟩⟩
  have memBotL : (!₂[(-1 : ℝ), -2] : Plane) ∈ Bot := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num,
    by norm_num⟩⟩
  have memBotR : (!₂[(1 : ℝ), -2] : Plane) ∈ Bot := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num,
    by norm_num⟩⟩
  have memR : (!₂[(1 : ℝ), -2] : Plane) ∈ Rt := ⟨by simp, by rw [mem_Ico]; exact ⟨by simp, by
    norm_num⟩⟩
  have hLB : IsPathConnected (L ∪ Bot) := hLpc.union hBpc ⟨_, memL, memBotL⟩
  have hG : IsPathConnected ((L ∪ Bot) ∪ Rt) := hLB.union hRpc ⟨_, Or.inr memBotR, memR⟩
  refine ⟨(L ∪ Bot) ∪ Rt, hG,
    Or.inl (Or.inr ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩), ?_, ?_, ?_⟩
  · rintro p ((hpp | hpp) | hpp)
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ico] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨h1.1, by linarith [h1.2]⟩⟩
    · obtain ⟨h1, h0⟩ := hpp
      exact ⟨h0, by rw [mem_Icc, h1]; norm_num⟩
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ico] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨h1.1, by linarith [h1.2]⟩⟩
  · rintro p ((hpp | hpp) | hpp) hpr
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inl hpp.1); linarith [hpp.2.2]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inr (Or.inl hpp.1))); linarith
      [hpp.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inl hpp.1)); linarith [hpp.2.2]
  · intro p hp0 hp1 hnint hpneg
    rcases not_and_or.mp hnint with hn0 | hn1
    · rw [mem_Ioo, not_and_or] at hn0
      rcases hn0 with h | h
      · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h) hp0.1, mem_Ico.mpr ⟨hp1.1, hpneg⟩⟩)
      · exact Or.inr ⟨le_antisymm hp0.2 (not_lt.mp h), mem_Ico.mpr ⟨hp1.1, hpneg⟩⟩
    · rw [mem_Ioo, not_and_or] at hn1
      rcases hn1 with h | h
      · exact Or.inl (Or.inr ⟨le_antisymm (not_lt.mp h) hp1.1, hp0⟩)
      · exfalso; linarith [not_lt.mp h]

/-- **Upper boundary arc (A.2).** The part of the rectangle frontier with `y > 0` is
path-connected, contains the top axis point `!₂[0,2]`, lies in the rectangle, and
avoids the curve; moreover any frontier point with `y > 0` lies in it. -/
theorem exists_upper_boundary_path
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ G : Set Plane,
      IsPathConnected G ∧
      (!₂[(0 : ℝ), 2] : Plane) ∈ G ∧
      G ⊆ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} ∧
      (∀ p ∈ G, p ∉ range r) ∧
      (∀ p : Plane, p 0 ∈ Icc (-1 : ℝ) 1 → p 1 ∈ Icc (-2 : ℝ) 2 →
        ¬(p 0 ∈ Ioo (-1 : ℝ) 1 ∧ p 1 ∈ Ioo (-2 : ℝ) 2) → 0 < p 1 → p ∈ G) := by
  set L : Set Plane := {p : Plane | p 0 = -1 ∧ p 1 ∈ Ioc (0 : ℝ) 2} with hLdef
  set Rt : Set Plane := {p : Plane | p 0 = 1 ∧ p 1 ∈ Ioc (0 : ℝ) 2} with hRdef
  set Top : Set Plane := {p : Plane | p 1 = 2 ∧ p 0 ∈ Icc (-1 : ℝ) 1} with hTdef
  have hLpc : IsPathConnected L :=
    isPathConnected_vertSeg (-1) ((convex_Ioc _ _).isPathConnected (nonempty_Ioc.mpr (by norm_num)))
  have hRpc : IsPathConnected Rt :=
    isPathConnected_vertSeg 1 ((convex_Ioc _ _).isPathConnected (nonempty_Ioc.mpr (by norm_num)))
  have hTpc : IsPathConnected Top :=
    isPathConnected_horizSeg 2 ((convex_Icc _ _).isPathConnected (nonempty_Icc.mpr (by norm_num)))
  have memL : (!₂[(-1 : ℝ), 2] : Plane) ∈ L := ⟨by simp, by rw [mem_Ioc]; exact ⟨by norm_num, by
    simp⟩⟩
  have memTopL : (!₂[(-1 : ℝ), 2] : Plane) ∈ Top := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num,
    by norm_num⟩⟩
  have memTopR : (!₂[(1 : ℝ), 2] : Plane) ∈ Top := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by
    norm_num⟩⟩
  have memR : (!₂[(1 : ℝ), 2] : Plane) ∈ Rt := ⟨by simp, by rw [mem_Ioc]; exact ⟨by norm_num, by
    simp⟩⟩
  have hLT : IsPathConnected (L ∪ Top) := hLpc.union hTpc ⟨_, memL, memTopL⟩
  have hG : IsPathConnected ((L ∪ Top) ∪ Rt) := hLT.union hRpc ⟨_, Or.inr memTopR, memR⟩
  refine ⟨(L ∪ Top) ∪ Rt, hG,
    Or.inl (Or.inr ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩), ?_, ?_, ?_⟩
  · rintro p ((hpp | hpp) | hpp)
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ioc] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨by linarith [h1.1], h1.2⟩⟩
    · obtain ⟨h1, h0⟩ := hpp
      exact ⟨h0, by rw [mem_Icc, h1]; norm_num⟩
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ioc] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨by linarith [h1.1], h1.2⟩⟩
  · rintro p ((hpp | hpp) | hpp) hpr
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inl hpp.1); linarith [hpp.2.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inr (Or.inr hpp.1))); linarith
      [hpp.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inl hpp.1)); linarith [hpp.2.1]
  · intro p hp0 hp1 hnint hppos
    rcases not_and_or.mp hnint with hn0 | hn1
    · rw [mem_Ioo, not_and_or] at hn0
      rcases hn0 with h | h
      · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h) hp0.1, mem_Ioc.mpr ⟨hppos, hp1.2⟩⟩)
      · exact Or.inr ⟨le_antisymm hp0.2 (not_lt.mp h), mem_Ioc.mpr ⟨hppos, hp1.2⟩⟩
    · rw [mem_Ioo, not_and_or] at hn1
      rcases hn1 with h | h
      · exfalso; linarith [not_lt.mp h]
      · exact Or.inl (Or.inr ⟨le_antisymm hp1.2 (not_lt.mp h), hp0⟩)

/-- Points on the vertical axis are neither `!₂[-1,0]` nor `!₂[1,0]`. -/
private lemma off_axis_endpoints {x : Plane} (hx : x 0 = 0) :
    x ∉ ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h) <;>
    (have hc := congrArg (fun w : Plane => w 0) h; simp only [hx] at hc; norm_num at hc)

/-- `tw * u ∈ [0, tw]` for a unit-interval scalar `u`. -/
private lemma mul_unit_mem_Icc {tw u : ℝ} (htw : 0 ≤ tw) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    tw * u ∈ Icc (0 : ℝ) tw := by
  rw [mem_Icc]
  refine ⟨mul_nonneg htw h0, ?_⟩
  calc tw * u ≤ tw * 1 := mul_le_mul_of_nonneg_left h1 htw
    _ = tw := mul_one tw

/-- The vertical segment from `x` up to `y` on the axis, parametrized over `[-1,1]`. -/
private lemma axis_segment {x y : Plane} (hx0 : x 0 = 0) (hy0 : y 0 = 0) (hxy : x 1 ≤ y 1) :
    ∃ g : ℝ → Plane, ContinuousOn g (Icc (-1 : ℝ) 1) ∧ g (-1) = x ∧ g 1 = y ∧
      (∀ t, g t 0 = 0) ∧ ∀ t ∈ Icc (-1 : ℝ) 1, g t 1 ∈ Icc (x 1) (y 1) := by
  refine ⟨fun t => x + ((t + 1) / 2) • (y - x),
    (by fun_prop : Continuous fun t : ℝ => x + ((t + 1) / 2) • (y - x)).continuousOn,
    by change x + (((-1 : ℝ) + 1) / 2) • (y - x) = x; module,
    by change x + (((1 : ℝ) + 1) / 2) • (y - x) = y; module,
    fun t => by simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hx0, hy0], ?_⟩
  intro t ht; rw [mem_Icc] at ht ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have h0 : (0 : ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have h1 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  have hd : (0 : ℝ) ≤ y 1 - x 1 := by linarith
  constructor
  · linarith [mul_nonneg h0 hd]
  · linarith [mul_le_mul_of_nonneg_right h1 hd]

/-- The closed rectangle `[-1,1] × [-2,2]` is bounded. -/
private lemma isBounded_rectE :
    IsBounded {w : Plane | w 0 ∈ Icc (-1 : ℝ) 1 ∧ w 1 ∈ Icc (-2 : ℝ) 2} := by
  apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 3)).subset
  intro z hz
  rw [Metric.mem_closedBall]
  have hz1 := hz.1; have hz2 := hz.2; rw [mem_Icc] at hz1 hz2
  have hsq : dist z (0:Plane) ^ 2 ≤ 9 := by
    rw [dist_sq_coord, show (0:Plane) 0 = 0 from by simp, show (0:Plane) 1 = 0 from by simp]
    nlinarith [hz1.1, hz1.2, hz2.1, hz2.2]
  nlinarith [dist_nonneg (x := z) (y := (0:Plane)), hsq]

/-- The open rectangle `(-1,1) × (-2,2)` is open. -/
private lemma isOpen_rectO :
    IsOpen {w : Plane | w 0 ∈ Ioo (-1 : ℝ) 1 ∧ w 1 ∈ Ioo (-2 : ℝ) 2} := by
  have hEq : {w : Plane | w 0 ∈ Ioo (-1 : ℝ) 1 ∧ w 1 ∈ Ioo (-2 : ℝ) 2}
      = (fun w : Plane => w 0) ⁻¹' Ioo (-1 : ℝ) 1 ∩ (fun w : Plane => w 1) ⁻¹' Ioo (-2 : ℝ) 2 := by
    ext w; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  rw [hEq]
  exact (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))

/-- The closed rectangle `[-1,1] × [-2,2]` is closed. -/
private lemma isClosed_rectE :
    IsClosed {w : Plane | w 0 ∈ Icc (-1 : ℝ) 1 ∧ w 1 ∈ Icc (-2 : ℝ) 2} := by
  have hEq : {w : Plane | w 0 ∈ Icc (-1 : ℝ) 1 ∧ w 1 ∈ Icc (-2 : ℝ) 2}
      = (fun w : Plane => w 0) ⁻¹' Icc (-1 : ℝ) 1 ∩ (fun w : Plane => w 1) ⁻¹' Icc (-2 : ℝ) 2 := by
    ext w; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  rw [hEq]
  exact (isClosed_Icc.preimage (by fun_prop)).inter (isClosed_Icc.preimage (by fun_prop))

/-- A point of the frontier `E ∖ O` on the horizontal axis is one of the endpoints
`!₂[±1, 0]`, hence on the curve. -/
private lemma axis_zero_mem_range {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    {x : Plane} (hxIcc : x 0 ∈ Icc (-1 : ℝ) 1)
    (hxO : ¬(x 0 ∈ Ioo (-1 : ℝ) 1 ∧ x 1 ∈ Ioo (-2 : ℝ) 2))
    (hx1 : x 1 = 0) : x ∈ range r := by
  have hnotIoo0 : x 0 ∉ Ioo (-1 : ℝ) 1 := fun hIoo =>
    hxO ⟨hIoo, by rw [hx1, mem_Ioo]; constructor <;> norm_num⟩
  rw [mem_Ioo, not_and_or] at hnotIoo0
  rcases hnotIoo0 with h | h
  · have hx : x 0 = -1 := le_antisymm (not_lt.mp h) hxIcc.1
    rw [show x = !₂[(-1 : ℝ), 0] from by ext i; fin_cases i <;> simp [hx, hx1]]; exact hm
  · have hx : x 0 = 1 := le_antisymm hxIcc.2 (not_lt.mp h)
    rw [show x = !₂[(1 : ℝ), 0] from by ext i; fin_cases i <;> simp [hx, hx1]]; exact hp

/-- **Step A, low exit case.** If the escaping path first meets the frontier at a point
below the axis, the concatenation `s → w → z₀ → m → l → n` (lower boundary region,
escaping path reversed, axis, north arc, axis) misses `J_s`, contradicting
`vertical_meets_arc`. -/
private lemma step_A_case_low (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane} (hJnr : J_n ⊆ range r) (hJsr : J_s ⊆ range r)
    (hInter : J_n ∩ J_s = ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane))
    (hpcJn : IsPathConnected (J_n \ ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane)))
    (hJoinJs : JoinedIn J_s (!₂[(-1 : ℝ), 0]) (!₂[(1 : ℝ), 0]))
    {l m p z₀ : Plane}
    (hlJn : l ∈ J_n) (hl0 : l 0 = 0) (hlmax : ∀ w ∈ range r, w 0 = 0 → w 1 ≤ l 1)
    (hmJn : m ∈ J_n) (hm0 : m 0 = 0)
    (hpJs : p ∈ J_s) (hpmax : ∀ w ∈ J_s, w 0 = 0 → w 1 ≤ m 1 → w 1 ≤ p 1)
    (hz₀0 : z₀ 0 = 0) (hpz₀_lt : p 1 < z₀ 1) (hz₀m_lt : z₀ 1 < m 1)
    {α : ℝ → Plane} {tw : ℝ}
    (hαcont : Continuous α) (hα0 : α 0 = z₀) (htw0 : 0 ≤ tw)
    (hαE : ∀ u ∈ Icc (0 : ℝ) tw, α u 0 ∈ Icc (-1 : ℝ) 1 ∧ α u 1 ∈ Icc (-2 : ℝ) 2)
    (hαnr : ∀ u : ℝ, α u ∉ range r)
    (hwC0 : α tw 0 ∈ Icc (-1 : ℝ) 1) (hwC1 : α tw 1 ∈ Icc (-2 : ℝ) 2)
    (hwO : ¬(α tw 0 ∈ Ioo (-1 : ℝ) 1 ∧ α tw 1 ∈ Ioo (-2 : ℝ) 2))
    (hwneg : α tw 1 < 0) : False := by
  have hErect := normalized_subset_rectangle hm hp hfar
  have hmab := off_axis_endpoints hm0
  have hlab := off_axis_endpoints hl0
  have hlE1 : l 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJnr hlJn)).2
  have hmE1 : m 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJnr hmJn)).2
  have hpE1 : p 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJsr hpJs)).2
  have hz₀1lb : (-2 : ℝ) ≤ z₀ 1 := le_of_lt (lt_of_le_of_lt hpE1.1 hpz₀_lt)
  have hs1 : (!₂[(0 : ℝ), -2] : Plane) 1 = -2 := by simp
  have hn1 : (!₂[(0 : ℝ), 2] : Plane) 1 = 2 := by simp
  obtain ⟨Glo, hGloPC, hsGlo, hGloSub, hGloAvoid, hGloFrom⟩ :=
    exists_lower_boundary_path hm hp hfar
  have hwGlo : α tw ∈ Glo := hGloFrom (α tw) hwC0 hwC1 hwO hwneg
  -- piece 1 : `s → w` inside `Glo`
  obtain ⟨g1, hg1cont, hg1a, hg1b, hg1mem⟩ :=
    arc_path (hGloPC.joinedIn (!₂[(0 : ℝ), -2]) hsGlo (α tw) hwGlo)
  -- piece 2 : `w → z₀` along the escaping path
  set g2 : ℝ → Plane := fun t => α (tw * (1 - t) / 2) with hg2def
  have hg2cont : ContinuousOn g2 (Icc (-1 : ℝ) 1) :=
    (hαcont.comp (by fun_prop : Continuous fun t : ℝ => tw * (1 - t) / 2)).continuousOn
  have hg2a : g2 (-1) = α tw := by change α (tw * (1 - (-1)) / 2) = α tw; congr 1; ring
  have hg2b : g2 1 = z₀ := by
    change α (tw * (1 - 1) / 2) = z₀; rw [show tw * (1 - 1) / 2 = (0 : ℝ) from by ring, hα0]
  have hg2arg : ∀ t ∈ Icc (-1 : ℝ) 1, tw * (1 - t) / 2 ∈ Icc (0 : ℝ) tw := by
    intro t ht; rw [mem_Icc] at ht
    rw [mul_div_assoc]
    exact mul_unit_mem_Icc htw0 (by linarith [ht.2]) (by linarith [ht.1])
  -- piece 3 : `z₀ → m` along the axis
  obtain ⟨g3, hg3cont, hg3a, hg3b, hg3x, hg3y⟩ := axis_segment hz₀0 hm0 hz₀m_lt.le
  have hg3missJs : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t ∉ J_s := by
    intro t ht hJs
    have hy := hg3y t ht; rw [mem_Icc] at hy
    have := hpmax (g3 t) hJs (hg3x t) hy.2
    linarith [hy.1, hpz₀_lt]
  -- piece 4 : `m → l` inside `J_n \ {a,b}`
  obtain ⟨g4, hg4cont, hg4a, hg4b, hg4mem⟩ :=
    arc_path (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
  have hg4missJs : ∀ t ∈ Icc (-1 : ℝ) 1, g4 t ∉ J_s := by
    intro t ht hJs
    have hg4 := hg4mem t ht
    have hmem : g4 t ∈ J_n ∩ J_s := ⟨hg4.1, hJs⟩
    rw [hInter] at hmem; exact hg4.2 hmem
  -- piece 5 : `l → n` along the axis
  obtain ⟨g5, hg5cont, hg5a, hg5b, hg5x, hg5y⟩ :=
    axis_segment hl0 (show (!₂[(0 : ℝ), 2] : Plane) 0 = 0 from by simp) (by rw [hn1]; exact hlE1.2)
  have hg5missJs : ∀ t ∈ Icc (-1 : ℝ) 1, g5 t ∉ J_s := by
    intro t ht hJs
    have hy := hg5y t ht; rw [mem_Icc] at hy
    have hle := hlmax (g5 t) (hJsr hJs) (hg5x t)
    have heq : g5 t 1 = l 1 := le_antisymm hle hy.1
    have hgl : g5 t = l := by ext i; fin_cases i <;> simp [hg5x t, hl0, heq]
    rw [hgl] at hJs
    have hmem : l ∈ J_n ∩ J_s := ⟨hlJn, hJs⟩
    rw [hInter] at hmem; exact hlab hmem
  -- concatenate `s → w → z₀ → m → l → n`
  obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
    concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
      (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
  have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact hs1
  have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact hn1
  have hVE : ∀ t ∈ Icc (-1 : ℝ) 1, V t 0 ∈ Icc (-1 : ℝ) 1 ∧ V t 1 ∈ Icc (-2 : ℝ) 2 := by
    intro t ht
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGloSub (hg1mem u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg2arg u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg3y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hz₀1lb hy.1, le_trans hy.2 hmE1.2⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hg4mem u hu).1)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg5y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg5x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hlE1.1 hy.1, hy.2⟩⟩
  have hVmiss : ∀ t ∈ Icc (-1 : ℝ) 1, V t ∉ J_s := by
    intro t ht hJs
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs
      exact hGloAvoid (g1 u) (hg1mem u hu) (hJsr hJs)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs
      exact hαnr (tw * (1 - u) / 2) (hJsr hJs)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg3missJs u hu hJs
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg4missJs u hu hJs
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg5missJs u hu hJs
  have hJsrect : J_s ⊆ {w : Plane | w 0 ∈ Icc (-1 : ℝ) 1 ∧ w 1 ∈ Icc (-2 : ℝ) 2} :=
    fun w hw => hErect (hJsr hw)
  obtain ⟨t, ht, htJs⟩ := vertical_meets_arc hbr hJsrect hJoinJs hVcont hVE hVm1 hVn1
  exact hVmiss t ht htJs

/-- **Step A, high exit case.** Mirror of `step_A_case_low`: if the escaping path first
meets the frontier above the axis, the concatenation `s → q → p → z₀ → w → n` misses
`J_n`, contradicting `vertical_meets_arc`. -/
private lemma step_A_case_high (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane} (hJnr : J_n ⊆ range r) (hJsr : J_s ⊆ range r)
    (hInter : J_n ∩ J_s = ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane))
    (hpcJs : IsPathConnected (J_s \ ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane)))
    (hJoinJn : JoinedIn J_n (!₂[(-1 : ℝ), 0]) (!₂[(1 : ℝ), 0]))
    {m p q z₀ : Plane}
    (hmJn : m ∈ J_n) (_hm0 : m 0 = 0) (hmmin : ∀ w ∈ J_n, w 0 = 0 → m 1 ≤ w 1)
    (hpJs : p ∈ J_s) (hp0 : p 0 = 0)
    (hqJs : q ∈ J_s) (hq0 : q 0 = 0) (hqm : q 1 < m 1)
    (hz₀0 : z₀ 0 = 0) (hpz₀_lt : p 1 < z₀ 1) (hz₀m_lt : z₀ 1 < m 1)
    {α : ℝ → Plane} {tw : ℝ}
    (hαcont : Continuous α) (hα0 : α 0 = z₀) (htw0 : 0 ≤ tw)
    (hαE : ∀ u ∈ Icc (0 : ℝ) tw, α u 0 ∈ Icc (-1 : ℝ) 1 ∧ α u 1 ∈ Icc (-2 : ℝ) 2)
    (hαnr : ∀ u : ℝ, α u ∉ range r)
    (hwC0 : α tw 0 ∈ Icc (-1 : ℝ) 1) (hwC1 : α tw 1 ∈ Icc (-2 : ℝ) 2)
    (hwO : ¬(α tw 0 ∈ Ioo (-1 : ℝ) 1 ∧ α tw 1 ∈ Ioo (-2 : ℝ) 2))
    (hwpos : 0 < α tw 1) : False := by
  have hErect := normalized_subset_rectangle hm hp hfar
  have hqab := off_axis_endpoints hq0
  have hpab := off_axis_endpoints hp0
  have hqE1 : q 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJsr hqJs)).2
  have hpE1 : p 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJsr hpJs)).2
  have hmE1 : m 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJnr hmJn)).2
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt (lt_of_lt_of_le hz₀m_lt hmE1.2)
  have hs1 : (!₂[(0 : ℝ), -2] : Plane) 1 = -2 := by simp
  have hn1 : (!₂[(0 : ℝ), 2] : Plane) 1 = 2 := by simp
  obtain ⟨Gup, hGupPC, hnGup, hGupSub, hGupAvoid, hGupFrom⟩ :=
    exists_upper_boundary_path hm hp hfar
  have hwGup : α tw ∈ Gup := hGupFrom (α tw) hwC0 hwC1 hwO hwpos
  -- piece 1 : `s → q` along the axis
  obtain ⟨g1, hg1cont, hg1a, hg1b, hg1x, hg1y⟩ :=
    axis_segment (show (!₂[(0 : ℝ), -2] : Plane) 0 = 0 from by simp) hq0 (by rw [hs1]; exact hqE1.1)
  have hg1missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g1 t ∉ J_n := by
    intro t ht hJn
    have hy := hg1y t ht; rw [mem_Icc] at hy
    have := hmmin (g1 t) hJn (hg1x t)
    linarith [hy.2, hqm]
  -- piece 2 : `q → p` inside `J_s \ {a,b}`
  obtain ⟨g2, hg2cont, hg2a, hg2b, hg2mem⟩ :=
    arc_path (hpcJs.joinedIn q ⟨hqJs, hqab⟩ p ⟨hpJs, hpab⟩)
  have hg2missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g2 t ∉ J_n := by
    intro t ht hJn
    have hg2' := hg2mem t ht
    have hmem : g2 t ∈ J_n ∩ J_s := ⟨hJn, hg2'.1⟩
    rw [hInter] at hmem; exact hg2'.2 hmem
  -- piece 3 : `p → z₀` along the axis
  obtain ⟨g3, hg3cont, hg3a, hg3b, hg3x, hg3y⟩ := axis_segment hp0 hz₀0 hpz₀_lt.le
  have hg3missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t ∉ J_n := by
    intro t ht hJn
    have hy := hg3y t ht; rw [mem_Icc] at hy
    have := hmmin (g3 t) hJn (hg3x t)
    linarith [hy.2, hz₀m_lt]
  -- piece 4 : `z₀ → w` along the escaping path
  set g4 : ℝ → Plane := fun t => α (tw * (t + 1) / 2) with hg4def
  have hg4cont : ContinuousOn g4 (Icc (-1 : ℝ) 1) :=
    (hαcont.comp (by fun_prop : Continuous fun t : ℝ => tw * (t + 1) / 2)).continuousOn
  have hg4a : g4 (-1) = z₀ := by
    change α (tw * ((-1) + 1) / 2) = z₀; rw [show tw * ((-1) + 1) / 2 = (0 : ℝ) from by ring, hα0]
  have hg4b : g4 1 = α tw := by change α (tw * (1 + 1) / 2) = α tw; congr 1; ring
  have hg4arg : ∀ t ∈ Icc (-1 : ℝ) 1, tw * (t + 1) / 2 ∈ Icc (0 : ℝ) tw := by
    intro t ht; rw [mem_Icc] at ht
    rw [mul_div_assoc]
    exact mul_unit_mem_Icc htw0 (by linarith [ht.1]) (by linarith [ht.2])
  -- piece 5 : `w → n` inside `Gup`
  obtain ⟨g5, hg5cont, hg5a, hg5b, hg5mem⟩ :=
    arc_path (hGupPC.joinedIn (α tw) hwGup (!₂[(0 : ℝ), 2]) hnGup)
  have hg5missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g5 t ∉ J_n := by
    intro t ht hJn; exact hGupAvoid (g5 t) (hg5mem t ht) (hJnr hJn)
  -- concatenate `s → q → p → z₀ → w → n`
  obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
    concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
      (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
  have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact hs1
  have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact hn1
  have hVE : ∀ t ∈ Icc (-1 : ℝ) 1, V t 0 ∈ Icc (-1 : ℝ) 1 ∧ V t 1 ∈ Icc (-2 : ℝ) 2 := by
    intro t ht
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg1y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg1x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨hy.1, le_trans hy.2 hqE1.2⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hg2mem u hu).1)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg3y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hpE1.1 hy.1, le_trans hy.2 hz₀1ub⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg4arg u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGupSub (hg5mem u hu)
  have hVmiss : ∀ t ∈ Icc (-1 : ℝ) 1, V t ∉ J_n := by
    intro t ht hJn
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg1missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg2missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg3missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn
      exact hαnr (tw * (u + 1) / 2) (hJnr hJn)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg5missJn u hu hJn
  have hJnrect : J_n ⊆ {w : Plane | w 0 ∈ Icc (-1 : ℝ) 1 ∧ w 1 ∈ Icc (-2 : ℝ) 2} :=
    fun w hw => hErect (hJnr hw)
  obtain ⟨t, ht, htJn⟩ := vertical_meets_arc hbr hJnrect hJoinJn hVcont hVE hVm1 hVn1
  exact hVmiss t ht htJn

/-- **Maehara Step A (normalized).** The geometric core in normalized coordinates:
the farthest pair sits at `!₂[-1,0]`, `!₂[1,0]` (so the diameter is `2`). -/
theorem step_A_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
  classical
  obtain ⟨J_n, J_s, l, m, p, q, z₀, hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩, ⟨hpJs, hp0, hpm, hpmax⟩,
    ⟨hqJs, hq0, hqmin⟩, hz₀def, hml, hqp, hpz₀, hz₀m,
    hpcJs, hJoinJn, hJoinJs⟩ := exists_construction_points hbr hcont hinj hm hp hfar
  -- basic containments, coordinates, and rectangle bounds
  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have hz₀0 : z₀ 0 = 0 := by rw [hz₀def]; simp
  have hz₀1e : z₀ 1 = (m 1 + p 1) / 2 := by rw [hz₀def]; simp
  have hmE1 : m 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJnr hmJn)).2
  have hpE1 : p 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJsr hpJs)).2
  -- `p 1 < m 1` (else `p = m` would lie in `J_n ∩ J_s = {a,b}` off the axis)
  have hpm_lt : p 1 < m 1 := by
    rcases lt_or_eq_of_le hpm with h | h
    · exact h
    · exfalso
      have hpm_eq : p = m := by ext i; fin_cases i <;> simp [hp0, hm0, h]
      have hmem : m ∈ J_n ∩ J_s := ⟨hmJn, hpm_eq ▸ hpJs⟩
      rw [hInter] at hmem
      rcases hmem with h' | h' <;>
        (have hc := congrArg (fun x : Plane => x 0) h'; simp only [hm0] at hc; norm_num at hc)
  have hqm : q 1 < m 1 := lt_of_le_of_lt hqp hpm_lt
  have hpz₀_lt : p 1 < z₀ 1 := by rw [hz₀1e]; linarith
  have hz₀m_lt : z₀ 1 < m 1 := by rw [hz₀1e]; linarith
  -- **A.0** : `z₀ ∉ range r`
  have hz₀c : z₀ ∈ (range r)ᶜ := by
    intro hz₀r
    rw [← hUnion] at hz₀r
    rcases hz₀r with hJn | hJs
    · exact absurd (hmmin z₀ hJn hz₀0) (not_le.2 hz₀m_lt)
    · exact absurd (hpmax z₀ hJs hz₀0 hz₀m_lt.le) (not_le.2 hpz₀_lt)
  refine ⟨z₀, hz₀c, ?_⟩
  -- the rectangle `E`, its open interior `O`
  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} with hEdef
  set O : Set Plane := {p : Plane | p 0 ∈ Ioo (-1 : ℝ) 1 ∧ p 1 ∈ Ioo (-2 : ℝ) 2} with hOdef
  have hEbdd : IsBounded E := by rw [hEdef]; exact isBounded_rectE
  have hOopen : IsOpen O := by rw [hOdef]; exact isOpen_rectO
  have hEclosed : IsClosed E := by rw [hEdef]; exact isClosed_rectE
  have hOE : O ⊆ E := fun w hw => ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
  have hz₀O : z₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · rw [mem_Ioo, hz₀0]; constructor <;> norm_num
    · rw [mem_Ioo, hz₀1e]; exact ⟨by linarith [hpE1.1, hpm_lt], by linarith [hmE1.2, hpm_lt]⟩
  -- assume the component is unbounded and derive a contradiction
  by_contra hUunb
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUeq
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀c
  have hUpc : IsPathConnected U := isPathConnected_component r hcont hz₀c
  have hUnotsub : ¬ U ⊆ E := fun h => hUunb (hEbdd.subset h)
  obtain ⟨y, hyU, hyE⟩ := Set.not_subset.mp hUnotsub
  -- reparametrized escaping path `α : ℝ → Plane`
  have hJoinU : JoinedIn U z₀ y := hUpc.joinedIn z₀ hz₀U y hyU
  set α : ℝ → Plane := fun t => hJoinU.somePath (Set.projIcc (0 : ℝ) 1 (by norm_num) t) with hαdef
  have hαcont : Continuous α := hJoinU.somePath.continuous.comp continuous_projIcc
  have hα0 : α 0 = z₀ := by
    change hJoinU.somePath _ = z₀
    rw [show Set.projIcc (0 : ℝ) 1 (by norm_num) 0 = 0 from Subtype.ext
      (by rw [Set.coe_projIcc]; norm_num)]
    exact hJoinU.somePath.source
  have hα1 : α 1 = y := by
    change hJoinU.somePath _ = y
    rw [show Set.projIcc (0 : ℝ) 1 (by norm_num) 1 = 1 from Subtype.ext
      (by rw [Set.coe_projIcc]; norm_num)]
    exact hJoinU.somePath.target
  have hαU : ∀ t : ℝ, α t ∈ U := fun t => hJoinU.somePath_mem _
  -- first exit through the frontier `E \ O`
  obtain ⟨tw, htw, hwC, hwO, hbelow⟩ :=
    exists_first_exit hOopen hEclosed hOE hαcont.continuousOn (by rw [hα0]; exact hz₀O)
      (by rw [hα1]; exact hyE)
  have hαE : ∀ u ∈ Icc (0 : ℝ) tw, α u ∈ E := by
    intro u hu
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact hwC
    · exact hOE (hbelow u ⟨hu.1, h⟩)
  have hwnr : α tw ∉ range r := hUsub (hαU tw)
  -- `α tw` is off the axis
  have hw1ne : α tw 1 ≠ 0 := fun hzero =>
    hwnr (axis_zero_mem_range hm hp hwC.1 hwO hzero)
  rcases lt_or_gt_of_ne hw1ne with hwneg | hwpos
  · exact step_A_case_low hbr hm hp hfar hJnr hJsr hInter hpcJn hJoinJs
      hlJn hl0 hlmax hmJn hm0 hpJs hpmax hz₀0 hpz₀_lt hz₀m_lt
      hαcont hα0 htw.1.le (fun u hu => hαE u hu) (fun u => hUsub (hαU u))
      hwC.1 hwC.2 hwO hwneg
  · exact step_A_case_high hbr hm hp hfar hJnr hJsr hInter hpcJs hJoinJn
      hmJn hm0 hmmin hpJs hp0 hqJs hq0 hqm hz₀0 hpz₀_lt hz₀m_lt
      hαcont hα0 htw.1.le (fun u hu => hαE u hu) (fun u => hUsub (hαU u))
      hwC.1 hwC.2 hwO hwpos

/-- **Maehara Step A (geometric core).** The complement `ℝ²∖J` of a Jordan curve
has at least one *bounded* connected component.  Reduced to the normalized version
`step_A_normalized` via the farthest-pair similarity `T`. -/
theorem step_A_exists_bounded (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
  obtain ⟨a, ha, b, hb, hfar, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0 : ℝ) < 2 / dist a b := by positivity
  -- the transported curve `r' = T ∘ r`
  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]
  -- normalized hypotheses for `r'`
  have hm' : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : (!₂[(1 : ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTb]; exact mem_image_of_mem _ hb
  have hfar' : ∀ z ∈ range r', ∀ w ∈ range r', dist z w ≤ 2 := by
    rw [hrange]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hscale]
    calc 2 / dist a b * dist z w
        ≤ 2 / dist a b * dist a b := by
          exact mul_le_mul_of_nonneg_left (hfar z hz w hw) hcpos.le
      _ = 2 := by field_simp
  obtain ⟨x, hx, hxb⟩ := step_A_normalized hbr hr'cont hr'inj hm' hp' hfar'
  -- transport the bounded component back by `T⁻¹`
  rw [hrange] at hx hxb
  -- `x ∈ (T '' range r)ᶜ = T '' (range r)ᶜ`
  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  rw [himg] at hx hxb
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  refine ⟨x₀, hx₀, ?_⟩
  -- component of `x = T x₀` corresponds to component of `x₀` under `T`
  have hcc : connectedComponentIn ((T : Plane → Plane) '' (range r)ᶜ) (T x₀)
      = T '' connectedComponentIn (range r)ᶜ x₀ :=
    (T.image_connectedComponentIn hx₀).symm
  rw [hcc] at hxb
  exact (isBounded_image_scaling hcpos hscale _).mp hxb

/-- The Euclidean norm of an axis point `!₂[0,y]` equals `|y|`. -/
private lemma norm_axis_pt (y : ℝ) : ‖(!₂[(0 : ℝ), y] : Plane)‖ = |y| := by
  have e0 : (!₂[(0 : ℝ), y] : Plane) 0 = 0 := by simp
  have e1 : (!₂[(0 : ℝ), y] : Plane) 1 = y := by simp
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, e0, e1]
  simp [Real.sqrt_sq_eq_abs]

/-- The upward axis ray `{p | p 0 = 0 ∧ c < p 1}` is unbounded. -/
private lemma axis_ray_up_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0 : ℝ), |c| + |M| + 1] : Plane) 1 = |c| + |M| + 1 := by simp
  have hmem : (!₂[(0 : ℝ), |c| + |M| + 1] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Ioi, hy1]; linarith [le_abs_self c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_axis_pt, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |c| + |M| +
    1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

/-- The downward axis ray `{p | p 0 = 0 ∧ p 1 < c}` is unbounded. -/
private lemma axis_ray_down_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0 : ℝ), -(|c| + |M| + 1)] : Plane) 1 = -(|c| + |M| + 1) := by simp
  have hmem : (!₂[(0 : ℝ), -(|c| + |M| + 1)] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Iio, hy1]; linarith [neg_abs_le c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_axis_pt, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

/-- The complement of the normalized rectangle `[-1,1]×[-2,2]` is preconnected
(it is the union of four half-planes chained around the rectangle). -/
private lemma isPreconnected_rect_compl :
    IsPreconnected {v : Plane | ¬(v 0 ∈ Icc (-1 : ℝ) 1 ∧ v 1 ∈ Icc (-2 : ℝ) 2)} := by
  have cA : Convex ℝ {v : Plane | v 0 ∈ Iio (-1 : ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cB : Convex ℝ {v : Plane | v 0 ∈ Ioi (1 : ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cC : Convex ℝ {v : Plane | v 1 ∈ Iio (-2 : ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  have cD : Convex ℝ {v : Plane | v 1 ∈ Ioi (2 : ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  -- membership witnesses at the four "corners"
  have mAD_A : (!₂[(-2 : ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Iio (-1 : ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Iio]; norm_num
  have mAD_D : (!₂[(-2 : ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2 : ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Ioi]; norm_num
  have mB_D : (!₂[(2 : ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2 : ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Ioi]; norm_num
  have mB_B : (!₂[(2 : ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1 : ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Ioi]; norm_num
  have mC_B : (!₂[(2 : ℝ), -3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1 : ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Ioi]; norm_num
  have mC_C : (!₂[(2 : ℝ), -3] : Plane) ∈ {v : Plane | v 1 ∈ Iio (-2 : ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Iio]; norm_num
  have hAD : IsPreconnected ({v : Plane | v 0 ∈ Iio (-1 : ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2 : ℝ)}) :=
    cA.isPreconnected.union _ mAD_A mAD_D cD.isPreconnected
  have hADB : IsPreconnected (({v : Plane | v 0 ∈ Iio (-1 : ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2 : ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1 : ℝ)}) :=
    hAD.union _ (Or.inr mB_D) mB_B cB.isPreconnected
  have hADBC : IsPreconnected ((({v : Plane | v 0 ∈ Iio (-1 : ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2 : ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1 : ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2 : ℝ)}) :=
    hADB.union _ (Or.inr mC_B) mC_C cC.isPreconnected
  have hEq : {v : Plane | ¬(v 0 ∈ Icc (-1 : ℝ) 1 ∧ v 1 ∈ Icc (-2 : ℝ) 2)}
      = ((({v : Plane | v 0 ∈ Iio (-1 : ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2 : ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1 : ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2 : ℝ)}) := by
    ext v
    simp only [mem_ofPred_eq, mem_union, mem_Icc, mem_Iio, mem_Ioi, not_and_or, not_le]
    tauto
  rw [hEq]; exact hADBC

/-- Straight segment from `P` to `Q`, reparametrized on `[-1,1]`. -/
private noncomputable def segP (P Q : Plane) : ℝ → Plane := fun t => P + ((t + 1) / 2) • (Q - P)

private lemma segP_cont (P Q : Plane) : Continuous (segP P Q) := by unfold segP; fun_prop

private lemma segP_neg1 (P Q : Plane) : segP P Q (-1) = P := by simp [segP]

private lemma segP_one (P Q : Plane) : segP P Q 1 = Q := by simp [segP]

private lemma segP_coord (P Q : Plane) (t : ℝ) (i : Fin 2) :
    segP P Q t i = P i + ((t + 1) / 2) * (Q i - P i) := by
  simp only [segP, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

private lemma segP_dist_le (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    dist (segP P Q t) P ≤ dist Q P := by
  have hs : |(t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segP P Q t) P = |(t + 1) / 2| * dist Q P := by
    rw [segP, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |(t + 1) / 2| * dist Q P ≤ 1 * dist Q P :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist Q P := one_mul _

private lemma segP_dist_le' (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    dist (segP P Q t) Q ≤ dist P Q := by
  have hs : |1 - (t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segP P Q t) Q = |1 - (t + 1) / 2| * dist P Q := by
    rw [segP, dist_eq_norm,
      show P + ((t + 1) / 2) • (Q - P) - Q = (1 - (t + 1) / 2) • (P - Q) from by module,
      norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |1 - (t + 1) / 2| * dist P Q ≤ 1 * dist P Q :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist P Q := one_mul _

/-- A coordinate of a segment point lies in any interval containing both endpoints'
corresponding coordinates. -/
private lemma segP_coord_mem_Icc {P Q : Plane} (i : Fin 2) {lo hi : ℝ}
    (hP : P i ∈ Icc lo hi) (hQ : Q i ∈ Icc lo hi) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    segP P Q t i ∈ Icc lo hi := by
  rw [mem_Icc] at hP hQ ht
  rw [segP_coord, mem_Icc]
  have hs0 : (0 : ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have hs1 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  constructor
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.1] : (0 : ℝ) ≤ Q i - lo),
      mul_nonneg (by linarith [hs1] : (0 : ℝ) ≤ 1 - (t + 1) / 2) (by linarith [hP.1] : (0 : ℝ) ≤ P
        i -
        lo)]
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.2] : (0 : ℝ) ≤ hi - Q i),
      mul_nonneg (by linarith [hs1] : (0 : ℝ) ≤ 1 - (t + 1) / 2) (by linarith [hP.2] : (0 : ℝ) ≤
        hi -
        P i)]

/-- **Maehara Step B (normalized).** Uniqueness of the bounded component in
normalized coordinates (farthest pair at `!₂[-1,0]`, `!₂[1,0]`). Any bounded
component equals the `z₀`-component `U`, hence all bounded components coincide. -/
private theorem bounded_component_subset_normalized_rectangle
    {r : sphere (0 : Plane) 1 → Plane}
    (hErect : range r ⊆ {p | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2})
    (w : Plane) (hwb : IsBounded (connectedComponentIn (range r)ᶜ w)) :
    connectedComponentIn (range r)ᶜ w ⊆
      {p | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} := by
  let W := connectedComponentIn (range r)ᶜ w
  have hbounded : IsBounded W := hwb
  have compW : ∀ {v : Plane}, v ∈ W → connectedComponentIn (range r)ᶜ v = W := by
    intro v hv
    exact (connectedComponentIn_eq hv).symm
  intro v hvW
  by_contra hvE
  change ¬(v 0 ∈ Icc (-1 : ℝ) 1 ∧ v 1 ∈ Icc (-2 : ℝ) 2) at hvE
  have hvEc : v ∈ {u : Plane | ¬(u 0 ∈ Icc (-1 : ℝ) 1 ∧ u 1 ∈ Icc (-2 : ℝ) 2)} := hvE
  have hEcc : {u : Plane | ¬(u 0 ∈ Icc (-1 : ℝ) 1 ∧ u 1 ∈ Icc (-2 : ℝ) 2)} ⊆ (range r)ᶜ :=
    fun u hu hur => hu (hErect hur)
  have h1 := isPreconnected_rect_compl.subset_connectedComponentIn hvEc hEcc
  have hup : {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi (2 : ℝ)}
      ⊆ {u : Plane | ¬(u 0 ∈ Icc (-1 : ℝ) 1 ∧ u 1 ∈ Icc (-2 : ℝ) 2)} := by
    rintro u ⟨_, hu1⟩ ⟨_, hu2⟩
    rw [mem_Icc] at hu2; rw [mem_Ioi] at hu1; linarith [hu2.2]
  exact axis_ray_up_unbounded 2 (hbounded.subset (subset_trans hup (compW hvW ▸ h1)))

private theorem path_component_crossing_contradiction (hbr : BrouwerFPT)
    (W : Set Plane) (hWpc : IsPathConnected W)
    (hWE : W ⊆ {p | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2})
    (β : ℝ → Plane) (hβcont : ContinuousOn β (Icc (-1 : ℝ) 1))
    (hβE : ∀ t ∈ Icc (-1 : ℝ) 1, β t 0 ∈ Icc (-1 : ℝ) 1 ∧ β t 1 ∈ Icc (-2 : ℝ) 2)
    (hβa : β (-1) = !₂[(0 : ℝ), 2]) (hβb : β 1 = !₂[(0 : ℝ), -2])
    (hβmiss : ∀ t ∈ Icc (-1 : ℝ) 1, β t ∉ W)
    (haclW : (!₂[(-1 : ℝ), 0] : Plane) ∈ closure W)
    (hbclW : (!₂[(1 : ℝ), 0] : Plane) ∈ closure W)
    (ha_notβ : (!₂[(-1 : ℝ), 0] : Plane) ∉ β '' Icc (-1 : ℝ) 1)
    (hb_notβ : (!₂[(1 : ℝ), 0] : Plane) ∉ β '' Icc (-1 : ℝ) 1) : False := by
  classical
  let βimg := β '' Icc (-1 : ℝ) 1
  have hβimg_closed : IsClosed βimg := (isCompact_Icc.image_of_continuousOn hβcont).isClosed
  have ha0 : (!₂[(-1 : ℝ), 0] : Plane) 0 = -1 := by simp
  have ha1 : (!₂[(-1 : ℝ), 0] : Plane) 1 = 0 := by simp
  have hb0 : (!₂[(1 : ℝ), 0] : Plane) 0 = 1 := by simp
  have hb1 : (!₂[(1 : ℝ), 0] : Plane) 1 = 0 := by simp
  have hs0 : (!₂[(0 : ℝ), -2] : Plane) 0 = 0 := by simp
  have hs1 : (!₂[(0 : ℝ), -2] : Plane) 1 = -2 := by simp
  have hn0 : (!₂[(0 : ℝ), 2] : Plane) 0 = 0 := by simp
  have hn1 : (!₂[(0 : ℝ), 2] : Plane) 1 = 2 := by simp
  have hIcc0x : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc0y : (0 : ℝ) ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIcc2y : (2 : ℝ) ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm2y : (-2 : ℝ) ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm1x : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc1x : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by rw [mem_Icc]; norm_num
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ ha_notβ
  obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ hb_notβ
  -- points of `W` near `a, b`
  rw [Metric.mem_closure_iff] at haclW hbclW
  obtain ⟨a₁, ha₁W, ha₁d⟩ := haclW εa hεa
  obtain ⟨b₁, hb₁W, hb₁d⟩ := hbclW εb hεb
  have ha₁E : a₁ 0 ∈ Icc (-1 : ℝ) 1 ∧ a₁ 1 ∈ Icc (-2 : ℝ) 2 := hWE ha₁W
  have hb₁E : b₁ 0 ∈ Icc (-1 : ℝ) 1 ∧ b₁ 1 ∈ Icc (-2 : ℝ) 2 := hWE hb₁W
  -- **path** `H : a → b`, left to right, inside `E`, missing `β`
  have hHp1_cont : ContinuousOn (segP (!₂[(-1 : ℝ), 0]) a₁) (Icc (-1 : ℝ) 1) := (segP_cont _
    _).continuousOn
  obtain ⟨Harc, hHarc_cont, hHarc_a, hHarc_b, hHarc_mem⟩ :=
    arc_path (hWpc.joinedIn a₁ ha₁W b₁ hb₁W)
  have hHp3_cont : ContinuousOn (segP b₁ (!₂[(1 : ℝ), 0])) (Icc (-1 : ℝ) 1) := (segP_cont _
    _).continuousOn
  obtain ⟨H, hHcont, hHa, hHb, hHmem⟩ :=
    concatPath3 hHp1_cont hHarc_cont hHp3_cont
      (by rw [segP_one, hHarc_a]) (by rw [hHarc_b, segP_neg1])
  have hHa0 : H (-1) 0 = -1 := by rw [hHa, segP_neg1, ha0]
  have hHb0 : H 1 0 = 1 := by rw [hHb, segP_one, hb0]
  have hHE : ∀ t ∈ Icc (-1 : ℝ) 1, H t 0 ∈ Icc (-1 : ℝ) 1 ∧ H t 1 ∈ Icc (-2 : ℝ) 2 := by
    intro t ht
    rcases hHmem t ht with (h | h) | h
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      exact ⟨segP_coord_mem_Icc 0 (by rw [ha0]; exact hIccm1x) ha₁E.1 hu,
        segP_coord_mem_Icc 1 (by rw [ha1]; exact hIcc0y) ha₁E.2 hu⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hWE (hHarc_mem u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      exact ⟨segP_coord_mem_Icc 0 hb₁E.1 (by rw [hb0]; exact hIcc1x) hu,
        segP_coord_mem_Icc 1 hb₁E.2 (by rw [hb1]; exact hIcc0y) hu⟩
  have hHmiss : ∀ t ∈ Icc (-1 : ℝ) 1, H t ∉ βimg := by
    intro t ht
    rcases hHmem t ht with (h | h) | h
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
      have hin : segP (!₂[(-1 : ℝ), 0]) a₁ u ∈ Metric.ball (!₂[(-1 : ℝ), 0] : Plane) εa := by
        rw [Metric.mem_ball]
        calc dist (segP (!₂[(-1 : ℝ), 0]) a₁ u) (!₂[(-1 : ℝ), 0])
              ≤ dist a₁ (!₂[(-1 : ℝ), 0]) := segP_dist_le _ _ hu
          _ < εa := by rw [dist_comm]; exact ha₁d
      exact hballa hin hmemβ
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
      obtain ⟨t', ht', ht'e⟩ := hmemβ
      exact hβmiss t' ht' (by rw [ht'e]; exact hHarc_mem u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
      have hin : segP b₁ (!₂[(1 : ℝ), 0]) u ∈ Metric.ball (!₂[(1 : ℝ), 0] : Plane) εb := by
        rw [Metric.mem_ball]
        calc dist (segP b₁ (!₂[(1 : ℝ), 0]) u) (!₂[(1 : ℝ), 0])
              ≤ dist b₁ (!₂[(1 : ℝ), 0]) := segP_dist_le' _ _ hu
          _ < εb := by rw [dist_comm]; exact hb₁d
      exact hballb hin hmemβ
  -- reorient `β` bottom-to-top and cross with `H`
  set v : ℝ → Plane := fun t => β (-t) with hvdef
  have hvcont : ContinuousOn v (Icc (-1 : ℝ) 1) :=
    hβcont.comp continuous_neg.continuousOn (fun t ht => by
      rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hvE : ∀ t ∈ Icc (-1 : ℝ) 1, v t 0 ∈ Icc (-1 : ℝ) 1 ∧ v t 1 ∈ Icc (-2 : ℝ) 2 := by
    intro t ht; rw [mem_Icc] at ht
    exact hβE (-t) (by rw [mem_Icc]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hv1 : v (-1) 1 = -2 := by change β (-(-1)) 1 = -2; rw [neg_neg, hβb, hs1]
  have hv2 : v 1 1 = 2 := by change β (-1) 1 = 2; rw [hβa, hn1]
  obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (-2 : ℝ)
    ≤ 2)
    H v hHcont hvcont hHE hvE hHa0 hHb0 hv1 hv2
  apply hHmiss s hs
  rw [heq]
  exact Set.mem_image_of_mem β (show (-t) ∈ Icc (-1 : ℝ) 1 by
    rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)

private theorem spine_image_avoids_horizontal_endpoint
    (l m p q : Plane) (hl0 : l 0 = 0) (hm0 : m 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 0)
    (lm pq β : ℝ → Plane)
    (hβmem : ∀ t ∈ Icc (-1 : ℝ) 1,
      β t ∈ ((((segP !₂[(0 : ℝ), 2] l '' Icc (-1 : ℝ) 1 ∪
        lm '' Icc (-1 : ℝ) 1) ∪ segP m p '' Icc (-1 : ℝ) 1) ∪
        pq '' Icc (-1 : ℝ) 1) ∪ segP q !₂[(0 : ℝ), -2] '' Icc (-1 : ℝ) 1))
    (u : Plane) (hu0 : u 0 ≠ 0)
    (hLm : u ∉ lm '' Icc (-1 : ℝ) 1) (hPq : u ∉ pq '' Icc (-1 : ℝ) 1) :
    u ∉ β '' Icc (-1 : ℝ) 1 := by
  have hseg (a b : Plane) (ha : a 0 = 0) (hb : b 0 = 0) :
      u ∉ segP a b '' Icc (-1 : ℝ) 1 := by
    rintro ⟨t, _, htu⟩
    apply hu0
    rw [← htu, segP_coord, ha, hb]
    ring
  rintro ⟨t, ht, htu⟩
  have h := hβmem t ht
  rw [htu] at h
  rcases h with (((h | h) | h) | h) | h
  · exact hseg _ _ (by simp) hl0 h
  · exact hLm h
  · exact hseg _ _ hm0 hp0 h
  · exact hPq h
  · exact hseg _ _ hq0 (by simp) h

private theorem bounded_component_avoids_axis_up
    (S W : Set Plane) (hWsub : W ⊆ Sᶜ) (hwb : IsBounded W)
    (compW : ∀ {v : Plane}, v ∈ W → connectedComponentIn Sᶜ v = W)
    (l : Plane) (hl0 : l 0 = 0) (hlr : l ∈ S)
    (hRayNc : {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioi (l 1)} ⊆ Sᶜ) :
    ∀ v : Plane, v 0 = 0 → l 1 ≤ v 1 → v ∉ W := by
  let RayN : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioi (l 1)}
  have hRayNPC : IsPathConnected RayN :=
    isPathConnected_vertSeg 0 ((convex_Ioi (l 1)).isPathConnected Set.nonempty_Ioi)
  intro v hv0 hvl hvW
  rcases eq_or_lt_of_le hvl with h | h
  · have hveq : v = l := by ext i; fin_cases i <;> simp [hv0, hl0, h]
    exact hWsub hvW (by rw [hveq]; exact hlr)
  · have h1 := hRayNPC.isConnected.isPreconnected.subset_connectedComponentIn
      (show v ∈ RayN from ⟨hv0, h⟩) hRayNc
    exact axis_ray_up_unbounded (l 1) (hwb.subset (compW hvW ▸ h1))

private theorem bounded_component_avoids_axis_down
    (S W : Set Plane) (hWsub : W ⊆ Sᶜ) (hwb : IsBounded W)
    (compW : ∀ {v : Plane}, v ∈ W → connectedComponentIn Sᶜ v = W)
    (q : Plane) (hq0 : q 0 = 0) (hqr : q ∈ S)
    (hRaySc : {v : Plane | v 0 = 0 ∧ v 1 ∈ Iio (q 1)} ⊆ Sᶜ) :
    ∀ v : Plane, v 0 = 0 → v 1 ≤ q 1 → v ∉ W := by
  let RayS : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Iio (q 1)}
  have hRaySPC : IsPathConnected RayS :=
    isPathConnected_vertSeg 0 ((convex_Iio (q 1)).isPathConnected Set.nonempty_Iio)
  intro v hv0 hvq hvW
  rcases eq_or_lt_of_le hvq with h | h
  · have hveq : v = q := by ext i; fin_cases i <;> simp [hv0, hq0, h]
    exact hWsub hvW (by rw [hveq]; exact hqr)
  · have h1 := hRaySPC.isConnected.isPreconnected.subset_connectedComponentIn
      (show v ∈ RayS from ⟨hv0, h⟩) hRaySc
    exact axis_ray_down_unbounded (q 1) (hwb.subset (compW hvW ▸ h1))

private theorem disjoint_component_avoids_axis_middle
    (S W U : Set Plane) (hWsub : W ⊆ Sᶜ) (hWU_disj : Disjoint W U)
    (p m : Plane) (hp0 : p 0 = 0) (hm0 : m 0 = 0) (hpr : p ∈ S) (hmr : m ∈ S)
    (hMidU : {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioo (p 1) (m 1)} ⊆ U) :
    ∀ v : Plane, v 0 = 0 → p 1 ≤ v 1 → v 1 ≤ m 1 → v ∉ W := by
  intro v hv0 hvp hvm hvW
  rcases eq_or_lt_of_le hvp with h | h
  · have hveq : v = p := by ext i; fin_cases i <;> simp [hv0, hp0, h]
    exact hWsub hvW (by rw [hveq]; exact hpr)
  · rcases eq_or_lt_of_le hvm with h' | h'
    · have hveq : v = m := by ext i; fin_cases i <;> simp [hv0, hm0, h']
      exact hWsub hvW (by rw [hveq]; exact hmr)
    · exact (Set.disjoint_left.mp hWU_disj hvW) (hMidU ⟨hv0, ⟨h, h'⟩⟩)

private theorem axis_point_avoids_horizontal_endpoints (p : Plane) (hp : p 0 = 0) :
    p ∉ ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h) <;>
    (have hc := congrArg (fun x : Plane => x 0) h; simp only [hp] at hc; norm_num at hc)

theorem step_B_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  classical
  obtain ⟨J_n, J_s, l, m, p, q, z₀, hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩, ⟨hpJs, hp0, hpm, hpmax⟩,
    ⟨hqJs, hq0, hqmin⟩, hz₀def, hml, hqp, hpz₀, hz₀m,
    hpcJs, hJoinJn, hJoinJs⟩ := exists_construction_points hbr hcont hinj hm hp hfar
  -- basic containments, coordinates, and rectangle bounds
  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have hs0 : (!₂[(0 : ℝ), -2] : Plane) 0 = 0 := by simp
  have hs1 : (!₂[(0 : ℝ), -2] : Plane) 1 = -2 := by simp
  have hn0 : (!₂[(0 : ℝ), 2] : Plane) 0 = 0 := by simp
  have hn1 : (!₂[(0 : ℝ), 2] : Plane) 1 = 2 := by simp
  have hz₀0 : z₀ 0 = 0 := by rw [hz₀def]; simp
  have hz₀1e : z₀ 1 = (m 1 + p 1) / 2 := by rw [hz₀def]; simp
  have hmr : m ∈ range r := hJnr hmJn
  have hlr : l ∈ range r := hJnr hlJn
  have hpr : p ∈ range r := hJsr hpJs
  have hqr : q ∈ range r := hJsr hqJs
  have hmE1 : m 1 ∈ Icc (-2 : ℝ) 2 := (hErect hmr).2
  have hlE1 : l 1 ∈ Icc (-2 : ℝ) 2 := (hErect hlr).2
  have hpE1 : p 1 ∈ Icc (-2 : ℝ) 2 := (hErect hpr).2
  have hqE1 : q 1 ∈ Icc (-2 : ℝ) 2 := (hErect hqr).2
  have hpm_lt : p 1 < m 1 := by
    rcases lt_or_eq_of_le hpm with h | h
    · exact h
    · exfalso
      have hpm_eq : p = m := by ext i; fin_cases i <;> simp [hp0, hm0, h]
      have hmem : m ∈ J_n ∩ J_s := ⟨hmJn, hpm_eq ▸ hpJs⟩
      rw [hInter] at hmem
      rcases hmem with h' | h' <;>
        (have hc := congrArg (fun x : Plane => x 0) h'; simp only [hm0] at hc; norm_num at hc)
  have hpz₀_lt : p 1 < z₀ 1 := by rw [hz₀1e]; linarith
  have hz₀m_lt : z₀ 1 < m 1 := by rw [hz₀1e]; linarith
  have hmab := axis_point_avoids_horizontal_endpoints m hm0
  have hlab := axis_point_avoids_horizontal_endpoints l hl0
  have hqab := axis_point_avoids_horizontal_endpoints q hq0
  have hpab := axis_point_avoids_horizontal_endpoints p hp0
  have hz₀c : z₀ ∈ (range r)ᶜ := by
    intro hz₀r
    rw [← hUnion] at hz₀r
    rcases hz₀r with hJn | hJs
    · exact absurd (hmmin z₀ hJn hz₀0) (not_le.2 hz₀m_lt)
    · exact absurd (hpmax z₀ hJs hz₀0 hz₀m_lt.le) (not_le.2 hpz₀_lt)
  -- interval facts
  have hIcc0x : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc2y : (2 : ℝ) ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm2y : (-2 : ℝ) ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc]; norm_num
  -- the `z₀`-component `U`, the rectangle `E`
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUdef
  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} with hEdef
  -- the open middle axis segment `(p,m)` lies in `U`
  set Mid : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioo (p 1) (m 1)} with hMiddef
  have hMidPC : IsPathConnected Mid :=
    isPathConnected_vertSeg 0 ((convex_Ioo (p 1) (m 1)).isPathConnected (Set.nonempty_Ioo.mpr
      hpm_lt))
  have hMidc : Mid ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (hmmin v h hv0) (not_le.2 hv1.2)
    · exact absurd (hpmax v h hv0 hv1.2.le) (not_le.2 hv1.1)
  have hz₀Mid : z₀ ∈ Mid :=
    ⟨hz₀0, by rw [hz₀1e]; exact ⟨by linarith [hpm_lt], by linarith [hpm_lt]⟩⟩
  have hMidU : Mid ⊆ U :=
    hMidPC.isConnected.isPreconnected.subset_connectedComponentIn hz₀Mid hMidc
  -- upward and downward axis rays lie in the complement
  set RayN : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioi (l 1)} with hRayNdef
  have hRayNc : RayN ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr; exact absurd (hlmax v hvr hv0) (not_le.2 hv1)
  set RayS : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Iio (q 1)} with hRaySdef
  have hRaySc : RayS ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (le_trans (le_trans hqp hpm) (hmmin v h hv0)) (not_le.2 hv1)
    · exact absurd (hqmin v h hv0) (not_le.2 hv1)
  -- **KEY**: every bounded component equals `U`.
  have KEY : ∀ w ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ w) →
      connectedComponentIn (range r)ᶜ w = U := by
    intro w hw hwb
    by_contra hWne
    set W : Set Plane := connectedComponentIn (range r)ᶜ w with hWdef
    have hWsub : W ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
    have hWpc : IsPathConnected W := isPathConnected_component r hcont hw
    -- `W` and `U` are disjoint
    have hWU_disj : Disjoint W U := by
      rw [Set.disjoint_left]
      intro v hvW hvU
      apply hWne
      rw [hWdef, connectedComponentIn_eq (hWdef ▸ hvW), hUdef]
      exact (connectedComponentIn_eq (hUdef ▸ hvU)).symm
    -- component-equation helper: any `v ∈ W` has component `= W`
    have compW : ∀ {v : Plane}, v ∈ W → connectedComponentIn (range r)ᶜ v = W := by
      intro v hvW; rw [hWdef]; exact (connectedComponentIn_eq (hWdef ▸ hvW)).symm
    -- avoid lemmas
    have avoid_up := bounded_component_avoids_axis_up
      (range r) W hWsub hwb compW l hl0 hlr hRayNc
    have avoid_down := bounded_component_avoids_axis_down
      (range r) W hWsub hwb compW q hq0 hqr hRaySc
    have avoid_mid := disjoint_component_avoids_axis_middle
      (range r) W U hWsub hWU_disj p m hp0 hm0 hpr hmr hMidU
    -- `W ⊆ E` (a bounded component lies in the rectangle)
    have hWE : W ⊆ E := bounded_component_subset_normalized_rectangle hErect w hwb
    -- **spine path** `β : n → s`, top to bottom, missing `W`, inside `E`
    have hnl_cont : ContinuousOn (segP (!₂[(0 : ℝ), 2]) l) (Icc (-1 : ℝ) 1) := (segP_cont _
      _).continuousOn
    obtain ⟨lm, hlm_cont, hlm_a, hlm_b, hlm_mem⟩ :=
      arc_path (hpcJn.joinedIn l ⟨hlJn, hlab⟩ m ⟨hmJn, hmab⟩)
    have hmp_cont : ContinuousOn (segP m p) (Icc (-1 : ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨pq, hpq_cont, hpq_a, hpq_b, hpq_mem⟩ :=
      arc_path (hpcJs.joinedIn p ⟨hpJs, hpab⟩ q ⟨hqJs, hqab⟩)
    have hqs_cont : ContinuousOn (segP q (!₂[(0 : ℝ), -2])) (Icc (-1 : ℝ) 1) := (segP_cont _
      _).continuousOn
    obtain ⟨β, hβcont, hβa, hβb, hβmem⟩ :=
      concatPath5 hnl_cont hlm_cont hmp_cont hpq_cont hqs_cont
        (by rw [segP_one, hlm_a]) (by rw [hlm_b, segP_neg1]) (by rw [segP_one, hpq_a])
        (by rw [hpq_b, segP_neg1])
    have hβE : ∀ t ∈ Icc (-1 : ℝ) 1, β t 0 ∈ Icc (-1 : ℝ) 1 ∧ β t 1 ∈ Icc (-2 : ℝ) 2 := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hn0]; exact hIcc0x) (by rw [hl0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 (by rw [hn1]; exact hIcc2y) hlE1 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hm0]; exact hIcc0x) (by rw [hp0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 hmE1 hpE1 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hq0]; exact hIcc0x) (by rw [hs0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 hqE1 (by rw [hs1]; exact hIccm2y) hu⟩
    have hβmiss : ∀ t ∈ Icc (-1 : ℝ) 1, β t ∉ W := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_up _ ?_ ?_
        · rw [segP_coord, hn0, hl0]; ring
        · rw [segP_coord, hn1]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hlE1.2]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_mid _ ?_ ?_ ?_
        · rw [segP_coord, hm0, hp0]; ring
        · rw [segP_coord]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hpm_lt.le]
        · rw [segP_coord]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hpm_lt.le]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_down _ ?_ ?_
        · rw [segP_coord, hq0, hs0]; ring
        · rw [segP_coord, hs1]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hqE1.1]
    -- `a, b ∈ closure W` (frontier of a component is the whole curve)
    have hfrW : frontier W = range r := by
      have hexists : ∃ y ∈ (range r)ᶜ,
          connectedComponentIn (range r)ᶜ y ≠ connectedComponentIn (range r)ᶜ w := by
        refine ⟨z₀, hz₀c, ?_⟩
        rw [← hUdef, ← hWdef]; exact fun h => hWne h.symm
      have hcbe := component_boundary_eq hbr hcont hinj hw hexists
      rwa [← hWdef] at hcbe
    have hafrW : (!₂[(-1 : ℝ), 0] : Plane) ∈ frontier W := by rw [hfrW]; exact hm
    have hbfrW : (!₂[(1 : ℝ), 0] : Plane) ∈ frontier W := by rw [hfrW]; exact hp
    have haclW : (!₂[(-1 : ℝ), 0] : Plane) ∈ closure W := frontier_subset_closure hafrW
    have hbclW : (!₂[(1 : ℝ), 0] : Plane) ∈ closure W := frontier_subset_closure hbfrW
    -- The crossing contradiction uses horizontal endpoints outside the spine.
    set βimg : Set Plane := β '' Icc (-1 : ℝ) 1 with hβimgdef
    have ha_notβ : (!₂[(-1 : ℝ), 0] : Plane) ∉ βimg := by
      apply spine_image_avoids_horizontal_endpoint l m p q hl0 hm0 hp0 hq0 lm pq β hβmem
        (!₂[(-1 : ℝ), 0]) (by norm_num)
      · rintro ⟨u, hu, hue⟩
        exact (hlm_mem u hu).2 (by rw [hue]; exact Set.mem_insert _ _)
      · rintro ⟨u, hu, hue⟩
        exact (hpq_mem u hu).2 (by rw [hue]; exact Set.mem_insert _ _)
    have hb_notβ : (!₂[(1 : ℝ), 0] : Plane) ∉ βimg := by
      apply spine_image_avoids_horizontal_endpoint l m p q hl0 hm0 hp0 hq0 lm pq β hβmem
        (!₂[(1 : ℝ), 0]) (by norm_num)
      · rintro ⟨u, hu, hue⟩
        exact (hlm_mem u hu).2 (by rw [hue]; exact Set.mem_insert_of_mem _ rfl)
      · rintro ⟨u, hu, hue⟩
        exact (hpq_mem u hu).2 (by rw [hue]; exact Set.mem_insert_of_mem _ rfl)
    exact path_component_crossing_contradiction hbr W hWpc hWE β hβcont hβE
      (by simpa only [segP_neg1] using hβa) (by simpa only [segP_one] using hβb)
      hβmiss haclW hbclW ha_notβ hb_notβ
  -- assemble: bounded components of `x, y` both equal `U`
  intro x hx y hy hxb hyb
  rw [KEY x hx hxb, KEY y hy hyb]

/-- **Maehara Step B (geometric core).** Bounded components of `ℝ²∖J` are unique.
Reduced to the normalized version `step_B_normalized` via the farthest-pair
similarity `T`. -/
theorem step_B_bounded_unique (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  intro x hx y hy hxb hyb
  obtain ⟨a, ha, b, hb, hfar0, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0 : ℝ) < 2 / dist a b := by positivity
  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]
  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  have hrc : (range r')ᶜ = (T : Plane → Plane) '' (range r)ᶜ := by rw [hrange, himg]
  have hm' : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : (!₂[(1 : ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTb]; exact mem_image_of_mem _ hb
  have hfar' : ∀ z ∈ range r', ∀ w ∈ range r', dist z w ≤ 2 := by
    rw [hrange]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hscale]
    calc 2 / dist a b * dist z w
        ≤ 2 / dist a b * dist a b :=
          mul_le_mul_of_nonneg_left (hfar0 z hz w hw) hcpos.le
      _ = 2 := by field_simp
  -- transport the two components forward by `T`
  have hTx : T x ∈ (range r')ᶜ := by rw [hrc]; exact mem_image_of_mem _ hx
  have hTy : T y ∈ (range r')ᶜ := by rw [hrc]; exact mem_image_of_mem _ hy
  have hccx : connectedComponentIn (range r')ᶜ (T x)
      = T '' connectedComponentIn (range r)ᶜ x := by
    rw [hrc]; exact (T.image_connectedComponentIn hx).symm
  have hccy : connectedComponentIn (range r')ᶜ (T y)
      = T '' connectedComponentIn (range r)ᶜ y := by
    rw [hrc]; exact (T.image_connectedComponentIn hy).symm
  have hTxb : IsBounded (connectedComponentIn (range r')ᶜ (T x)) := by
    rw [hccx]; exact (isBounded_image_scaling hcpos hscale _).mpr hxb
  have hTyb : IsBounded (connectedComponentIn (range r')ᶜ (T y)) := by
    rw [hccy]; exact (isBounded_image_scaling hcpos hscale _).mpr hyb
  have hEq := step_B_normalized hbr hr'cont hr'inj hm' hp' hfar'
    (T x) hTx (T y) hTy hTxb hTyb
  rw [hccx, hccy] at hEq
  exact Set.image_injective.mpr T.injective hEq

/-- The Jordan curve theorem reduced to Brouwer (Maehara). The eval `jordan_curve`
follows by discharging `BrouwerFPT`. Given the two geometric core facts — existence
(`step_A_exists_bounded`) and uniqueness (`step_B_bounded_unique`) of a bounded
component — together with the unique unbounded component (`exists_unbounded_component`,
`unbounded_component_unique`), the complement has exactly two components. -/
theorem jordan_curve_of_brouwer (hbr : BrouwerFPT)
    (r : sphere (0 : Plane) 1 → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set Plane)) = 2 := by
  -- The unbounded component `x₀` and a bounded component `x₁`.
  obtain ⟨x₀, hx₀S, hx₀u⟩ := exists_unbounded_component r hcont
  obtain ⟨x₁, hx₁S, hx₁b⟩ := step_A_exists_bounded hbr hcont hinj
  set a : ↥((range r)ᶜ) := ⟨x₀, hx₀S⟩ with ha
  set b : ↥((range r)ᶜ) := ⟨x₁, hx₁S⟩ with hb
  -- The two components are distinct: one unbounded, one bounded.
  have hne : connectedComponentIn (range r)ᶜ x₀ ≠ connectedComponentIn (range r)ᶜ x₁ := by
    intro heq
    exact hx₀u (heq ▸ hx₁b)
  have hab : ConnectedComponents.mk a ≠ ConnectedComponents.mk b :=
    (Counting.connectedComponents_subtype_eq_iff hx₀S hx₁S).not.mpr hne
  -- Every component is either the bounded one (`= b`) or the unbounded one (`= a`).
  have hcover : ∀ z : ↥((range r)ᶜ),
      ConnectedComponents.mk z = ConnectedComponents.mk a
        ∨ ConnectedComponents.mk z = ConnectedComponents.mk b := by
    intro z
    by_cases hzb : IsBounded (connectedComponentIn (range r)ᶜ z.val)
    · right
      exact (Counting.connectedComponents_subtype_eq_iff z.2 hx₁S).mpr
        (step_B_bounded_unique hbr hcont hinj z.val z.2 x₁ hx₁S hzb hx₁b)
    · left
      exact (Counting.connectedComponents_subtype_eq_iff z.2 hx₀S).mpr
        (unbounded_component_unique r hcont hzb hx₀u)
  exact Counting.nat_card_connectedComponents_eq_two a b hab hcover

/-- **Jordan curve theorem** (the eval statement). -/
theorem jordan_curve
    (r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) = 2 := by
  -- Brouwer FPT for the plane, built from scratch in `JordanCurve.Brouwer`
  -- (circle non-nullhomotopy via Mathlib's covering-space lifting → no-retraction
  -- → disk Brouwer → convex-compact).
  have hbr : BrouwerFPT := Brouwer.brouwerFPT
  exact jordan_curve_of_brouwer hbr r _hcont _hinj

end JordanCurve

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Metric variation of a continuously differentiable curve

For a continuously differentiable curve in a complete real normed space, its
metric total variation equals the integral of the norm of its derivative.

The upper bound sums the fundamental theorem of calculus over finite
partitions. For the reverse bound, the curve is clamped to the compact
parameter interval. The resulting globally Lipschitz curve has bounded
variation, and its associated vector measure has density given by the
derivative on the interval.

## Main result

* `TauCeti.eVariationOn_eq_lintegral_enorm_derivWithin`: metric variation
  equals the integral of the derivative norm.

## Roadmap alignment

This module advances the `Regular reparametrization and limits` target under
`Layer 0: the reconciled Riemannian distance` in
`roadmap/HopfRinow/README.md`. It supplies the vector metric-variation
identity used as an analytic prerequisite by the lower-semicontinuity
comparison; this file does not claim the broader
Hopf--Rinow dependency path.

## Provenance

The partition-comparison architecture follows
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean` in the
Apache-2.0 `frenzymath/Poincare-Conjecture` source at revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. That source proves the forward
comparison with Riemannian path length. The reverse derivative-integral
comparison here is a Tau Ceti proof using Mathlib's clamped-curve and
vector-measure APIs; it is not asserted to be present in that source.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.
* The source-first Lean snapshot above, revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321`, supplies the partition architecture
  via `eVariationOn_le_pathELength`; the reverse inequality is original to this
  module.

Original authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu.
-/

public section

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a `C¹` curve in a real normed space, metric total variation is bounded
by the integral of the norm of its derivative. -/
theorem eVariationOn_le_lintegral_enorm_derivWithin {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ := by
  let L : ℝ → ℝ → ℝ≥0∞ := fun c d ↦
    ∫⁻ t in Icc c d, ‖derivWithin f (Icc a b) t‖ₑ
  have hL_add {c d e : ℝ} (hcd : c ≤ d) (hde : d ≤ e) : L c d + L d e = L c e := by
    have hset : Icc c e = Icc c d ∪ Ioc d e := (Icc_union_Ioc_eq_Icc hcd hde).symm
    simp only [L, hset]
    rw [lintegral_union measurableSet_Ioc]
    · simp only [restrict_Ioc_eq_restrict_Icc]
    · exact disjoint_iff_forall_ne.mpr (fun u hu v hv ↦ (hu.2.trans_lt hv.1).ne)
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hsegment : ∀ i, edist (f (u (i + 1))) (f (u i)) ≤ L (u i) (u (i + 1)) := by
    intro i
    have hlocal := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
      (hf.mono (Icc_subset_Icc (hus i).1 (hus (i + 1)).2)) (hu (Nat.le_succ i))
    calc
      edist (f (u (i + 1))) (f (u i)) = ‖f (u (i + 1)) - f (u i)‖ₑ := by
        rw [edist_eq_enorm_sub, enorm_sub_rev]
      _ ≤ ∫⁻ t in Icc (u i) (u (i + 1)),
          ‖derivWithin f (Icc (u i) (u (i + 1))) t‖ₑ := hlocal
      _ = L (u i) (u (i + 1)) := by
        simp only [L]
        rw [← restrict_Ioo_eq_restrict_Icc]
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        have hderiv :
            derivWithin f (Icc (u i) (u (i + 1))) t = derivWithin f (Icc a b) t := by
          rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
            derivWithin_of_mem_nhds
              (Icc_mem_nhds ((hus i).1.trans_lt ht.1) (ht.2.trans_le (hus (i + 1)).2))]
        simp only [hderiv]
  have htelescoping : ∀ m, ∑ i ∈ Finset.range m, L (u i) (u (i + 1)) = L (u 0) (u m) := by
    intro m
    induction m with
    | zero => simp [L]
    | succ k ih => rw [Finset.sum_range_succ, ih, hL_add
        (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]
  calc
    ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
        ≤ ∑ i ∈ Finset.range n, L (u i) (u (i + 1)) :=
      Finset.sum_le_sum fun i _ ↦ hsegment i
    _ = L (u 0) (u n) := htelescoping n
    _ ≤ L a b := lintegral_mono_set (Icc_subset_Icc (hus 0).1 (hus n).2)
    _ = ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ := rfl

variable [CompleteSpace F]

/-- For a `C¹` curve in a complete real normed space, the integral of the norm
of its derivative is bounded by its metric total variation. -/
theorem lintegral_enorm_derivWithin_le_eVariationOn {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ ≤ eVariationOn f (Icc a b) := by
  by_cases hab : a ≤ b
  swap
  · rw [Icc_eq_empty hab]
    simp
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let p : ℝ → ℝ := fun t ↦ (Set.projIcc a b hab.le t).val
  let g : ℝ → F := f ∘ p
  let D : ℝ → F := (Icc a b).indicator (derivWithin f (Icc a b))
  have hp_mono : Monotone p := fun x y hxy ↦ by
    exact_mod_cast Set.monotone_projIcc hab.le hxy
  have hp_mem : MapsTo p univ (Icc a b) := fun t _ ↦ (Set.projIcc a b hab.le t).2
  have hD_cont : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  obtain ⟨C, hCpos, hC⟩ :=
    (isCompact_Icc.image_of_continuousOn hD_cont).isBounded.exists_pos_norm_le
  let K : ℝ≥0 := ⟨C, hCpos.le⟩
  have hK : LipschitzOnWith K f (Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_derivWithin_le
      hf.differentiableOn_one
    intro t ht
    exact_mod_cast hC _ (mem_image_of_mem _ ht)
  have hg_lip : LipschitzWith K g := by
    have h := hK.comp (s := univ) (LipschitzWith.projIcc hab.le).lipschitzOnWith hp_mem
    rw [mul_one, lipschitzOnWith_univ] at h
    exact h
  have hp_bv : BoundedVariationOn p univ := by
    apply MonotoneOn.boundedVariationOn (hp_mono.monotoneOn univ) (C := max |a| |b|)
    intro t _
    exact (abs_le_max_abs_abs (Set.projIcc a b hab.le t).2.1
      (Set.projIcc a b hab.le t).2.2)
  have hg_bv : BoundedVariationOn g univ := hK.comp_boundedVariationOn hp_mem hp_bv
  have hg_cont : Continuous g := hg_lip.continuous
  have hright : Function.rightLim g = g := by
    funext t
    exact hg_cont.continuousWithinAt.rightLim_eq
  have hD_int : Integrable D :=
    hD_cont.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hprimitive : ∀ x : ℝ, ∫ t in a..x, D t = g x - g a := by
    intro x
    rcases le_total x a with hxa | hax
    · have hz : ∫ t in x..a, D t = 0 := by
        apply intervalIntegral.integral_zero_ae
        filter_upwards [volume.ae_ne a] with t hne hmem
        rw [uIoc_of_le hxa] at hmem
        have hlt : t < a := lt_of_le_of_ne hmem.2 hne
        have hnot : t ∉ Icc a b := fun hmem ↦ (not_le_of_gt hlt) hmem.1
        simp [D, hnot]
      rw [intervalIntegral.integral_symm, hz, neg_zero]
      have hpa : p a = a := by simp [p]
      have hpx : p x = a := by simp [p, Set.projIcc_of_le_left hab.le hxa]
      simp [g, hpa, hpx]
    · rcases le_total x b with hxb | hbx
      · have hcongr : ∫ t in a..x, D t = ∫ t in a..x, deriv f t := by
          apply intervalIntegral.integral_congr_Ioo_of_le hax
          intro t ht
          have htab : t ∈ Icc a b := ⟨ht.1.le, ht.2.le.trans hxb⟩
          simp only [D, Set.indicator_of_mem htab]
          exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 (ht.2.trans_le hxb))
        rw [hcongr, intervalIntegral.integral_deriv_of_contDiffOn_Icc
          (hf.mono (Icc_subset_Icc_right hxb)) hax]
        have hpa : p a = a := by simp [p]
        have hpx : p x = x := by simp [p, Set.projIcc_of_mem hab.le ⟨hax, hxb⟩]
        simp [g, hpa, hpx]
      · have hab_int : ∫ t in a..b, D t = f b - f a := by
          have hcongr : ∫ t in a..b, D t = ∫ t in a..b, deriv f t := by
            apply intervalIntegral.integral_congr_Ioo_of_le hab.le
            intro t ht
            simp only [D, Set.indicator_of_mem (Ioo_subset_Icc_self ht)]
            exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
          rw [hcongr, intervalIntegral.integral_deriv_of_contDiffOn_Icc hf hab.le]
        have hzero : ∫ t in b..x, D t = 0 := by
          apply intervalIntegral.integral_zero_ae
          filter_upwards with t ht
          rw [uIoc_of_le hbx] at ht
          have hnot : t ∉ Icc a b := fun hmem ↦ (not_le_of_gt ht.1) hmem.2
          simp [D, hnot]
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hD_int.intervalIntegrable hD_int.intervalIntegrable, hab_int, hzero, add_zero]
        have hpa : p a = a := by simp [p]
        have hpx : p x = b := by simp [p, Set.projIcc_of_right_le hab.le hbx]
        simp [g, hpa, hpx]
  have hinterval : ∀ {c d : ℝ}, c ≤ d → ∫ t in c..d, D t = g d - g c := by
    intro c d hcd
    have hac := intervalIntegral.integral_add_adjacent_intervals
      hD_int.intervalIntegrable hD_int.intervalIntegrable (a := a) (b := c) (c := d)
    rw [hprimitive c, hprimitive d] at hac
    apply eq_sub_iff_add_eq.mpr
    calc
      (∫ t in c..d, D t) + g c = (g c - g a + ∫ t in c..d, D t) + g a := by abel
      _ = (g d - g a) + g a := by rw [hac]
      _ = g d := by abel
  have hmeasure : hg_bv.vectorMeasure = volume.withDensityᵥ D := by
    apply VectorMeasure.ext_of_generateFrom
      {s : Set ℝ | ∃ c d, c ≤ d ∧ s = Ioc c d}
    · rintro s ⟨c, d, hcd, rfl⟩
      rw [hg_bv.vectorMeasure_Ioc hcd, hright, withDensityᵥ_apply hD_int measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hcd, hinterval hcd]
    · convert! BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc_le ℝ) using 2;
        grind only
    · exact IsSetSemiring.Ioc.isPiSystem
    · rw [hg_bv.vectorMeasure_univ, withDensityᵥ_apply hD_int MeasurableSet.univ]
      simp only [Measure.restrict_univ, D]
      rw [MeasureTheory.integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab.le,
        intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hf hab.le]
      have htop : Tendsto g atTop (𝓝 (f b)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Ici_mem_atTop b] with t ht
        simp [g, p, Set.projIcc_of_right_le hab.le ht]
      have hbot : Tendsto g atBot (𝓝 (f a)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Iic_mem_atBot a] with t ht
        simp [g, p, Set.projIcc_of_le_left hab.le ht]
      rw [tendsto_nhds_unique hg_bv.tendsto_atTop_limUnder htop,
        tendsto_nhds_unique hg_bv.tendsto_atBot_limUnder hbot]
  have hvariation : eVariationOn g univ = eVariationOn f (Icc a b) := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨n, u, hu, -⟩
      simpa only [g, Function.comp_apply] using
        (eVariationOn.sum_le (f := f) (hp_mono.comp hu)
          (fun i ↦ hp_mem (mem_univ _)))
    · calc
        eVariationOn f (Icc a b) = eVariationOn g (Icc a b) := by
          apply eVariationOn.eq_of_eqOn
          intro t ht
          simp [g, p, Set.projIcc_of_mem hab.le ht]
        _ ≤ eVariationOn g univ := eVariationOn.mono g (subset_univ _)
  calc
    ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ
        = (volume.withDensity fun t ↦ ‖D t‖ₑ) univ := by
          rw [withDensity_apply _ MeasurableSet.univ]
          simp only [Measure.restrict_univ]
          rw [← lintegral_indicator measurableSet_Icc]
          apply lintegral_congr
          intro t
          by_cases ht : t ∈ Icc a b <;> simp [D, ht]
    _ = (volume.withDensityᵥ D).variation univ := by
      rw [Measure.variation_withDensityᵥ hD_int]
    _ = hg_bv.vectorMeasure.variation univ := by rw [hmeasure]
    _ ≤ eVariationOn g univ := hg_bv.variation_vectorMeasure_univ_le
    _ = eVariationOn f (Icc a b) := hvariation

/-- The metric total variation of a `C¹` curve in a complete real normed space
equals the integral of the norm of its derivative. -/
theorem eVariationOn_eq_lintegral_enorm_derivWithin {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    eVariationOn f (Icc a b) = ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ :=
  le_antisymm (eVariationOn_le_lintegral_enorm_derivWithin hf)
    (lintegral_enorm_derivWithin_le_eVariationOn hf)

end

end TauCeti

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The exterior of a closed ball is preconnected

In a real normed space of dimension at least two the complement of a closed ball is preconnected:
it is the union, over the radii `M` exceeding the ball's, of the spheres of radius `M`, strung
together along a single ray from the centre.

The consequences for bounded sets — uniqueness of the unbounded component and the filled-hull
alternative — are in `TauCeti/Analysis/Normed/Module/FilledHull.lean`.

## Main results

* `TauCeti.isPreconnected_compl_closedBall` — the exterior of a closed ball is preconnected in a
  real normed space of dimension at least two.

This is a prerequisite of the planar-separation step of the `ConformalMapping` roadmap (L5).

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The exterior of a closed ball is preconnected** in a real normed space of dimension at least
two. -/
theorem isPreconnected_compl_closedBall (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPreconnected (closedBall x r)ᶜ := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [closedBall_eq_empty.mpr hr, compl_empty]
    exact isPreconnected_univ
  have : Nontrivial E := rank_pos_iff_nontrivial.mp (zero_lt_one.trans h)
  obtain ⟨u, hu⟩ := exists_norm_eq E zero_le_one
  set L : Set E := (fun t : ℝ => x + t • u) '' Ioi r
  have hLc : IsPreconnected L :=
    isPreconnected_Ioi.image _ (by fun_prop : Continuous fun t : ℝ => x + t • u).continuousOn
  have hLmem : ∀ t, r < t → x + t • u ∈ L := fun t ht => ⟨t, ht, rfl⟩
  have hdist : ∀ t : ℝ, 0 ≤ t → dist (x + t • u) x = t := by
    intro t ht
    simp [dist_eq_norm, norm_smul, hu, abs_of_nonneg ht]
  have hmem : ∀ w, w ∈ (closedBall x r)ᶜ ↔ r < dist w x := by
    simp [mem_closedBall, not_le]
  have hLsub : L ⊆ (closedBall x r)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hmem, hdist t (hr.trans ht.le)]
    exact ht
  have key : (closedBall x r)ᶜ = ⋃ M : Ioi r, (sphere x M ∪ L) := by
    ext w
    constructor
    · intro hw
      exact mem_iUnion.mpr ⟨⟨dist w x, (hmem w).mp hw⟩, Or.inl (mem_sphere.mpr rfl)⟩
    · intro hw
      obtain ⟨⟨M, hM⟩, hwM⟩ := mem_iUnion.mp hw
      rcases hwM with hwM | hwM
      · rw [hmem]; rw [mem_sphere, dist_comm] at hwM; rw [dist_comm, hwM]; exact hM
      · exact hLsub hwM
  rw [key]
  refine isPreconnected_iUnion ⟨x + (r + 1) • u, ?_⟩ fun ⟨M, hM⟩ => ?_
  · simp only [mem_iInter]
    exact fun _ => Or.inr (hLmem _ (by linarith))
  · refine IsPreconnected.union (x + M • u) ?_ (hLmem M hM) (isPreconnected_sphere h x M) hLc
    rw [mem_sphere, hdist M (hr.trans hM.le)]

end TauCeti

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Strict half-spaces of a real normed space are unbounded

A strict half-space `{y | φ y < u}` cut out by a nonzero linear functional holds points of
arbitrarily large norm, and is therefore unbounded. Linearity alone suffices: `φ` need not be
continuous, so the results apply to a discontinuous functional on an infinite-dimensional space.
For such a `φ` the set need not be topologically open, which is why it is called strict rather
than open here.

## Main results

* `TauCeti.exists_apply_lt_and_lt_norm` and `TauCeti.exists_lt_apply_and_lt_norm` — either side
  of a nonzero linear functional holds points of arbitrarily large norm.
* `TauCeti.not_isBounded_halfSpace_lt` and `TauCeti.not_isBounded_halfSpace_gt` — either strict
  half-space is unbounded.
-/

public section

namespace TauCeti

open Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A strict half-space contains points of arbitrarily large norm.** For a nonzero linear
functional `φ`, every bound `u` and every radius `R` admit a `y` with `φ y < u` and `R < ‖y‖`.
Linearity suffices; `φ` need not be continuous. -/
theorem exists_apply_lt_and_lt_norm {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, φ y < u ∧ R < ‖y‖ := by
  obtain ⟨v, hφv⟩ := LinearMap.surjective_iff_ne_zero.mpr hφ 1
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr fun h => by simp [h] at hφv
  -- Walk to `-t • v` for a `t` large enough to break both the bound `u` and the radius `R`.
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, (R + 1) / ‖v‖ ≤ t ∧ |u| + 1 ≤ t :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have ht0 : 0 ≤ t := le_trans (by positivity) ht2
  refine ⟨(-t) • v, ?_, ?_⟩
  · rw [map_smul, hφv, smul_eq_mul, mul_one]
    linarith [neg_abs_le u]
  · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith [(div_le_iff₀ hvnorm).mp ht1]

/-- **The other side of a nonzero linear functional also contains points of arbitrarily large
norm**: every bound `u` and radius `R` admit a `y` with `u < φ y` and `R < ‖y‖`. -/
theorem exists_lt_apply_and_lt_norm {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, u < φ y ∧ R < ‖y‖ := by
  obtain ⟨y, hy, hn⟩ := exists_apply_lt_and_lt_norm (φ := -φ) (neg_ne_zero.mpr hφ) (-u) R
  exact ⟨y, by simpa using hy, hn⟩

/-- **A strict half-space cut out by a nonzero linear functional is unbounded.** No radius bounds
`{y | φ y < u}`. Linearity suffices; `φ` need not be continuous. -/
theorem not_isBounded_halfSpace_lt {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ¬ IsBounded {y | φ y < u} := by
  intro hbdd
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
  obtain ⟨y, hy, hn⟩ := exists_apply_lt_and_lt_norm hφ u R
  exact absurd (hR y (by simpa using hy)) (not_le.mpr hn)

/-- **The half-space on the other side of a nonzero linear functional is unbounded.** No radius
bounds `{y | u < φ y}` either. Linearity suffices; `φ` need not be continuous. -/
theorem not_isBounded_halfSpace_gt {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ¬ IsBounded {y | u < φ y} := by
  intro hbdd
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
  obtain ⟨y, hy, hn⟩ := exists_lt_apply_and_lt_norm hφ u R
  exact absurd (hR y (by simpa using hy)) (not_le.mpr hn)

end TauCeti

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Limits of total variation bounds

This file transfers eventual upper bounds on the total variations of a family of maps to a
`liminf` bound on the total variation of a pointwise limit.

## Main results

* `TauCeti.eVariationOn_le_liminf_of_eventually_le`: an eventual bound on the total variations of
  a family of maps bounds the total variation of a pointwise limit by the `liminf` of the bounds.
-/

public section

open Filter
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [LinearOrder α] {X : Type*} [PseudoEMetricSpace X]

/-- The metric variation of a path in a subtype is unchanged by applying its coercion. -/
@[simp] theorem eVariationOn_subtypeVal_comp {s : Set X} {f : α → s} {t : Set α} :
    eVariationOn f t = eVariationOn ((Subtype.val : s → X) ∘ f) t := by
  rfl

/-- If the total variations of the maps `F i` on `s` are eventually bounded by `u i`, then the
total variation on `s` of a pointwise limit of the `F i` is at most `liminf u`. -/
theorem eVariationOn_le_liminf_of_eventually_le {ι : Type*} {l : Filter ι} {s : Set α}
    {f : α → X} {F : ι → α → X} {u : ι → ℝ≥0∞}
    (hu : ∀ᶠ i in l, eVariationOn (F i) s ≤ u i)
    (hf : ∀ x ∈ s, Tendsto (fun i ↦ F i x) l (nhds (f x))) :
    eVariationOn f s ≤ liminf u l := by
  rw [le_liminf_iff]
  intro v hv
  filter_upwards [eVariationOn.lowerSemicontinuous_aux hf hv, hu] with i hi hui
  exact hi.trans_le hui

end TauCeti

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# External libraries

The modules from Mathlib, lean-pool, TauCeti and jordan_pick that the development uses beyond its
own files, collected in one place.
-/

public section

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Three frontier lemmas: straddling, splitting a domain in two, and clinging to it from inside

Three elementary facts about `frontier`, each the topological core of a step that a boundary
argument would otherwise carry out inside a concrete space.

## A connected set that straddles a set meets its frontier

A preconnected set that meets both a set `V` and its complement must meet `frontier V`: it cannot
cross from the inside of `V` to the outside without touching the boundary. This is the
intermediate-value principle in its purely topological form, and it is the mechanism by which a
*path* leaving a set produces a *boundary point* of that set.

Mathlib records the two extreme cases — `frontier_eq_empty_iff` and `nonempty_frontier_iff` say
that in a preconnected *space* the frontier of `V` is empty exactly when `V` is `∅` or `univ` — but
not this relative form, which is the one an argument along a segment or a path needs. No hypothesis
is placed on `V`; only preconnectedness of the straddling set is used.

The proof is the standard clopen argument: the complement of `frontier V` is the disjoint union of
the two open sets `interior V` and `interior Vᶜ` (`compl_frontier_eq_union_interior`), so a
preconnected set avoiding the frontier lies inside one of them, and then it misses `V` entirely or
is contained in `V` entirely.

## Where the boundary of the image of one side of a split domain can lie

Split a set `U` into two pieces `s` and `t` that a map `f` sends to *disjoint open* sets, plus a
remainder `u`. Then `frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`
(`TauCeti.frontier_image_subset_image_union_frontier_image`): the boundary of the image of one side
consists of images of the remainder — the cut — and of boundary points of the whole image, and of
nothing else.

The proof is a three-way case split. A point `p` of `frontier (f '' s)` lies in `closure (f '' U)`,
so if it is not on `frontier (f '' U)` it is a value `f w` with `w` in one of the three covering
sets. It cannot come from `s`, since `f '' s` is open and therefore disjoint from its own frontier;
and it cannot come from `t`, since `f '' t` is then an open neighbourhood of `p`, which must meet
`f '' s`, contradicting disjointness of the two images. So `w ∈ u`.

The source carries no topology; the sides enter topologically only through their images, which are
asked to be open and disjoint, and that is all the argument uses of them. What is asked of the
sides themselves is purely set-theoretic: `s ⊆ U` and the covering `U ⊆ s ∪ t ∪ u`. In particular
`t` need not lie in `U`, and neither side need be open or disjoint from the other. A consumer whose
map is open and injective on two disjoint open sides supplies both image hypotheses, as the
conformal one below does through the open mapping theorem and `Disjoint.image`.

## What a set's frontier sees of a subset

A subset `A` of a set `V` cannot reach `frontier V` except through its own frontier:

> `frontier V ∩ closure A = frontier V ∩ frontier A`

(`TauCeti.frontier_inter_closure_eq_frontier_inter_frontier`). The reason is that `closure A` is
`A ∪ frontier A`, and a point of `A` on `frontier V` is already on `frontier A`: it is adherent to
`A` and, since `interior A ⊆ interior V`, it is not interior to `A`. So the part of `frontier V`
that `A` clings to has two interchangeable descriptions — as the reach of `closure A`, and as the
meeting of two frontiers. The first is the one an argument about limits of points of `A` produces;
the second is the one a diameter estimate consumes, `frontier` being where the estimates of a
domain-splitting argument live.

## Consumers

All three lemmas serve layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's
boundary correspondence. The first does so through
`TauCeti/Analysis/Normed/Module/DiamFrontier.lean`: a ray leaving a bounded set crosses its
frontier, which is what makes the frontier of such a set as wide as the set itself. The second is
the splitting step of `TauCeti/Analysis/Complex/Conformal/CutDiameter.lean`, where `s` and `t` are
the two sides of a circular crosscut of a domain and `u` is the crosscut arc. The third is what
lets `TauCeti/Analysis/Complex/Conformal/ClusterSet.lean` identify the boundary piece that one
side of such a crosscut cuts off, whose description as a union of cluster sets is naturally a
statement about a closure. Nothing here is specific to those uses; no lemma mentions a metric, let
alone a holomorphic map.

## Main results

* `IsPreconnected.inter_frontier_nonempty` — a preconnected set meeting both a set and its
  complement meets the frontier of that set.
* `TauCeti.frontier_image_subset_image_union_frontier_image` — for a set split into two sides with
  disjoint open images plus a remainder, the frontier of the image of the side lying in that set
  lies on the image of the remainder and on the frontier of the image of the whole.
* `TauCeti.frontier_inter_closure_eq_frontier_inter_frontier` — the frontier of a set meets the
  closure of a subset exactly where it meets that subset's frontier.
-/

public section

namespace TauCeti

open Set

section Straddle

variable {X : Type*} [TopologicalSpace X] {S V : Set X}

/-- **A preconnected set that meets both a set and its complement meets its frontier.** If `S` is
preconnected and contains a point of `V` and a point outside `V`, then `S` meets `frontier V`.

Nothing is assumed about `V`; the argument is that `(frontier V)ᶜ` is the union of the two disjoint
open sets `interior V` and `interior Vᶜ`, so a preconnected set missing the frontier is confined to
one of them and therefore cannot straddle `V`. -/
theorem _root_.IsPreconnected.inter_frontier_nonempty (hS : IsPreconnected S)
    (h₁ : (S ∩ V).Nonempty) (h₂ : (S \ V).Nonempty) : (S ∩ frontier V).Nonempty := by
  by_contra hcon
  have hsub : S ⊆ interior V ∪ interior Vᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact fun x hx hxf => hcon ⟨x, hx, hxf⟩
  have hdisj : Disjoint (interior V) (interior Vᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  rcases hS.subset_or_subset isOpen_interior isOpen_interior hdisj hsub with h | h
  · obtain ⟨x, hxS, hxV⟩ := h₂
    exact hxV (interior_subset (h hxS))
  · obtain ⟨x, hxS, hxV⟩ := h₁
    exact interior_subset (h hxS) hxV

end Straddle

section ImageSplit

variable {X Y : Type*} [TopologicalSpace Y] {f : X → Y} {U s t u : Set X}

/-- **The boundary of the image of one side of a split domain lies on the image of the remainder
and on the boundary of the image of the domain.** If `U` is covered by two sets `s`, `t` with
disjoint open images together with a third set `u`, and `s ⊆ U`, then
`frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`.

The conclusion is about `s`, the side that is asked to lie in `U`. The argument treats the two
sides alike apart from that, so a consumer with `t ⊆ U` in hand bounds `t` as well by swapping
their roles.

A frontier point of `f '' s` lies in `closure (f '' U)`, so if it is not a frontier point of
`f '' U` it is a value `f w` with `w` in one of the three covering sets: `w ∈ s` would place it
inside the open set `f '' s`, which is disjoint from its own frontier, and `w ∈ t` inside the open
set `f '' t`, which meets `f '' s` because the point is in its closure, contradicting disjointness
of the two images. So `w ∈ u`.

The source carries no topology at all: `U` and the three sets covering it are constrained only by
the two set-theoretic hypotheses `hsU : s ⊆ U` and `hcov : U ⊆ s ∪ t ∪ u`, while every topological
hypothesis, and the conclusion, lives in the target. In particular `t` need not lie in `U`, and
the two sides need be neither open nor disjoint nor separated by injectivity — only their images
need be open and disjoint, which is what the argument uses and what an injective open map on two
disjoint open sides supplies. -/
theorem frontier_image_subset_image_union_frontier_image (hfs : IsOpen (f '' s))
    (hft : IsOpen (f '' t)) (hst : Disjoint (f '' s) (f '' t)) (hsU : s ⊆ U)
    (hcov : U ⊆ s ∪ t ∪ u) :
    frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U) := by
  intro p hp
  have hpΩ : p ∈ closure (f '' U) := closure_mono (image_mono hsU) hp.1
  rw [closure_eq_self_union_frontier] at hpΩ
  rcases hpΩ with hpin | hpfr
  · obtain ⟨w, hw, rfl⟩ := hpin
    rcases hcov hw with (hws | hwt) | hwu
    · exact absurd ⟨mem_image_of_mem f hws, hp⟩
        (eq_empty_iff_forall_notMem.mp hfs.inter_frontier_eq (f w))
    · obtain ⟨q, hqt, hqs⟩ := mem_closure_iff.mp hp.1 _ hft (mem_image_of_mem f hwt)
      exact absurd hqs (disjoint_right.mp hst hqt)
    · exact Or.inl (mem_image_of_mem f hwu)
  · exact Or.inr hpfr

end ImageSplit

section Inside

variable {X : Type*} [TopologicalSpace X] {A V : Set X}

/-- **The frontier of a set meets the closure of a subset exactly where it meets that subset's
frontier.** For any `A ⊆ V`,

> `frontier V ∩ closure A = frontier V ∩ frontier A`.

Writing `closure A` as `A ∪ frontier A`, the first piece brings nothing new: a point of `A` on
`frontier V` is adherent to `A` and is kept out of `interior A` by `interior A ⊆ interior V`, so it
already lies on `frontier A`. Only the inclusion `A ⊆ V` is used — `V` need be neither open nor
closed, and `A` is arbitrary.

So the part of `frontier V` that `A` clings to may be described either as its meeting with
`closure A` or as its meeting with `frontier A`. An argument about limits of points of `A` produces
the first; a diameter estimate obtained by splitting `V` into pieces consumes the second. -/
theorem frontier_inter_closure_eq_frontier_inter_frontier (hAV : A ⊆ V) :
    frontier V ∩ closure A = frontier V ∩ frontier A := by
  rw [closure_eq_self_union_frontier, inter_union_distrib_left]
  refine union_eq_right.mpr fun x hx =>
    ⟨hx.1, (mem_frontier_iff_notMem_interior hx.2).mpr fun hint => ?_⟩
  exact (mem_frontier_iff_notMem_interior (hAV hx.2)).mp hx.1 (interior_mono hAV hint)

end Inside

end TauCeti

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Filling in the bounded complementary components of a set

The **filled hull** `TauCeti.filledHull K` of a subset `K` of a topological space with a bornology
is `K` together with the bounded connected components of its complement: the points whose component
in `Kᶜ` is bounded. Points of `K` qualify vacuously, their component in `Kᶜ` being empty. Filling a
circle gives the closed disc it bounds; filling a segment, or any set whose complement is connected
and unbounded, changes nothing.

This file is the topological layer: the definition and the structural facts, which ask only for a
topology and a bornology, being about components and boundedness and nothing else. That filling
does not make a set wider needs a real normed space and lives in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

The shape in which the structural side is spent is `IsPreconnected.subset_filledHull`: a
preconnected set disjoint from `K` is trapped inside the filled hull as soon as it meets it, since
it then lies in a single bounded component. Together with the width bound of the normed file it
says that *a connected set that a small `K` cuts off from infinity is itself small*, with no
regularity asked of `K`; that composite is `IsPreconnected.diam_le_diam_of_disjoint` there.

The negation of membership — that the component of a point in the complement of `K` is *unbounded*
— already occurs, unfolded, in the winding-number layer: it is the hypothesis of
`TauCeti.Contour.windingNumber_eq_zero_of_unbounded_component` in
`TauCeti/Analysis/Contour/Winding/UnboundedComponent.lean` and of its cycle form
`TauCeti.Contour.Cycle.windingNumber_eq_zero_of_unbounded_component` in
`TauCeti/Analysis/Contour/Cycle/Winding.lean`, both of which say that the winding number vanishes
off the filled hull of the trace. Those statements are left as they stand: they are about the
unbounded side, which needs no name, whereas everything here is about the filled side.

The hull is deliberately *not* claimed to be closed, connected, or idempotent — none of which is
needed downstream, and the first two of which fail without hypotheses on `K`.

## Roadmap role

Plane separation for Jordan curves was the open frontier item of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Carathéodory boundary correspondence. The
enclosure step now runs through `IsPreconnected (K \ {f z₀})` and the winding-number two-sidedness
theorem
(`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton`),
which `IsJordanCurve.isPathConnected_sdiff_singleton` discharges; `Caratheodory.lean` is
unconditional.
The inside of `J` is `filledHull J \ J` in the vocabulary defined here. Nothing here assumes
separation, or any other regularity of `K`.

## Main results

* `TauCeti.filledHull` — the filled hull, and `TauCeti.subset_filledHull`,
  `TauCeti.filledHull_mono` its two structural properties.
* `TauCeti.filledHull_eq_self` — filling a set whose complement is preconnected and unbounded
  changes nothing.
* `IsPreconnected.subset_filledHull` — a preconnected set disjoint from `K` that meets the
  filled hull lies in it.
* `TauCeti.subset_filledHull_of_frontier_subset` — a bounded set whose frontier `K` swallows
  lies in the filled hull, with no connectivity asked of it.
-/

public section

namespace TauCeti

open Bornology Set

variable {E : Type*} [TopologicalSpace E] [Bornology E] {K L S : Set E} {x : E}

/-- The **filled hull** of a set `K`: the points whose connected component in the complement of `K`
is bounded. Equivalently, `K` together with the bounded connected components of `Kᶜ`; a point of
`K` belongs because its component in `Kᶜ` is empty. -/
def filledHull (K : Set E) : Set E := {x | IsBounded (connectedComponentIn Kᶜ x)}

@[simp]
theorem mem_filledHull_iff : x ∈ filledHull K ↔ IsBounded (connectedComponentIn Kᶜ x) := Iff.rfl

/-- **A set lies in its filled hull.** For `x ∈ K` the component of `x` in `Kᶜ` is empty, and the
empty set is bounded. -/
theorem subset_filledHull : K ⊆ filledHull K := by
  intro x hx
  have hxc : x ∉ Kᶜ := by simpa using hx
  simp [mem_filledHull_iff, connectedComponentIn_eq_empty hxc]

/-- **Filling is monotone.** Enlarging `K` shrinks the complement, hence shrinks each component of
it, hence can only turn unbounded components into bounded ones. -/
@[gcongr]
theorem filledHull_mono (h : K ⊆ L) : filledHull K ⊆ filledHull L := fun _ hx =>
  mem_filledHull_iff.mpr <|
    (mem_filledHull_iff.mp hx).subset (connectedComponentIn_mono _ (compl_subset_compl.mpr h))

/-- **Filling changes nothing when the complement is connected and unbounded.** The complement is
then a single component and that component is unbounded, so no point outside `K` is filled in. This
is the case of a segment in the plane, and of any set that does not separate the space. -/
theorem filledHull_eq_self (h : IsPreconnected Kᶜ) (hu : ¬ IsBounded Kᶜ) : filledHull K = K := by
  refine Subset.antisymm (fun x hx => ?_) subset_filledHull
  by_contra hxK
  exact hu ((mem_filledHull_iff.mp hx).subset
    (h.subset_connectedComponentIn (mem_compl hxK) subset_rfl))

/-- **A preconnected set that a set cuts off from infinity lies in its filled hull.** If `S` is
preconnected and disjoint from `K`, then `S` lies in a single connected component of `Kᶜ`; meeting
the filled hull says that component is bounded, so all of `S` is in the hull. -/
theorem _root_.IsPreconnected.subset_filledHull (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) : S ⊆ filledHull K := by
  obtain ⟨x, hxS, hxH⟩ := hne
  have hScompl : S ⊆ Kᶜ := fun y hy => Set.disjoint_left.mp hSK hy
  have hScomp : S ⊆ connectedComponentIn Kᶜ x := hS.subset_connectedComponentIn hxS hScompl
  intro y hy
  rw [mem_filledHull_iff, ← connectedComponentIn_eq (hScomp hy)]
  exact mem_filledHull_iff.mp hxH

/-- **A bounded set whose frontier lies in `K` is cut off from infinity by `K`.** A point of
`S \ K` lies in `interior S`, since every non-interior point of `S` lies on `frontier S ⊆ K`. Its
connected component in `Kᶜ` cannot leave `interior S`: were it to, it would meet
`frontier (interior S) ⊆ frontier S ⊆ K` by `IsPreconnected.inter_frontier_nonempty`,
while lying in `Kᶜ`. So that component is bounded because `S` is. Points of `S ∩ K` lie in the
filled hull directly.

Unlike `IsPreconnected.subset_filledHull` this asks nothing of the connectivity of `S` and
nothing about the hull being met, at the price of asking `K` to swallow the whole frontier — the
same trade as between `TauCeti.diam_le_diam_of_frontier_subset` and
`IsPreconnected.diam_le_diam_of_disjoint`. -/
theorem subset_filledHull_of_frontier_subset (hSb : IsBounded S) (hfr : frontier S ⊆ K) :
    S ⊆ filledHull K := by
  intro x hx
  by_cases hxK : x ∈ K
  · exact subset_filledHull hxK
  have hxKc : x ∈ Kᶜ := hxK
  have hxi : x ∈ interior S := (mem_interior_iff_notMem_frontier hx).2 fun h => hxK (hfr h)
  have hcomp : connectedComponentIn Kᶜ x ⊆ interior S := by
    by_contra h
    obtain ⟨y, hy, hyi⟩ := not_subset.mp h
    obtain ⟨z, hz, hzf⟩ := isPreconnected_connectedComponentIn.inter_frontier_nonempty
      ⟨x, mem_connectedComponentIn hxKc, hxi⟩ ⟨y, hy, hyi⟩
    exact connectedComponentIn_subset _ _ hz (hfr (frontier_interior_subset hzf))
  exact mem_filledHull_iff.mpr (hSb.subset (hcomp.trans interior_subset))

end TauCeti

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- `NormedSpace.toLocallyConvexSpace`, needed to apply `geometric_hahn_banach_point_closed`.

/-!
# The width of a filled hull

The filled hull `TauCeti.filledHull K` — `K` together with the bounded connected components of its
complement — is defined in `TauCeti/Topology/FilledHull.lean`, where it needs only a topology and a
bornology. In a real normed space the one substantial fact is that filling does not make a set
wider:

> `TauCeti.filledHull_subset_closedConvexHull` — `filledHull K ⊆ closedConvexHull ℝ K`,

whence `TauCeti.diam_filledHull`: a set and its filled hull have the same diameter. The
mechanism is separation: a point `x` outside the closed convex hull of `K` is cut off
from it by a continuous linear functional (`geometric_hahn_banach_point_closed`), and the open
half-space `{y | φ y < u}` so produced is a convex — hence preconnected — subset of `Kᶜ` containing
`x`, and it is unbounded (`TauCeti.not_isBounded_halfSpace_lt`). So the component of `x` in `Kᶜ` is
unbounded and `x` is not in the filled hull. Nonemptiness of `K` is needed only to know that
`φ ≠ 0`; for `K = ∅` and a zero-dimensional space the convex-hull statement is false, the hull then
being everything and the convex hull empty. The diameter statements survive that case
unhypothesised, because `filledHull ∅` is empty in a nontrivial space
(`TauCeti.filledHull_empty`) and the single point of the zero space otherwise, of diameter `0`
either way.

Because the width of a filled hull is controlled, so is that of anything inside it, and the shape
in which this is spent is `IsPreconnected.subset_filledHull`: a preconnected set disjoint from `K`
is trapped inside the filled hull as soon as it meets it. Their composite,
`IsPreconnected.diam_le_diam_of_disjoint`, says that *a connected set that a small `K` cuts off
from infinity is itself small*, with no regularity asked of `K`.

## Roadmap role

The filled hull is the vocabulary in which the enclosure step of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` is stated. That step is now unconditional: the
preconnectedness/winding-number route in `TauCeti/Analysis/Complex/Conformal/Crosscut/Inside.lean`
places one image piece of a crosscut in the filled hull without plane separation. In the diameter
bound that follows, `TauCeti/Analysis/Complex/Conformal/Crosscut/SmallJordanCurve.lean` encloses a
short image crosscut in an arbitrarily small Jordan curve `J`, and
`IsPreconnected.diam_le_diam_of_disjoint` makes the cut-off piece no wider than `J`.

This is a different route to a diameter bound from `TauCeti.diam_le_diam_of_frontier_subset` of
`TauCeti/Analysis/Normed/Module/DiamFrontier.lean`, which bounds a set by *any* bounded set
containing its frontier: there the enclosing set must be known to contain the whole frontier, here
only that the set is cut off from infinity. The frontier route is the special case of the enclosure
route obtained from `TauCeti.subset_filledHull_of_frontier_subset`; the enclosure route does not
require the whole frontier to be caught.

## Generality

The width statements are stated for an arbitrary real normed space — nothing about the plane is
used, and the separation argument is the general Hahn–Banach one.

## Main results

* `TauCeti.filledHull_subset_closedConvexHull` — a filled hull lies in the closed convex hull.
* `TauCeti.diam_filledHull` and `TauCeti.isBounded_filledHull` — filling preserves the diameter, and
  a filled hull is bounded exactly when the set filled is.
* `TauCeti.diam_le_diam_of_subset_filledHull` and
  `IsPreconnected.diam_le_diam_of_disjoint` — a set inside the filled hull of a bounded `K`,
  in particular a preconnected set that `K` cuts off from infinity, is no wider than `K`.
* `TauCeti.isBounded_closedConvexHull`,
  `TauCeti.diam_closedConvexHull` — the closed forms of the two convex-hull facts the width
  argument runs on.
* `TauCeti.connectedComponentIn_compl_eq_of_unbounded_component` — the unbounded connected
  component of the complement of a bounded set is unique (dimension at least two).
* `TauCeti.mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn` — of two points in
  different components, at least one lies in the filled hull (dimension at least two).
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K S : Set E}

/-- **A closed convex hull is bounded exactly when the set is.** The closed form of
`isBounded_convexHull`, the closure adding nothing. -/
@[simp]
theorem isBounded_closedConvexHull : IsBounded (closedConvexHull ℝ K) ↔ IsBounded K := by
  rw [closedConvexHull_eq_closure_convexHull, isBounded_closure_iff, isBounded_convexHull]

/-- **Taking the closed convex hull preserves the diameter.** The closed form of `convexHull_diam`,
the closure adding nothing by `Metric.diam_closure`. -/
@[simp]
theorem diam_closedConvexHull : diam (closedConvexHull ℝ K) = diam K := by
  rw [closedConvexHull_eq_closure_convexHull, diam_closure, convexHull_diam]

/-- **The filled hull lies in the closed convex hull.** A point outside the closed convex hull of a
nonempty `K` is separated from it by a continuous linear functional; the open half-space this
produces is convex, avoids `K`, and is unbounded, so the component of the point in `Kᶜ` is
unbounded.

Nonemptiness of `K` is what forces the separating functional to be nonzero, and so the half-space to
be unbounded; without it the statement fails in the zero space, where `filledHull ∅ = univ`. -/
theorem filledHull_subset_closedConvexHull (hK : K.Nonempty) :
    filledHull K ⊆ closedConvexHull ℝ K := by
  intro x hx
  rw [mem_filledHull_iff] at hx
  by_contra hxC
  obtain ⟨φ, u, hφx, hφC⟩ := geometric_hahn_banach_point_closed convex_closedConvexHull
    isClosed_closedConvexHull hxC
  -- The open half-space cut off by `φ` is a preconnected subset of `Kᶜ` containing `x`.
  have hHK : {y | φ y < u} ⊆ Kᶜ :=
    fun y hy hyK => absurd (hφC y (subset_closedConvexHull hyK)) (not_lt.mpr hy.le)
  have hsub : {y | φ y < u} ⊆ connectedComponentIn Kᶜ x :=
    (convex_halfSpace_lt φ.toLinearMap.isLinear u).isPreconnected.subset_connectedComponentIn
      hφx hHK
  -- It is unbounded, because a nonempty `K` forces `φ` to be nonzero.
  obtain ⟨b, hb⟩ := hK
  have hφne : (φ : E →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    have hzero : ∀ y : E, φ y = 0 := fun y =>
      (LinearMap.congr_fun h y).trans (LinearMap.zero_apply y)
    have hb' := hφC b (subset_closedConvexHull hb)
    rw [hzero] at hφx hb'
    linarith
  exact not_isBounded_halfSpace_lt (φ := (φ : E →ₗ[ℝ] ℝ)) hφne u (hx.subset hsub)

/-- **The filled hull of the empty set is empty** in a nontrivial space: the whole space is
connected and unbounded, so every component of `∅ᶜ = univ` is unbounded. -/
@[simp]
theorem filledHull_empty [Nontrivial E] : filledHull (∅ : Set E) = ∅ := by
  apply filledHull_eq_self
  · rw [compl_empty]
    exact isPreconnected_univ
  · rw [compl_empty]
    exact NormedSpace.unbounded_univ ℝ E

/-- The filled hull of the empty set is a subsingleton: empty in a nontrivial space by
`TauCeti.filledHull_empty`, and the whole zero space, a single point, otherwise. Either way it is as
wide as `∅`, which is why the diameter statements below need no nonemptiness hypothesis. -/
private theorem subsingleton_filledHull_empty : (filledHull (∅ : Set E)).Subsingleton := by
  rcases subsingleton_or_nontrivial E with _ | _
  · exact fun a _ b _ => Subsingleton.elim a b
  · rw [filledHull_empty]
    exact subsingleton_empty

/-- **A filled hull is bounded exactly when the set filled is.** One direction is
`TauCeti.subset_filledHull`; the other holds because the hull lies in the closed convex hull. -/
@[simp]
theorem isBounded_filledHull : IsBounded (filledHull K) ↔ IsBounded K := by
  refine ⟨fun h => h.subset subset_filledHull, fun hKb => ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hK
  · exact subsingleton_filledHull_empty.finite.isBounded
  · exact (isBounded_closedConvexHull.mpr hKb).subset (filledHull_subset_closedConvexHull hK)

/-- **Filling preserves the diameter.** The hull contains `K`, and for nonempty `K` it is contained
in the closed convex hull of `K`, which by `TauCeti.diam_closedConvexHull` is exactly as wide as
`K`; `filledHull ∅` is a subsingleton, of diameter `0` like `∅` itself. An unbounded `K` has an
unbounded hull by `TauCeti.isBounded_filledHull`, and both diameters are then `0`. -/
@[simp]
theorem diam_filledHull : diam (filledHull K) = diam K := by
  by_cases hKb : IsBounded K
  · rcases K.eq_empty_or_nonempty with rfl | hK
    · rw [diam_subsingleton subsingleton_filledHull_empty, diam_empty]
    refine le_antisymm ?_ (diam_mono subset_filledHull (isBounded_filledHull.mpr hKb))
    calc diam (filledHull K) ≤ diam (closedConvexHull ℝ K) :=
          diam_mono (filledHull_subset_closedConvexHull hK) (isBounded_closedConvexHull.mpr hKb)
      _ = diam K := diam_closedConvexHull
  · rw [diam_eq_zero_of_unbounded (mt isBounded_filledHull.mp hKb), diam_eq_zero_of_unbounded hKb]

/-- **Anything a bounded `K` cuts off from infinity is no wider than `K`.** A set inside the filled
hull is no wider than the hull by `Metric.diam_mono`, and the hull is no wider than `K` by
`TauCeti.diam_filledHull`. -/
theorem diam_le_diam_of_subset_filledHull (hK : IsBounded K) (h : S ⊆ filledHull K) :
    diam S ≤ diam K :=
  (diam_mono h (isBounded_filledHull.mpr hK)).trans_eq diam_filledHull

/-- **A preconnected set that a bounded `K` cuts off from infinity is no wider than `K`.** If `S` is
preconnected, disjoint from `K`, and meets the filled hull of `K`, then it lies inside that hull by
`IsPreconnected.subset_filledHull`, which is no wider than `K` by
`TauCeti.diam_filledHull`. No regularity is asked of `K`. -/
theorem _root_.IsPreconnected.diam_le_diam_of_disjoint (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) (hK : IsBounded K) : diam S ≤ diam K :=
  diam_le_diam_of_subset_filledHull hK (hS.subset_filledHull hSK hne)

variable {x y : E}

/-- **The unbounded component of the complement of a bounded set is unique** in a real normed space
of dimension at least two. -/
theorem connectedComponentIn_compl_eq_of_unbounded_component (h : 1 < Module.rank ℝ E)
    (hK : IsBounded K) (hx : ¬ IsBounded (connectedComponentIn Kᶜ x))
    (hy : ¬ IsBounded (connectedComponentIn Kᶜ y)) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : E)
  have hext : (closedBall (0 : E) R)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hR
  have hesc : ∀ z : E, ¬ IsBounded (connectedComponentIn Kᶜ z) →
      ∃ z' ∈ connectedComponentIn Kᶜ z, z' ∈ (closedBall (0 : E) R)ᶜ := fun z hz => by
    by_contra hcon
    push Not at hcon
    exact hz ((isBounded_closedBall (x := (0 : E)) (r := R)).subset fun w hw =>
      notMem_compl_iff.mp (hcon w hw))
  obtain ⟨x', hx'c, hx'R⟩ := hesc x hx
  obtain ⟨y', hy'c, hy'R⟩ := hesc y hy
  have h1 : y' ∈ connectedComponentIn Kᶜ x' :=
    (isPreconnected_compl_closedBall h 0 R).subset_connectedComponentIn hx'R hext hy'R
  rw [connectedComponentIn_eq hx'c, connectedComponentIn_eq h1, ← connectedComponentIn_eq hy'c]

/-- **Two points in different components of the complement of a bounded set cannot both lie outside
the filled hull** in a real normed space of dimension at least two. -/
theorem mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn (h : 1 < Module.rank ℝ E)
    (hK : IsBounded K) (hxy : y ∉ connectedComponentIn Kᶜ x) :
    x ∈ filledHull K ∨ y ∈ filledHull K := by
  by_cases hy : y ∈ K
  · exact Or.inr (subset_filledHull hy)
  · by_contra hcon
    push Not at hcon
    simp only [mem_filledHull_iff] at hcon
    exact hxy ((connectedComponentIn_compl_eq_of_unbounded_component h hK hcon.1 hcon.2).symm ▸
      mem_connectedComponentIn (mem_compl hy))

end TauCeti

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Local connectedness of continuous images of compact spaces

Local connectedness is not preserved by continuous images in general — every metric space is a
continuous image of a discrete one — but it *is* preserved by quotient maps, and hence by the
continuous images that are automatically quotient maps: those of a compact space in a Hausdorff
one. This file proves that, in the type-level form and in the set-level form
`TauCeti.locallyConnectedSpace_image_of_isCompact` that a subset of a topological space needs.

The quotient step itself is Mathlib's. `Topology.IsCoinducing.locallyConnectedSpace` states that
a topology coinduced by a locally connected one is locally connected, which reaches quotient maps
through `IsQuotientMap.isCoinducing` and is strictly more general, since coinducing does not ask
for surjectivity. What is added here is the passage from that to a continuous surjection out of a
compact space, which is closed and therefore a quotient map.

The intended consumer is layer **L5** of the conformal-mapping roadmap, Carathéodory's boundary
correspondence: a conformal map that extends continuously to the closure of its domain carries a
locally connected boundary to a locally connected boundary, which is the necessary half of
Carathéodory's continuity theorem. That application is in
`TauCeti/Analysis/Complex/Conformal/LocallyConnectedBoundary.lean`; nothing here is specific to it.

## Main results

* `TauCeti.locallyConnectedSpace_of_continuous_surjective` — the continuous image of a compact
  locally connected space in a Hausdorff space is locally connected.
* `TauCeti.locallyConnectedSpace_image_of_isCompact` — the set-level form: `f '' s` is locally
  connected for a compact, locally connected `s` on which `f` is continuous.

## References

* Mathlib, `Mathlib.Topology.Connected.LocallyConnected`,
  `Topology.IsCoinducing.locallyConnectedSpace`: a topology coinduced by a locally connected
  topology is locally connected. This is the quotient-map result applied below.
-/

public section

namespace TauCeti

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The continuous image of a compact locally connected space in a Hausdorff space is locally
connected.** A continuous surjection out of a compact space onto a Hausdorff one is closed, hence
a quotient map, hence coinducing, so `Topology.IsCoinducing.locallyConnectedSpace` applies. -/
theorem locallyConnectedSpace_of_continuous_surjective [LocallyConnectedSpace X] [CompactSpace X]
    [T2Space Y] {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f) :
    LocallyConnectedSpace Y :=
  (hf.isClosedMap.isQuotientMap hf hsurj).isCoinducing.locallyConnectedSpace

/-- **The set-level form: a compact, locally connected set has locally connected continuous
images.** Stated with the subtype topologies on `s` and on `f '' s`, which is how a boundary or a
closure of a subset of a normed space is met in practice. -/
theorem locallyConnectedSpace_image_of_isCompact [T2Space Y] {s : Set X} {f : X → Y}
    [LocallyConnectedSpace s] (hs : IsCompact s) (hf : ContinuousOn f s) :
    LocallyConnectedSpace (f '' s) := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact locallyConnectedSpace_of_continuous_surjective (hf.mapsToRestrict (mapsTo_image f s))
    (surjective_mapsTo_image_restrict f s)

end TauCeti

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Jordan curves

A **Jordan curve** — a simple closed curve — is a subset of a topological space homeomorphic to
the circle. This file introduces the predicate `TauCeti.IsJordanCurve` and its basic API.

The circle is Mathlib's `Circle`, the unit circle of `ℂ` as a topological group; the notion itself
is purely topological, so `TauCeti.IsJordanCurve` is stated for a subset of an arbitrary
topological space. `ℂ` is mentioned only by the two concrete curves towards the end of the file:
the model curve, a circle `Metric.sphere c r` of positive radius, and the frontier of a bounded
convex set with nonempty interior. The model is built from the complex affine change of coordinates
`w ↦ (w - c) / r`, so it uses the field structure of `ℂ` and not only its metric, and the convex
frontier is obtained from the model by transport.

Phrasing the predicate as *the set is homeomorphic to the circle*, rather than *the set is the
range of a continuous map on `[0, 1]` that is injective except for matching endpoints*, is what
makes it usable: over a Hausdorff ambient space the two agree, because there a continuous injection
out of a compact space is an embedding, but the parametrized form buries that argument in every
use. Passing from a parametrization to the predicate is `TauCeti.IsJordanCurve.image`, which turns
a continuous injective map defined on a set already known to be a Jordan curve — a circle in `ℂ`,
say — into a proof that its image is one; `TauCeti.IsJordanCurve.of_image` runs the other way,
transporting the property back to a compact set from an image already known to be a Jordan curve.

## Main definitions

* `TauCeti.IsJordanCurve` — a set homeomorphic to the circle.
* `TauCeti.jordanParam` — the parametrization of a Jordan curve by the circle underlying a
  homeomorphism of the curve with `Circle`.

## Main results

* `TauCeti.IsJordanCurve.isCompact`, `TauCeti.IsJordanCurve.isPathConnected`,
  `TauCeti.IsJordanCurve.nonempty` and `TauCeti.IsJordanCurve.not_subsingleton` — a Jordan curve is
  a nonempty compact path-connected set with more than one point.
* `TauCeti.IsJordanCurve.image` and `TauCeti.IsJordanCurve.of_image` — being a Jordan curve
  transfers in both directions along a map that is continuous and injective on the set, provided
  the codomain is Hausdorff (and, in the direction that transports the property back from the
  image, the source set is known to be compact).
* `TauCeti.IsJordanCurve.image_homeomorph` and `TauCeti.isJordanCurve_image_homeomorph_iff` — being
  a Jordan curve is invariant under a homeomorphism of the ambient spaces; no separation axiom is
  needed.
* `TauCeti.continuous_jordanParam`, `TauCeti.jordanParam_injective`,
  `TauCeti.isInducing_jordanParam`, `TauCeti.range_jordanParam`, `TauCeti.jordanParam_apply` and
  `TauCeti.jordanParam_apply_apply` — the parametrization of a Jordan curve by the circle is a
  continuous injection, is inducing, traces out exactly the curve, and undoes `e`; this is what
  carries a statement about the circle to one about an arbitrary Jordan curve.
* `TauCeti.sphereCircleHomeomorph` and `TauCeti.isJordanCurve_sphere` — a circle of positive radius
  in `ℂ` is a Jordan curve, by the affine change of coordinates `w ↦ (w - c) / r`.
* `TauCeti.isJordanCurve_frontier_of_convex` — the frontier of a bounded convex subset of `ℂ` with
  nonempty interior is a Jordan curve. This is `TauCeti.isJordanCurve_sphere` with the disc
  weakened to an arbitrary convex body, the affine change of coordinates being replaced by Mathlib's
  gauge rescaling.
* `TauCeti.locallyConnectedSpace_sphere` and `TauCeti.IsJordanCurve.locallyConnectedSpace` — a
  circle in `ℂ`, and hence every Jordan curve, is locally connected.

## Motivation

This is the vocabulary layer **L5** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`) is stated in: its milestone, the Carathéodory
boundary correspondence, is about the Riemann map of a *Jordan domain*, and the roadmap records
that the pinned Mathlib has no Jordan-curve vocabulary to state it against. The complex-analytic
half — Jordan domains, the discs among them, and the boundary of a domain that a conformal map
carries onto a disc — is in `TauCeti/Analysis/Complex/Conformal/Jordan/Domain.lean`.

Local connectedness of a Jordan curve is what that milestone needs of the *hypothesis* side: the
route to the extension theorem for a Jordan domain `Ω` runs through Carathéodory's continuity
theorem, whose hypothesis is that `frontier Ω` be locally connected, and
`TauCeti.IsJordanCurve.locallyConnectedSpace` is what discharges it (as
`TauCeti.IsJordanDomain.locallyConnectedSpace_frontier`). Mathlib knows the circle is compact,
connected and path connected, but records no local connectedness for it, and the property is not
preserved by continuous images, so it is proved here from
`TauCeti.locallyConnectedSpace_image_of_isCompact`.

## References

* C. Jordan, *Cours d'analyse de l'École Polytechnique*, vol. 3 (1887).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {C : Set X} {p : X} {r : ℝ}

/-- A **Jordan curve**, or simple closed curve, in a topological space: a subset homeomorphic to
the circle.

The predicate is `Nonempty (C ≃ₜ Circle)` rather than a chosen homeomorphism, so that it is a
`Prop`; `TauCeti.isJordanCurve_iff` recovers the homeomorphism from another module, where the
definition itself is not exposed. -/
def IsJordanCurve (C : Set X) : Prop := Nonempty (C ≃ₜ Circle)

/-- A set is a Jordan curve exactly when it is homeomorphic to the circle. This is the interface
to `TauCeti.IsJordanCurve` outside its defining module. -/
theorem isJordanCurve_iff : IsJordanCurve C ↔ Nonempty (C ≃ₜ Circle) := Iff.rfl

/-- A continuous injection defined on a compact set is a homeomorphism onto its image, the image
carrying the subspace topology of a Hausdorff space. This is the set-level form of
`Continuous.homeoOfEquivCompactToT2`, and the engine of both transfer lemmas below. -/
private noncomputable def imageHomeomorphOfIsCompact [T2Space Y] (hC : IsCompact C) {g : X → Y}
    (hg : ContinuousOn g C) (hgi : InjOn g C) : C ≃ₜ g '' C :=
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  Continuous.homeoOfEquivCompactToT2 (f := hgi.bijOn_image.equiv g)
    (hg.mapsToRestrict hgi.bijOn_image.mapsTo)

/-- A Jordan curve is compact: the circle is. -/
theorem IsJordanCurve.isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨e⟩ := h
  exact isCompact_iff_compactSpace.mpr e.symm.compactSpace

/-- A Jordan curve in a Hausdorff space is closed. -/
theorem IsJordanCurve.isClosed [T2Space X] (h : IsJordanCurve C) : IsClosed C :=
  h.isCompact.isClosed

/-- A Jordan curve is path connected: the circle is. -/
theorem IsJordanCurve.isPathConnected (h : IsJordanCurve C) : IsPathConnected C := by
  obtain ⟨e⟩ := h
  exact isPathConnected_iff_pathConnectedSpace.mpr
    (e.symm.surjective.pathConnectedSpace e.symm.continuous)

/-- A Jordan curve is connected. -/
theorem IsJordanCurve.isConnected (h : IsJordanCurve C) : IsConnected C :=
  h.isPathConnected.isConnected

/-- A Jordan curve is nonempty. -/
theorem IsJordanCurve.nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

/-- A Jordan curve has more than one point: the circle contains both `1` and `-1`. Together with
`TauCeti.IsJordanCurve.isConnected` this rules out the degenerate curves, so a Jordan curve is a
nondegenerate continuum. -/
theorem IsJordanCurve.not_subsingleton (h : IsJordanCurve C) : ¬ C.Subsingleton := by
  obtain ⟨e⟩ := h
  intro hsub
  exact Circle.neg_ne_self 1
    (e.symm.injective (Subtype.ext (hsub (e.symm (-1)).2 (e.symm 1).2)))

/-- **A Jordan curve is carried to a Jordan curve by a continuous injection.** Only continuity and
injectivity *on the curve* are needed, the curve supplying the compactness that upgrades them to a
homeomorphism onto the image. -/
theorem IsJordanCurve.image [T2Space Y] (h : IsJordanCurve C) {g : X → Y} (hg : ContinuousOn g C)
    (hgi : InjOn g C) : IsJordanCurve (g '' C) := by
  have hC := h.isCompact
  obtain ⟨e⟩ := h
  exact ⟨(imageHomeomorphOfIsCompact hC hg hgi).symm.trans e⟩

/-- **A compact set carried onto a Jordan curve by a continuous injection is a Jordan curve.**
This is the converse of `TauCeti.IsJordanCurve.image`; compactness of the source has to be assumed
here, since it is no longer inherited from the curve. It is the form in which the predicate is
verified when the curve is the *unknown* rather than the parameter: one exhibits a continuous
injective map of the set onto a set already known to be a Jordan curve, as the boundary
correspondence does with the boundary of a disc. -/
theorem IsJordanCurve.of_image [T2Space Y] (hC : IsCompact C) {g : X → Y} (hg : ContinuousOn g C)
    (hgi : InjOn g C) (h : IsJordanCurve (g '' C)) : IsJordanCurve C := by
  obtain ⟨e⟩ := h
  exact ⟨(imageHomeomorphOfIsCompact hC hg hgi).trans e⟩

/-- The image of a Jordan curve under a homeomorphism of the ambient spaces is a Jordan curve.
Unlike `TauCeti.IsJordanCurve.image` this needs no separation axiom on the codomain, because
`Homeomorph.image` supplies the homeomorphism onto the image outright. -/
theorem IsJordanCurve.image_homeomorph (h : IsJordanCurve C) (e : X ≃ₜ Y) :
    IsJordanCurve (e '' C) := by
  obtain ⟨f⟩ := h
  exact ⟨(e.image C).symm.trans f⟩

/-- Being a Jordan curve is invariant under a homeomorphism of the ambient spaces. This is the
characteristic form of `TauCeti.IsJordanCurve.image_homeomorph`: the backward direction is that
lemma applied to `e.symm`, which no consumer then has to spell out. -/
@[simp]
theorem isJordanCurve_image_homeomorph_iff (e : X ≃ₜ Y) :
    IsJordanCurve (e '' C) ↔ IsJordanCurve C :=
  ⟨fun h => e.symm_image_image C ▸ h.image_homeomorph e.symm, fun h => h.image_homeomorph e⟩

/-! ## The parametrization by the circle

Every transport of a statement about `Circle` to a Jordan curve goes through the parametrization
`jordanParam e` attached to a homeomorphism `e`, so its properties — continuity, injectivity,
range, and that it is inducing — are collected here rather than rebuilt at each use, both by the
cutting of a curve at one or two of its points
(`TauCeti/Topology/JordanCurve/Separation.lean`) and by the quantitative form of that cutting
(`TauCeti/Topology/JordanCurve/SmallArc.lean`). -/

/-- The parametrization of a Jordan curve by the circle underlying a homeomorphism `e`: the
composite of `e.symm` with the inclusion of the curve into the ambient space. -/
noncomputable def jordanParam (e : C ≃ₜ Circle) : Circle → X :=
  fun u => ((e.symm u : C) : X)

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle is continuous. -/
lemma continuous_jordanParam (e : C ≃ₜ Circle) : Continuous (jordanParam e) :=
  continuous_subtype_val.comp e.symm.continuous

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle is injective: this is
the simplicity of the curve. -/
lemma jordanParam_injective (e : C ≃ₜ Circle) : Function.Injective (jordanParam e) :=
  Subtype.val_injective.comp e.symm.injective

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle is inducing, so
preconnectedness of a subset of the curve may be tested on its preimage of parameters. -/
lemma isInducing_jordanParam (e : C ≃ₜ Circle) : Topology.IsInducing (jordanParam e) :=
  Topology.IsInducing.subtypeVal.comp e.symm.isInducing

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle traces out exactly the
curve. -/
@[simp]
lemma range_jordanParam (e : C ≃ₜ Circle) : range (jordanParam e) = C := by
  refine subset_antisymm ?_ fun x hx => ⟨e ⟨x, hx⟩, by simp [jordanParam]⟩
  rintro _ ⟨u, rfl⟩
  exact (e.symm u).2

/-- The defining equation of `TauCeti.jordanParam`: the parameter `u` names the point `e.symm u` of
the curve, read in the ambient space. This is the general application lemma, so a consumer never has
to unfold the definition. -/
@[simp]
lemma jordanParam_apply (e : C ≃ₜ Circle) (u : Circle) :
    jordanParam e u = ((e.symm u : C) : X) := by
  simp [jordanParam]

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle undoes `e`: it sends
the parameter `e ⟨p, hp⟩` of a point `p` of the curve back to `p`. Simp proves this from
`TauCeti.jordanParam_apply`; it is stated for the `rw` steps that produce the point `p` itself
rather than a coerced parameter. -/
lemma jordanParam_apply_apply (e : C ≃ₜ Circle) (hp : p ∈ C) :
    jordanParam e (e ⟨p, hp⟩) = p := by
  simp

/-! ## The model curve: a circle in `ℂ` -/

/-- `Circle` is *by definition* the unit sphere of `ℂ`, but it is a `def` rather than an
abbreviation, so its topology is only definitionally the subtype topology. This identification is
the one place where that unfolding happens; the lemmas below then compute with the unit sphere
alone. -/
noncomputable def unitSphereCircleHomeomorph : sphere (0 : ℂ) 1 ≃ₜ Circle :=
  Homeomorph.refl _

private lemma coe_unitSphereCircleHomeomorph (z : sphere (0 : ℂ) 1) :
    (unitSphereCircleHomeomorph z : ℂ) = (z : ℂ) := rfl

private lemma coe_unitSphereCircleHomeomorph_symm (z : Circle) :
    ((unitSphereCircleHomeomorph.symm z : sphere (0 : ℂ) 1) : ℂ) = (z : ℂ) := rfl

/-- The affine parametrization `w ↦ (w - c) / r` of a circle of centre `c` and positive radius `r`
in `ℂ` by the unit circle. It is the restriction to the spheres of the inverse of Mathlib's ambient
`affineHomeomorph r c`, so only the membership equivalence is proved here. -/
noncomputable def sphereCircleHomeomorph (c : ℂ) (hr : 0 < r) : sphere c r ≃ₜ Circle :=
  haveI hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  (((affineHomeomorph (r : ℂ) c hr0).symm).subtype fun w => by
      rw [affineHomeomorph_symm_apply]
      simp [mem_sphere_iff_norm, abs_of_pos hr, div_eq_one_iff_eq, hr.ne']).trans
    unitSphereCircleHomeomorph

/-- The parametrization of `sphere c r` by the unit circle divides out the affine change of
coordinates. -/
@[simp]
lemma coe_sphereCircleHomeomorph_apply (c : ℂ) (hr : 0 < r) (w : sphere c r) :
    (sphereCircleHomeomorph c hr w : ℂ) = ((w : ℂ) - c) / r := by
  simp [sphereCircleHomeomorph, coe_unitSphereCircleHomeomorph]

/-- The inverse parametrization of `sphere c r` by the unit circle is the affine change of
coordinates. -/
@[simp]
lemma coe_sphereCircleHomeomorph_symm_apply (c : ℂ) (hr : 0 < r) (z : Circle) :
    (((sphereCircleHomeomorph c hr).symm z : sphere c r) : ℂ) = c + r * (z : ℂ) := by
  simp [sphereCircleHomeomorph, coe_unitSphereCircleHomeomorph_symm, add_comm]

/-- A circle of positive radius in `ℂ` is a Jordan curve. -/
theorem isJordanCurve_sphere (c : ℂ) (hr : 0 < r) : IsJordanCurve (sphere c r) :=
  isJordanCurve_iff.mpr ⟨sphereCircleHomeomorph c hr⟩

/-- **The frontier of a bounded convex subset of `ℂ` with nonempty interior is a Jordan curve.**

This is `TauCeti.isJordanCurve_sphere` with the disc weakened to an arbitrary convex body, which it
recovers at `s = Metric.ball c r`. The model curve transports because Mathlib's gauge rescaling
supplies an *ambient* homeomorphism `e : ℂ ≃ₜ ℂ` carrying `frontier s` onto the unit circle
(`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`), so the affine change of
coordinates above is simply replaced by a nonlinear one and no further topology is needed.

The set is asked neither to be open nor to be nonempty: what a convex set needs in order to have a
one-dimensional frontier is that it be *solid*, and that is `(interior s).Nonempty`. Without it the
statement fails — a segment is convex and bounded, and is its own frontier. -/
theorem isJordanCurve_frontier_of_convex {s : Set ℂ} (hs : Convex ℝ s)
    (hne : (interior s).Nonempty) (hb : Bornology.IsBounded s) : IsJordanCurve (frontier s) := by
  obtain ⟨e, -, -, hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hs hne hb
  refine (isJordanCurve_image_homeomorph_iff e).mp ?_
  rw [hfr]
  exact isJordanCurve_sphere 0 one_pos

/-! ## Local connectedness -/

open Complex in
/-- **A circle in `ℂ` is locally connected.** It is the image of the compact interval `[-π, π]`,
which is convex and hence locally connected, under the continuous `θ ↦ c + r * exp (θ * I)`, so
`TauCeti.locallyConnectedSpace_image_of_isCompact` applies. A sphere of negative radius is empty,
and vacuously locally connected. -/
instance locallyConnectedSpace_sphere (c : ℂ) (r : ℝ) : LocallyConnectedSpace (sphere c r) := by
  rcases lt_or_ge r 0 with hr | hr
  · have hempty : sphere c r = (∅ : Set ℂ) := by
      ext z
      simp only [mem_sphere_iff_norm, mem_empty_iff_false, iff_false]
      intro h
      have : (0 : ℝ) ≤ r := h ▸ norm_nonneg (z - c)
      linarith
    rw [hempty]
    exact ⟨fun x => absurd x.2 (notMem_empty _)⟩
  · have hparam :
        sphere c r = (fun θ : ℝ => c + r * exp (θ * I)) '' Icc (-Real.pi) Real.pi := by
      ext z
      simp only [mem_sphere_iff_norm, mem_image, mem_Icc]
      constructor
      · intro hz
        refine ⟨arg (z - c), ⟨(neg_pi_lt_arg (z - c)).le, arg_le_pi (z - c)⟩, ?_⟩
        rw [← hz, norm_mul_exp_arg_mul_I (z - c)]
        ring
      · rintro ⟨θ, -, rfl⟩
        simp [abs_of_nonneg hr]
    have := (convex_Icc (-Real.pi) Real.pi).locallyPathConnectedSpace
    rw [hparam]
    exact locallyConnectedSpace_image_of_isCompact isCompact_Icc
      (Continuous.continuousOn (by fun_prop))

/-- **The circle is locally connected.** `Circle` is the unit circle of `ℂ`, so this is the unit
case of `TauCeti.locallyConnectedSpace_sphere` transported along `TauCeti.sphereCircleHomeomorph`.
Mathlib records the circle as compact, connected and path connected, but not as locally
connected. -/
instance locallyConnectedSpace_circle : LocallyConnectedSpace Circle :=
  (sphereCircleHomeomorph (0 : ℂ) one_pos).symm.locallyConnectedSpace

/-- **A Jordan curve is locally connected**, being homeomorphic to the circle.

This is the form in which the hypothesis of Carathéodory's continuity theorem — that the boundary
of the domain be locally connected — is met by a Jordan domain, which is what layer **L5** of the
conformal-mapping roadmap is about; see `TauCeti.IsJordanDomain.locallyConnectedSpace_frontier`. -/
theorem IsJordanCurve.locallyConnectedSpace (h : IsJordanCurve C) : LocallyConnectedSpace C :=
  (isJordanCurve_iff.mp h).elim fun e => e.locallyConnectedSpace

end TauCeti

end

end

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Jordan curves traced by paths

A path whose two endpoints agree is a parametrised closed curve, but its range need not be a
Jordan curve: the path may pause, retrace an arc, or cross itself. This file supplies the exact
criterion needed to exclude those degeneracies. If a closed path has no repeated values except
for its two endpoint parameters, its range is a Jordan curve
(`TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints`).

The proof uses the quotient model of the circle already in Mathlib. The extension of a path
`γ : Path x x` to `ℝ` has equal values at `0` and `1`, so
`AddCircle.liftIco 1 0 γ.extend` factors it through the additive circle `ℝ / ℤ`. The hypothesis on
repetitions says precisely that this factor is injective, and its range is the range of `γ`. The
additive circle is itself a Jordan curve, `AddCircle.homeomorphCircle` identifying it with
`Circle`, so `TauCeti.IsJordanCurve.image` carries that along the factor: the compactness argument
upgrading a continuous injection to a homeomorphism onto its image is already packaged there and is
not repeated here.

The condition is stated directly rather than bundled as a new notion of simple closed path. This
is the only operation needed here, and keeping it as a theorem hypothesis avoids introducing a
second simplicity vocabulary alongside Mathlib's path API.

## Gluing two arcs

The criterion has one immediate use that is worth naming on its own: two *arcs* — ranges of
injective paths — that share their two endpoints and meet nowhere else glue to a Jordan curve
(`TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair`). The closed path traversed is
`γ.trans δ.symm`, whose range is `range γ ∪ range δ`; the meeting hypothesis is what turns a
coincidence between a value of `γ` and a value of `δ` into a coincidence of endpoints, and
injectivity of each of the two paths handles the coincidences internal to one of them. The
endpoints are not asked to be distinct: injectivity of `δ` already forces that, since a path with
equal endpoints repeats the value at the two distinct parameters `0` and `1`.

## Main results

* `TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints` — the range of a closed path whose only
  possible repetition is its pair of endpoints is a Jordan curve.
* `TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair` — two arcs with the same two
  endpoints, meeting exactly there, glue to a Jordan curve.

## Roadmap role

This is the topological gluing step used by layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Carathéodory boundary correspondence. A
finite-length image crosscut is already packaged as a path with exactly this simplicity property in
`TauCeti/Analysis/Complex/Conformal/Crosscut/Path.lean`; when its two boundary ends coincide, the
first result below identifies the closure of that crosscut as a Jordan curve, and when they are
distinct the second closes that crosscut up with an arc of the boundary of the image domain. The
coincident-end specialization is in `TauCeti/Analysis/Complex/Conformal/Crosscut/Jordan.lean` and
the distinct-end one in `TauCeti/Analysis/Complex/Conformal/Crosscut/Arc.lean`.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] {x : X}

omit [T2Space X] in
/-- **A simple closed path lifts injectively to the circle.** If equality `γ s = γ t` forces `s = t`
or the unordered pair of parameters to be `{0, 1}`, then `AddCircle.liftIco 1 0 γ.extend` is
injective. -/
private theorem liftIco_extend_injective (γ : Path x x)
    (hγ : ∀ ⦃s t : unitInterval⦄, γ s = γ t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    Function.Injective (AddCircle.liftIco 1 0 γ.extend) := by
  intro q q' hqq'
  -- representatives in `[0, 1)` cannot form the exceptional endpoint pair
  obtain ⟨s, hs, rfl⟩ := AddCircle.eq_coe_Ico q
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico q'
  rw [(AddCircle.liftIco_zero_coe_apply hs).trans (γ.extend_extends' ⟨s, hs.1, hs.2.le⟩),
    (AddCircle.liftIco_zero_coe_apply ht).trans (γ.extend_extends' ⟨t, ht.1, ht.2.le⟩)] at hqq'
  rcases hγ hqq' with hst | hends | hends
  · exact congrArg (fun u : unitInterval => ((u : ℝ) : AddCircle (1 : ℝ))) hst
  · exact absurd (congrArg ((↑) : unitInterval → ℝ) hends.2) ht.2.ne
  · exact absurd (congrArg ((↑) : unitInterval → ℝ) hends.1) hs.2.ne

/-- **The range of a simple closed path is a Jordan curve.** Let `γ : Path x x` be a closed path.
If equality `γ s = γ t` forces either `s = t` or the unordered pair of parameters to be `{0, 1}`,
then `range γ` is homeomorphic to the circle.

The disjunction records both orientations of the exceptional endpoint pair explicitly. No local
injectivity or embedding hypothesis is needed, and no separation assumption on the ambient space
beyond the Hausdorffness that `TauCeti.IsJordanCurve.image` asks for. -/
theorem isJordanCurve_range_of_eq_or_eq_endpoints (γ : Path x x)
    (hγ : ∀ ⦃s t : unitInterval⦄, γ s = γ t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    IsJordanCurve (range γ) := by
  -- Factor the extended path through `[0, 1]` with its endpoints identified; the additive circle
  -- is a Jordan curve, and the factor carries it onto the range of `γ`.
  have hg0 : γ.extend 0 = γ.extend 1 := by rw [γ.extend_zero, γ.extend_one]
  have hgc : Continuous (AddCircle.liftIco 1 0 γ.extend) :=
    AddCircle.liftIco_zero_continuous hg0 γ.continuous_extend.continuousOn
  have huniv : IsJordanCurve (univ : Set (AddCircle (1 : ℝ))) :=
    isJordanCurve_iff.mpr
      ⟨(Homeomorph.Set.univ (AddCircle (1 : ℝ))).trans (AddCircle.homeomorphCircle one_ne_zero)⟩
  have himage := huniv.image hgc.continuousOn (liftIco_extend_injective γ hγ).injOn
  -- present the lift as a quotient map off `[0, 1]` and read its range through the quotient
  rwa [image_univ, AddCircle.liftIco_eq_lift_Icc (by simp), (Equiv.surjective _).range_comp,
    Set.range_quot_lift, Set.range_domRestrict, γ.image_extend_of_subset (by norm_num)] at himage

/-! ### Gluing two arcs along their endpoints -/

omit [T2Space X] in
/-- **A value shared by two arcs with the same endpoints is attained at a shared parameter.** If
the ranges of `γ δ : Path x y` meet exactly in `{x, y}`, then `γ a = δ b` forces both parameters to
be `0` or both to be `1`.

The shared value lies in `range γ ∩ range δ = {x, y}`, and injectivity of each path identifies the
parameter at which it takes the endpoint value. -/
private theorem eq_zero_and_eq_zero_or_eq_one_and_eq_one_of_apply_eq {y : X} {γ δ : Path x y}
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hmeet : range γ ∩ range δ = {x, y}) {a b : unitInterval} (hab : γ a = δ b) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  have hmem : γ a ∈ ({x, y} : Set X) :=
    hmeet ▸ ⟨mem_range_self a, hab ▸ mem_range_self b⟩
  rcases hmem with h | h
  · exact Or.inl ⟨hγ (h.trans γ.source.symm), hδ (hab.symm.trans (h.trans δ.source.symm))⟩
  · exact Or.inr ⟨hγ (h.trans γ.target.symm), hδ (hab.symm.trans (h.trans δ.target.symm))⟩

/-- **Two arcs meeting exactly at their common endpoints glue to a Jordan curve.** Let
`γ δ : Path x y` be injective and let their ranges meet in exactly the two endpoints,
`range γ ∩ range δ = {x, y}`. Then `range γ ∪ range δ` is a Jordan curve.

The curve traversed is `γ.trans δ.symm`, a closed path at `x` whose range is `range γ ∪ range δ`
by `Path.trans_range` and `Path.symm_range`. Its only repetitions are the ones
`TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints` allows: a coincidence between two parameters on
the same half is excluded by injectivity of that half, and one between the two halves lands in
`{x, y}`, so it is either the pair `{0, 1}` of endpoint parameters or the single parameter `1 / 2`
at which the two halves are joined.

Distinctness of `x` and `y` is a consequence rather than a hypothesis: `δ 0 = δ 1` would contradict
injectivity of `δ`. -/
theorem isJordanCurve_range_union_range_of_inter_eq_pair {y : X} {γ δ : Path x y}
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hmeet : range γ ∩ range δ = {x, y}) :
    IsJordanCurve (range γ ∪ range δ) := by
  have hrange : range (γ.trans δ.symm) = range γ ∪ range δ := by
    rw [Path.trans_range, Path.symm_range]
  rw [← hrange]
  refine isJordanCurve_range_of_eq_or_eq_endpoints _ fun s t hst => ?_
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · -- Both parameters on the first half: injectivity of `γ`.
    have h : (2 : ℝ) * s = 2 * t := congrArg Subtype.val (hγ hst)
    exact Or.inl (Subtype.ext (show (s : ℝ) = (t : ℝ) by linarith))
  · -- The first parameter on `γ`, the second on `δ` read backwards.
    simp only [Path.symm_apply, Function.comp_apply] at hst
    rcases eq_zero_and_eq_zero_or_eq_one_and_eq_one_of_apply_eq hγ hδ hmeet hst with ⟨ha, hb⟩ | h
    · have h1 : (2 : ℝ) * s = 0 := congrArg Subtype.val ha
      have h2 : 1 - (2 * (t : ℝ) - 1) = 0 := congrArg Subtype.val hb
      exact Or.inr (Or.inl ⟨Subtype.ext (show (s : ℝ) = 0 by linarith),
        Subtype.ext (show (t : ℝ) = 1 by linarith)⟩)
    · have h1 : (2 : ℝ) * s = 1 := congrArg Subtype.val h.1
      have h2 : 1 - (2 * (t : ℝ) - 1) = 1 := congrArg Subtype.val h.2
      exact Or.inl (Subtype.ext (show (s : ℝ) = (t : ℝ) by linarith))
  · -- The mirror image of the previous case.
    simp only [Path.symm_apply, Function.comp_apply] at hst
    rcases eq_zero_and_eq_zero_or_eq_one_and_eq_one_of_apply_eq hγ hδ hmeet hst.symm with
      ⟨ha, hb⟩ | h
    · have h1 : (2 : ℝ) * t = 0 := congrArg Subtype.val ha
      have h2 : 1 - (2 * (s : ℝ) - 1) = 0 := congrArg Subtype.val hb
      exact Or.inr (Or.inr ⟨Subtype.ext (show (s : ℝ) = 1 by linarith),
        Subtype.ext (show (t : ℝ) = 0 by linarith)⟩)
    · have h1 : (2 : ℝ) * t = 1 := congrArg Subtype.val h.1
      have h2 : 1 - (2 * (s : ℝ) - 1) = 1 := congrArg Subtype.val h.2
      exact Or.inl (Subtype.ext (show (s : ℝ) = (t : ℝ) by linarith))
  · -- Both parameters on the second half: injectivity of `δ` read backwards.
    simp only [Path.symm_apply, Function.comp_apply] at hst
    have h : 1 - (2 * (s : ℝ) - 1) = 1 - (2 * (t : ℝ) - 1) := congrArg Subtype.val (hδ hst)
    exact Or.inl (Subtype.ext (show (s : ℝ) = (t : ℝ) by linarith))

end TauCeti

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Curve.Foundations.Development002`.
* `Curve.Foundations.Development003`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Curve.Jordan.Separation`.
* `Curve.Jordan.Interior`.
* `Curve.Jordan.OrientationTransport`.
* `Curve.Jordan.AreaTransport`.
* `Curve.Jordan.ClosedArea`.
* `Curve.Jordan.SignedArea`.
* `Curve.Jordan.SupportingOrientation`.
* `Curve.Jordan.Subarc`.
* `Curve.Reparametrization`.
* `Curve.SegmentAreaProperties`.
* `Curve.Jordan.SubarcArea`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Separation
-/

public section

namespace MovingSofa

private theorem IsJordanCurve.exists_sphere_parametrization {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) :
    ∃ r : Metric.sphere (0 : Point) 1 → Point,
      Continuous r ∧ Function.Injective r ∧ Set.range r = Γ := by
  obtain ⟨f, hf, hfi, hfr⟩ := hΓ
  let e := Complex.orthonormalBasisOneI.repr.symm
  let φ : Metric.sphere (0 : Point) 1 → Circle := fun p ↦
    ⟨e p.val, mem_sphere_zero_iff_norm.mpr (by
      rw [e.norm_map]
      exact mem_sphere_zero_iff_norm.mp p.property)⟩
  have hφc : Continuous φ := (e.continuous.comp continuous_subtype_val).subtype_mk _
  have hφi : Function.Injective φ := by
    intro p q h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  have hφs : Function.Surjective φ := by
    intro z
    refine ⟨⟨e.symm z.val, mem_sphere_zero_iff_norm.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [e.symm.norm_map]
      exact Circle.norm_coe z
    · exact e.apply_symm_apply z.val
  refine ⟨f ∘ φ, hf.comp hφc, hfi.comp hφi, ?_⟩
  rw [Set.range_comp, hφs.range_eq, Set.image_univ, hfr]

theorem jordan_separation {Γ : Set Point} (hΓ : IsJordanCurve Γ) :
    ∃ U V : Set Point,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Bornology.IsBounded U ∧ ¬Bornology.IsBounded V ∧
      Disjoint U V ∧ U ∪ V = Γᶜ ∧ frontier U = Γ ∧ frontier V = Γ ∧
      (∀ p ∈ U, connectedComponentIn Γᶜ p = U) ∧
      (∀ p ∈ V, connectedComponentIn Γᶜ p = V) := by
  obtain ⟨r, hr, hri, hrΓ⟩ := hΓ.exists_sphere_parametrization
  rw [← hrΓ]
  obtain ⟨u, hu, hub⟩ := JordanCurve.step_A_exists_bounded JordanCurve.Brouwer.brouwerFPT hr hri
  obtain ⟨v, hv, hvu⟩ := JordanCurve.exists_unbounded_component r hr
  let U := connectedComponentIn (Set.range r)ᶜ u
  let V := connectedComponentIn (Set.range r)ᶜ v
  have hne : U ≠ V := by
    intro h
    change connectedComponentIn (Set.range r)ᶜ u = connectedComponentIn (Set.range r)ᶜ v at h
    exact hvu (h ▸ hub)
  have hdis : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro p hpU hpV
    exact hne ((connectedComponentIn_eq hpU).trans (connectedComponentIn_eq hpV).symm)
  have hcover : U ∪ V = (Set.range r)ᶜ := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
    · intro p hp
      by_cases hpb : Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ p)
      · left
        have h := JordanCurve.step_B_bounded_unique JordanCurve.Brouwer.brouwerFPT hr hri
          p hp u hu hpb hub
        simpa only [U, ← h] using mem_connectedComponentIn hp
      · right
        have h := JordanCurve.unbounded_component_unique r hr hpb hvu
        simpa only [V, ← h] using mem_connectedComponentIn hp
  refine ⟨U, V, JordanCurve.isOpen_component r hr u, JordanCurve.isOpen_component r hr v,
    isConnected_connectedComponentIn_iff.mpr hu, isConnected_connectedComponentIn_iff.mpr hv,
    hub, hvu, hdis, hcover, ?_, ?_, ?_, ?_⟩
  · exact JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT hr hri hu
      ⟨v, hv, hne.symm⟩
  · exact JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT hr hri hv
      ⟨u, hu, hne⟩
  · intro p hp
    exact (connectedComponentIn_eq hp).symm
  · intro p hp
    exact (connectedComponentIn_eq hp).symm

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Interior
-/

public section

namespace MovingSofa

/-- A Jordan curve has a point in its bounded complementary component. -/
theorem IsJordanCurve.jordanInterior_nonempty {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) : (jordanInterior Γ).Nonempty := by
  obtain ⟨U, V, _, _, hU, _, hUb, _, _, hcover, _, _, hcomp, _⟩ :=
    jordan_separation hΓ
  obtain ⟨p, hp⟩ := hU.nonempty
  refine ⟨p, ?_, ?_⟩
  · have : p ∈ Γᶜ := hcover ▸ Set.mem_union_left V hp
    exact this
  · rw [hcomp p hp]
    exact hUb

/-- The frontier of the bounded complementary component of a Jordan curve is the curve
itself. -/
theorem IsJordanCurve.frontier_jordanInterior {Γ : Set Point} (hΓ : IsJordanCurve Γ) :
    frontier (jordanInterior Γ) = Γ := by
  obtain ⟨U, V, -, -, -, -, hUbdd, hVunbdd, -, hcover, hfrontU, -, hUcomp, hVcomp⟩ :=
    jordan_separation hΓ
  have hUeq : jordanInterior Γ = U := by
    ext p
    simp only [jordanInterior, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpΓ, hpb⟩
      rcases hcover.symm.subset hpΓ with h | h
      · exact h
      · rw [hVcomp p h] at hpb
        exact absurd hpb hVunbdd
    · intro hpU
      refine ⟨?_, ?_⟩
      · have hmem : p ∈ Γᶜ := by rw [← hcover]; exact Or.inl hpU
        exact hmem
      · rw [hUcomp p hpU]
        exact hUbdd
  rw [hUeq]
  exact hfrontU

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Orientation Transport
-/

public section

noncomputable section
namespace MovingSofa

/-- Endpoint-preserving continuous parameter changes preserve Jordan orientation. -/
theorem IsOrientedJordanParametrization.orientation_eq_of_comp
    {a b c d : ℝ} {hab : a ≤ b} {hcd : c ≤ d} {Γ : Set Point}
    {ccw₁ ccw₂ : Bool} {x : Set.Icc a b → Point} {y : Set.Icc c d → Point}
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y)
    (φ : Set.Icc c d → Set.Icc a b) (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩)
    (hxy : y = x ∘ φ) : ccw₂ = ccw₁ := by
  obtain ⟨p, hp⟩ := hx.2.1.jordanInterior_nonempty
  have hxw := hx.2.2.2.2.2.2 p hp
  have hyw := hy.2.2.2.2.2.2 p hp
  have hn : curveWinding hab x p ≠ 0 := by
    rw [hxw]
    cases ccw₁ <;> norm_num
  have hw := curveWinding_comp_of_endpoints hab hcd
    (exists_curveAngleLift_of_curveWinding_ne_zero hab hn) hφ hφa hφb
  rw [← hxy, hxw, hyw] at hw
  cases ccw₁ <;> cases ccw₂ <;> first | rfl | norm_num at hw

/-- Exchanging the parameter endpoints reverses Jordan orientation. -/
theorem IsOrientedJordanParametrization.orientation_eq_not_of_comp
    {a b c d : ℝ} {hab : a ≤ b} {hcd : c ≤ d} {Γ : Set Point}
    {ccw₁ ccw₂ : Bool} {x : Set.Icc a b → Point} {y : Set.Icc c d → Point}
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y)
    (φ : Set.Icc c d → Set.Icc a b) (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩)
    (hxy : y = x ∘ φ) : ccw₂ = !ccw₁ := by
  obtain ⟨p, hp⟩ := hx.2.1.jordanInterior_nonempty
  have hxw := hx.2.2.2.2.2.2 p hp
  have hyw := hy.2.2.2.2.2.2 p hp
  have hn : curveWinding hab x p ≠ 0 := by
    rw [hxw]
    cases ccw₁ <;> norm_num
  have hw := curveWinding_comp_of_reversed_endpoints hab hcd
    (exists_curveAngleLift_of_curveWinding_ne_zero hab hn) hφ hφa hφb
  rw [← hxy, hxw, hyw] at hw
  cases ccw₁ <;> cases ccw₂ <;> first | rfl | norm_num at hw

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Area Transport
-/

public section

namespace MovingSofa

/-- A monotone or antitone transition between oriented Jordan paths determines their
signed areas. -/
theorem curveArea_eq_of_oriented_reparametrization
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {Γ : Set Point} {ccw₁ ccw₂ : Bool}
    (x : ContinuousBVPaths a b) (y : ContinuousBVPaths c d)
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x.val)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y.val)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφs : Function.Surjective φ) (hφ : Monotone φ ∨ Antitone φ)
    (hcomp : y.val = x.val ∘ φ) :
    (ccw₁ = ccw₂ → curveAreaFunctional x = curveAreaFunctional y) ∧
    (ccw₁ ≠ ccw₂ → curveAreaFunctional x = -curveAreaFunctional y) := by
  obtain ⟨z, hz, hmarea, haarea⟩ :=
    curveArea_comp_monotone_or_antitone_surjective hab hcd x φ hφc hφs hφ
  have hzy : z = y := Subtype.ext (hz.trans hcomp.symm)
  subst z
  obtain ⟨u, hu⟩ := hφs ⟨a, le_rfl, hab⟩
  obtain ⟨v, hv⟩ := hφs ⟨b, hab, le_rfl⟩
  rcases hφ with hm | ha
  · have hleft : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ := by
      apply le_antisymm
      · simpa only [hu] using
          hm (show (⟨c, le_rfl, hcd⟩ : Set.Icc c d) ≤ u from u.property.1)
      · exact (φ ⟨c, le_rfl, hcd⟩).property.1
    have hright : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ := by
      apply le_antisymm
      · exact (φ ⟨d, hcd, le_rfl⟩).property.2
      · simpa only [hv] using
          hm (show v ≤ (⟨d, hcd, le_rfl⟩ : Set.Icc c d) from v.property.2)
    have horient := hx.orientation_eq_of_comp hy φ hφc hleft hright hcomp
    exact ⟨fun _ ↦ (hmarea hm).symm, fun hn ↦ (hn horient.symm).elim⟩
  · have hleft : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩ := by
      apply le_antisymm
      · exact (φ ⟨c, le_rfl, hcd⟩).property.2
      · simpa only [hv] using
          ha (show (⟨c, le_rfl, hcd⟩ : Set.Icc c d) ≤ v from v.property.1)
    have hright : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩ := by
      apply le_antisymm
      · simpa only [hu] using
          ha (show u ≤ (⟨d, hcd, le_rfl⟩ : Set.Icc c d) from u.property.2)
      · exact (φ ⟨d, hcd, le_rfl⟩).property.1
    have horient := hx.orientation_eq_not_of_comp hy φ hφc hleft hright hcomp
    constructor
    · intro heq
      have hf : ccw₁ = !ccw₁ := heq.trans horient
      cases ccw₁ <;> contradiction
    · intro _
      have heq := haarea ha
      linarith

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Closed Area
-/

public section

noncomputable section

namespace MovingSofa

/-- Same-carrier closed Jordan parametrizations have signed areas determined by orientation. -/
theorem curveArea_closed_same_carrier (Γ Δ : OrientedJordanCurve)
    (x : ClosedBVParametrization Γ) (y : ClosedBVParametrization Δ)
    (hcarrier : Γ.carrier = Δ.carrier) :
    (Γ.counterclockwise = Δ.counterclockwise →
      curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
    (Γ.counterclockwise ≠ Δ.counterclockwise →
      curveAreaFunctional x.path = -curveAreaFunctional y.path) := by
  have hy : IsOrientedJordanParametrization y.ordered Γ.carrier Δ.counterclockwise y.path.val := by
    rw [hcarrier]
    exact y.oriented
  have hcompare (z : ClosedBVParametrization Γ)
      (hstart : z.path.val ⟨z.a, le_rfl, z.ordered⟩ =
        y.path.val ⟨y.a, le_rfl, y.ordered⟩) :
      (Γ.counterclockwise = Δ.counterclockwise →
        curveAreaFunctional z.path = curveAreaFunctional y.path) ∧
      (Γ.counterclockwise ≠ Δ.counterclockwise →
        curveAreaFunctional z.path = -curveAreaFunctional y.path) := by
    obtain ⟨φ, hφc, hφs, hφo, hcomp⟩ :=
      z.exists_reparametrization_of_start_eq y hcarrier hstart
    exact curveArea_eq_of_oriented_reparametrization z.ordered y.ordered z.path y.path
      z.oriented hy φ hφc hφs hφo hcomp
  by_cases hstart : x.path.val ⟨x.a, le_rfl, x.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩
  · exact hcompare x hstart
  have hmem : y.path.val ⟨y.a, le_rfl, y.ordered⟩ ∈ Set.range x.path.val := by
    rw [x.oriented.2.2.2.1, hcarrier, ← y.oriented.2.2.2.1]
    exact Set.mem_range_self _
  obtain ⟨s, hsb, hs⟩ := exists_param_lt_top_of_mem_range x.oriented.1 x.path.val
    x.oriented.2.2.2.2.1 hmem
  have has : x.a < (s : ℝ) := by
    apply lt_of_le_of_ne s.property.1
    intro heq
    have hsa : s = ⟨x.a, le_rfl, x.ordered⟩ := Subtype.ext heq.symm
    apply hstart
    simpa only [hsa] using hs
  obtain ⟨r, hr, hrstart, hrarea⟩ :=
    exists_oriented_cyclic_rotation x.ordered x.path x.oriented s has hsb
  let z : ClosedBVParametrization Γ :=
    { a := 0, b := 2, ordered := by norm_num, path := r, oriented := hr }
  have hzstart : z.path.val ⟨z.a, le_rfl, z.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩ := hrstart.trans hs
  simpa only [show z.path = r from rfl, hrarea] using hcompare z hzstart

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Signed Area
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem windingKernel_disk_integral (R : ℝ) (hR : 0 < R) (z : Point) (hz : ‖z‖ < R) :
    Integrable (windingKernel z) (volume.restrict (Metric.ball 0 R)) ∧
    (∀ i : Fin 2, Integrable (fun p ↦ windingKernel z p i)
      (volume.restrict (Metric.ball 0 R))) ∧
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤ 4 * Real.pi * R ∧
    (∫ p in Metric.ball 0 R, windingKernel z p) = Real.pi • z := by
  have hInt := integrableOn_windingKernel_ball R z hz
  exact ⟨hInt, fun i ↦ by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hInt,
    setIntegral_norm_windingKernel_ball_le R hR z hz,
    setIntegral_windingKernel_ball R z hz⟩

theorem jordanBV_winding_integral (a b : ℝ) (hab : a < b) (x : ContinuousBVPaths a b)
    (hclosed : x.val ⟨a, le_rfl, hab.le⟩ = x.val ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x.val {t | (t : ℝ) < b}) :
    volume (Set.range x.val) = 0 ∧
    (∀ p ∉ Set.range x.val,
      (∀ i : Fin 2, Continuous (fun t ↦ windingKernel (x.val t) p i) ∧
        ∃ C : ℝ, ∀ t, |windingKernel (x.val t) p i| ≤ C) ∧
      2 * Real.pi * curveWinding hab.le x.val p =
        intervalStieltjesIntegral (continuousBVCoordinate x 1)
          (fun t ↦ windingKernel (x.val t) p 0) Set.univ -
        intervalStieltjesIntegral (continuousBVCoordinate x 0)
          (fun t ↦ windingKernel (x.val t) p 1) Set.univ) ∧
    (∀ p ∉ Set.range x.val, ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, q ∉ Set.range x.val ∧
        curveWinding hab.le x.val q = curveWinding hab.le x.val p) ∧
    (∀ p ∉ Set.range x.val,
      ¬Bornology.IsBounded (connectedComponentIn (Set.range x.val)ᶜ p) →
      curveWinding hab.le x.val p = 0) := by
  refine ⟨x.volume_range_eq_zero_of_injOn hab.le hinj, ?_, ?_, ?_⟩
  · intro p hp
    refine ⟨fun i ↦ windingKernel_coord_continuous_bounded x.property.1 hp i, ?_⟩
    obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids hab x.property.1 hp
    have hnormpos : ∀ t, 0 < ‖x.val t - p‖ := by
      intro t
      rw [norm_pos_iff, sub_ne_zero]
      intro h
      exact hp ⟨t, h⟩
    have : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
      ((x.property.1.sub continuous_const).norm).continuousOn
    set m : ℝ := ‖x.val t₀ - p‖ with hmdef
    have hmpos : 0 < m := hnormpos t₀
    have hmle : ∀ t, m ≤ ‖x.val t - p‖ := fun t ↦ ht₀ (Set.mem_univ t)
    obtain ⟨δ₀, hδ₀, hmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous x.property.1) (m / 2) (by linarith)
    have hclose : ∀ t u : Set.Icc a b, |(u : ℝ) - (t : ℝ)| < δ₀ →
        ‖x.val u - x.val t‖ < m / 2 := by
      intro t u hlt
      have hd : dist u t < δ₀ := by
        rw [Subtype.dist_eq, Real.dist_eq]; exact hlt
      simpa only [dist_eq_norm] using hmod hd
    set D : Point → Fin 2 → ℝ := fun z ↦ ![windingKernel z p 1, windingKernel z p 0] with hDdef
    have hD0 : ∀ z, D z 0 = windingKernel z p 1 := fun z ↦ rfl
    have hD1 : ∀ z, D z 1 = windingKernel z p 0 := fun z ↦ rfl
    have hDcont : ∀ i, Continuous (fun t ↦ D (x.val t) i) := by
      intro i
      fin_cases i
      · change Continuous (fun t ↦ D (x.val t) 0)
        simpa only [hD0] using (windingKernel_coord_continuous_bounded x.property.1 hp 1).1
      · change Continuous (fun t ↦ D (x.val t) 1)
        simpa only [hD1] using (windingKernel_coord_continuous_bounded x.property.1 hp 0).1
    have hcoordsub : ∀ (v w : Point) (i : Fin 2), (v - w) i = v i - w i := by
      intro v w i; simp
    have hkey : ∀ t u : Set.Icc a b, (t : ℝ) ≤ (u : ℝ) → (u : ℝ) - (t : ℝ) < δ₀ →
        |θ u - θ t -
          (D (x.val t) 1 * (x.val u 1 - x.val t 1) -
            D (x.val t) 0 * (x.val u 0 - x.val t 0))| ≤
          6 / m ^ 2 * ‖x.val u - x.val t‖ ^ 2 := by
      intro t u htu hlt
      have hnwpos : 0 < ‖x.val t - p‖ := hnormpos t
      have hnw2 : ‖x.val t - p‖ ^ 2 = (x.val t - p) 0 ^ 2 + (x.val t - p) 1 ^ 2 :=
        Point.norm_sq_eq _
      have hnd2 : ‖x.val u - x.val t‖ ^ 2 =
          (x.val u - x.val t) 0 ^ 2 + (x.val u - x.val t) 1 ^ 2 := Point.norm_sq_eq _
      have hndlt : ‖x.val u - x.val t‖ < m / 2 :=
        hclose t u (by rw [abs_of_nonneg (by linarith)]; exact hlt)
      have hsmall : 2 * ‖x.val u - x.val t‖ ≤ ‖x.val t - p‖ := by
        have := hmle t; linarith
      have hposdot : ∀ s : Set.Icc a b, (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (u : ℝ) →
          0 < (x.val t - p) 0 * (x.val s - p) 0 + (x.val t - p) 1 * (x.val s - p) 1 := by
        intro s hts hsu
        have hds : ‖x.val s - x.val t‖ < m / 2 :=
          hclose t s (by rw [abs_of_nonneg (by linarith)]; linarith)
        have hdot := Point.abs_inner_coords_le (x.val t - p) (x.val s - x.val t)
        have he0 : (x.val s - p) 0 = (x.val t - p) 0 + (x.val s - x.val t) 0 := by
          rw [hcoordsub, hcoordsub, hcoordsub]; ring
        have he1 : (x.val s - p) 1 = (x.val t - p) 1 + (x.val s - x.val t) 1 := by
          rw [hcoordsub, hcoordsub, hcoordsub]; ring
        rw [he0, he1]
        have hmt := hmle t
        have hnn := norm_nonneg (x.val s - x.val t)
        nlinarith [abs_le.mp hdot, hnw2]
      have hangle := hθ.sub_eq_arctan_of_dot_pos x.property.1 htu hposdot
      have hest := Real.abs_arctan_div_sub_le_of_small (w0 := (x.val t - p) 0)
        (w1 := (x.val t - p) 1) (d0 := (x.val u - x.val t) 0)
        (d1 := (x.val u - x.val t) 1) (nw := ‖x.val t - p‖)
        (nd := ‖x.val u - x.val t‖) hnwpos hnw2 (norm_nonneg _) hnd2 hsmall
      have he0 : (x.val u - p) 0 = (x.val t - p) 0 + (x.val u - x.val t) 0 := by
        rw [hcoordsub, hcoordsub, hcoordsub]; ring
      have he1 : (x.val u - p) 1 = (x.val t - p) 1 + (x.val u - x.val t) 1 := by
        rw [hcoordsub, hcoordsub, hcoordsub]; ring
      have harg :
          ((x.val t - p) 0 * (x.val u - x.val t) 1 -
              (x.val t - p) 1 * (x.val u - x.val t) 0) /
            (‖x.val t - p‖ ^ 2 +
              ((x.val t - p) 0 * (x.val u - x.val t) 0 +
                (x.val t - p) 1 * (x.val u - x.val t) 1)) =
          ((x.val t - p) 0 * (x.val u - p) 1 - (x.val t - p) 1 * (x.val u - p) 0) /
            ((x.val t - p) 0 * (x.val u - p) 0 + (x.val t - p) 1 * (x.val u - p) 1) := by
        have hquot : ∀ A B C E : ℝ,
            (A * E - B * C) / (A ^ 2 + B ^ 2 + (A * C + B * E)) =
              (A * (B + E) - B * (A + C)) / (A * (A + C) + B * (B + E)) := by
          intro A B C E
          congr 1 <;> ring
        rw [hnw2, he0, he1]
        exact hquot _ _ _ _
      rw [harg, ← hangle] at hest
      have hlin : D (x.val t) 1 * (x.val u 1 - x.val t 1) -
          D (x.val t) 0 * (x.val u 0 - x.val t 0) =
          ((x.val t - p) 0 * (x.val u - x.val t) 1 -
            (x.val t - p) 1 * (x.val u - x.val t) 0) / ‖x.val t - p‖ ^ 2 := by
        have hne : ‖x.val t - p‖ ≠ 0 := ne_of_gt hnwpos
        rw [hD0, hD1]
        simp only [windingKernel, PiLp.smul_apply, smul_eq_mul, hcoordsub]
        field_simp
      rw [hlin]
      refine hest.trans ?_
      have hmsq : m ^ 2 ≤ ‖x.val t - p‖ ^ 2 := by
        have := hmle t; nlinarith
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hmsq
    have hchain := ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder
      hab.le x x.boundedVariationOn θ D hDcont (by positivity) hδ₀ hkey
    simp only [hD0, hD1] at hchain
    rw [hθ.curveWinding_eq hab.le, ← hchain]
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    field_simp
  · intro p hp
    exact curveWinding_locally_constant_on_compl_range hab.le x.property.1 hclosed hp
  · intro p hp hub
    exact curveWinding_eq_zero_of_unbounded_component hab.le x.property.1 hclosed hp hub

/-- Joint measurability of the winding kernel along a continuous path. -/
private theorem measurable_windingKernel_prod {a b : ℝ} (x : ContinuousBVPaths a b) :
    Measurable fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1 := by
  have h1 : Measurable fun q : Point × Set.Icc a b ↦ x.val q.2 - q.1 :=
    (x.property.1.measurable.comp measurable_snd).sub measurable_fst
  have h2 : Measurable fun q : Point × Set.Icc a b ↦
      (‖x.val q.2 - q.1‖ ^ 2)⁻¹ • (x.val q.2 - q.1) :=
    Measurable.smul ((h1.norm.pow_const 2).inv) h1
  exact h2

/-- The winding kernel of a path is product-integrable against area on an enclosing disk
and any finite measure in the time variable. -/
private theorem integrable_windingKernel_prod {a b : ℝ} (x : ContinuousBVPaths a b)
    {R : ℝ} (hR : 0 < R) (hxR : ∀ t, ‖x.val t‖ < R)
    (ν : Measure (Set.Icc a b)) [IsFiniteMeasure ν] :
    Integrable (fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1)
      ((volume.restrict (Metric.ball (0 : Point) R)).prod ν) := by
  have hfinball : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Point) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmeas := measurable_windingKernel_prod x
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbound : ∀ t : Set.Icc a b,
      (∫⁻ p, ‖windingKernel (x.val t) p‖ₑ ∂(volume.restrict (Metric.ball (0 : Point) R)))
        ≤ ENNReal.ofReal (4 * Real.pi * R) := by
    intro t
    obtain ⟨hint, -, hnorm, -⟩ := windingKernel_disk_integral R hR (x.val t) (hxR t)
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
    exact ENNReal.ofReal_le_ofReal hnorm
  rw [HasFiniteIntegral, lintegral_prod_symm _ hmeas.enorm.aemeasurable]
  calc
    (∫⁻ t, ∫⁻ p, ‖windingKernel (x.val t) p‖ₑ
        ∂(volume.restrict (Metric.ball (0 : Point) R)) ∂ν)
        ≤ ∫⁻ _, ENNReal.ofReal (4 * Real.pi * R) ∂ν := lintegral_mono hbound
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Set.univ)

/-- Fubini exchange between the coordinate Stieltjes measure of a continuous BV path and
planar area on an enclosing disk, evaluated through the disk mean of the winding kernel. -/
private theorem setIntegral_ball_stieltjes_windingKernel {a b : ℝ} (x : ContinuousBVPaths a b)
    {R : ℝ} (hR : 0 < R) (hxR : ∀ t, ‖x.val t‖ < R) (i j : Fin 2) :
    Integrable (fun p ↦ intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ windingKernel (x.val t) p i) Set.univ)
      (volume.restrict (Metric.ball (0 : Point) R)) ∧
    (∫ p in Metric.ball (0 : Point) R, intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ windingKernel (x.val t) p i) Set.univ) =
      Real.pi * intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ x.val t i) Set.univ := by
  have hfinball : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Point) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfinvar : IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure
      (continuousBVCoordinate x j).boundedVariation
  have hfinmu : IsFiniteMeasure
      ((volume.restrict (Metric.ball (0 : Point) R)).toSignedMeasure).variation := by
    rw [Measure.variation_toSignedMeasure]
    infer_instance
  simp only [intervalStieltjesIntegral_univ]
  have hprodK : Integrable (fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1 i)
      ((volume.restrict (Metric.ball (0 : Point) R)).prod
        (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation) := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp
      (integrable_windingKernel_prod x hR hxR
        (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation)
  have hintI : Integrable (fun p ↦ VectorMeasure.integral
      (intervalStieltjesMeasure (continuousBVCoordinate x j))
      (fun t ↦ windingKernel (x.val t) p i) (ContinuousLinearMap.mul ℝ ℝ))
      (volume.restrict (Metric.ball (0 : Point) R)) := by
    have hh := Integrable.integral_vectorMeasure_prod_left
      (B := ContinuousLinearMap.mul ℝ ℝ) hprodK
    simpa using hh
  refine ⟨hintI, ?_⟩
  have hinner : ∀ t : Set.Icc a b,
      (∫ p in Metric.ball (0 : Point) R, windingKernel (x.val t) p i) =
        Real.pi * x.val t i := by
    intro t
    obtain ⟨hint, -, -, heq⟩ := windingKernel_disk_integral R hR (x.val t) (hxR t)
    have hc := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hint
    rw [heq] at hc
    simpa using hc
  have hfub := VectorMeasure.integral_integral_swap
    (μ := (volume.restrict (Metric.ball (0 : Point) R)).toSignedMeasure)
    (ν := intervalStieltjesMeasure (continuousBVCoordinate x j))
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (C := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (A := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (D := ContinuousLinearMap.mul ℝ ℝ)
    (f := fun (p : Point) (t : Set.Icc a b) ↦ windingKernel (x.val t) p i)
    (by rw [Measure.variation_toSignedMeasure]; exact hprodK)
    (by intro u v w; simp; ring)
  simp only [VectorMeasure.integral_toSignedMeasure] at hfub
  rw [hfub]
  simp only [hinner]
  simpa [smul_eq_mul] using VectorMeasure.integral_fun_smul
    (μ := intervalStieltjesMeasure (continuousBVCoordinate x j))
    (B := ContinuousLinearMap.mul ℝ ℝ) Real.pi (fun t ↦ x.val t i)

theorem curveArea_eq_jordanInterior_area (a b : ℝ) (hab : a ≤ b)
    (Γ : Set Point) (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ true x.val) :
    curveAreaFunctional x = ClassicalResults.area (jordanInterior Γ) := by
  obtain ⟨hlt, hΓ, hcont, hrange, hclosed, hinj, hwind⟩ := hx
  subst hrange
  obtain ⟨U, V, hUopen, -, -, -, hUbdd, hVunbdd, -, hcover, -, -, hUcomp, hVcomp⟩ :=
    jordan_separation hΓ
  obtain ⟨hnull, hwindint, -, hext⟩ := jordanBV_winding_integral a b hlt x hclosed hinj
  have hUeq : jordanInterior (Set.range x.val) = U := by
    ext p
    simp only [jordanInterior, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpΓ, hpb⟩
      have hpc : p ∈ U ∪ V := by rw [hcover]; exact hpΓ
      rcases hpc with h | h
      · exact h
      · rw [hVcomp p h] at hpb
        exact absurd hpb hVunbdd
    · intro hpU
      refine ⟨?_, ?_⟩
      · have hmem : p ∈ (Set.range x.val)ᶜ := by rw [← hcover]; exact Or.inl hpU
        exact hmem
      · rw [hUcomp p hpU]
        exact hUbdd
  obtain ⟨R, hR, hxR, hUR⟩ :
      ∃ R : ℝ, 0 < R ∧ (∀ t, ‖x.val t‖ < R) ∧ U ⊆ Metric.ball (0 : Point) R := by
    have hcpt : IsCompact (Set.range x.val) := isCompact_range hcont
    obtain ⟨r, hr⟩ := (hcpt.isBounded.union hUbdd).subset_closedBall (0 : Point)
    refine ⟨max r 0 + 1, by have := le_max_right r 0; linarith, ?_, ?_⟩
    · intro t
      have h1 : x.val t ∈ Metric.closedBall (0 : Point) r :=
        hr (Set.mem_union_left _ ⟨t, rfl⟩)
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      have := le_max_left r 0
      linarith
    · intro p hp
      have h1 : p ∈ Metric.closedBall (0 : Point) r := hr (Set.mem_union_right _ hp)
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      rw [Metric.mem_ball, dist_zero_right]
      have := le_max_left r 0
      linarith
  have hae : ∀ᵐ p ∂(volume : Measure Point), p ∉ Set.range x.val :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  -- winding equals the indicator of the bounded component off the curve
  have hwind_eq : ∀ p ∉ Set.range x.val,
      curveWinding hab x.val p = U.indicator (fun _ ↦ (1 : ℝ)) p := by
    intro p hp
    by_cases hpU : p ∈ U
    · rw [Set.indicator_of_mem hpU]
      have hw := hwind p (by rw [hUeq]; exact hpU)
      simpa using hw
    · rw [Set.indicator_of_notMem hpU]
      have hpV : p ∈ V := by
        have hpc : p ∈ U ∪ V := by rw [hcover]; exact hp
        rcases hpc with h | h
        · exact absurd h hpU
        · exact h
      refine hext p hp ?_
      rw [hVcomp p hpV]
      exact hVunbdd
  have hArea : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
      ClassicalResults.area (jordanInterior (Set.range x.val)) := by
    have h1 : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
        ∫ p in Metric.ball (0 : Point) R, U.indicator (fun _ ↦ (1 : ℝ)) p := by
      refine setIntegral_congr_ae measurableSet_ball ?_
      filter_upwards [hae] with p hp _
      exact hwind_eq p hp
    rw [h1, setIntegral_indicator hUopen.measurableSet,
      Set.inter_eq_self_of_subset_right hUR, setIntegral_const, hUeq]
    simp [ClassicalResults.area, measureReal_def]
  have hFunctional : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
      curveAreaFunctional x := by
    obtain ⟨hint01, heq01⟩ := setIntegral_ball_stieltjes_windingKernel x hR hxR 0 1
    obtain ⟨hint10, heq10⟩ := setIntegral_ball_stieltjes_windingKernel x hR hxR 1 0
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hL : (∫ p in Metric.ball (0 : Point) R, 2 * Real.pi * curveWinding hab x.val p) =
        2 * Real.pi * ∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p :=
      integral_const_mul _ _
    have hcong : (∫ p in Metric.ball (0 : Point) R, 2 * Real.pi * curveWinding hab x.val p)
        = ∫ p in Metric.ball (0 : Point) R,
            (intervalStieltjesIntegral (continuousBVCoordinate x 1)
              (fun t ↦ windingKernel (x.val t) p 0) Set.univ -
             intervalStieltjesIntegral (continuousBVCoordinate x 0)
              (fun t ↦ windingKernel (x.val t) p 1) Set.univ) := by
      refine setIntegral_congr_ae measurableSet_ball ?_
      filter_upwards [hae] with p hp _
      exact (hwindint p hp).2
    rw [hcong, integral_sub hint01 hint10, heq01, heq10] at hL
    refine mul_left_cancel₀ (ne_of_gt hpi) ?_
    rw [← hL, curveAreaFunctional]
    ring
  rw [← hFunctional, hArea]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Supporting Orientation
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

private lemma pointComplex_re_me89eded (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).re =
    v 0 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma pointComplex_im_me89eded (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).im =
    v 1 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma conj_pointComplex_mul_re_me89eded (v w : Point) :
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w).re = inner ℝ v w := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply, inner, Fin.sum_univ_two]
  ring

private theorem continuous_arg_comp_of_re_nonneg {A : Type*} [TopologicalSpace A]
    {z : A → ℂ} (hz : Continuous z) (hre : ∀ u, 0 ≤ (z u).re) (hne : ∀ u, z u ≠ 0) :
    Continuous (fun u ↦ Complex.arg (z u)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hmem : z u ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    constructor
    · intro harg
      have hneg := (Complex.arg_eq_pi_iff.mp harg).1
      linarith [hre u]
    · exact hne u
  exact (Complex.continuousAt_arg hmem).comp_of_eq hz.continuousAt rfl

private def frameComplex (t : Real.Angle) (v : Point) : ℂ :=
  inner ℝ v (normalVector t) + inner ℝ v (tangentVector t) * Complex.I

@[simp] private theorem frameComplex_re (t : Real.Angle) (v : Point) :
    (frameComplex t v).re = inner ℝ v (normalVector t) := by
  simp [frameComplex]

@[simp] private theorem frameComplex_im (t : Real.Angle) (v : Point) :
    (frameComplex t v).im = inner ℝ v (tangentVector t) := by
  simp [frameComplex]

private theorem norm_frameComplex (t : Real.Angle) (v : Point) :
    ‖frameComplex t v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [frameComplex, Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.norm_sq_eq,
    normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring_nf
  linear_combination (v 0 ^ 2 + v 1 ^ 2) * t.cos_sq_add_sin_sq

private theorem conj_pointComplex_mul_eq_conj_frameComplex_mul (t : Real.Angle)
    (v w : Point) :
    starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w =
      starRingEnd ℂ (frameComplex t v) * frameComplex t w := by
  apply Complex.ext <;>
    simp [Complex.orthonormalBasisOneI_repr_symm_apply, frameComplex, normalVector, tangentVector,
        frame,
      PiLp.inner_apply, Fin.sum_univ_two] <;> ring_nf
  · linear_combination -(v 0 * w 0 + v 1 * w 1) * t.cos_sq_add_sin_sq
  · linear_combination -(v 0 * w 1 - v 1 * w 0) * t.cos_sq_add_sin_sq

private theorem frameComplex_ne_zero {t : Real.Angle} {v : Point} (hv : v ≠ 0) :
    frameComplex t v ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_frameComplex, norm_ne_zero_iff]
  exact hv

private theorem normalized_frameComplex_arg (t : Real.Angle) (v : Point) (hv : v ≠ 0) :
    Real.cos (t.toReal + Complex.arg (frameComplex t v)) = v 0 / ‖v‖ ∧
      Real.sin (t.toReal + Complex.arg (frameComplex t v)) = v 1 / ‖v‖ := by
  have hf := frameComplex_ne_zero (t := t) hv
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg hf, Complex.sin_arg,
    norm_frameComplex]
  simp [frameComplex, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two]
  constructor
  · field_simp
    ring_nf
    linear_combination (v 0) * t.cos_sq_add_sin_sq
  · field_simp
    ring_nf
    linear_combination (v 1) * t.cos_sq_add_sin_sq

/-- The frame argument gives an angle lift when a path lies on the nonnegative side of a normal
through its basepoint. -/
private theorem isCurveAngleLift_frameArg_of_inner_nonneg {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} (t : Real.Angle)
    (hx : Continuous x) (hre : ∀ u, 0 ≤ inner ℝ (x u - p) (normalVector t))
    (hne : ∀ u, x u ≠ p) :
    IsCurveAngleLift x p
      (fun u ↦ t.toReal + Complex.arg (frameComplex t (x u - p))) := by
  have hz : Continuous (fun u ↦ frameComplex t (x u - p)) := by
    unfold frameComplex
    fun_prop
  have hzne (u) : frameComplex t (x u - p) ≠ 0 :=
    frameComplex_ne_zero (sub_ne_zero.mpr (hne u))
  refine ⟨continuous_const.add (continuous_arg_comp_of_re_nonneg hz
    (fun u ↦ by simpa using hre u) hzne),
    fun u ↦ ?_⟩
  exact normalized_frameComplex_arg t (x u - p) (sub_ne_zero.mpr (hne u))

/-- Negating frame coordinates and adding `π` gives the corresponding lift on the nonpositive
side of a normal through the basepoint. -/
private theorem isCurveAngleLift_frameArg_neg_add_pi_of_inner_nonpos {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} (t : Real.Angle)
    (hx : Continuous x) (hre : ∀ u, inner ℝ (x u - p) (normalVector t) ≤ 0)
    (hne : ∀ u, x u ≠ p) :
    IsCurveAngleLift x p (fun u ↦
      t.toReal + Complex.arg (-frameComplex t (x u - p)) + Real.pi) := by
  have hz : Continuous (fun u ↦ -frameComplex t (x u - p)) := by
    unfold frameComplex
    fun_prop
  have hzne (u) : frameComplex t (x u - p) ≠ 0 :=
    frameComplex_ne_zero (sub_ne_zero.mpr (hne u))
  have harg : Continuous (fun u ↦ Complex.arg (-frameComplex t (x u - p))) :=
    continuous_arg_comp_of_re_nonneg hz (by
      intro u
      simpa using neg_nonneg.mpr (hre u)) (fun u ↦ neg_ne_zero.mpr (hzne u))
  refine ⟨(continuous_const.add harg).add continuous_const, fun u ↦ ?_⟩
  have hbase := normalized_frameComplex_arg t (x u - p) (sub_ne_zero.mpr (hne u))
  have hneg :
      Real.cos (Complex.arg (-frameComplex t (x u - p)) + Real.pi) =
          (frameComplex t (x u - p)).re / ‖frameComplex t (x u - p)‖ ∧
        Real.sin (Complex.arg (-frameComplex t (x u - p)) + Real.pi) =
          (frameComplex t (x u - p)).im / ‖frameComplex t (x u - p)‖ := by
    rw [Real.cos_add_pi, Real.sin_add_pi,
      Complex.cos_arg (neg_ne_zero.mpr (hzne u)), Complex.sin_arg, norm_neg]
    simp only [Complex.neg_re, Complex.neg_im, neg_div, neg_neg]
    exact ⟨trivial, trivial⟩
  dsimp only
  rw [add_assoc, Real.cos_add t.toReal, Real.sin_add t.toReal, hneg.1, hneg.2,
    norm_frameComplex]
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg (hzne u), Complex.sin_arg,
    norm_frameComplex] at hbase
  exact hbase

private def cyclicComplement {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → Point)
    (s t : Set.Icc a b) : Set.Icc (0 : ℝ) 2 → Point :=
  Function.concatUnitIntervals
    (x ∘ Set.Icc.convexComb t ⟨b, hab, le_rfl⟩)
    (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)

private theorem continuous_cyclicComplement {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s t : Set.Icc a b) : Continuous (cyclicComplement hab x s t) := by
  apply Function.continuous_concatUnitIntervals
  · exact hx.comp (Set.Icc.continuous_convexComb _ _)
  · exact hx.comp (Set.Icc.continuous_convexComb _ _)
  · simpa [Function.comp_apply] using hclosed.symm

@[simp] private theorem cyclicComplement_zero {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s t : Set.Icc a b) :
    cyclicComplement hab x s t ⟨0, by norm_num⟩ = x t := by
  simp [cyclicComplement]

@[simp] private theorem cyclicComplement_two {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s t : Set.Icc a b) :
    cyclicComplement hab x s t ⟨2, by norm_num⟩ = x s := by
  simp [cyclicComplement]

private theorem tangentVector_ne_zero (t : Real.Angle) : tangentVector t ≠ 0 := by
  intro h
  have hone : inner ℝ (tangentVector t) (tangentVector t) = 1 := by
    rw [← t.coe_toReal]
    exact inner_tangentVector_self t.toReal
  rw [h] at hone
  simp at hone

private theorem convexComb_between {a b : ℝ} {l u : Set.Icc a b} (hlu : l ≤ u)
    (r : Set.Icc (0 : ℝ) 1) :
    l ≤ Set.Icc.convexComb l u r ∧ Set.Icc.convexComb l u r ≤ u := by
  change (l : ℝ) ≤ (1 - (r : ℝ)) * l + (r : ℝ) * u ∧
    (1 - (r : ℝ)) * l + (r : ℝ) * u ≤ u
  constructor <;> nlinarith [r.property.1, r.property.2, show (l : ℝ) ≤ u from hlu]

private theorem range_comp_convexComb {a b : ℝ} {l u : Set.Icc a b} (hlu : l ≤ u)
    (x : Set.Icc a b → Point) :
    Set.range (x ∘ Set.Icc.convexComb l u) = x '' Set.Icc l u := by
  by_cases heq : l = u
  · subst u
    simp [Set.Icc_self]
  have hneval : (l : ℝ) ≠ (u : ℝ) := fun h ↦ heq (Subtype.ext h)
  have hlt : (l : ℝ) < (u : ℝ) := lt_of_le_of_ne hlu hneval
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, convexComb_between hlu r, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    let r : I := ⟨((v : ℝ) - l) / ((u : ℝ) - l), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hv.1)
          (sub_nonneg.mpr (show (l : ℝ) ≤ u from hlu))
      · exact (div_le_one (sub_pos.mpr hlt)).2
          (by
            have hv₂ : (v : ℝ) ≤ (u : ℝ) := hv.2
            linarith)⟩
    refine ⟨r, congrArg x ?_⟩
    apply Subtype.ext
    simp [r]
    field_simp [sub_ne_zero.mpr hlt.ne']
    ring

private theorem inner_eq_of_mem_segment {P Q z v : Point} {c : ℝ}
    (hP : inner ℝ P v = c) (hQ : inner ℝ Q v = c)
    (hz : z ∈ segment ℝ P Q) : inner ℝ z v = c := by
  rw [segment_eq_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hP, hQ]
  nlinarith [hr.1, hr.2]

private theorem arg_conj_I_mul_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg (starRingEnd ℂ Complex.I * z) = Complex.arg z - Real.pi / 2 := by
  have hzne : z ≠ 0 := fun h ↦ by simp [h] at hz
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [Complex.arg_mul (by simp) hzne]
  · simp only [Complex.conj_I, Complex.arg_neg_I]
    ring
  · simp only [Complex.conj_I, Complex.arg_neg_I]
    constructor <;> have h := abs_lt.mp harg <;> linarith [Real.pi_pos]

private theorem arg_conj_neg_I_mul_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg (starRingEnd ℂ (-Complex.I) * z) = Complex.arg z + Real.pi / 2 := by
  have hzne : z ≠ 0 := fun h ↦ by simp [h] at hz
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [Complex.arg_mul (by simp) hzne]
  · simp only [map_neg, Complex.conj_I, neg_neg, Complex.arg_I]
    ring
  · simp only [map_neg, Complex.conj_I, neg_neg, Complex.arg_I]
    constructor <;> have h := abs_lt.mp harg <;> linarith [Real.pi_pos]

private theorem relative_arg_of_frame_eq_pos_I {t : Real.Angle} {v w : Point}
    {D : ℝ} (hD : 0 < D) (hv : frameComplex t v = (D : ℂ) * Complex.I)
    (hw : 0 < (frameComplex t w).re) :
    Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w) =
      Complex.arg (frameComplex t w) - Real.pi / 2 := by
  rw [conj_pointComplex_mul_eq_conj_frameComplex_mul, hv]
  have heq : starRingEnd ℂ ((D : ℂ) * Complex.I) * frameComplex t w =
      (D : ℂ) * (starRingEnd ℂ Complex.I * frameComplex t w) := by
    simp [mul_assoc]
  rw [heq, Complex.arg_real_mul _ hD]
  exact arg_conj_I_mul_of_re_pos hw

private theorem relative_arg_of_frame_eq_neg_I {t : Real.Angle} {v w : Point}
    {D : ℝ} (hD : 0 < D) (hv : frameComplex t v = -(D : ℂ) * Complex.I)
    (hw : 0 < (frameComplex t w).re) :
    Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w) =
      Complex.arg (frameComplex t w) + Real.pi / 2 := by
  rw [conj_pointComplex_mul_eq_conj_frameComplex_mul, hv]
  have heq : starRingEnd ℂ (-(D : ℂ) * Complex.I) * frameComplex t w =
      (D : ℂ) * (starRingEnd ℂ (-Complex.I) * frameComplex t w) := by
    simp [mul_assoc]
  rw [heq, Complex.arg_real_mul _ hD]
  exact arg_conj_neg_I_mul_of_re_pos hw

/-- The midpoint of a nontrivial segment traversed on `[s,t]` is avoided by the cyclic
complementary path. -/
private theorem cyclicComplement_ne_midpoint {a b : ℝ} (hab : a < b)
    {x : Set.Icc a b → Point}
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {u | (u : ℝ) < b})
    (s t : Set.Icc a b) (hst : s < t) (hxt : x s ≠ x t)
    (hsegment : x '' Set.Icc s t = segment ℝ (x s) (x t)) :
    ∀ u, cyclicComplement hab.le x s t u ≠ midpoint ℝ (x s) (x t) := by
  have hmseg : midpoint ℝ (x s) (x t) ∈ x '' Set.Icc s t := by
    rw [hsegment]
    exact midpoint_mem_segment _ _
  obtain ⟨v, hvst, hv⟩ := hmseg
  have hmvP : midpoint ℝ (x s) (x t) ≠ x s := by
    intro hm
    exact hxt ((midpoint_eq_left_iff ℝ).mp hm)
  have hmvQ : midpoint ℝ (x s) (x t) ≠ x t := by
    intro hm
    exact hxt ((midpoint_eq_right_iff ℝ).mp hm)
  have hsv : s < v := lt_of_le_of_ne hvst.1 (fun h ↦ hmvP (hv ▸ congrArg x h.symm))
  have hvt : v < t := lt_of_le_of_ne hvst.2 (fun h ↦ hmvQ (hv ▸ congrArg x h))
  have hsv' : (s : ℝ) < v := hsv
  have hvt' : (v : ℝ) < t := hvt
  have hvb : (v : ℝ) < b := lt_of_lt_of_le hvt t.property.2
  intro u hu
  have heval :
      (x ∘ Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩)
          (Set.projIcc 0 1 (by norm_num) (u : ℝ)) =
          midpoint ℝ (x s) (x t) ∨
        (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s)
            (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1)) =
              midpoint ℝ (x s) (x t) := by
    unfold cyclicComplement Function.concatUnitIntervals at hu
    split_ifs at hu with h
    · exact Or.inl hu
    · exact Or.inr hu
  rcases heval with htail | hhead
  · let w := Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
      (Set.projIcc 0 1 (by norm_num) (u : ℝ))
    have htw : t ≤ w := (convexComb_between t.property.2 _).1
    have hxwv : x w = x v := htail.trans hv.symm
    by_cases hwb : (w : ℝ) = b
    · have hwtop : w = (⟨b, hab.le, le_rfl⟩ : Set.Icc a b) := Subtype.ext hwb
      have hxav : x ⟨a, le_rfl, hab.le⟩ = x v := hclosed.trans (hwtop ▸ hxwv)
      have hav := hinj (by simp [hab]) (by exact hvb) hxav
      have hav' := congrArg Subtype.val hav
      linarith [s.property.1]
    · have hwb' : (w : ℝ) < b := lt_of_le_of_ne w.property.2 hwb
      have hwv := hinj hwb' hvb hxwv
      have hwv' := congrArg Subtype.val hwv
      have htw' : (t : ℝ) ≤ w := htw
      linarith
  · let w := Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
      (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1))
    have hws : w ≤ s := (convexComb_between s.property.1 _).2
    have hxwv : x w = x v := hhead.trans hv.symm
    have hwb : (w : ℝ) < b := lt_of_le_of_lt hws (lt_of_lt_of_le hst t.property.2)
    have hwv := hinj hwb hvb hxwv
    have hwv' := congrArg Subtype.val hwv
    have hws' : (w : ℝ) ≤ s := hws
    linarith

private theorem jordan_counterclockwise_of_winding_one
    (a b : ℝ) (hab : a < b) (x : Set.Icc a b → Point)
    (hx : Continuous x) (hΓ : IsJordanCurve (Set.range x))
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (q : Point) (hqrange : q ∉ Set.range x)
    (hwinding_q : curveWinding hab.le x q = 1) :
    IsOrientedJordanParametrization hab.le (Set.range x) true x := by
  refine ⟨hab, hΓ, hx, rfl, hclosed, hinj, ?_⟩
  intro p hp
  obtain ⟨U, V, hUopen, hVopen, hUconn, hVconn, hUbounded, hVunbounded, hdis,
    hcover, hfrontU, hfrontV, hcompU, hcompV⟩ := jordan_separation hΓ
  have hqcompl : q ∈ (Set.range x)ᶜ := hqrange
  have hqUV : q ∈ U ∪ V := hcover.symm.subset hqcompl
  have hqU : q ∈ U := by
    rcases hqUV with hqU | hqV
    · exact hqU
    · exfalso
      let _ : PreconnectedSpace V := Subtype.preconnectedSpace hVconn.isPreconnected
      have hlc : IsLocallyConstant
          (fun z : V ↦ curveWinding hab.le x z.val) := by
        apply (IsLocallyConstant.iff_exists_open _).mpr
        intro z
        have hzout : z.val ∉ Set.range x := by
          have hzcompl : z.val ∈ (Set.range x)ᶜ := hcover ▸ Or.inr z.property
          exact hzcompl
        obtain ⟨W, hWopen, hzW, hWeq⟩ :=
          curveWinding_locally_constant_off_range hab.le hx hclosed hzout
        exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
          fun z' hz' ↦ hWeq z'.val hz'⟩
      have hrangeBounded : Bornology.IsBounded (Set.range x) :=
        by simpa only [Set.image_univ] using (isCompact_univ.image hx).isBounded
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp
        hrangeBounded
      have hRnonneg : 0 ≤ R := by
        have := hR (Set.mem_range_self ⟨a, le_rfl, hab.le⟩)
        have hnorm : ‖x ⟨a, le_rfl, hab.le⟩‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using this
        exact (norm_nonneg _).trans hnorm
      have hvfar : ∃ v ∈ V, R + 1 < ‖v‖ := by
        by_contra hn
        push Not at hn
        apply hVunbounded
        refine (Metric.isBounded_iff_subset_closedBall (0 : Point)).2 ⟨R + 1, ?_⟩
        intro v hv
        simpa [Metric.mem_closedBall, dist_zero_right] using hn v hv
      obtain ⟨v, hvV, hvnorm⟩ := hvfar
      have hvzero : curveWinding hab.le x v = 0 := by
        apply curveWinding_eq_zero_of_inner_pos hab.le hx hclosed v (-v)
        · exact neg_ne_zero.mpr (by
            intro hv0
            rw [hv0, norm_zero] at hvnorm
            linarith)
        · intro u
          rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
          rw [← real_inner_comm v (x u)]
          have hxu := hR (Set.mem_range_self u)
          have hinner := abs_real_inner_le_norm (x u) v
          have hxnorm : ‖x u‖ ≤ R := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hxu
          have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hRnonneg (lt_add_one R) |>.trans hvnorm
          have hvlarge : R < ‖v‖ := lt_trans (lt_add_one R) hvnorm
          have hlower : inner ℝ (x u) v ≤ ‖x u‖ * ‖v‖ := le_trans (le_abs_self _) hinner
          have hprod : ‖x u‖ * ‖v‖ < ‖v‖ * ‖v‖ :=
            lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxnorm (norm_nonneg v))
              (mul_lt_mul_of_pos_right hvlarge hvpos)
          rw [pow_two]
          linarith
      have heq := hlc.apply_eq_of_preconnectedSpace ⟨q, hqV⟩ ⟨v, hvV⟩
      rw [hwinding_q, hvzero] at heq
      norm_num at heq
  have hpUV : p ∈ U ∪ V := hcover.symm.subset hp.1
  have hpU : p ∈ U := by
    rcases hpUV with hpU | hpV
    · exact hpU
    · exfalso
      apply hVunbounded
      rw [← hcompV p hpV]
      exact hp.2
  let _ : PreconnectedSpace U := Subtype.preconnectedSpace hUconn.isPreconnected
  have hlcU : IsLocallyConstant (fun z : U ↦ curveWinding hab.le x z.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro z
    have hzout : z.val ∉ Set.range x := by
      have : z.val ∈ (Set.range x)ᶜ := hcover ▸ Or.inl z.property
      exact this
    obtain ⟨W, hWopen, hzW, hWeq⟩ :=
      curveWinding_locally_constant_off_range hab.le hx hclosed hzout
    exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
      fun z' hz' ↦ hWeq z'.val hz'⟩
  exact (hlcU.apply_eq_of_preconnectedSpace ⟨p, hpU⟩ ⟨q, hqU⟩).trans hwinding_q

private theorem supporting_segment_argument_corrections (P Q : Point) (θ : Real.Angle)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) (hdirection : Q = P + d • tangentVector θ) :
    let m := midpoint ℝ P Q
    let q := m - ε • normalVector θ
    (Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (Q - m)) *
    Complex.orthonormalBasisOneI.repr.symm (Q - q)) =
  Complex.arg (frameComplex θ (Q - q)) - Real.pi / 2) ∧
    (Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (P - m)) *
    Complex.orthonormalBasisOneI.repr.symm (P - q)) =
  Complex.arg (frameComplex θ (P - q)) + Real.pi / 2) ∧
    (Complex.arg ((d / 2 : ℝ) * Complex.I) = Real.pi / 2) ∧
    (Complex.arg (-((d / 2 : ℝ) * Complex.I)) = -Real.pi / 2) ∧
    (-frameComplex θ (P - m) = (d / 2 : ℝ) * Complex.I) ∧
    (-frameComplex θ (Q - m) = -((d / 2 : ℝ) * Complex.I)) := by
  let m := midpoint ℝ P Q
  let q := m - ε • normalVector θ
  have htn : inner ℝ (tangentVector θ) (normalVector θ) = 0 := by
    rw [← θ.coe_toReal, real_inner_comm]
    exact inner_normalVector_tangentVector θ.toReal
  have htm : Q - m = (d / 2) • tangentVector θ := by
    dsimp [m]
    rw [midpoint_eq_smul_add, hdirection]
    norm_num
    module
  have hsm : P - m = -(d / 2) • tangentVector θ := by
    dsimp [m]
    rw [midpoint_eq_smul_add, hdirection]
    norm_num
    module
  have hTT : inner ℝ (tangentVector θ) (tangentVector θ) = 1 := by
    rw [← θ.coe_toReal]
    exact inner_tangentVector_self θ.toReal
  have hNN : inner ℝ (normalVector θ) (normalVector θ) = 1 := by
    rw [← θ.coe_toReal]
    exact inner_normalVector_self θ.toReal
  have hNT : inner ℝ (normalVector θ) (tangentVector θ) = 0 := by
    rw [real_inner_comm]
    exact htn
  have hframe_tm : frameComplex θ (Q - m) = (d / 2 : ℝ) * Complex.I := by
    rw [htm]
    apply Complex.ext
    · rw [frameComplex_re, real_inner_smul_left, htn]
      simp
    · rw [frameComplex_im, real_inner_smul_left, hTT]
      simp
  have hframe_sm : frameComplex θ (P - m) = -(d / 2 : ℝ) * Complex.I := by
    rw [hsm]
    apply Complex.ext
    · rw [frameComplex_re, real_inner_smul_left, htn]
      simp
    · rw [frameComplex_im, real_inner_smul_left, hTT]
      simp
  have htq : Q - q = ε • normalVector θ + (d / 2) • tangentVector θ := by
    calc
      Q - q = (Q - m) + ε • normalVector θ := by dsimp [q]; abel
      _ = _ := by rw [htm]; abel
  have hsq : P - q = ε • normalVector θ - (d / 2) • tangentVector θ := by
    calc
      P - q = (P - m) + ε • normalVector θ := by dsimp [q]; abel
      _ = _ := by rw [hsm]; module
  have hframe_tq : frameComplex θ (Q - q) = ε + (d / 2 : ℝ) * Complex.I := by
    rw [htq]
    apply Complex.ext
    · rw [frameComplex_re, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, hNN, htn]
      simp
    · rw [frameComplex_im, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, hNT, hTT]
      simp
  have hframe_sq : frameComplex θ (P - q) = ε - (d / 2 : ℝ) * Complex.I := by
    rw [hsq]
    apply Complex.ext
    · rw [frameComplex_re, inner_sub_left, real_inner_smul_left,
        real_inner_smul_left, hNN, htn]
      simp
    · rw [frameComplex_im, inner_sub_left, real_inner_smul_left,
        real_inner_smul_left, hNT, hTT]
      simp
  have hcorr_t :
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (Q - m)) *
          Complex.orthonormalBasisOneI.repr.symm (Q - q)) =
        Complex.arg (frameComplex θ (Q - q)) - Real.pi / 2 := by
    apply relative_arg_of_frame_eq_pos_I (half_pos hd) hframe_tm
    rw [hframe_tq]
    simpa using hε
  have hcorr_s :
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (P - m)) *
          Complex.orthonormalBasisOneI.repr.symm (P - q)) =
        Complex.arg (frameComplex θ (P - q)) + Real.pi / 2 := by
    apply relative_arg_of_frame_eq_neg_I (half_pos hd) hframe_sm
    rw [hframe_sq]
    simpa using hε
  have harg_tm : Complex.arg ((d / 2 : ℝ) * Complex.I) = Real.pi / 2 := by
    rw [Complex.arg_real_mul _ (half_pos hd), Complex.arg_I]
  have harg_sm : Complex.arg (-((d / 2 : ℝ) * Complex.I)) = -Real.pi / 2 := by
    rw [show -((d / 2 : ℝ) * Complex.I) = (d / 2 : ℝ) * (-Complex.I) by ring,
      Complex.arg_real_mul _ (half_pos hd), Complex.arg_neg_I]
    ring
  have hneg_frame_sm : -frameComplex θ (P - m) = (d / 2 : ℝ) * Complex.I := by
    rw [hframe_sm]
    ring
  have hneg_frame_tm : -frameComplex θ (Q - m) = -((d / 2 : ℝ) * Complex.I) := by
    rw [hframe_tm]
  exact ⟨hcorr_t, hcorr_s, harg_tm, harg_sm, hneg_frame_sm, hneg_frame_tm⟩

private theorem cyclic_partition_range {a b : ℝ} (hab : a < b)
    (x : Set.Icc a b → Point)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (s t : Set.Icc a b) (hst : s < t) :
    let y := cyclicComplement hab.le x s t
    let z : Set.Icc (0 : ℝ) 1 → Point := fun u ↦ x (Set.Icc.convexComb s t u)
    let doubleParam : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 := fun u ↦
    ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.property.1, u.property.2]⟩
    let y₁ : Set.Icc (0 : ℝ) 1 → Point := y ∘ doubleParam
    Set.range (Function.concatUnitIntervals z y₁) = Set.range x := by
  let y := cyclicComplement hab.le x s t
  let z : Set.Icc (0 : ℝ) 1 → Point := fun u ↦ x (Set.Icc.convexComb s t u)
  let doubleParam : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 := fun u ↦
    ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.property.1, u.property.2]⟩
  let y₁ : Set.Icc (0 : ℝ) 1 → Point := y ∘ doubleParam
  have hjoin : z ⟨1, by norm_num⟩ = y₁ ⟨0, by norm_num⟩ := by
    simp [z, y₁, doubleParam, y]
  have hdouble_surj : Function.Surjective doubleParam := by
    intro u
    refine ⟨⟨(u : ℝ) / 2, by constructor <;> nlinarith [u.property.1, u.property.2]⟩, ?_⟩
    apply Subtype.ext
    dsimp [doubleParam]
    ring
  have hrange_y₁ : Set.range y₁ = Set.range y := by
    change Set.range (y ∘ doubleParam) = Set.range y
    rw [Set.range_comp, hdouble_surj.range_eq, Set.image_univ]
  have hrange_w : Set.range (Function.concatUnitIntervals z y₁) = Set.range x := by
    rw [Function.range_concatUnitIntervals z y₁ hjoin, hrange_y₁]
    change Set.range z ∪ Set.range (Function.concatUnitIntervals
      (x ∘ Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩)
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s)) = Set.range x
    rw [Function.range_concatUnitIntervals _ _ (by simpa using hclosed.symm),
      show Set.range z = x '' Set.Icc s t by
        change Set.range (x ∘ Set.Icc.convexComb s t) = _
        exact range_comp_convexComb hst.le x,
      range_comp_convexComb t.property.2 x, range_comp_convexComb s.property.1 x]
    ext p
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;>
        exact Set.mem_range_self u
    · rintro ⟨u, rfl⟩
      by_cases hus : u ≤ s
      · exact Or.inr (Or.inr ⟨u, ⟨u.property.1, hus⟩, rfl⟩)
      by_cases hut : u ≤ t
      · exact Or.inl ⟨u, ⟨le_of_not_ge hus, hut⟩, rfl⟩
      · exact Or.inr (Or.inl ⟨u, ⟨le_of_not_ge hut, u.property.2⟩, rfl⟩)
  exact hrange_w

theorem jordan_counterclockwise_of_supporting_segment
    (a b : ℝ) (hab : a < b) (x : Set.Icc a b → Point)
    (hx : Continuous x) (hΓ : IsJordanCurve (Set.range x))
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (θ : Real.Angle) (h : ℝ)
    (hhalf : ∀ t, x t ∈ normalHalfPlane θ h false false)
    (s t : Set.Icc a b) (hst : s < t)
    (hline : x s ∈ normalLine θ h)
    (d : ℝ) (hd : 0 < d) (hdirection : x t = x s + d • tangentVector θ)
    (hsegment : x '' Set.Icc s t = segment ℝ (x s) (x t)) :
    IsOrientedJordanParametrization hab.le (Set.range x) true x := by
  have hxt : x s ≠ x t := by
    intro heq
    have hz : d • tangentVector θ = 0 := by
      calc
        d • tangentVector θ = x t - x s := by rw [hdirection]; abel
        _ = 0 := by rw [← heq, sub_self]
    exact tangentVector_ne_zero θ ((smul_eq_zero.mp hz).resolve_left hd.ne')
  let m := midpoint ℝ (x s) (x t)
  let y := cyclicComplement hab.le x s t
  have hy : Continuous y := continuous_cyclicComplement hab.le hx hclosed s t
  have hym (u : Set.Icc (0 : ℝ) 2) : y u ≠ m := by
    exact cyclicComplement_ne_midpoint hab hclosed hinj s t hst hxt hsegment u
  obtain ⟨r, hr, hdot⟩ := exists_ball_relative_dot_pos (by norm_num) hy (by
    intro hm
    obtain ⟨u, hu⟩ := hm
    exact hym u hu)
  have hxsN : inner ℝ (x s) (normalVector θ) = h := hline
  have htn : inner ℝ (tangentVector θ) (normalVector θ) = 0 := by
    rw [← θ.coe_toReal, real_inner_comm]
    exact inner_normalVector_tangentVector θ.toReal
  have hxtN : inner ℝ (x t) (normalVector θ) = h := by
    rw [hdirection, inner_add_left, real_inner_smul_left, hxsN, htn, mul_zero, add_zero]
  have hmN : inner ℝ m (normalVector θ) = h := by
    dsimp [m]
    rw [midpoint_eq_smul_add, real_inner_smul_left, inner_add_left, hxsN, hxtN]
    norm_num
    ring
  have hyhalf (u : Set.Icc (0 : ℝ) 2) :
      inner ℝ (y u - m) (normalVector θ) ≤ 0 := by
    unfold y cyclicComplement Function.concatUnitIntervals
    split_ifs
    · rw [inner_sub_left, hmN]
      have hh := hhalf (Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
        (Set.projIcc 0 1 (by norm_num) (u : ℝ)))
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq] at hh
      simpa only [Function.comp_apply] using sub_nonpos.mpr hh
    · rw [inner_sub_left, hmN]
      have hh := hhalf (Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
        (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1)))
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq] at hh
      simpa only [Function.comp_apply] using sub_nonpos.mpr hh
  have hymLift : IsCurveAngleLift y m (fun u ↦
      θ.toReal + Complex.arg (-frameComplex θ (y u - m)) + Real.pi) :=
    isCurveAngleLift_frameArg_neg_add_pi_of_inner_nonpos θ hy hyhalf hym
  let ε := min (r / 2) (d / 4)
  have hε : 0 < ε := lt_min (half_pos hr) (by positivity)
  have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  let q := m - ε • normalVector θ
  have hnormN : ‖normalVector θ‖ = 1 := by
    rw [← θ.coe_toReal]
    exact norm_normalVector_real θ.toReal
  have hqm : dist q m = ε := by
    rw [dist_eq_norm]
    simp only [q, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, hnormN,
      mul_one, abs_of_pos hε]
  have hqclose : dist q m < r := hqm.trans_lt hεr
  have hyqLift := hymLift.add_principal_basepoint_correction hy (hdot q hqclose)
  let z : Set.Icc (0 : ℝ) 1 → Point := fun u ↦ x (Set.Icc.convexComb s t u)
  have hz : Continuous z := hx.comp (Set.Icc.continuous_convexComb _ _)
  have hzN (u : Set.Icc (0 : ℝ) 1) : inner ℝ (z u) (normalVector θ) = h := by
    apply inner_eq_of_mem_segment hxsN hxtN
    rw [← hsegment]
    exact ⟨Set.Icc.convexComb s t u, convexComb_between hst.le u, rfl⟩
  have hqN : inner ℝ q (normalVector θ) = h - ε := by
    dsimp [q]
    rw [inner_sub_left, real_inner_smul_left, hmN]
    have hNN : inner ℝ (normalVector θ) (normalVector θ) = 1 := by
      rw [← θ.coe_toReal]
      exact inner_normalVector_self θ.toReal
    rw [hNN, mul_one]
  have hzright (u : Set.Icc (0 : ℝ) 1) :
      0 ≤ inner ℝ (z u - q) (normalVector θ) := by
    rw [inner_sub_left, hzN, hqN]
    linarith
  have hzq (u : Set.Icc (0 : ℝ) 1) : z u ≠ q := by
    intro heq
    have := congrArg (fun w : Point ↦ inner ℝ w (normalVector θ)) heq
    rw [hzN, hqN] at this
    linarith
  have hzqLift : IsCurveAngleLift z q
      (fun u ↦ θ.toReal + Complex.arg (frameComplex θ (z u - q))) :=
    isCurveAngleLift_frameArg_of_inner_nonneg θ hz hzright hzq
  let doubleParam : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 := fun u ↦
    ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.property.1, u.property.2]⟩
  have hdouble : Continuous doubleParam := by
    exact Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
  let y₁ : Set.Icc (0 : ℝ) 1 → Point := y ∘ doubleParam
  have hy₁ : Continuous y₁ := hy.comp hdouble
  have hy₁qLift : IsCurveAngleLift y₁ q
      ((fun u ↦ θ.toReal + Complex.arg (-frameComplex θ (y u - m)) + Real.pi +
        Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (y u - m)) *
            Complex.orthonormalBasisOneI.repr.symm (y u - q))) ∘
          doubleParam) := hyqLift.comp hdouble
  have hjoin : z ⟨1, by norm_num⟩ = y₁ ⟨0, by norm_num⟩ := by
    simp [z, y₁, doubleParam, y]
  obtain ⟨hcorr_t, hcorr_s, harg_tm, harg_sm, hneg_frame_sm, hneg_frame_tm⟩ :=
    supporting_segment_argument_corrections (x s) (x t) θ d ε hd hε hdirection
  change Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x t - m)) *
          Complex.orthonormalBasisOneI.repr.symm (x t - q)) =
        Complex.arg (frameComplex θ (x t - q)) - Real.pi / 2 at hcorr_t
  change Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x s - m)) *
          Complex.orthonormalBasisOneI.repr.symm (x s - q)) =
        Complex.arg (frameComplex θ (x s - q)) + Real.pi / 2 at hcorr_s
  have hz0 : z ⟨0, by norm_num⟩ = x s := by simp [z]
  have hz1 : z ⟨1, by norm_num⟩ = x t := by simp [z]
  have hy₁0 : y₁ ⟨0, by norm_num⟩ = x t := by
    simp [y₁, doubleParam, y]
  have hy₁1 : y₁ ⟨1, by norm_num⟩ = x s := by
    simp [y₁, doubleParam, y]
  have hwinding : curveWinding (by norm_num)
      (Function.concatUnitIntervals z y₁) q = 1 := by
    rw [curveWinding_concatUnitIntervals hzqLift hy₁qLift hjoin,
      hzqLift.curveWinding_eq, hy₁qLift.curveWinding_eq]
    rw [hz1, hz0]
    simp only [Function.comp_apply]
    simp only [add_sub_add_left_eq_sub, cyclicComplement, mul_one, Function.concatUnitIntervals_two,
      Set.Icc.mk_one, Function.comp_apply, Set.Icc.convexComb_one,
      Complex.orthonormalBasisOneI_repr_symm_apply, Fin.isValue, map_add, map_sub,
        Complex.conj_ofReal, map_mul, Complex.conj_I,
      mul_neg, mul_zero, Function.concatUnitIntervals_zero, Set.Icc.mk_zero,
      Set.Icc.convexComb_zero, y, doubleParam]
    simp only [Complex.orthonormalBasisOneI_repr_symm_apply, Fin.isValue, map_add, map_sub,
      Complex.conj_ofReal, map_mul, Complex.conj_I,
      mul_neg] at hcorr_t hcorr_s
    rw [hneg_frame_sm, hneg_frame_tm, harg_tm, harg_sm, hcorr_t, hcorr_s]
    field_simp [Real.pi_ne_zero]
    ring
  have hrange_w := cyclic_partition_range hab x hclosed s t hst
  have hwinding_eq_x (p : Point) (hp : p ∉ Set.range x) :
      curveWinding (by norm_num) (Function.concatUnitIntervals z y₁) p =
        curveWinding hab.le x p := by
    obtain ⟨α, hα⟩ := exists_curveAngleLift_of_avoids hab hx hp
    let φst := Set.Icc.convexComb s t
    let φtb := Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
    let φas := Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
    have hzα : IsCurveAngleLift z p (α ∘ φst) := hα.comp (Set.Icc.continuous_convexComb _ _)
    have htbα : IsCurveAngleLift (x ∘ φtb) p (α ∘ φtb) :=
      hα.comp (Set.Icc.continuous_convexComb _ _)
    have hasα : IsCurveAngleLift (x ∘ φas) p (α ∘ φas) :=
      hα.comp (Set.Icc.continuous_convexComb _ _)
    have htailJoin : (x ∘ φtb) ⟨1, by norm_num⟩ = (x ∘ φas) ⟨0, by norm_num⟩ := by
      simpa [φtb, φas] using hclosed.symm
    have hyp : p ∉ Set.range y := by
      rintro ⟨u, rfl⟩
      apply hp
      unfold y cyclicComplement Function.concatUnitIntervals
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ := exists_curveAngleLift_of_avoids (by norm_num) hy hyp
    have hy₁wind : curveWinding (by norm_num) y₁ p = curveWinding (by norm_num) y p := by
      apply curveWinding_comp_of_endpoints (by norm_num) (by norm_num) ⟨β, hβ⟩ hdouble
      · apply Subtype.ext
        simp [doubleParam]
      · apply Subtype.ext
        simp [doubleParam]
    rw [curveWinding_concatUnitIntervals hzα (hβ.comp hdouble) hjoin, hy₁wind]
    change curveWinding (by norm_num) z p +
      curveWinding (by norm_num) (Function.concatUnitIntervals (x ∘ φtb) (x ∘ φas)) p = _
    rw [curveWinding_concatUnitIntervals htbα hasα htailJoin]
    rw [hzα.curveWinding_eq, htbα.curveWinding_eq, hasα.curveWinding_eq,
      hα.curveWinding_eq]
    have hst0 : α (φst ⟨0, by norm_num⟩) = α s := congrArg α (by simp [φst])
    have hst1 : α (φst ⟨1, by norm_num⟩) = α t := congrArg α (by simp [φst])
    have htb0 : α (φtb ⟨0, by norm_num⟩) = α t := congrArg α (by simp [φtb])
    have htb1 : α (φtb ⟨1, by norm_num⟩) = α ⟨b, hab.le, le_rfl⟩ :=
      congrArg α (by simp [φtb])
    have has0 : α (φas ⟨0, by norm_num⟩) = α ⟨a, le_rfl, hab.le⟩ :=
      congrArg α (by simp [φas])
    have has1 : α (φas ⟨1, by norm_num⟩) = α s := congrArg α (by simp [φas])
    simp only [Function.comp_apply]
    rw [hst0, hst1, htb0, htb1, has0, has1]
    ring
  have hqrange : q ∉ Set.range x := by
    rw [← hrange_w]
    intro hq
    obtain ⟨α, hα⟩ := exists_curveAngleLift_of_curveWinding_ne_zero
      (a := 0) (b := 2) (by norm_num)
      (by rw [hwinding]; norm_num)
    obtain ⟨u, hu⟩ := hq
    have hc := (hα.2 u).1
    have hs := (hα.2 u).2
    rw [hu, sub_self] at hc hs
    simp at hc hs
    nlinarith only [hc, hs, Real.cos_sq_add_sin_sq (α u)]
  have hwinding_q : curveWinding hab.le x q = 1 := by
    rw [← hwinding_eq_x q hqrange, hwinding]
  exact jordan_counterclockwise_of_winding_one a b hab x hx hΓ hclosed hinj q
    hqrange hwinding_q

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Subarc
-/

public section

noncomputable section

namespace MovingSofa

open Set

/-- Reversing the parameter of a closed path preserves injectivity away from the
identified terminal endpoint. -/
theorem injOn_comp_reverse_of_closed_injOn
    {α : Type*} {a b : ℝ} (hab : a < b) (x : Set.Icc a b → α)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Set.InjOn (x ∘ Set.Icc.reverse hab.le) {t | (t : ℝ) < b} := by
  intro s hs t ht hst
  change (s : ℝ) < b at hs
  change (t : ℝ) < b at ht
  have hrs_pos : a < (Set.Icc.reverse hab.le s : ℝ) := by
    change a < a + b - (s : ℝ)
    linarith
  have hrt_pos : a < (Set.Icc.reverse hab.le t : ℝ) := by
    change a < a + b - (t : ℝ)
    linarith
  by_cases hrs : (Set.Icc.reverse hab.le s : ℝ) < b
  · by_cases hrt : (Set.Icc.reverse hab.le t : ℝ) < b
    · exact (Set.Icc.involutive_reverse hab.le).injective (hinj hrs hrt hst)
    · have hrteq : Set.Icc.reverse hab.le t = ⟨b, hab.le, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm (Set.Icc.reverse hab.le t).property.2 (le_of_not_gt hrt)
      have hra : x (Set.Icc.reverse hab.le s) = x ⟨a, le_rfl, hab.le⟩ := by
        rw [hclosed, ← hrteq]
        exact hst
      have heq := hinj hrs hab hra
      exfalso
      have := congrArg Subtype.val heq
      linarith
  · have hrseq : Set.Icc.reverse hab.le s = ⟨b, hab.le, le_rfl⟩ := by
      apply Subtype.ext
      exact le_antisymm (Set.Icc.reverse hab.le s).property.2 (le_of_not_gt hrs)
    by_cases hrt : (Set.Icc.reverse hab.le t : ℝ) < b
    · have hra : x ⟨a, le_rfl, hab.le⟩ = x (Set.Icc.reverse hab.le t) := by
        rw [hclosed, ← hrseq]
        exact hst
      have heq := hinj hab hrt hra
      exfalso
      have := congrArg Subtype.val heq
      linarith
    · have hrteq : Set.Icc.reverse hab.le t = ⟨b, hab.le, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm (Set.Icc.reverse hab.le t).property.2 (le_of_not_gt hrt)
      exact (Set.Icc.involutive_reverse hab.le).injective (hrseq.trans hrteq.symm)

/-- Parameter reversal sends the reversed closed interval to the original interval image. -/
theorem image_Icc_reverse_interval {α : Type*} {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → α) (l u : Set.Icc a b) (_hlu : l ≤ u) :
    (x ∘ Set.Icc.reverse hab) ''
        Set.Icc (Set.Icc.reverse hab u) (Set.Icc.reverse hab l) =
      x '' Set.Icc l u := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Set.Icc.reverse hab s, ?_, rfl⟩
    constructor
    · simpa only [Set.Icc.involutive_reverse hab l] using
        Set.Icc.antitone_reverse hab hs.2
    · simpa only [Set.Icc.involutive_reverse hab u] using
        Set.Icc.antitone_reverse hab hs.1
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Set.Icc.reverse hab s, ?_, ?_⟩
    · constructor
      · exact Set.Icc.antitone_reverse hab hs.2
      · exact Set.Icc.antitone_reverse hab hs.1
    · simp only [Function.comp_apply, Set.Icc.involutive_reverse hab s]

-- Duplicate of the current private UpperGraph helper; promote to Geometry.Support.
private theorem exists_Icc_coe_image_of_compact_connected_Ioo {a b : ℝ}
    {S : Set (Set.Ioo a b)} (hS : IsCompact S) (hconn : IsConnected S) :
    ∃ l u : ℝ, ((fun t : Set.Ioo a b ↦ (t : ℝ)) '' S) = Set.Icc l u := by
  let T := (fun t : Set.Ioo a b ↦ (t : ℝ)) '' S
  have hTc : IsCompact T := hS.image continuous_subtype_val
  have hTconn : IsConnected T := hconn.image _ continuous_subtype_val.continuousOn
  exact ⟨sInf T, sSup T, eq_Icc_of_connected_compact hTconn hTc⟩

private theorem exists_Icc_pullback_of_compact_connected_puncturedLoop
    {a b : ℝ} {x : Set.Icc a b → Point} (hab : a ≤ b) (hab' : a < b)
    (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (C : Set (puncturedLoopRangeSet hab x)) (hC : IsCompact C)
    (hconn : IsConnected C) :
    ∃ l u : ℝ,
      (fun t : Set.Ioo a b ↦ (t : ℝ)) ''
          ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj).symm '' C) =
        Set.Icc l u := by
  let e := openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj
  exact exists_Icc_coe_image_of_compact_connected_Ioo
    (hC.image e.symm.continuous) (hconn.image e.symm e.symm.continuous.continuousOn)

private theorem exists_Icc_parameters_of_compact_pathConnected_subset_loop
    {a b : ℝ} {x : Set.Icc a b → Point} (hab : a ≤ b) (hab' : a < b)
    (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (C : Set Point) (hC : IsCompact C) (hpath : IsPathConnected C)
    (hCrange : C ⊆ Set.range x) (hbase : x ⟨a, le_rfl, hab⟩ ∉ C) :
    ∃ l u : ℝ,
      (fun t : Set.Ioo a b ↦ (t : ℝ)) ''
          ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj).symm ''
            {q : puncturedLoopRangeSet hab x | (q : Point) ∈ C}) = Set.Icc l u := by
  let D : Set (puncturedLoopRangeSet hab x) := {q | (q : Point) ∈ C}
  let f : puncturedLoopRangeSet hab x → Point := fun q ↦ q
  have hf_ind : Topology.IsInducing f :=
    Topology.IsInducing.comp Topology.IsEmbedding.subtypeVal.isInducing
      Topology.IsEmbedding.subtypeVal.isInducing
  have hCrange' : C ⊆ Set.range f := by
    intro p hp
    obtain ⟨t, ht⟩ := hCrange hp
    let q : Set.range x := ⟨p, ⟨t, ht⟩⟩
    have hq : (q : Point) ≠ x ⟨a, le_rfl, hab⟩ := by
      intro heq
      exact hbase (heq ▸ hp)
    exact ⟨⟨q, hq⟩, rfl⟩
  have hDcompact : IsCompact D := by
    change IsCompact (f ⁻¹' C)
    exact hf_ind.isCompact_preimage' hC hCrange'
  have hDrange : {q : Set.range x | (q : Point) ∈ C} ⊆ puncturedLoopRangeSet hab x := by
    intro q hq
    exact fun heq ↦ hbase (heq ▸ hq)
  have hDpath : IsPathConnected D := by
    have h₁ := hpath.preimage_coe hCrange
    exact h₁.preimage_coe hDrange
  exact exists_Icc_pullback_of_compact_connected_puncturedLoop hab hab' hx hclosed hinj
    D hDcompact hDpath.isConnected

private theorem exists_rectifiableOrientedArc_restrict_closedJordan_of_lt_top
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hlu : l ≤ u) (hub : (u : ℝ) < b) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range (ContinuousBVPaths.restrict x l u hlu).val ∧
      A.val.startPoint = x.val l ∧ A.val.endPoint = x.val u := by
  let y := ContinuousBVPaths.restrict x l u hlu
  have hyinj : Function.Injective y.val := by
    intro s t hst
    apply Subtype.ext
    have hs : (s : ℝ) < b := lt_of_le_of_lt s.property.2 hub
    have ht : (t : ℝ) < b := lt_of_le_of_lt t.property.2 hub
    have h := hx.2.2.2.2.2.1 hs ht hst
    exact congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) h
  let A0 : OrientedJordanArc :=
    { carrier := Set.range y.val
      startPoint := x.val l
      endPoint := x.val u
      parametrizable := ⟨l, u, hlu, y.val, y.property.1, hyinj, rfl, rfl, rfl⟩ }
  let p : ArcBVParametrization A0 :=
    { a := l, b := u, ordered := hlu, path := y, injective := hyinj,
      range_eq := rfl, start_eq := rfl, end_eq := rfl }
  exact ⟨⟨A0, ⟨p⟩⟩, rfl, rfl, rfl⟩

/-- Convex interpolation between ordered interval points is strictly increasing. -/
theorem strictMono_convexComb_of_lt {a b : ℝ}
    (l u : Set.Icc a b) (hlu : l < u) : StrictMono (Set.Icc.convexComb l u) := by
  intro s t hst
  have hlu' : (l : ℝ) < u := hlu
  have hst' : (s : ℝ) < t := hst
  change (1 - (s : ℝ)) * l + (s : ℝ) * u <
    (1 - (t : ℝ)) * l + (t : ℝ) * u
  nlinarith [mul_pos (sub_pos.mpr hst') (sub_pos.mpr hlu')]

/-- The two closed pieces outside an interior parameter interval trace exactly the
closed curve with the open interval image removed. -/
theorem image_complement_interval_of_closed_injOn
    {α : Type*} {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → α)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hal : a < l) (hub : (u : ℝ) < b) :
    x '' {t | t ≤ l ∨ u ≤ t} =
      Set.range x \ x '' {t | l < t ∧ t < u} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Set.mem_range_self t, ?_⟩
    rintro ⟨s, hs, heq⟩
    have hsb : (s : ℝ) < b := lt_trans hs.2 hub
    by_cases htb : (t : ℝ) < b
    · have hst := hinj hsb htb heq
      subst t
      exact ht.elim (not_le_of_gt hs.1) (not_le_of_gt hs.2)
    · have hte : t = ⟨b, hab, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm t.2.2 (le_of_not_gt htb)
      have hab' : a < b := hal.trans_le l.2.2
      have hsa : s = ⟨a, le_rfl, hab⟩ :=
        hinj hsb hab' (heq.trans ((congrArg x hte).trans hclosed.symm))
      have : (l : ℝ) < a := by
        have h := hs.1
        rw [hsa] at h
        exact h
      exact (not_lt_of_ge hal.le) this
  · rintro ⟨⟨t, rfl⟩, hp⟩
    refine ⟨t, ?_, rfl⟩
    by_contra ht
    have hs : l < t ∧ t < u := ⟨lt_of_not_ge (fun h ↦ ht (Or.inl h)),
      lt_of_not_ge (fun h ↦ ht (Or.inr h))⟩
    exact hp ⟨t, hs, rfl⟩

/-- Convex interpolation between the interval endpoints covers the interval. -/
theorem surjective_convexComb_endpoints (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective
      (Set.Icc.convexComb (⟨a, le_rfl, hab⟩ : Set.Icc a b) ⟨b, hab, le_rfl⟩) := by
  intro x
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨⟨0, by norm_num⟩, Subtype.ext ?_⟩
    change (1 - (0 : ℝ)) * a + 0 * a = (x : ℝ)
    have hx : (x : ℝ) = a := le_antisymm x.property.2 x.property.1
    simp [hx]
  · refine ⟨⟨((x : ℝ) - a) / (b - a), ?_⟩, Subtype.ext ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr x.property.1) (sub_nonneg.mpr hab.le)
      · exact (div_le_one (sub_pos.mpr hab)).2 (sub_le_sub_right x.property.2 a)
    · change (1 - ((x : ℝ) - a) / (b - a)) * a +
        ((x : ℝ) - a) / (b - a) * b = (x : ℝ)
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring

/-- The initial restriction of a cyclically concatenated closed path traces the
complement of an interior parameter interval. -/
theorem range_cyclicConcat_restrict_to_complement
    {α : Type*} {a b : ℝ} (hab : a ≤ b) (f : Set.Icc a b → α)
    (hclosed : f ⟨a, le_rfl, hab⟩ = f ⟨b, hab, le_rfl⟩)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (θ : Set.Icc (0 : ℝ) 1)
    (hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l) :
    let v : ℝ := 1 + θ
    Set.range (fun z : Set.Icc (0 : ℝ) v ↦
      Function.concatUnitIntervals
        (f ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
        (f ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)
        ⟨z, z.property.1, z.property.2.trans (by
          have hθle : (θ : ℝ) ≤ 1 := θ.property.2
          dsimp only [v]
          linarith)⟩) = f '' {z | z ≤ l ∨ u ≤ z} := by
  dsimp only
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : (z : ℝ) ≤ 1
    · let q : Set.Icc (0 : ℝ) 1 := ⟨z, z.property.1, hz⟩
      let y := Set.Icc.convexComb u ⟨b, hab, le_rfl⟩ q
      refine ⟨y, Or.inr ?_, ?_⟩
      · change (u : ℝ) ≤ (1 - (q : ℝ)) * u + (q : ℝ) * b
        nlinarith [q.property.1, q.property.2, u.property.2]
      · have hvnonneg : 0 ≤ 1 + (θ : ℝ) := by linarith [θ.property.1]
        have hzmem : (z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨z.property.1, hz⟩
        change f y = Function.concatUnitIntervals _ _
          (⟨z, z.property.1, z.property.2.trans (by linarith [θ.property.2])⟩ :
            Set.Icc (0 : ℝ) 2)
        simp [Function.concatUnitIntervals, hz, q, y,
          Set.projIcc_of_mem (by norm_num) hzmem]
    · have hz1 : 1 < (z : ℝ) := lt_of_not_ge hz
      have hzsub0 : 0 ≤ (z : ℝ) - 1 := by linarith
      have hzsub1 : (z : ℝ) - 1 ≤ 1 := by
        have := z.property.2
        nlinarith [θ.property.2]
      let q : Set.Icc (0 : ℝ) 1 := ⟨(z : ℝ) - 1, hzsub0, hzsub1⟩
      let y := Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u q
      refine ⟨y, Or.inl ?_, ?_⟩
      · have hzθ : (q : ℝ) ≤ θ := by
          dsimp only [q]
          linarith [z.property.2]
        change (1 - (q : ℝ)) * a + (q : ℝ) * u ≤ (l : ℝ)
        have hθval := congrArg Subtype.val hθ
        change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
        nlinarith [hzθ, le_of_lt (lt_trans hal hlu)]
      · simp [Function.concatUnitIntervals, hz, q, y,
          Set.projIcc_of_mem (by norm_num) ⟨hzsub0, hzsub1⟩]
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hyl | huy
    · let y' : Set.Icc a (u : ℝ) := ⟨y, y.property.1, hyl.trans hlu.le⟩
      obtain ⟨q, hq'⟩ := surjective_convexComb_endpoints a u
        (le_trans l.property.1 hlu.le) y'
      have hq : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u q = y := by
        apply Subtype.ext
        have h := congrArg (fun z : Set.Icc a (u : ℝ) ↦ (z : ℝ)) hq'
        simpa only [Set.Icc.coe_convexComb] using h
      have hqθ : (q : ℝ) ≤ θ := by
        have hqval := congrArg Subtype.val hq
        have hθval := congrArg Subtype.val hθ
        change (1 - (q : ℝ)) * a + (q : ℝ) * u = (y : ℝ) at hqval
        change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
        have hau : a < (u : ℝ) := hal.trans hlu
        by_contra hn
        have hθq : (θ : ℝ) < q := lt_of_not_ge hn
        have hprod : 0 < ((q : ℝ) - θ) * ((u : ℝ) - a) :=
          mul_pos (sub_pos.mpr hθq) (sub_pos.mpr hau)
        have : (l : ℝ) < y := by nlinarith [hqval, hθval, hprod]
        exact (not_lt_of_ge hyl) this
      by_cases hq0 : (q : ℝ) = 0
      · let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨1, by
          constructor
          · norm_num
          · linarith [θ.property.1]⟩
        refine ⟨z, ?_⟩
        have hyA : y = ⟨a, le_rfl, hab⟩ := by
          apply Subtype.ext
          have hqval := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hq
          change (1 - (q : ℝ)) * a + (q : ℝ) * u = (y : ℝ) at hqval
          simp [hq0] at hqval
          exact hqval.symm
        rw [hyA, hclosed]
        simp [z, Function.comp_def]
      · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hq0)
        let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨(q : ℝ) + 1, by
          constructor <;> linarith⟩
        refine ⟨z, ?_⟩
        have hznot : ¬(z : ℝ) ≤ 1 := by dsimp only [z]; linarith
        rw [← hq]
        simp [z, Function.concatUnitIntervals, hznot,
          Set.projIcc_of_mem (by norm_num) q.property]
    · let y' : Set.Icc (u : ℝ) b := ⟨y, huy, y.property.2⟩
      obtain ⟨q, hq'⟩ := surjective_convexComb_endpoints u b hub.le y'
      have hq : Set.Icc.convexComb u ⟨b, hab, le_rfl⟩ q = y := by
        apply Subtype.ext
        have h := congrArg (fun z : Set.Icc (u : ℝ) b ↦ (z : ℝ)) hq'
        simpa only [Set.Icc.coe_convexComb] using h
      let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨q, by
        constructor
        · exact q.property.1
        · linarith [q.property.2, θ.property.1]⟩
      refine ⟨z, ?_⟩
      have hzle : (z : ℝ) ≤ 1 := q.property.2
      rw [← hq]
      simp [z, Function.concatUnitIntervals, hzle,
        Set.projIcc_of_mem (by norm_num) q.property]

private theorem exists_complementary_rectifiableOrientedArc
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hlQ : x.val l = Q) (huP : x.val u = P) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range x.val \ x.val '' {z | l < z ∧ z < u} ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q := by
  let l' : Set.Icc a (u : ℝ) := ⟨l, l.property.1, hlu.le⟩
  obtain ⟨θ, hθ'⟩ := surjective_convexComb_endpoints a u
    (le_trans l.property.1 hlu.le) l'
  have hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l := by
    apply Subtype.ext
    have h := congrArg (fun z : Set.Icc a (u : ℝ) ↦ (z : ℝ)) hθ'
    simpa only [Set.Icc.coe_convexComb] using h
  have hθpos : 0 < (θ : ℝ) := by
    by_contra hn
    have hθzero : (θ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) θ.property.1
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθzero] at h
    linarith
  have hθlt : (θ : ℝ) < 1 := by
    by_contra hn
    have hθone : (θ : ℝ) = 1 := le_antisymm θ.property.2 (le_of_not_gt hn)
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθone] at h
    exact hlu.ne (Subtype.ext h.symm)
  obtain ⟨r, hrJordan, hr⟩ :=
    exists_oriented_cyclic_rotation_eq_concat hab x hx u
      (hal.trans hlu) hub
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
    constructor <;> linarith⟩
  have hzv : z ≤ v := by change (0 : ℝ) ≤ 1 + θ; linarith
  have hvtop : (v : ℝ) < 2 := by dsimp only [v]; linarith
  obtain ⟨A, hAcarrier, hAstart, hAend⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_of_lt_top
      (a := 0) (b := 2) (x := r) (Γ := Γ) (by norm_num) hrJordan z v hzv hvtop
  have hrzero : r.val z = P := by
    rw [hr]
    simp [z, Function.comp_def, huP]
  have hrv : r.val v = Q := by
    rw [hr]
    have hvnot : ¬(v : ℝ) ≤ 1 := by dsimp only [v]; linarith
    have hθmem : (θ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := θ.property
    have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) ((v : ℝ) - 1) = θ := by
      apply Subtype.ext
      simp [v]
    simp [Function.concatUnitIntervals, hvnot, hproj, hθ, hlQ]
  refine ⟨A, ?_, hAstart.trans hrzero, hAend.trans hrv⟩
  rw [hAcarrier]
  have hrange : Set.range (ContinuousBVPaths.restrict r z v hzv).val =
      Set.range (fun w : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) ↦
        Function.concatUnitIntervals
          (x.val ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
          (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)
          ⟨w, w.property.1, w.property.2.trans (by linarith [θ.property.2])⟩) := by
    change Set.range (r.val ∘ fun w : Set.Icc (0 : ℝ) (v : ℝ) ↦
      (⟨w, w.property.1, w.property.2.trans v.property.2⟩ : Set.Icc (0 : ℝ) 2)) = _
    rw [hr]
    rfl
  rw [hrange, range_cyclicConcat_restrict_to_complement hab x.val
    hx.2.2.2.2.1 l u hal hlu hub θ hθ]
  exact image_complement_interval_of_closed_injOn hab x.val hx.2.2.2.2.1
    hx.2.2.2.2.2.1 l u hal hub

/-- If a closed parameter interval traces a nondegenerate segment injectively, its
open interval traces the segment with its endpoints removed. -/
theorem image_Ioo_eq_segment_diff_endpoints_of_image_Icc
    {a b : ℝ} {x : Set.Icc a b → Point}
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x l = Q) (hu : x u = P)
    (himage : x '' Set.Icc l u = segment ℝ P Q) :
    x '' {z | l < z ∧ z < u} = segment ℝ P Q \ {P, Q} := by
  apply Set.Subset.antisymm
  · rintro p ⟨z, hz, rfl⟩
    refine ⟨himage ▸ ⟨z, ⟨hz.1.le, hz.2.le⟩, rfl⟩, ?_⟩
    intro hp
    rcases hp with hp | hp
    · have hzu := hinj (show (z : ℝ) < b from lt_trans hz.2 hub) hub
        (hp.trans hu.symm)
      exact (ne_of_lt hz.2) hzu
    · have hzl := hinj (show (z : ℝ) < b from lt_trans hz.2 hub)
        (show (l : ℝ) < b from lt_trans hlu hub) (hp.trans hl.symm)
      exact (ne_of_gt hz.1) hzl
  · rintro p ⟨hpseg, hpends⟩
    rw [← himage] at hpseg
    obtain ⟨z, hz, rfl⟩ := hpseg
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · refine lt_of_le_of_ne hz.1 ?_
      intro h
      apply hpends
      exact Or.inr ((congrArg x h).symm.trans hl)
    · refine lt_of_le_of_ne hz.2 ?_
      intro h
      apply hpends
      exact Or.inl ((congrArg x h).trans hu)

private theorem exists_rectifiableOrientedArc_of_cut_parametrization
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x.val l = Q) (hu : x.val u = P)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  obtain ⟨A, hA, hstart, hend⟩ :=
    exists_complementary_rectifiableOrientedArc hab hx l u hal hlu hub P Q hl hu
  refine ⟨A, ?_, hstart, hend⟩
  rw [hA, hx.2.2.2.1, hfrontier,
    image_Ioo_eq_segment_diff_endpoints_of_image_Icc
      hx.2.2.2.2.2.1 l u hlu hub P Q hl hu himage]
  ext p
  constructor
  · rintro ⟨hp, hpnot⟩
    rcases hp with hpU | hpseg
    · exact hpU
    · have hpends : p ∈ ({P, Q} : Set Point) := by
        by_contra hn
        exact hpnot ⟨hpseg, hn⟩
      rw [← hinter] at hpends
      exact hpends.1
  · intro hpU
    refine ⟨Or.inl hpU, ?_⟩
    rintro ⟨hpseg, hpnotends⟩
    apply hpnotends
    rw [← hinter]
    exact ⟨hpU, hpseg⟩

/-- A nondegenerate segment in a closed Jordan curve, away from the base point,
is traced by an interior parameter interval. -/
theorem exists_parameter_interval_of_segment_subset_closedJordan
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q) (hsegment : segment ℝ P Q ⊆ Γ)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q) :
    ∃ l u : Set.Icc a b, a < l ∧ l < u ∧ (u : ℝ) < b ∧
      x.val '' Set.Icc l u = segment ℝ P Q := by
  have hcompact : IsCompact (segment ℝ P Q) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hpath : IsPathConnected (segment ℝ P Q) :=
    (convex_segment P Q).isPathConnected ⟨P, left_mem_segment ℝ P Q⟩
  have hCrange : segment ℝ P Q ⊆ Set.range x.val := by
    rw [hx.2.2.2.1]
    exact hsegment
  obtain ⟨l, u, hlu⟩ := exists_Icc_parameters_of_compact_pathConnected_subset_loop
    hab.le hab x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1
    (segment ℝ P Q) hcompact hpath hCrange hbase
  have hpre_nonempty :
      ((openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm ''
        {q : puncturedLoopRangeSet hab.le x.val | (q : Point) ∈ segment ℝ P Q}).Nonempty := by
    let q : Set.range x.val := ⟨P, hCrange (left_mem_segment ℝ P Q)⟩
    have hq : (q : Point) ≠ x.val ⟨a, le_rfl, hab.le⟩ := by
      intro heq
      exact hbase (heq ▸ left_mem_segment ℝ P Q)
    let q' : puncturedLoopRangeSet hab.le x.val := ⟨q, hq⟩
    refine ⟨(openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
      hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm q', ?_⟩
    exact ⟨q', left_mem_segment ℝ P Q, rfl⟩
  have hIcc_nonempty : (Set.Icc l u).Nonempty := by
    rw [← hlu]
    exact hpre_nonempty.image _
  have hlu_order : l ≤ u := Set.nonempty_Icc.mp hIcc_nonempty
  have hlmem : l ∈ Set.Icc l u := ⟨le_rfl, hlu_order⟩
  have humem : u ∈ Set.Icc l u := ⟨hlu_order, le_rfl⟩
  rw [← hlu] at hlmem humem
  obtain ⟨sl, hsl, hslval⟩ := hlmem
  obtain ⟨su, hsu, hsuval⟩ := humem
  change (sl : ℝ) = l at hslval
  change (su : ℝ) = u at hsuval
  let l' : Set.Icc a b := ⟨sl, sl.property.1.le, sl.property.2.le⟩
  let u' : Set.Icc a b := ⟨su, su.property.1.le, su.property.2.le⟩
  have hlstrict : a < (l' : ℝ) := sl.property.1
  have hustricttop : (u' : ℝ) < b := su.property.2
  have hlu' : l' ≤ u' := by
    change (sl : ℝ) ≤ su
    linarith
  have himage : x.val '' Set.Icc l' u' = segment ℝ P Q := by
    apply Set.Subset.antisymm
    · rintro p ⟨s, hs, rfl⟩
      let si : Set.Ioo a b := ⟨s, lt_of_lt_of_le hlstrict hs.1,
        lt_of_le_of_lt hs.2 hustricttop⟩
      have hscoord : (s : ℝ) ∈
          (fun z : Set.Ioo a b ↦ (z : ℝ)) ''
            ((openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
              hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm ''
              {q : puncturedLoopRangeSet hab.le x.val |
                (q : Point) ∈ segment ℝ P Q}) := by
        rw [hlu]
        change l ≤ (s : ℝ) ∧ (s : ℝ) ≤ u
        constructor
        · calc l = (sl : ℝ) := hslval.symm
               _ ≤ s := hs.1
        · calc (s : ℝ) ≤ su := hs.2
               _ = u := hsuval
      obtain ⟨z, hz, hzval⟩ := hscoord
      obtain ⟨q, hqseg, hzq⟩ := hz
      have hzcoe := openIntervalHomeomorphPuncturedRange_coe hab.le hab x.val
        x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 z
      have hzs : z = si := Subtype.ext hzval
      rw [hzs] at hzcoe hzq
      let e := openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1
      have heq : e si = q := by
        exact e.eq_symm_apply.mp hzq.symm
      have heq' := congrArg (fun z : puncturedLoopRangeSet hab.le x.val ↦ (z : Point)) heq
      rw [hzcoe] at heq'
      change (q : Point) ∈ segment ℝ P Q at hqseg
      have heq'' : x.val s = (q : Point) := by simpa [si] using heq'
      rw [heq'']
      exact hqseg
    · intro p hp
      let q : Set.range x.val := ⟨p, hCrange hp⟩
      have hqbase : (q : Point) ≠ x.val ⟨a, le_rfl, hab.le⟩ := by
        intro heq
        exact hbase (heq ▸ hp)
      let q' : puncturedLoopRangeSet hab.le x.val := ⟨q, hqbase⟩
      let s := (openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm q'
      have hscoord : (s : ℝ) ∈ Set.Icc l u := by
        rw [← hlu]
        exact ⟨s, ⟨q', hp, rfl⟩, rfl⟩
      let s' : Set.Icc a b := ⟨s, s.property.1.le, s.property.2.le⟩
      refine ⟨s', ?_, ?_⟩
      · change l' ≤ s' ∧ s' ≤ u'
        constructor <;> change (_ : ℝ) ≤ _ <;> dsimp only [l', u', s'] <;>
          linarith [hscoord.1, hscoord.2]
      have hscoe := openIntervalHomeomorphPuncturedRange_coe hab.le hab x.val
        x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 s
      let e := openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1
      have heq : e s = q' := e.apply_symm_apply q'
      have heq' := congrArg (fun z : puncturedLoopRangeSet hab.le x.val ↦ (z : Point)) heq
      exact hscoe.symm.trans heq'
  have hlune : l' ≠ u' := by
    intro heq
    have hsingle : segment ℝ P Q = {x.val l'} := by
      rw [← himage, heq, Set.Icc_self, Set.image_singleton]
    have hPm : P ∈ ({x.val l'} : Set Point) := hsingle ▸ left_mem_segment ℝ P Q
    have hQm : Q ∈ ({x.val l'} : Set Point) := hsingle ▸ right_mem_segment ℝ P Q
    exact hPQ (by simpa using hPm.trans hQm.symm)
  exact ⟨l', u', hlstrict, lt_of_le_of_ne hlu' hlune,
    hustricttop, himage⟩

private theorem inner_sub_right_injOn_segment (P Q : Point) (hPQ : P ≠ Q) :
    Set.InjOn (fun p : Point ↦ inner ℝ (p - P) (Q - P)) (segment ℝ P Q) := by
  intro p hp q hq hpq
  rw [segment_eq_image' ℝ P Q] at hp hq
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  have hd : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hnorm : 0 < ‖Q - P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hst : s = t := by
    simp only [add_sub_cancel_left, inner_smul_left, real_inner_self_eq_norm_sq] at hpq
    have hpq' : s * ‖Q - P‖ ^ 2 = t * ‖Q - P‖ ^ 2 := by simpa using hpq
    nlinarith
  rw [hst]

private theorem exists_rectifiableOrientedArc_reverse (A : RectifiableOrientedArc) :
    ∃ B : RectifiableOrientedArc,
      B.val.carrier = A.val.carrier ∧ B.val.startPoint = A.val.endPoint ∧
        B.val.endPoint = A.val.startPoint := by
  let p := Classical.choice A.property
  let r := Set.Icc.reverse p.ordered
  let y : ContinuousBVPaths p.a p.b :=
    ⟨p.path.val ∘ r, p.path.property.1.comp (Set.Icc.continuous_reverse p.ordered),
      fun i ↦ BoundedVariationOn.comp_antitone_surjective_Icc p.ordered
        (p.path.property.2 i) (Set.Icc.antitone_reverse p.ordered)
          (Set.Icc.surjective_reverse p.ordered)⟩
  have hyinj : Function.Injective y.val :=
    p.injective.comp (Set.Icc.involutive_reverse p.ordered).injective
  have hyrange : Set.range y.val = A.val.carrier := by
    have hrange : Set.range y.val = Set.range p.path.val := by
      apply Set.Subset.antisymm
      · rintro z ⟨t, rfl⟩
        exact ⟨r t, rfl⟩
      · rintro z ⟨t, rfl⟩
        obtain ⟨s, hs⟩ := Set.Icc.surjective_reverse p.ordered t
        refine ⟨s, ?_⟩
        change p.path.val (r s) = p.path.val t
        rw [show r s = t by exact hs]
    rw [hrange]
    exact p.range_eq
  have hystart : y.val ⟨p.a, le_rfl, p.ordered⟩ = A.val.endPoint := by
    simpa [y, r, Set.Icc.reverse] using p.end_eq
  have hyend : y.val ⟨p.b, p.ordered, le_rfl⟩ = A.val.startPoint := by
    simpa [y, r, Set.Icc.reverse] using p.start_eq
  let B0 : OrientedJordanArc :=
    { carrier := A.val.carrier
      startPoint := A.val.endPoint
      endPoint := A.val.startPoint
      parametrizable := ⟨p.a, p.b, p.ordered, y.val, y.property.1, hyinj,
        hyrange, hystart, hyend⟩ }
  let q : ArcBVParametrization B0 :=
    { a := p.a
      b := p.b
      ordered := p.ordered
      path := y
      injective := hyinj
      range_eq := hyrange
      start_eq := hystart
      end_eq := hyend }
  exact ⟨⟨B0, ⟨q⟩⟩, rfl, rfl, rfl⟩

/-- The endpoints of an injectively parametrized nondegenerate segment are the
parameter-interval endpoints, in one of the two possible orders. -/
theorem endpoints_eq_or_eq_swap_of_image_Icc_eq_segment
    {a b : ℝ} {x : ContinuousBVPaths a b}
    (hab : a ≤ b) (hinj : Set.InjOn x.val {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hPQ : P ≠ Q)
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    (x.val l = P ∧ x.val u = Q) ∨ (x.val l = Q ∧ x.val u = P) := by
  let f : ℝ → ℝ := fun t ↦
    inner ℝ (x.val (Set.projIcc a b hab t) - P) (Q - P)
  have hf_cont : Continuous f := by
    exact (x.property.1.comp continuous_projIcc).sub continuous_const |>.inner
      continuous_const
  have hproj (t : ℝ) (ht : t ∈ Set.Icc (l : ℝ) u) :
      Set.projIcc a b hab t =
        ⟨t, l.property.1.trans ht.1, ht.2.trans u.property.2⟩ := by
    exact Set.projIcc_of_mem hab ⟨l.property.1.trans ht.1, ht.2.trans u.property.2⟩
  have hparam (t : ℝ) (ht : t ∈ Set.Icc (l : ℝ) u) :
      x.val (Set.projIcc a b hab t) ∈ segment ℝ P Q := by
    rw [← himage]
    refine ⟨⟨t, l.property.1.trans ht.1, ht.2.trans u.property.2⟩, ?_, ?_⟩
    · exact ht
    · apply congrArg x.val
      apply Subtype.ext
      exact congrArg Subtype.val (hproj t ht).symm
  have hf_inj : Set.InjOn f (Set.Icc (l : ℝ) u) := by
    intro s hs t ht hst
    have hxs := inner_sub_right_injOn_segment P Q hPQ
      (hparam s hs) (hparam t ht) hst
    have hst' := hinj
      (show ((Set.projIcc a b hab s : Set.Icc a b) : ℝ) < b by
        simpa [hproj s hs] using lt_of_le_of_lt hs.2 hub)
      (show ((Set.projIcc a b hab t : Set.Icc a b) : ℝ) < b by
        simpa [hproj t ht] using lt_of_le_of_lt ht.2 hub)
      hxs
    simpa [hproj s hs, hproj t ht] using congrArg Subtype.val hst'
  have hmono := ContinuousOn.strictMonoOn_of_injOn_Icc'
    (show (l : ℝ) ≤ u from hlu.le) hf_cont.continuousOn hf_inj
  have hP : P ∈ x.val '' Set.Icc l u := himage ▸ left_mem_segment ℝ P Q
  have hQ : Q ∈ x.val '' Set.Icc l u := himage ▸ right_mem_segment ℝ P Q
  obtain ⟨s, hs, hsP⟩ := hP
  obtain ⟨t, ht, htQ⟩ := hQ
  have hs' : (s : ℝ) ∈ Set.Icc (l : ℝ) u := hs
  have ht' : (t : ℝ) ∈ Set.Icc (l : ℝ) u := ht
  have hl' : (l : ℝ) ∈ Set.Icc (l : ℝ) u := ⟨le_rfl, hlu.le⟩
  have hu' : (u : ℝ) ∈ Set.Icc (l : ℝ) u := ⟨hlu.le, le_rfl⟩
  rcases hmono with hmono | hanti
  · left
    constructor
    · have hfls : f l ≤ f s := hmono.monotoneOn hl' hs' hs.1
      have hflP : f l = f s := by
        have hnonneg : 0 ≤ f l := by
          have hmem := hparam l hl'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hrl⟩ := hmem
          dsimp only [f]
          rw [← hrl]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_nonneg hr.1 (sq_nonneg _)
        have hfs : f s = 0 := by simp [f, hproj s hs', hsP]
        linarith
      simpa [hproj l hl'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam l hl') (hparam s hs') hflP |>.trans
            (by simpa [hproj s hs'] using hsP))
    · have hftu : f t ≤ f u := hmono.monotoneOn ht' hu' ht.2
      have hfuQ : f u = f t := by
        have hupper : f u ≤ ‖Q - P‖ ^ 2 := by
          have hmem := hparam u hu'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hru⟩ := hmem
          dsimp only [f]
          rw [← hru]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_le_of_le_one_left (sq_nonneg _) hr.2
        have hft : f t = ‖Q - P‖ ^ 2 := by
          simp [f, hproj t ht', htQ]
        linarith
      simpa [hproj u hu'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam u hu') (hparam t ht') hfuQ |>.trans
            (by simpa [hproj t ht'] using htQ))
  · right
    constructor
    · have hftl : f t ≤ f l := hanti.antitoneOn hl' ht' ht.1
      have hflQ : f l = f t := by
        have hupper : f l ≤ ‖Q - P‖ ^ 2 := by
          have hmem := hparam l hl'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hrl⟩ := hmem
          dsimp only [f]
          rw [← hrl]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_le_of_le_one_left (sq_nonneg _) hr.2
        have hft : f t = ‖Q - P‖ ^ 2 := by
          simp [f, hproj t ht', htQ]
        linarith
      simpa [hproj l hl'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam l hl') (hparam t ht') hflQ |>.trans
            (by simpa [hproj t ht'] using htQ))
    · have hfus : f u ≤ f s := hanti.antitoneOn hs' hu' hs.2
      have hfuP : f u = f s := by
        have hnonneg : 0 ≤ f u := by
          have hmem := hparam u hu'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hru⟩ := hmem
          dsimp only [f]
          rw [← hru]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_nonneg hr.1 (sq_nonneg _)
        have hfs : f s = 0 := by simp [f, hproj s hs', hsP]
        linarith
      simpa [hproj u hu'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam u hu') (hparam s hs') hfuP |>.trans
            (by simpa [hproj s hs'] using hsP))

/-- Removing a supporting chord from a counterclockwise closed Jordan path yields the oriented
complementary arc. -/
theorem exists_rectifiableOrientedArc_of_closedJordan_cut
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q}) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  have hsegment : segment ℝ P Q ⊆ Γ := by
    rw [hfrontier]
    exact Set.subset_union_right
  obtain ⟨l, u, hal, hlu, hub, himage⟩ :=
    exists_parameter_interval_of_segment_subset_closedJordan hab hx P Q hPQ hsegment hbase
  rcases endpoints_eq_or_eq_swap_of_image_Icc_eq_segment hab.le
      hx.2.2.2.2.2.1 l u hlu hub P Q hPQ himage with hend | hend
  · have hfrontier' : Γ = U ∪ segment ℝ Q P := by
      simpa only [segment_symm ℝ Q P] using hfrontier
    have hinter' : U ∩ segment ℝ Q P = {Q, P} := by
      rw [segment_symm ℝ Q P, hinter]
      exact Set.pair_comm P Q
    have himage' : x.val '' Set.Icc l u = segment ℝ Q P := by
      simpa only [segment_symm ℝ Q P] using himage
    obtain ⟨A, hA, hstart, hend'⟩ :=
      exists_rectifiableOrientedArc_of_cut_parametrization hab.le hx l u hal hlu hub
        Q P hend.1 hend.2 hfrontier' hinter' himage'
    obtain ⟨B, hB, hBstart, hBend⟩ := exists_rectifiableOrientedArc_reverse A
    exact ⟨B, hB.trans hA, hBstart.trans hend', hBend.trans hstart⟩
  · exact exists_rectifiableOrientedArc_of_cut_parametrization hab.le hx l u hal hlu hub
      P Q hend.1 hend.2 hfrontier hinter himage

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Reparametrization
-/

public section

namespace MovingSofa

theorem curveArea_reparametrization :
    (∀ (a b c d : ℝ), a < b → c < d →
      ∀ (x : ContinuousBVPaths a b) (φ : Set.Icc c d → Set.Icc a b),
      Continuous φ → Function.Surjective φ → (Monotone φ ∨ Antitone φ) →
      ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ ∧
        (Monotone φ → curveAreaFunctional y = curveAreaFunctional x) ∧
        (Antitone φ → curveAreaFunctional y = -curveAreaFunctional x)) ∧
    (∀ (Γ Δ : OrientedJordanArc) (x : ArcBVParametrization Γ)
      (y : ArcBVParametrization Δ), Γ.carrier = Δ.carrier →
      (Γ.startPoint = Δ.startPoint → Γ.endPoint = Δ.endPoint →
        curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
      (Γ.startPoint = Δ.endPoint → Γ.endPoint = Δ.startPoint →
        curveAreaFunctional x.path = -curveAreaFunctional y.path)) ∧
    (∀ (Γ Δ : OrientedJordanCurve) (x : ClosedBVParametrization Γ)
      (y : ClosedBVParametrization Δ), Γ.carrier = Δ.carrier →
      (Γ.counterclockwise = Δ.counterclockwise →
        curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
      (Γ.counterclockwise ≠ Δ.counterclockwise →
        curveAreaFunctional x.path = -curveAreaFunctional y.path)) ∧
    (∀ (a b : ℝ) (x : ContinuousBVPaths a b) (p : Point),
      (∀ t, x.val t = p) → curveAreaFunctional x = 0) := by
  refine ⟨?_, curveArea_arc_same_carrier, ?_, ?_⟩
  · intro a b c d hab hcd x φ hφc hφs hφ
    exact curveArea_comp_monotone_or_antitone_surjective hab.le hcd.le x φ hφc hφs hφ
  · exact curveArea_closed_same_carrier
  · intro a b x p hx
    exact curveAreaFunctional_eq_zero_of_constant x p hx

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Segment Area Properties
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

theorem segmentArea_jordan_and_frame (p q : Point) :
    (∃ A : RectifiableOrientedArc,
      A.val.carrier = segment ℝ p q ∧ A.val.startPoint = p ∧ A.val.endPoint = q ∧
      jordanArcArea A = segmentArea p q) ∧
    (∀ (t : Real.Angle) (h d : ℝ), p ∈ normalLine t h → q ∈ normalLine t h →
      q - p = d • tangentVector t → segmentArea p q = h * d / 2) := by
  constructor
  · by_cases hpq : p = q
    · subst q
      let Γ : OrientedJordanArc :=
        { carrier := segment ℝ p p
          startPoint := p
          endPoint := p
          parametrizable := by
            refine ⟨0, 0, le_rfl, (constBVPath 0 0 p).val,
              (constBVPath 0 0 p).property.1, ?_, ?_, rfl, rfl⟩
            · intro s t _
              apply Subtype.ext
              exact le_antisymm (s.property.2.trans t.property.1)
                (t.property.2.trans s.property.1)
            · simp [constBVPath] }
      let z : ArcBVParametrization Γ :=
        { a := 0
          b := 0
          ordered := le_rfl
          path := constBVPath 0 0 p
          injective := by
            intro s t _
            apply Subtype.ext
            exact le_antisymm (s.property.2.trans t.property.1)
              (t.property.2.trans s.property.1)
          range_eq := by simp [constBVPath, Γ]
          start_eq := rfl
          end_eq := rfl }
      let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
      refine ⟨A, rfl, rfl, rfl, ?_⟩
      change curveAreaFunctional (Classical.choice A.property).path = segmentArea p p
      calc
        _ = curveAreaFunctional z.path :=
          (curveArea_reparametrization.2.1 Γ Γ
            (Classical.choice A.property) z rfl).1 rfl rfl
        _ = 0 := curveArea_reparametrization.2.2.2 0 0 z.path p (by intro t; rfl)
        _ = segmentArea p p := by simp [segmentArea, planeCrossProduct]; ring
    · let Γ : OrientedJordanArc :=
        { carrier := segment ℝ p q
          startPoint := p
          endPoint := q
          parametrizable := by
            refine ⟨0, 1, by norm_num, Path.segment p q,
              (Path.segment p q).continuous, Path.segment_injective_of_ne hpq,
              Path.range_segment p q, ?_, ?_⟩
            · simp
            · simp }
      let z : ArcBVParametrization Γ :=
        { a := 0
          b := 1
          ordered := by norm_num
          path := lineSegmentBVPath p q
          injective := Path.segment_injective_of_ne hpq
          range_eq := Path.range_segment p q
          start_eq := by simp [lineSegmentBVPath, Γ]
          end_eq := by simp [lineSegmentBVPath, Γ] }
      let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
      refine ⟨A, rfl, rfl, rfl, ?_⟩
      change curveAreaFunctional (Classical.choice A.property).path = segmentArea p q
      calc
        _ = curveAreaFunctional z.path :=
          (curveArea_reparametrization.2.1 Γ Γ
            (Classical.choice A.property) z rfl).1 rfl rfl
        _ = segmentArea p q := curveAreaFunctional_lineSegmentBVPath p q
  · intro t h d hp hq hd
    simp only [normalLine, Set.mem_ofPred_eq, segmentArea, planeCrossProduct] at hp hq ⊢
    have hd0 := congrArg (fun x : Point => x 0) hd
    have hd1 := congrArg (fun x : Point => x 1) hd
    simp only [normalVector, frame, Fin.isValue, PiLp.sub_apply, tangentVector, PiLp.smul_apply,
      Matrix.cons_val_zero, smul_eq_mul, mul_neg, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj'] at hp hq hd0 hd1 ⊢
    rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply] at hp hq
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hp hq
    have hq0 : q.ofLp 0 = p.ofLp 0 - d * t.sin := by linarith [hd0]
    have hq1 : q.ofLp 1 = p.ofLp 1 + d * t.cos := by linarith [hd1]
    rw [hq0, hq1]
    calc
      p.ofLp 0 * (p.ofLp 1 + d * t.cos) - p.ofLp 1 * (p.ofLp 0 - d * t.sin) =
          d * (p.ofLp 0 * t.cos + p.ofLp 1 * t.sin) := by ring
      _ = d * h := by rw [hp]
      _ = h * d := by ring

theorem segmentArea_collinear_origin (p q : Point)
    (h : Collinear ℝ ({0, p, q} : Set Point)) : segmentArea p q = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : (0 : Point) ∈ ({0, p, q} : Set Point))).mp h
  obtain ⟨a, ha⟩ := hv p (by simp)
  obtain ⟨b, hb⟩ := hv q (by simp)
  simp only [vadd_eq_add, add_zero] at ha hb
  rw [ha, hb]
  simp [segmentArea, planeCrossProduct]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Subarc Area
-/

public section

noncomputable section

namespace MovingSofa

open Set
/-- A proper restriction of a closed BV Jordan parametrization realizes an arc with the same
signed area as the restricted path. -/
theorem exists_rectifiableOrientedArc_restrict_closedJordan_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hlu : l ≤ u) (hub : (u : ℝ) < b) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range (ContinuousBVPaths.restrict x l u hlu).val ∧
      A.val.startPoint = x.val l ∧ A.val.endPoint = x.val u ∧
      jordanArcArea A =
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu) := by
  let y := ContinuousBVPaths.restrict x l u hlu
  have hyinj : Function.Injective y.val := by
    intro s t hst
    apply Subtype.ext
    have hs : (s : ℝ) < b := lt_of_le_of_lt s.property.2 hub
    have ht : (t : ℝ) < b := lt_of_le_of_lt t.property.2 hub
    have h := hx.2.2.2.2.2.1 hs ht hst
    exact congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) h
  let A0 : OrientedJordanArc :=
    { carrier := Set.range y.val
      startPoint := x.val l
      endPoint := x.val u
      parametrizable := ⟨l, u, hlu, y.val, y.property.1, hyinj, rfl, rfl, rfl⟩ }
  let p : ArcBVParametrization A0 :=
    { a := l, b := u, ordered := hlu, path := y, injective := hyinj,
      range_eq := rfl, start_eq := rfl, end_eq := rfl }
  let A : RectifiableOrientedArc := ⟨A0, ⟨p⟩⟩
  refine ⟨A, rfl, rfl, rfl, ?_⟩
  change curveAreaFunctional (Classical.choice A.property).path = curveAreaFunctional y
  exact (curveArea_reparametrization.2.1 A0 A0
    (Classical.choice A.property) p rfl).1 rfl rfl

/-- The suffix of the cyclic rotation, after the complementary arc, is an increasing
reparametrization of the removed interval. -/
theorem curveArea_cyclicSuffix_eq_restriction
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u)
    (θ : Set.Icc (0 : ℝ) 1)
    (hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l)
    (r : ContinuousBVPaths 0 2)
    (hr : r.val = Function.concatUnitIntervals
      (x.val ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
      (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)) :
    let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
      constructor <;> linarith [θ.property.1, θ.property.2]⟩
    curveAreaFunctional (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2) =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
  let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
    constructor <;> linarith [θ.property.1, θ.property.2]⟩
  change curveAreaFunctional (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩
      v.property.2) =
    curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le)
  have hθlt : (θ : ℝ) < 1 := by
    by_contra hn
    have hθone : (θ : ℝ) = 1 := le_antisymm θ.property.2 (le_of_not_gt hn)
    have h := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθone] at h
    exact hlu.ne (Subtype.ext h.symm)
  have hθpos_suffix : 0 < (θ : ℝ) := by
    by_contra hn
    have hθzero : (θ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) θ.property.1
    have h := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθzero] at h
    linarith
  have hvlt : (v : ℝ) < 2 := by dsimp only [v]; linarith
  let ψ : Set.Icc (v : ℝ) 2 → Set.Icc (0 : ℝ) 1 := fun w ↦
    ⟨((w : ℝ) - (v : ℝ)) / (2 - (v : ℝ)), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr w.property.1) (sub_nonneg.mpr hvlt.le)
      · exact (div_le_one (sub_pos.mpr hvlt)).2
          (sub_le_sub_right w.property.2 (v : ℝ))⟩
  let φ : Set.Icc (v : ℝ) 2 → Set.Icc (l : ℝ) u := fun w ↦
    Set.Icc.convexComb (⟨l, le_rfl, hlu.le⟩ : Set.Icc (l : ℝ) u)
      ⟨u, hlu.le, le_rfl⟩ (ψ w)
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    fun_prop
  have hψm : Monotone ψ := by
    intro s t hst
    apply Subtype.coe_le_coe.mp
    dsimp only [ψ]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (show (s : ℝ) ≤ t from hst) _) (sub_nonneg.mpr hvlt.le)
  have hψs : Function.Surjective ψ := by
    intro q
    let w : Set.Icc (v : ℝ) 2 := ⟨(v : ℝ) + (2 - (v : ℝ)) * (q : ℝ), by
      constructor
      · nlinarith [q.property.1, sub_pos.mpr hvlt]
      · nlinarith [q.property.2, sub_pos.mpr hvlt]⟩
    refine ⟨w, Subtype.ext ?_⟩
    dsimp only [ψ, w]
    field_simp [ne_of_gt (sub_pos.mpr hvlt)]
    ring
  have hφc : Continuous φ :=
    (Set.Icc.continuous_convexComb _ _).comp hψc
  have hφm : Monotone φ := by
    intro s t hst
    change (1 - (ψ s : ℝ)) * (l : ℝ) + (ψ s : ℝ) * (u : ℝ) ≤
      (1 - (ψ t : ℝ)) * (l : ℝ) + (ψ t : ℝ) * (u : ℝ)
    have hψ := show (ψ s : ℝ) ≤ ψ t from hψm hst
    nlinarith [show (l : ℝ) < u from hlu]
  have hφs : Function.Surjective φ :=
    (surjective_convexComb_endpoints (l : ℝ) u hlu.le).comp hψs
  let xu := ContinuousBVPaths.restrict x l u hlu.le
  obtain ⟨y, hy, hyarea⟩ := curveArea_comp_monotone_surjective
    hlu.le v.property.2 xu φ hφc hφm hφs
  have hyval : y.val = (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩
      v.property.2).val := by
    rw [hy]
    funext w
    simp only [xu, ContinuousBVPaths.restrict, Function.comp_apply]
    rw [hr]
    have hwlow : 1 + (θ : ℝ) ≤ (w : ℝ) := w.property.1
    have hwsub : (w : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [w.property.2]
    have hwnle : ¬(w : ℝ) ≤ 1 := by
      linarith
    simp only [Function.concatUnitIntervals, hwnle, ↓reduceIte,
      Set.projIcc_of_mem (by norm_num) hwsub]
    apply congrArg x.val
    apply Subtype.ext
    have hθval := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
    dsimp only [φ, ψ]
    simp only [Set.Icc.coe_convexComb]
    dsimp only [v]
    rw [← hθval]
    have hdenne : 2 - (1 + (θ : ℝ)) ≠ 0 := by linarith
    field_simp [hdenne]
    ring
  have hyEq : y = ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2 := by
    ext w i
    exact congrArg (fun z : Point ↦ z i) (congrFun hyval w)
  rw [← hyEq, hyarea]

private theorem exists_complementary_rectifiableOrientedArc_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hlQ : x.val l = Q) (huP : x.val u = P) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range x.val \ x.val '' {z | l < z ∧ z < u} ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A +
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
  let l' : Set.Icc a (u : ℝ) := ⟨l, l.property.1, hlu.le⟩
  obtain ⟨θ, hθ'⟩ := surjective_convexComb_endpoints a u
    (le_trans l.property.1 hlu.le) l'
  have hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l := by
    apply Subtype.ext
    have h := congrArg (fun z : Set.Icc a (u : ℝ) ↦ (z : ℝ)) hθ'
    simpa only [Set.Icc.coe_convexComb] using h
  have hθpos : 0 < (θ : ℝ) := by
    by_contra hn
    have hθzero : (θ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) θ.property.1
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθzero] at h
    linarith
  have hθlt : (θ : ℝ) < 1 := by
    by_contra hn
    have hθone : (θ : ℝ) = 1 := le_antisymm θ.property.2 (le_of_not_gt hn)
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθone] at h
    exact hlu.ne (Subtype.ext h.symm)
  obtain ⟨r, hrJordan, hr⟩ :=
    exists_oriented_cyclic_rotation_eq_concat hab x hx u
      (hal.trans hlu) hub
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
    constructor <;> linarith⟩
  have hzv : z ≤ v := by change (0 : ℝ) ≤ 1 + θ; linarith
  have hvtop : (v : ℝ) < 2 := by dsimp only [v]; linarith
  obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_with_area
      (a := 0) (b := 2) (x := r) (Γ := Γ) (by norm_num) hrJordan z v hzv hvtop
  have hrzero : r.val z = P := by
    rw [hr]
    simp [z, Function.comp_def, huP]
  have hrv : r.val v = Q := by
    rw [hr]
    have hvnot : ¬(v : ℝ) ≤ 1 := by dsimp only [v]; linarith
    have hθmem : (θ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := θ.property
    have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) ((v : ℝ) - 1) = θ := by
      apply Subtype.ext
      simp [v]
    simp [Function.concatUnitIntervals, hvnot, hproj, hθ, hlQ]
  have hcarrier : A.val.carrier =
      Set.range x.val \ x.val '' {z | l < z ∧ z < u} := by
    rw [hAcarrier]
    have hrange : Set.range (ContinuousBVPaths.restrict r z v hzv).val =
        Set.range (fun w : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) ↦
          Function.concatUnitIntervals
            (x.val ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
            (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)
            ⟨w, w.property.1, w.property.2.trans (by linarith [θ.property.2])⟩) := by
      change Set.range (r.val ∘ fun w : Set.Icc (0 : ℝ) (v : ℝ) ↦
        (⟨w, w.property.1, w.property.2.trans v.property.2⟩ : Set.Icc (0 : ℝ) 2)) = _
      rw [hr]
      rfl
    rw [hrange, range_cyclicConcat_restrict_to_complement hab x.val
      hx.2.2.2.2.1 l u hal hlu hub θ hθ]
    exact image_complement_interval_of_closed_injOn hab x.val hx.2.2.2.2.1
      hx.2.2.2.2.2.1 l u hal hub
  have hsuffix : curveAreaFunctional
      (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2) =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) :=
    curveArea_cyclicSuffix_eq_restriction hab x l u hal hlu θ hθ r hr
  obtain ⟨r', hr', _, hrotate'⟩ :=
    exists_cyclic_rotation_eq_concat hab x u hx.2.2.2.2.1.symm
  have hrr : r = r' := by
    ext w i
    exact congrArg (fun z : Point ↦ z i) (congrFun (hr.trans hr'.symm) w)
  have hrotate : curveAreaFunctional r = curveAreaFunctional x := by
    rw [hrr]
    exact hrotate'
  have hsplit := curveArea_eq_restriction_add_restriction (by norm_num) r v
  dsimp only at hsplit
  refine ⟨A, hcarrier, hAstart.trans hrzero, hAend.trans hrv, ?_⟩
  rw [← hrotate, hsplit, ← hAarea, hsuffix]

private theorem exists_rectifiableOrientedArc_of_cut_parametrization_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x.val l = Q) (hu : x.val u = P)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A +
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
  obtain ⟨A, hA, hstart, hend, harea⟩ :=
    exists_complementary_rectifiableOrientedArc_with_area
      hab hx l u hal hlu hub P Q hl hu
  refine ⟨A, ?_, hstart, hend, harea⟩
  rw [hA, hx.2.2.2.1, hfrontier,
    image_Ioo_eq_segment_diff_endpoints_of_image_Icc
      hx.2.2.2.2.2.1 l u hlu hub P Q hl hu himage]
  ext p
  constructor
  · rintro ⟨hp, hpnot⟩
    rcases hp with hpU | hpseg
    · exact hpU
    · have hpends : p ∈ ({P, Q} : Set Point) := by
        by_contra hn
        exact hpnot ⟨hpseg, hn⟩
      rw [← hinter] at hpends
      exact hpends.1
  · intro hpU
    refine ⟨Or.inl hpU, ?_⟩
    rintro ⟨hpseg, hpnotends⟩
    apply hpnotends
    rw [← hinter]
    exact ⟨hpU, hpseg⟩

theorem endpoints_eq_of_counterclockwise_supporting_chord
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hPQ : P ≠ Q)
    (himage : x.val '' Set.Icc l u = segment ℝ P Q)
    (θ : Real.Angle) (h : ℝ)
    (hhalf : Γ ⊆ normalHalfPlane θ h false false)
    (hQline : Q ∈ normalLine θ h) (d : ℝ) (hd : 0 < d)
    (hdir : P = Q + d • tangentVector θ) :
    x.val l = Q ∧ x.val u = P := by
  rcases endpoints_eq_or_eq_swap_of_image_Icc_eq_segment hab.le
      hx.2.2.2.2.2.1 l u hlu hub P Q hPQ himage with hbad | hgood
  · exfalso
    let r := Set.Icc.reverse hab.le
    let y : Set.Icc a b → Point := x.val ∘ r
    let l' := r u
    let u' := r l
    have hl'u' : l' < u' := by
      have hlu' : (l : ℝ) < u := hlu
      change a + b - (u : ℝ) < a + b - (l : ℝ)
      linarith
    have hyrange : Set.range y = Γ := by
      rw [show Set.range y = Set.range x.val by
        apply Set.Subset.antisymm
        · rintro z ⟨s, rfl⟩; exact ⟨r s, rfl⟩
        · rintro z ⟨s, rfl⟩
          obtain ⟨q, hq⟩ := Set.Icc.surjective_reverse hab.le s
          exact ⟨q, by simpa [y, r] using congrArg x.val hq⟩]
      exact hx.2.2.2.1
    have hyl : y l' = Q := by
      change x.val (r (r u)) = Q
      rw [show r (r u) = u by exact Set.Icc.involutive_reverse hab.le u, hbad.2]
    have hyu : y u' = P := by
      change x.val (r (r l)) = P
      rw [show r (r l) = l by exact Set.Icc.involutive_reverse hab.le l, hbad.1]
    have hytrue := jordan_counterclockwise_of_supporting_segment a b hab y
      (hx.2.2.1.comp (Set.Icc.continuous_reverse hab.le))
      (by rw [hyrange]; exact hx.2.1)
      (by simpa [y, r, Set.Icc.reverse] using hx.2.2.2.2.1.symm)
      (injOn_comp_reverse_of_closed_injOn hab x.val hx.2.2.2.2.1
        hx.2.2.2.2.2.1) θ h
      (fun z ↦ hhalf (by rw [← hyrange]; exact Set.mem_range_self z)) l' u' hl'u'
      (by rw [hyl]; exact hQline) d hd
      (by rw [hyl, hyu, hdir])
      (by rw [image_Icc_reverse_interval hab.le x.val l u hlu.le, himage,
        segment_symm ℝ P Q, hyl, hyu])
    rw [hyrange] at hytrue
    have horient := hx.orientation_eq_not_of_comp hytrue r
      (Set.Icc.continuous_reverse hab.le) (by simp [r, Set.Icc.reverse])
      (by simp [r, Set.Icc.reverse]) rfl
    norm_num at horient
  · exact hgood

/-- Removing a supporting chord from a counterclockwise closed BV Jordan path gives the
complementary arc, and closed signed area splits into arc area and the oriented chord area. -/
theorem exists_rectifiableOrientedArc_of_supportingChord_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (θ : Real.Angle) (h : ℝ)
    (hhalf : Γ ⊆ normalHalfPlane θ h false false)
    (hQline : Q ∈ normalLine θ h) (d : ℝ) (hd : 0 < d)
    (hdir : P = Q + d • tangentVector θ) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A + segmentArea Q P := by
  have hsegment : segment ℝ P Q ⊆ Γ := by
    rw [hfrontier]
    exact Set.subset_union_right
  obtain ⟨l, u, hal, hlu, hub, himage⟩ :=
    exists_parameter_interval_of_segment_subset_closedJordan
      hab hx P Q hPQ hsegment hbase
  have hend := endpoints_eq_of_counterclockwise_supporting_chord hab hx l u hlu hub
    P Q hPQ himage θ h hhalf hQline d hd hdir
  obtain ⟨A, hA, hAstart, hAend, harea⟩ :=
    exists_rectifiableOrientedArc_of_cut_parametrization_with_area hab.le hx l u hal hlu hub
      P Q hend.1 hend.2 hfrontier hinter himage
  obtain ⟨B, hBcarrier, hBstart, hBend, hBarea⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_with_area
      hab.le hx l u hlu.le hub
  obtain ⟨S, hScarrier, hSstart, hSend, hSarea⟩ :=
    (segmentArea_jordan_and_frame Q P).1
  have hBcarrier' : B.val.carrier = segment ℝ Q P := by
    rw [hBcarrier]
    change Set.range (x.val ∘ fun z : Set.Icc (l : ℝ) u ↦
      (⟨z, le_trans l.property.1 z.property.1,
        le_trans z.property.2 u.property.2⟩ : Set.Icc a b)) = _
    rw [segment_symm ℝ Q P, ← himage]
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨z, le_trans l.property.1 z.property.1,
        le_trans z.property.2 u.property.2⟩, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hBstart' : B.val.startPoint = Q := hBstart.trans hend.1
  have hBend' : B.val.endPoint = P := hBend.trans hend.2
  have hBSarea : jordanArcArea B = jordanArcArea S := by
    change curveAreaFunctional (Classical.choice B.property).path =
      curveAreaFunctional (Classical.choice S.property).path
    exact (curveArea_reparametrization.2.1 B.val S.val
      (Classical.choice B.property) (Classical.choice S.property)
      (hBcarrier'.trans hScarrier.symm)).1
        (hBstart'.trans hSstart.symm) (hBend'.trans hSend.symm)
  refine ⟨A, hA, hAstart, hAend, ?_⟩
  rw [harea, ← hBarea, hBSarea, hSarea]

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Curve.PositiveGraphOrientation`.
* `Curve.PositiveGraphRegion`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The counterclockwise loop around a positive graph

For `a < b` and a continuous `f : ℝ → ℝ` vanishing at `a` and `b` and positive on `(a, b)`,
`MovingSofa.positiveGraphLoop` traverses the graph of `f` from `(b, 0)` to `(a, 0)` and then the
base segment from `(a, 0)` back to `(b, 0)`. The main result
`MovingSofa.positiveGraphLoop_counterclockwise` shows that this is a counterclockwise once-traversed
Jordan parametrization whose bounded complementary component is the open subgraph
`{p | a < p 0 ∧ p 0 < b ∧ 0 < p 1 ∧ p 1 < f (p 0)}`.
-/

public section

noncomputable section

namespace MovingSofa

/-- Traverse the graph from right to left and return along the horizontal axis. -/
def positiveGraphLoop (a b : ℝ) (f : ℝ → ℝ) (t : Set.Icc (0 : ℝ) 2) : Point :=
  if t.val ≤ 1 then !₂[b - (b - a) * t.val, f (b - (b - a) * t.val)]
  else !₂[a + (b - a) * (t.val - 1), 0]

/-- Every planar point is built from its two coordinates. -/
private lemma point_eq_vecNotation_coords (p : Point) : p = !₂[p 0, p 1] := by
  ext i
  fin_cases i <;> simp

section PositiveGraph

variable {a b : ℝ} {f : ℝ → ℝ}

/-- A positive graph over `[a, b]` vanishing at the ends is nonnegative there. -/
private lemma nonneg_of_pos_on_Ioo (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) {c : ℝ} (hc : c ∈ Set.Icc a b) : 0 ≤ f c := by
  rcases eq_or_lt_of_le hc.1 with h | h
  · rw [← h, ha]
  · rcases eq_or_lt_of_le hc.2 with h' | h'
    · rw [h', hb]
    · exact (hpos c ⟨h, h'⟩).le

/-- Such a graph vanishes only at the two endpoints. -/
private lemma eq_endpoint_of_apply_eq_zero (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x)
    {c : ℝ} (hc : c ∈ Set.Icc a b) (h : f c = 0) : c = a ∨ c = b := by
  by_contra hcon
  push Not at hcon
  exact (hpos c ⟨lt_of_le_of_ne hc.1 (Ne.symm hcon.1), lt_of_le_of_ne hc.2 hcon.2⟩).ne' h

/-- The reversed affine reparametrization of `[0, 1]` lands in the base interval `[a, b]`. -/
private lemma sub_mul_mem_Icc (hab : a < b) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    b - (b - a) * s ∈ Set.Icc a b := by
  obtain ⟨h0, h1⟩ := hs
  constructor <;> nlinarith [sub_pos.mpr hab]

/-- On the first half of the parameter interval the loop traverses the graph right to left. -/
lemma positiveGraphLoop_apply_of_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 2) (h : s ≤ 1) :
    positiveGraphLoop a b f ⟨s, hs⟩ = !₂[b - (b - a) * s, f (b - (b - a) * s)] :=
  ite_eq_left h

/-- On the second half of the parameter interval the loop traverses the base left to right. -/
lemma positiveGraphLoop_apply_of_not_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 2)
    (h : ¬ s ≤ 1) : positiveGraphLoop a b f ⟨s, hs⟩ = !₂[a + (b - a) * (s - 1), 0] :=
  ite_eq_right h

/-- Values of the loop on the base half, including the joining parameter. -/
private lemma positiveGraphLoop_apply_base (ha : f a = 0) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 2)
    (h1 : 1 ≤ u) : positiveGraphLoop a b f ⟨u, hu⟩ = !₂[a + (b - a) * (u - 1), 0] := by
  by_cases h : u ≤ 1
  · have hu1 : u = 1 := le_antisymm h h1
    rw [positiveGraphLoop_apply_of_le hu h, show b - (b - a) * u = a by rw [hu1]; ring, ha,
      show a + (b - a) * (u - 1) = a by rw [hu1]; ring]
  · exact positiveGraphLoop_apply_of_not_le hu h

/-- The two halves agree at the joining parameter, so the loop is continuous. -/
private lemma continuous_positiveGraphLoop (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) : Continuous (positiveGraphLoop a b f) := by
  unfold positiveGraphLoop
  apply continuous_if_le continuous_subtype_val continuous_const
  · refine (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
      (ContinuousOn.matrixVecCons (by fun_prop)
        (ContinuousOn.matrixVecCons (hf.comp (by fun_prop) ?_) continuousOn_const))
    intro t ht
    exact sub_mul_mem_Icc hab ⟨t.property.1, ht⟩
  · exact (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
      (ContinuousOn.matrixVecCons (by fun_prop)
        (ContinuousOn.matrixVecCons continuousOn_const continuousOn_const))
  · intro t ht
    have h1 : b - (b - a) * (t : ℝ) = a := by rw [ht]; ring
    have h2 : a + (b - a) * ((t : ℝ) - 1) = a := by rw [ht]; ring
    rw [h1, h2, ha]

/-- The loop traces exactly the graph of `f` together with the base segment. -/
private lemma range_positiveGraphLoop (hab : a < b) (ha : f a = 0) :
    Set.range (positiveGraphLoop a b f) =
      (fun c ↦ (!₂[c, f c] : Point)) '' Set.Icc a b ∪
        (fun c ↦ (!₂[c, (0 : ℝ)] : Point)) '' Set.Icc a b := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    obtain ⟨h0, h2⟩ := hs
    by_cases h : s ≤ 1
    · exact Or.inl ⟨_, sub_mul_mem_Icc hab ⟨h0, h⟩, (positiveGraphLoop_apply_of_le _ h).symm⟩
    · push Not at h
      exact Or.inr ⟨_, ⟨by nlinarith, by nlinarith⟩,
        (positiveGraphLoop_apply_of_not_le _ (not_le.mpr h)).symm⟩
  · rintro p (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · have h1 : (b - c) / (b - a) ≤ 1 := (div_le_one hL).mpr (by linarith [hc.1])
      have h0 : 0 ≤ (b - c) / (b - a) := div_nonneg (by linarith [hc.2]) hL.le
      have hmem : (b - c) / (b - a) ∈ Set.Icc (0 : ℝ) 2 := ⟨h0, by linarith⟩
      refine ⟨⟨(b - c) / (b - a), hmem⟩, ?_⟩
      rw [positiveGraphLoop_apply_of_le hmem h1,
        show b - (b - a) * ((b - c) / (b - a)) = c by field_simp; ring]
    · by_cases hca : c = a
      · have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by norm_num
        refine ⟨⟨1, hmem⟩, ?_⟩
        rw [positiveGraphLoop_apply_of_le hmem le_rfl,
          show b - (b - a) * (1 : ℝ) = a by ring, ha, hca]
      · have hac : a < c := lt_of_le_of_ne hc.1 (Ne.symm hca)
        have h0 : 0 < (c - a) / (b - a) := div_pos (by linarith) hL
        have h1 : (c - a) / (b - a) ≤ 1 := (div_le_one hL).mpr (by linarith [hc.2])
        have hmem : 1 + (c - a) / (b - a) ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith, by linarith⟩
        refine ⟨⟨1 + (c - a) / (b - a), hmem⟩, ?_⟩
        rw [positiveGraphLoop_apply_of_not_le hmem (by simp; linarith),
          show a + (b - a) * (1 + (c - a) / (b - a) - 1) = c by field_simp; ring]

/-- The loop is injective before its final parameter: the two halves meet only at the ends. -/
private lemma injOn_positiveGraphLoop (hab : a < b)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    Set.InjOn (positiveGraphLoop a b f) {t | (t : ℝ) < 2} := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  rintro ⟨s, hs⟩ hs2 ⟨u, hu⟩ hu2 heq
  simp only [Set.mem_ofPred_eq] at hs2 hu2
  refine Subtype.ext (show s = u from ?_)
  by_cases hsl : s ≤ 1 <;> by_cases hul : u ≤ 1
  · rw [positiveGraphLoop_apply_of_le hs hsl, positiveGraphLoop_apply_of_le hu hul] at heq
    simp only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at heq
    have h := heq.1
    nlinarith
  · exfalso
    rw [positiveGraphLoop_apply_of_le hs hsl, positiveGraphLoop_apply_of_not_le hu hul] at heq
    simp only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at heq
    push Not at hul
    rcases eq_endpoint_of_apply_eq_zero hpos (sub_mul_mem_Icc hab ⟨hs.1, hsl⟩) heq.2 with h | h
    · rw [h] at heq
      nlinarith [heq.1]
    · rw [h] at heq
      nlinarith [heq.1]
  · exfalso
    rw [positiveGraphLoop_apply_of_not_le hs hsl, positiveGraphLoop_apply_of_le hu hul] at heq
    simp only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at heq
    push Not at hsl
    rcases eq_endpoint_of_apply_eq_zero hpos (sub_mul_mem_Icc hab ⟨hu.1, hul⟩) heq.2.symm with h | h
    · rw [h] at heq
      nlinarith [heq.1]
    · rw [h] at heq
      nlinarith [heq.1]
  · rw [positiveGraphLoop_apply_of_not_le hs hsl, positiveGraphLoop_apply_of_not_le hu hul] at heq
    simp only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at heq
    nlinarith [heq]

/-- The graph arc and the base arc share exactly their endpoints, so they glue to a Jordan
curve. -/
private lemma isJordanCurve_range_positiveGraphLoop (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    IsJordanCurve (Set.range (positiveGraphLoop a b f)) := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hmapsto : ∀ u : unitInterval, b - (b - a) * (u : ℝ) ∈ Set.Icc a b :=
    fun u ↦ sub_mul_mem_Icc hab u.property
  have hcontf : Continuous fun u : unitInterval ↦ f (b - (b - a) * (u : ℝ)) :=
    continuousOn_univ.mp (hf.comp (by fun_prop) fun u _ ↦ hmapsto u)
  have hcontx : Continuous fun u : unitInterval ↦ b - (b - a) * (u : ℝ) := by fun_prop
  let γ : Path (!₂[b, (0 : ℝ)] : Point) (!₂[a, (0 : ℝ)] : Point) :=
    { toFun := fun u ↦ !₂[b - (b - a) * (u : ℝ), f (b - (b - a) * (u : ℝ))]
      continuous_toFun := (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp
        (hcontx.matrixVecCons (hcontf.matrixVecCons continuous_const))
      source' := by norm_num [hb]
      target' := by norm_num [ha] }
  let δ : Path (!₂[b, (0 : ℝ)] : Point) (!₂[a, (0 : ℝ)] : Point) :=
    { toFun := fun u ↦ !₂[b - (b - a) * (u : ℝ), (0 : ℝ)]
      continuous_toFun := (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp
        (hcontx.matrixVecCons (continuous_const.matrixVecCons continuous_const))
      source' := by norm_num
      target' := by norm_num }
  have hparam : ∀ {u v : unitInterval},
      b - (b - a) * (u : ℝ) = b - (b - a) * (v : ℝ) → u = v :=
    fun h ↦ Subtype.ext (by nlinarith)
  have hcoords : ∀ {x y u v : ℝ}, (!₂[x, y] : Point) = !₂[u, v] → x = u ∧ y = v := by
    intro x y u v h
    simpa only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] using h
  have hγinj : Function.Injective γ := fun u v h ↦ hparam (hcoords h).1
  have hδinj : Function.Injective δ := fun u v h ↦ hparam (hcoords h).1
  have hparam_surj : ∀ c ∈ Set.Icc a b, ∃ u : unitInterval, b - (b - a) * (u : ℝ) = c := by
    intro c hc
    have h0 : 0 ≤ (b - c) / (b - a) := div_nonneg (by linarith [hc.2]) hL.le
    have h1 : (b - c) / (b - a) ≤ 1 := (div_le_one hL).mpr (by linarith [hc.1])
    exact ⟨⟨(b - c) / (b - a), h0, h1⟩, by field_simp; ring⟩
  have hrangeγ : Set.range γ = (fun c ↦ (!₂[c, f c] : Point)) '' Set.Icc a b := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨_, hmapsto u, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨u, hu⟩ := hparam_surj c hc
      exact ⟨u, by change (!₂[_, f _] : Point) = _; rw [hu]⟩
  have hrangeδ : Set.range δ = (fun c ↦ (!₂[c, (0 : ℝ)] : Point)) '' Set.Icc a b := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨_, hmapsto u, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨u, hu⟩ := hparam_surj c hc
      exact ⟨u, by change (!₂[_, (0 : ℝ)] : Point) = _; rw [hu]⟩
  have hmeet : Set.range γ ∩ Set.range δ =
      {(!₂[b, (0 : ℝ)] : Point), (!₂[a, (0 : ℝ)] : Point)} := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
      have hcoord := hcoords
        (show (!₂[b - (b - a) * (u : ℝ), f (b - (b - a) * (u : ℝ))] : Point) =
          !₂[b - (b - a) * (v : ℝ), (0 : ℝ)] from hv.symm)
      rcases eq_endpoint_of_apply_eq_zero hpos (hmapsto u) hcoord.2 with h | h
      · have hu1 : u = 1 := Subtype.ext (by simpa using show (u : ℝ) = 1 by nlinarith)
        exact Or.inr (by rw [show (γ u : Point) = γ 1 from congrArg _ hu1, γ.target]; rfl)
      · have hu0 : u = 0 := Subtype.ext (by simpa using show (u : ℝ) = 0 by nlinarith)
        exact Or.inl (by rw [show (γ u : Point) = γ 0 from congrArg _ hu0, γ.source])
    · rintro z (rfl | rfl)
      · exact ⟨⟨0, γ.source⟩, ⟨0, δ.source⟩⟩
      · exact ⟨⟨1, γ.target⟩, ⟨1, δ.target⟩⟩
  have htau := TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair hγinj hδinj hmeet
  rw [range_positiveGraphLoop hab ha, ← hrangeγ, ← hrangeδ]
  obtain ⟨e⟩ := htau
  refine ⟨fun z ↦ (e.symm z : Point), continuous_subtype_val.comp e.symm.continuous,
    fun z w h ↦ e.symm.injective (Subtype.ext h), Set.Subset.antisymm ?_ ?_⟩
  · rintro z ⟨w, rfl⟩
    exact (e.symm w).property
  · intro z hz
    exact ⟨e ⟨z, hz⟩, congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)⟩

/-- The loop lies in the closed upper half-plane and traverses the supporting base segment in the
positive tangent direction, so it is counterclockwise. -/
private lemma isOrientedJordanParametrization_positiveGraphLoop (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 2)
      (Set.range (positiveGraphLoop a b f)) true (positiveGraphLoop a b f) := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  set θ : Real.Angle := ((-(Real.pi / 2) : ℝ) : Real.Angle) with hθ
  have hN : normalVector θ = !₂[(0 : ℝ), -1] := by
    ext i
    fin_cases i <;> simp [normalVector, frame, hθ, Real.Angle.cos_coe, Real.Angle.sin_coe]
  have hT : tangentVector θ = !₂[(1 : ℝ), 0] := by
    ext i
    fin_cases i <;> simp [tangentVector, frame, hθ, Real.Angle.cos_coe, Real.Angle.sin_coe]
  have hinner : ∀ p : Point, inner ℝ p (normalVector θ) = -p 1 := by
    intro p
    rw [hN]
    simp [PiLp.inner_apply, Fin.sum_univ_two]
  have hone : positiveGraphLoop a b f ⟨1, by norm_num⟩ = !₂[a, (0 : ℝ)] := by
    rw [positiveGraphLoop_apply_base ha (by norm_num) le_rfl]
    norm_num
  have htwo : positiveGraphLoop a b f ⟨2, by norm_num⟩ = !₂[b, (0 : ℝ)] := by
    rw [positiveGraphLoop_apply_base ha (by norm_num) (by norm_num)]
    norm_num
  refine jordan_counterclockwise_of_supporting_segment 0 2 (by norm_num) _
    (continuous_positiveGraphLoop hab hf ha)
    (isJordanCurve_range_positiveGraphLoop hab hf ha hb hpos) ?_
    (injOn_positiveGraphLoop hab hpos) θ 0 ?_ ⟨1, by norm_num⟩ ⟨2, by norm_num⟩
    (Subtype.mk_lt_mk.mpr (by norm_num)) ?_ (b - a) hL ?_ ?_
  · rw [positiveGraphLoop_apply_of_le (by norm_num) (by norm_num),
      positiveGraphLoop_apply_base ha (by norm_num) (by norm_num)]
    norm_num [hb]
  · intro t
    simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq, hinner,
      neg_nonpos]
    obtain ⟨s, hs⟩ := t
    by_cases h : s ≤ 1
    · rw [positiveGraphLoop_apply_of_le hs h]
      exact nonneg_of_pos_on_Ioo ha hb hpos (sub_mul_mem_Icc hab ⟨hs.1, h⟩)
    · rw [positiveGraphLoop_apply_of_not_le hs h]
      exact le_rfl
  · simp only [normalLine, Set.mem_ofPred_eq, hinner, hone]
    norm_num
  · rw [hone, htwo, hT]
    ext i
    fin_cases i <;> simp
  · rw [hone, htwo, segment_eq_image]
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨u, hu⟩, hmem, rfl⟩
      have h1 : (1 : ℝ) ≤ u := hmem.1
      have h2 : u ≤ 2 := hmem.2
      refine ⟨u - 1, ⟨by linarith, by linarith⟩, ?_⟩
      rw [positiveGraphLoop_apply_base ha hu h1]
      ext i
      fin_cases i
      · simp
        ring
      · simp
    · rintro _ ⟨c, hc, rfl⟩
      have hmem : 1 + c ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
      refine ⟨⟨1 + c, hmem⟩, ⟨Subtype.mk_le_mk.mpr (by linarith [hc.1]),
        Subtype.mk_le_mk.mpr (by linarith [hc.2])⟩, ?_⟩
      rw [positiveGraphLoop_apply_base ha hmem (by linarith [hc.1])]
      ext i
      fin_cases i
      · simp
        ring
      · simp

/-- The positive subgraph is open, connected, bounded and relatively closed in the complement of
the loop, hence it is the bounded complementary component. -/
private lemma jordanInterior_range_positiveGraphLoop_of_components (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    jordanInterior (Set.range (positiveGraphLoop a b f)) =
      {p : Point | a < p 0 ∧ p 0 < b ∧ 0 < p 1 ∧ p 1 < f (p 0)} := by
  set Γ := Set.range (positiveGraphLoop a b f) with hΓ
  set U : Set Point := {p : Point | a < p 0 ∧ p 0 < b ∧ 0 < p 1 ∧ p 1 < f (p 0)} with hU
  set K : Set Point := {p : Point | a ≤ p 0 ∧ p 0 ≤ b ∧ 0 ≤ p 1 ∧ p 1 ≤ f (p 0)} with hK
  have hrange : Γ = (fun c ↦ (!₂[c, f c] : Point)) '' Set.Icc a b ∪
      (fun c ↦ (!₂[c, (0 : ℝ)] : Point)) '' Set.Icc a b := range_positiveGraphLoop hab ha
  have hUK : U ⊆ K := fun p hp ↦ ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩
  have hUΓ : U ⊆ Γᶜ := by
    intro p hp hpΓ
    rw [hrange] at hpΓ
    rcases hpΓ with ⟨c, _, hc⟩ | ⟨c, _, hc⟩
    · exact absurd hp.2.2.2 (by rw [← hc]; simp)
    · exact absurd hp.2.2.1 (by rw [← hc]; simp)
  have hKΓU : ∀ p ∈ K, p ∉ Γ → p ∈ U := by
    intro p hp hpΓ
    rw [hrange] at hpΓ
    have hpc : p = !₂[p 0, p 1] := point_eq_vecNotation_coords p
    have h1 : p 1 ≠ 0 := fun h0 ↦ hpΓ (Or.inr ⟨p 0, ⟨hp.1, hp.2.1⟩,
      show (!₂[p 0, (0 : ℝ)] : Point) = p by rw [← h0]; exact hpc.symm⟩)
    have h2 : p 1 ≠ f (p 0) := fun heq ↦ hpΓ (Or.inl ⟨p 0, ⟨hp.1, hp.2.1⟩,
      show (!₂[p 0, f (p 0)] : Point) = p by rw [← heq]; exact hpc.symm⟩)
    have h3 : 0 < p 1 := lt_of_le_of_ne hp.2.2.1 (Ne.symm h1)
    have h4 : p 1 < f (p 0) := lt_of_le_of_ne hp.2.2.2 h2
    refine ⟨?_, ?_, h3, h4⟩
    · rcases eq_or_lt_of_le hp.1 with h | h
      · rw [← h, ha] at h4
        linarith
      · exact h
    · rcases eq_or_lt_of_le hp.2.1 with h | h
      · rw [h, hb] at h4
        linarith
      · exact h
  have hcoord0 : Continuous fun q : Point ↦ q 0 := by fun_prop
  have hcoord1 : Continuous fun q : Point ↦ q 1 := by fun_prop
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨h1, h2, h3, h4⟩
    have hfat : ContinuousAt f (p 0) :=
      (hf.mono Set.Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds h1 h2)
    have hfcoord : ContinuousAt (fun q : Point ↦ f (q 0)) p :=
      ContinuousAt.comp (g := f) (f := fun q : Point ↦ q 0) (x := p) hfat hcoord0.continuousAt
    have hgap : ContinuousAt (fun q : Point ↦ f (q 0) - q 1) p :=
      hfcoord.sub hcoord1.continuousAt
    filter_upwards [hcoord0.continuousAt (isOpen_Ioo.mem_nhds (⟨h1, h2⟩ : p 0 ∈ Set.Ioo a b)),
      hcoord1.continuousAt (isOpen_Ioi.mem_nhds (show p 1 ∈ Set.Ioi (0 : ℝ) from h3)),
      hgap (isOpen_Ioi.mem_nhds (show f (p 0) - p 1 ∈ Set.Ioi (0 : ℝ) from sub_pos.mpr h4))]
      with q hq1 hq2 hq3
    exact ⟨hq1.1, hq1.2, hq2, by simpa using sub_pos.mp hq3⟩
  have hSclosed : IsClosed {q : Point | q 0 ∈ Set.Icc a b} := isClosed_Icc.preimage hcoord0
  have hKclosed : IsClosed K := by
    have hgS : ContinuousOn (fun q : Point ↦ f (q 0) - q 1) {q : Point | q 0 ∈ Set.Icc a b} :=
      (hf.comp hcoord0.continuousOn fun q hq ↦ hq).sub hcoord1.continuousOn
    have hone := hgS.preimage_isClosed_of_isClosed hSclosed (isClosed_Ici (a := (0 : ℝ)))
    have htwo : IsClosed {q : Point | 0 ≤ q 1} := isClosed_Ici.preimage hcoord1
    have hsplit : K = ({q : Point | q 0 ∈ Set.Icc a b} ∩
        (fun q : Point ↦ f (q 0) - q 1) ⁻¹' Set.Ici 0) ∩ {q : Point | 0 ≤ q 1} := by
      ext q
      simp only [hK, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage,
        Set.mem_Ici, sub_nonneg]
      tauto
    rw [hsplit]
    exact hone.inter htwo
  have hUconn : IsConnected U := by
    have hfcomp : ContinuousOn (fun q : ℝ × ℝ ↦ f q.1) (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) 1) :=
      (hf.mono Set.Ioo_subset_Icc_self).comp continuous_fst.continuousOn fun q hq ↦ hq.1
    have hmap : ContinuousOn (fun q : ℝ × ℝ ↦ (!₂[q.1, q.2 * f q.1] : Point))
        (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) 1) :=
      (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
        (continuous_fst.continuousOn.matrixVecCons
          ((continuous_snd.continuousOn.mul hfcomp).matrixVecCons continuousOn_const))
    have hset : U = (fun q : ℝ × ℝ ↦ (!₂[q.1, q.2 * f q.1] : Point)) ''
        (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) 1) := by
      apply Set.Subset.antisymm
      · rintro p ⟨h1, h2, h3, h4⟩
        have hfpos : 0 < f (p 0) := h3.trans h4
        refine ⟨(p 0, p 1 / f (p 0)), ⟨⟨h1, h2⟩, div_pos h3 hfpos,
          (div_lt_one hfpos).mpr h4⟩, ?_⟩
        change (!₂[p 0, p 1 / f (p 0) * f (p 0)] : Point) = p
        rw [div_mul_cancel₀ _ hfpos.ne']
        exact (point_eq_vecNotation_coords p).symm
      · rintro _ ⟨⟨c, r⟩, ⟨⟨hc1, hc2⟩, hr1, hr2⟩, rfl⟩
        have hfc : 0 < f c := hpos c ⟨hc1, hc2⟩
        refine ⟨by simpa using hc1, by simpa using hc2, by simpa using mul_pos hr1 hfc, ?_⟩
        change r * f c < f c
        nlinarith
    rw [hset]
    exact ((isConnected_Ioo hab).prod (isConnected_Ioo (by norm_num))).image _ hmap
  obtain ⟨c₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab.le) hf
  have hKbdd : Bornology.IsBounded K :=
    (EuclideanSpace.isBounded_coordinate_rectangle a b 0 (f c₀)).subset (by
      rintro p ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, h4.trans (hmax ⟨h1, h2⟩)⟩)
  have hUbdd : Bornology.IsBounded U := hKbdd.subset hUK
  have hcompU : ∀ p ∈ U, connectedComponentIn Γᶜ p = U := by
    intro p hp
    have hsub : connectedComponentIn Γᶜ p ⊆ Γᶜ := connectedComponentIn_subset _ _
    refine Set.Subset.antisymm ?_ (hUconn.isPreconnected.subset_connectedComponentIn hp hUΓ)
    have hcover : connectedComponentIn Γᶜ p ⊆ U ∪ Kᶜ := by
      intro q hq
      by_cases hqK : q ∈ K
      · exact Or.inl (hKΓU q hqK (hsub hq))
      · exact Or.inr hqK
    have hmeet : (connectedComponentIn Γᶜ p ∩ U).Nonempty :=
      ⟨p, mem_connectedComponentIn (hUΓ hp), hp⟩
    have hempty : ¬ (connectedComponentIn Γᶜ p ∩ Kᶜ).Nonempty := by
      intro hk
      obtain ⟨z, hz⟩ := isPreconnected_connectedComponentIn U Kᶜ hUopen
        hKclosed.isOpen_compl hcover hmeet hk
      exact hz.2.2 (hUK hz.2.1)
    intro q hq
    by_contra hqU
    exact hempty ⟨q, hq, fun hqK ↦ hqU (hKΓU q hqK (hsub hq))⟩
  obtain ⟨p₀, hp₀⟩ := hUconn.nonempty
  obtain ⟨U', V', -, -, -, -, -, hV'ub, -, hcover, -, -, hcU, hcV⟩ :=
    jordan_separation (isJordanCurve_range_positiveGraphLoop hab hf ha hb hpos)
  have hp₀U' : p₀ ∈ U' := by
    rcases hcover.symm.subset (hUΓ hp₀) with h | h
    · exact h
    · exact absurd (by rw [← hcV p₀ h, hcompU p₀ hp₀]; exact hUbdd) hV'ub
  have hU'eq : U' = U := by rw [← hcU p₀ hp₀U', hcompU p₀ hp₀]
  ext p
  constructor
  · rintro ⟨hpΓ, hpb⟩
    rcases hcover.symm.subset hpΓ with h | h
    · rwa [← hU'eq]
    · exact absurd (by rwa [← hcV p h]) hV'ub
  · intro hp
    exact ⟨hUΓ hp, by rw [hcompU p hp]; exact hUbdd⟩

end PositiveGraph

theorem positiveGraphLoop_counterclockwise (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 2)
      (Set.range (positiveGraphLoop a b f)) true (positiveGraphLoop a b f) ∧
    jordanInterior (Set.range (positiveGraphLoop a b f)) =
      {p : Point | a < p 0 ∧ p 0 < b ∧ 0 < p 1 ∧ p 1 < f (p 0)} :=
  ⟨isOrientedJordanParametrization_positiveGraphLoop hab hf ha hb hpos,
    jordanInterior_range_positiveGraphLoop_of_components hab hf ha hb hpos⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The region enclosed by the counterclockwise loop around a positive graph

`MovingSofa.positiveGraphLoop_counterclockwise` identifies the bounded complementary component
of the loop around the graph of a positive `f` with the open subgraph of `f`.  This file records
the resulting description of the closed subgraph: the loop traces exactly the frontier of either
region, and the closed subgraph is the open one together with that frontier.
-/

public section

noncomputable section

namespace MovingSofa

variable {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
  (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x)

include hab hf ha hb hpos

/-- The bounded complementary component of the positive-graph loop is the open subgraph. -/
theorem jordanInterior_range_positiveGraphLoop :
    jordanInterior (Set.range (positiveGraphLoop a b f)) = openSubgraph a b f :=
  (positiveGraphLoop_counterclockwise a b hab f hf ha hb hpos).2

/-- The positive-graph loop traces the frontier of the open subgraph. -/
theorem frontier_openSubgraph :
    frontier (openSubgraph a b f) = Set.range (positiveGraphLoop a b f) := by
  rw [← jordanInterior_range_positiveGraphLoop hab hf ha hb hpos]
  exact (positiveGraphLoop_counterclockwise a b hab f hf ha hb
    hpos).1.2.1.frontier_jordanInterior

/-- The part of the closed subgraph outside the open one is exactly the loop. -/
theorem closedSubgraph_sdiff_openSubgraph :
    closedSubgraph a b f \ openSubgraph a b f = Set.range (positiveGraphLoop a b f) := by
  rw [← frontier_openSubgraph hab hf ha hb hpos, frontier, (isOpen_openSubgraph hf).interior_eq,
    closure_openSubgraph hab hf ha hb hpos]

/-- The closed subgraph is the open subgraph together with the loop. -/
theorem closedSubgraph_eq_openSubgraph_union_range :
    closedSubgraph a b f = openSubgraph a b f ∪ Set.range (positiveGraphLoop a b f) := by
  rw [← closedSubgraph_sdiff_openSubgraph hab hf ha hb hpos]
  exact (Set.union_sdiff_cancel openSubgraph_subset_closedSubgraph).symm

/-- The positive-graph loop also traces the frontier of the closed subgraph. -/
theorem frontier_closedSubgraph :
    frontier (closedSubgraph a b f) = Set.range (positiveGraphLoop a b f) := by
  rw [frontier, (isClosed_closedSubgraph hf).closure_eq, interior_closedSubgraph hf ha hb,
    closedSubgraph_sdiff_openSubgraph hab hf ha hb hpos]

end MovingSofa

end

end

end

end

end

end

end

end

end
