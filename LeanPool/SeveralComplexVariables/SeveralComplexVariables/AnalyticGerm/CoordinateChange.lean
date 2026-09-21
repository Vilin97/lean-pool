/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Order
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity

/-!
# Coordinate changes and regular analytic germs

Analytic changes of coordinates induce algebra isomorphisms on scalar germs. A nonzero germ on a
finite-dimensional parameter space times `ℂ` becomes regular in the scalar coordinate after a
complex linear change of coordinates. Finite families are normalized by applying the single-germ
theorem to their product. This includes the finite-family version discussed in [Suwa][Suwa2024]
§1.4; the unitary and countable-family refinements in [Jakóbczak–Jarnicki][JakobczakJarnicki2021],
Lemma 1.8.3 are not needed here.

## Main definitions

* `pullbackEquiv`: An analytic homeomorphism with analytic inverse induces an algebra isomorphism of
  germs.
* `pullbackEquivOfEq`: Pullback equivalence along a map whose value at the source point is only
  known up to a stated equation, letting the target germ's base point be phrased as any value equal
  to `e x`.
* `linearEquivPullback`: Continuous linear coordinate changes act contravariantly on analytic germs.
* `translateEquiv`: Translation identifies the germs at any point with the germs at the origin.
* `linearEquivPullbackZero`: A linear change of coordinates fixes the origin and identifies the
  corresponding germ rings.
* `orderInLastVariable`: Order of a scalar germ along the distinguished coordinate axis.
* `regularizingLinearEquiv`: A triangular linear coordinate change sends the last coordinate axis to
  the line through `v`, provided the last coordinate of `v` is nonzero.

## Main results

* `exists_regular_coordinate_change`: A nonzero analytic germ can be made regular in the last
  coordinate by an invertible complex linear change.
* `exists_regular_coordinate_change_finite`: One linear coordinate change makes every member of a
  finite family of nonzero analytic germs regular in the last variable.
* `isUnit_iff_orderInLastVariable_eq_zero`: A germ is a unit exactly when it has order zero along
  the distinguished coordinate.
* `orderInLastVariable_mul`: Order along the distinguished coordinate is additive under
  multiplication of germs.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [T. Suwa, *Complex Analytic Geometry: From the Localization Viewpoint*][Suwa2024]
-/

public noncomputable section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables
namespace AnalyticGerm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- An analytic homeomorphism with analytic inverse induces an algebra isomorphism of germs. -/
@[expose] def pullbackEquiv (e : E ≃ₜ F) (x : E) (he : AnalyticAt ℂ e x)
    (hi : AnalyticAt ℂ e.symm (e x)) : AnalyticGerm ℂ (e x) ≃ₐ[ℂ] AnalyticGerm ℂ x :=
  AlgEquiv.ofBijective (pullback e he) (by
    constructor
    · intro a b hab
      obtain ⟨f, hf, rfl⟩ := exists_rep a
      obtain ⟨g, hg, rfl⟩ := exists_rep b
      have hh : (f ∘ e) =ᶠ[𝓝 x] (g ∘ e) :=
        Germ.coe_eq.mp (congrArg Subtype.val hab)
      apply ofAnalyticAt_eq_iff.mpr
      have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
        simpa using e.symm.continuous.tendsto (e x)
      simpa only [Function.comp_def, e.apply_symm_apply] using hh.comp_tendsto ht
    · intro a
      obtain ⟨f, hf, rfl⟩ := exists_rep a
      refine ⟨ofAnalyticAt (f ∘ e.symm) (hf.comp_of_eq hi (e.symm_apply_apply x)), ?_⟩
      apply Subtype.ext
      apply Germ.coe_eq.mpr
      exact .of_forall fun y => by simp [Function.comp_def])

/-- Pullback equivalence along a map whose value at the source point is only known up to a stated
equation, letting the target germ's base point be phrased as any value equal to `e x`. Matches
`pullbackEquiv` definitionally once the equation is substituted. -/
def pullbackEquivOfEq (e : E ≃ₜ F) (x : E) (he : AnalyticAt ℂ e x)
    (hi : AnalyticAt ℂ e.symm (e x)) {y : F} (hy : e x = y) :
    AnalyticGerm ℂ y ≃ₐ[ℂ] AnalyticGerm ℂ x :=
  hy ▸ pullbackEquiv e x he hi

/-- Applying an equation-adjusted pullback equivalence to a represented germ is represented by
composition, matching the plain pullback. -/
theorem pullbackEquivOfEq_ofAnalyticAt (e : E ≃ₜ F) (x : E) (he : AnalyticAt ℂ e x)
    (hi : AnalyticAt ℂ e.symm (e x)) {y : F} (hy : e x = y) (g : F → ℂ)
    (hg : AnalyticAt ℂ g y) :
    pullbackEquivOfEq e x he hi hy (ofAnalyticAt g hg) =
      ofAnalyticAt (g ∘ e) (hg.comp_of_eq he hy) := by
  subst hy
  rfl

/-- An equation-adjusted pullback equivalence is bijective, like the plain pullback equivalence it
matches definitionally. -/
theorem pullbackEquivOfEq_bijective (e : E ≃ₜ F) (x : E) (he : AnalyticAt ℂ e x)
    (hi : AnalyticAt ℂ e.symm (e x)) {y : F} (hy : e x = y) :
    Function.Bijective (pullbackEquivOfEq e x he hi hy) := by
  subst hy
  exact (pullbackEquiv e x he hi).bijective

/-- Continuous linear coordinate changes act contravariantly on analytic germs. -/
def linearEquivPullback (e : E ≃L[ℂ] F) (x : E) :
    AnalyticGerm ℂ (e x) ≃ₐ[ℂ] AnalyticGerm ℂ x :=
  pullbackEquiv e.toHomeomorph x (e.toContinuousLinearMap.analyticAt x)
    (e.symm.toContinuousLinearMap.analyticAt (e x))

/-- Translation identifies the germs at any point with the germs at the origin. -/
def translateEquiv (x : E) : AnalyticGerm ℂ x ≃ₐ[ℂ] AnalyticGerm ℂ (0 : E) := by
  have e : AnalyticGerm ℂ (0 + x) ≃ₐ[ℂ] AnalyticGerm ℂ (0 : E) :=
    pullbackEquiv (Homeomorph.addRight x) 0
      (analyticAt_id.add analyticAt_const) (by
        change AnalyticAt ℂ (fun y : E => y + -x) _
        exact analyticAt_id.add analyticAt_const)
  exact (zero_add x) ▸ e

/-- A linear change of coordinates fixes the origin and identifies the corresponding germ rings. -/
def linearEquivPullbackZero (e : E ≃L[ℂ] F) :
    AnalyticGerm ℂ (0 : F) ≃ₐ[ℂ] AnalyticGerm ℂ (0 : E) := by
  have h := linearEquivPullback e (0 : E)
  exact (e.map_zero) ▸ h

/-- Order of a scalar germ along the distinguished coordinate axis. The definition uses Mathlib's
one-variable analytic order and is independent of representatives. -/
@[expose] def orderInLastVariable (φ : AnalyticGerm ℂ (0 : E × ℂ)) : ℕ∞ :=
  φ.val.liftOn (fun f => analyticOrderAt (fun w : ℂ => f (0, w)) 0) (by
    intro f g h
    have ht : Tendsto (fun w : ℂ => ((0 : E), w)) (𝓝 0) (𝓝 0) :=
      (continuous_const.prodMk continuous_id).tendsto 0
    exact analyticOrderAt_congr (h.comp_tendsto ht))

/-- The order of a represented germ is the order of its central scalar slice. -/
@[simp] theorem orderInLastVariable_ofAnalyticAt (f : E × ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    orderInLastVariable (ofAnalyticAt f hf) = analyticOrderAt (fun w : ℂ => f (0, w)) 0 := rfl

/-- The central slice of a represented germ is analytic at the scalar origin. -/
theorem analyticAt_ofAnalyticAt_central (f : E × ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (fun w : ℂ => f (0, w)) 0 :=
  hf.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl

/-- Order along the distinguished coordinate is additive under multiplication of germs. -/
theorem orderInLastVariable_mul (φ ψ : AnalyticGerm ℂ (0 : E × ℂ)) :
    orderInLastVariable (φ * ψ) = orderInLastVariable φ + orderInLastVariable ψ := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  obtain ⟨g, hg, rfl⟩ := exists_rep ψ
  rw [← ofAnalyticAt_mul]
  simp only [orderInLastVariable_ofAnalyticAt]
  exact analyticOrderAt_mul (analyticAt_ofAnalyticAt_central f hf)
    (analyticAt_ofAnalyticAt_central g hg)

/-- A germ is a unit exactly when it has order zero along the distinguished coordinate. -/
theorem isUnit_iff_orderInLastVariable_eq_zero (φ : AnalyticGerm ℂ (0 : E × ℂ)) :
    IsUnit φ ↔ orderInLastVariable φ = 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [isUnit_iff, eval_ofAnalyticAt, orderInLastVariable_ofAnalyticAt]
  exact (analyticAt_ofAnalyticAt_central f hf).analyticOrderAt_eq_zero.symm

end AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A triangular linear coordinate change sends the last coordinate axis to the line through `v`,
provided the last coordinate of `v` is nonzero. -/
def regularizingLinearEquiv (v : E × ℂ) (hv : v.2 ≠ 0) : (E × ℂ) ≃ₗ[ℂ] (E × ℂ) where
  toFun z := (z.1 + z.2 • v.1, z.2 * v.2)
  invFun z := (z.1 - (z.2 / v.2) • v.1, z.2 / v.2)
  left_inv z := by simp [hv]
  right_inv z := by simp [hv]
  map_add' z w := by
    ext <;> simp [add_smul, add_mul]; module
  map_smul' c z := by
    ext <;> simp [smul_add, mul_smul, smul_eq_mul, mul_assoc]

/-- A nonzero analytic germ can be made regular in the last coordinate by an invertible complex
linear change. The resulting order is finite, including order zero for units. Empty parameter
spaces are allowed, since the scalar coordinate is always present. -/
theorem exists_regular_coordinate_change [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hne : ¬ f =ᶠ[𝓝 0] 0) :
    ∃ (L : (E × ℂ) ≃L[ℂ] (E × ℂ)) (d : ℕ),
      analyticOrderAt (fun w : ℂ => f (L (0, w))) 0 = d := by
  have hsnd : ¬ (Prod.snd : E × ℂ → ℂ) =ᶠ[𝓝 0] 0 := by
    intro h
    have ht : Tendsto (fun w : ℂ => ((0 : E), w)) (𝓝 0) (𝓝 0) := by
      exact (continuous_const.prodMk continuous_id).tendsto 0
    have hi : (id : ℂ → ℂ) =ᶠ[𝓝 0] 0 := h.comp_tendsto ht
    have ho := analyticOrderAt_eq_top.mpr hi
    simp at ho
  have hprod : ¬ (fun z : E × ℂ => f z * z.2) =ᶠ[𝓝 0] 0 := by
    intro h
    exact (eventuallyEq_zero_or_eventuallyEq_zero_of_mul hf analyticAt_snd h).elim hne hsnd
  obtain ⟨r, hr, hfa⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨v, hvball, hfv⟩ : ∃ v ∈ ball (0 : E × ℂ) r, f v * v.2 ≠ 0 := by
    by_contra! h
    exact hprod (Filter.mem_of_superset (ball_mem_nhds 0 hr) (fun z hz => h z hz))
  have hv : v.2 ≠ 0 := (mul_ne_zero_iff.mp hfv).2
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr (fun h => hv (by simp [h]))
  have hline : AnalyticOnNhd ℂ (fun w : ℂ => f (w • v)) (ball 0 (r / ‖v‖)) := by
    intro w hw
    have hmem : w • v ∈ ball (0 : E × ℂ) r := by
      rw [mem_ball_zero_iff, norm_smul]
      exact (lt_div_iff₀ hvn).mp (mem_ball_zero_iff.mp hw)
    have hs : AnalyticAt ℂ (fun t : ℂ => t • v) w := analyticAt_id.smul analyticAt_const
    exact (hfa _ hmem).comp_of_eq hs rfl
  have hlinene : analyticOrderAt (fun w : ℂ => f (w • v)) 0 ≠ ⊤ := by
    intro h
    have heq := hline.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (r / ‖v‖)).isPreconnected (mem_ball_self (div_pos hr hvn))
      (analyticOrderAt_eq_top.mp h)
    have h1 : (1 : ℂ) ∈ ball 0 (r / ‖v‖) := by
      rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hvn, one_mul]
      exact mem_ball_zero_iff.mp hvball
    exact (mul_ne_zero_iff.mp hfv).1 (by simpa using heq h1)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hlinene
  refine ⟨(regularizingLinearEquiv v hv).toContinuousLinearEquiv, d, ?_⟩
  convert hd.symm using 1
  congr 1
  funext w
  simp [regularizingLinearEquiv]
  rfl

/-- One linear coordinate change makes every member of a finite family of nonzero analytic germs
regular in the last variable. Empty families and unit germs are allowed. Apply single-germ
normalization to the product, then use that no factor slice can vanish. -/
theorem exists_regular_coordinate_change_finite [FiniteDimensional ℂ E]
    {κ : Type*} [Finite κ] {f : κ → E × ℂ → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) (hne : ∀ i, ¬ f i =ᶠ[𝓝 0] 0) :
    ∃ (L : (E × ℂ) ≃L[ℂ] (E × ℂ)) (d : κ → ℕ),
      ∀ i, analyticOrderAt (fun w : ℂ => f i (L (0, w))) 0 = d i := by
  classical
  let := Fintype.ofFinite κ
  classical
  have hp : ∀ s : Finset κ, ¬ (fun z => ∏ i ∈ s, f i z) =ᶠ[𝓝 0] 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro h
        have h0 := h.self_of_nhds
        simp at h0
    | @insert i s hi ih =>
        simp only [Finset.prod_insert hi]
        intro h
        exact (eventuallyEq_zero_or_eventuallyEq_zero_of_mul (hf i)
          (s.analyticAt_fun_prod (fun j _ => hf j)) h).elim (hne i) ih
  obtain ⟨L, d, hd⟩ := exists_regular_coordinate_change
    (Finset.univ.analyticAt_fun_prod (fun i _ => hf i)) (hp Finset.univ)
  have hfin : ∀ i, analyticOrderAt (fun w : ℂ => f i (L (0, w))) 0 ≠ ⊤ := by
    intro i hi
    have he := analyticOrderAt_eq_top.mp hi
    have hz : (fun w : ℂ => ∏ j, f j (L (0, w))) =ᶠ[𝓝 0] 0 := by
      filter_upwards [he] with w hw
      exact Finset.prod_eq_zero (Finset.mem_univ i) hw
    have ht := analyticOrderAt_eq_top.mpr hz
    rw [hd] at ht
    simp at ht
  refine ⟨L, fun i => (analyticOrderAt (fun w : ℂ => f i (L (0, w))) 0).toNat, ?_⟩
  intro i
  exact (ENat.natCast_toNat (hfin i)).symm

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
