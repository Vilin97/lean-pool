/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.Elimination

/-!
# Persistence of relative primality

Relative primality is an open condition on the base point for two fixed analytic representatives
in finite dimension. We use `IsRelPrime`, not the stronger Bezout condition `IsCoprime`. A germ
at one point is not evaluated at other points; instead, the statement explicitly takes the germs
of the same representatives nearby. Weierstrass preparation and a resultant identity eliminate
one variable. The resulting nonzero parameter germ is relatively prime to the first germ on
every nearby scalar fiber, which excludes a common nonunit divisor. Analytic coordinate changes
reduce the general case to this argument; openness is its direct consequence.

## Main results

* `eventually_isRelPrime_of_orderInLastVariable`: Relative primality persists when the first germ
  has finite order on the central fiber.
* `eventually_isRelPrime_of_comp_homeomorph`: Persistence of relative primality transports through
  analytic changes of coordinates.
* `eventually_isRelPrime_ofAnalyticAt_prod`: Relative primality persists on a parameter space times
  the scalar line.
* `eventually_isRelPrime_ofAnalyticAt`: Relatively prime germs of two analytic representatives
  remain relatively prime nearby.
* `isOpen_isRelPrime_locus`: The locus where two functions are analytic and their germs are
  relatively prime is open.
-/

public section

open Filter Set
open scoped Topology

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Relative primality persists when the first germ has finite order on the central fiber. -/
theorem eventually_isRelPrime_of_orderInLastVariable {f g : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) {d : ℕ}
    (hd : orderInLastVariable (ofAnalyticAt f hf) = d)
    (hrel : IsRelPrime (ofAnalyticAt f hf) (ofAnalyticAt g hg)) :
    ∀ᶠ y in 𝓝 (0 : E × ℂ), ∃ (hfy : AnalyticAt ℂ f y) (hgy : AnalyticAt ℂ g y),
      IsRelPrime (ofAnalyticAt f hfy) (ofAnalyticAt g hgy) := by
  obtain ⟨h, hne, a, b, hab⟩ := exists_base_combination_of_isRelPrime hd hrel
  obtain ⟨h, hh, rfl⟩ := exists_rep h
  obtain ⟨a, ha, rfl⟩ := exists_rep a
  obtain ⟨b, hb, rfl⟩ := exists_rep b
  change ofAnalyticAt (fun y : E × ℂ => h y.1) (hh.comp_of_eq analyticAt_fst rfl) =
    ofAnalyticAt (fun y => a y * f y + b y * g y) ((ha.mul hf).add (hb.mul hg)) at hab
  have heq : (fun y : E × ℂ => h y.1) =ᶠ[𝓝 0]
      (fun y => a y * f y + b y * g y) := ofAnalyticAt_eq_iff.mp hab
  have hfiber : ¬ (fun w : ℂ => f (0, w)) =ᶠ[𝓝 0] 0 := by
    intro hz
    have ht := analyticOrderAt_eq_top.mpr hz
    rw [← orderInLastVariable_ofAnalyticAt f hf, hd] at ht
    exact ENat.natCast_ne_top d ht
  have hbase : ∀ᶠ y : E × ℂ in 𝓝 0,
      ∃ hy : AnalyticAt ℂ h y.1, ofAnalyticAt h hy ≠ 0 :=
    (continuous_fst.continuousAt : Tendsto (Prod.fst : E × ℂ → E) (𝓝 0) (𝓝 0)).eventually
      (eventually_ne_zero_ofAnalyticAt hh hne)
  filter_upwards [heq.eventually_nhds, hbase,
    eventually_fiber_ne_zero_ofAnalyticAt hf hfiber, hg.eventually_analyticAt,
    ha.eventually_analyticAt, hb.eventually_analyticAt] with y he hyh hyf hyg hya hyb
  obtain ⟨hyh, hyhne⟩ := hyh
  obtain ⟨hyf, hyfiber⟩ := hyf
  refine ⟨hyf, hyg, ?_⟩
  have hcomb : basePullback y (ofAnalyticAt h hyh) =
      ofAnalyticAt a hya * ofAnalyticAt f hyf + ofAnalyticAt b hyb * ofAnalyticAt g hyg := by
    change ofAnalyticAt (fun z : E × ℂ => h z.1) (hyh.comp_of_eq analyticAt_fst rfl) =
      ofAnalyticAt (fun z => a z * f z + b z * g z) ((hya.mul hyf).add (hyb.mul hyg))
    exact ofAnalyticAt_eq_iff.mpr he
  have hp := isRelPrime_basePullback_of_fiber_ne_zero y hyhne hyfiber
  intro c hcf hcg
  apply hp _ hcf
  rw [hcomb]
  exact dvd_add (dvd_mul_of_dvd_right hcf _) (dvd_mul_of_dvd_right hcg _)

omit [FiniteDimensional ℂ E] in
/-- Persistence of relative primality transports through analytic changes of coordinates. -/
theorem eventually_isRelPrime_of_comp_homeomorph
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃ₜ F) (he : ∀ z, AnalyticAt ℂ e z) (hi : ∀ y, AnalyticAt ℂ e.symm y)
    {f g : F → ℂ} {x : E}
    (h : ∀ᶠ z in 𝓝 x, ∃ (hf : AnalyticAt ℂ (f ∘ e) z)
      (hg : AnalyticAt ℂ (g ∘ e) z), IsRelPrime (ofAnalyticAt (f ∘ e) hf)
        (ofAnalyticAt (g ∘ e) hg)) :
    ∀ᶠ y in 𝓝 (e x), ∃ (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y),
      IsRelPrime (ofAnalyticAt f hf) (ofAnalyticAt g hg) := by
  have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e x)
  filter_upwards [ht.eventually h] with y hy
  obtain ⟨hf, hg, hrel⟩ := hy
  have hfy : AnalyticAt ℂ f y := by
    simpa only [Function.comp_def, e.apply_symm_apply] using
      hf.comp_of_eq (hi y) rfl
  have hgy : AnalyticAt ℂ g y := by
    simpa only [Function.comp_def, e.apply_symm_apply] using
      hg.comp_of_eq (hi y) rfl
  let q := pullbackEquivOfEq e (e.symm y) (he _) (hi _) (e.apply_symm_apply y)
  refine ⟨hfy, hgy, IsRelPrime.of_map q ?_⟩
  simpa only [q, pullbackEquivOfEq_ofAnalyticAt] using hrel

/-- Relative primality persists on a parameter space times the scalar line. -/
theorem eventually_isRelPrime_ofAnalyticAt_prod {f g : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : IsRelPrime (ofAnalyticAt f hf) (ofAnalyticAt g hg)) :
    ∀ᶠ y in 𝓝 (0 : E × ℂ), ∃ (hfy : AnalyticAt ℂ f y) (hgy : AnalyticAt ℂ g y),
      IsRelPrime (ofAnalyticAt f hfy) (ofAnalyticAt g hgy) := by
  by_cases hzero : ofAnalyticAt f hf = 0
  · have hunit : g 0 ≠ 0 := by
      simpa only [hzero, isRelPrime_zero_left, isUnit_iff, eval_ofAnalyticAt] using h
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt,
      hg.continuousAt.eventually_ne hunit] with y hfy hgy hy
    exact ⟨hfy, hgy, ((isUnit_iff (ofAnalyticAt g hgy)).mpr hy).isRelPrime_right⟩
  obtain ⟨L, d, hd⟩ := exists_regular_coordinate_change hf
    ((ofAnalyticAt_ne_zero_iff hf).mp hzero)
  have hfL : AnalyticAt ℂ (f ∘ L) 0 := hf.comp_of_eq (L.analyticAt 0) L.map_zero
  have hgL : AnalyticAt ℂ (g ∘ L) 0 := hg.comp_of_eq (L.analyticAt 0) L.map_zero
  let q := pullbackEquivOfEq L.toHomeomorph 0 (L.analyticAt 0)
    (L.symm.analyticAt (L 0)) L.map_zero
  have hq : IsRelPrime (q (ofAnalyticAt f hf)) (q (ofAnalyticAt g hg)) :=
    IsRelPrime.of_map q.symm (by simpa only [AlgEquiv.symm_apply_apply] using h)
  have hL : IsRelPrime (ofAnalyticAt (f ∘ L) hfL) (ofAnalyticAt (g ∘ L) hgL) := by
    have hqf : q (ofAnalyticAt f hf) = ofAnalyticAt (f ∘ L) hfL :=
      pullbackEquivOfEq_ofAnalyticAt L.toHomeomorph 0 (L.analyticAt 0)
        (L.symm.analyticAt (L 0)) L.map_zero f hf
    have hqg : q (ofAnalyticAt g hg) = ofAnalyticAt (g ∘ L) hgL :=
      pullbackEquivOfEq_ofAnalyticAt L.toHomeomorph 0 (L.analyticAt 0)
        (L.symm.analyticAt (L 0)) L.map_zero g hg
    rwa [hqf, hqg] at hq
  have hp := eventually_isRelPrime_of_orderInLastVariable hfL hgL hd hL
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph, map_zero] using
    eventually_isRelPrime_of_comp_homeomorph L.toHomeomorph L.analyticAt L.symm.analyticAt hp

/-- Relatively prime germs of two analytic representatives remain relatively prime nearby. Neither
germ is required to be nonzero: the relatively prime zero case forces a unit. -/
theorem eventually_isRelPrime_ofAnalyticAt {f g : E → ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (h : IsRelPrime (ofAnalyticAt f hf) (ofAnalyticAt g hg)) :
    ∀ᶠ y in 𝓝 x, ∃ (hfy : AnalyticAt ℂ f y) (hgy : AnalyticAt ℂ g y),
      IsRelPrime (ofAnalyticAt f hfy) (ofAnalyticAt g hgy) := by
  classical
  rcases hdim : Module.finrank ℂ E with _ | n
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    exact Filter.Eventually.of_forall (fun y => by
      obtain rfl := Subsingleton.elim y x
      exact ⟨hf, hg, h⟩)
  · let en : E ≃L[ℂ] (Fin (n + 1) → ℂ) := by
      rw [← hdim]
      exact (Module.finBasis ℂ E).equivFunL
    let ep : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × ℂ :=
      (LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) (finSuccEquiv n)).trans
        ((LinearEquiv.piOptionEquivProd ℂ).trans (LinearEquiv.prodComm ℂ _ _))
    let e := en.trans ep.toContinuousLinearEquiv
    let H := e.symm.toHomeomorph.trans (Homeomorph.addRight x)
    have hH : ∀ z, AnalyticAt ℂ H z := fun z => (e.symm.analyticAt z).add analyticAt_const
    have hHi : ∀ y, AnalyticAt ℂ H.symm y := fun y =>
      (e.analyticAt (y + -x)).comp_of_eq (analyticAt_id.add analyticAt_const) rfl
    have hH0 : H 0 = x := by simp [H]
    have hfH : AnalyticAt ℂ (f ∘ H) 0 := hf.comp_of_eq (hH 0) hH0
    have hgH : AnalyticAt ℂ (g ∘ H) 0 := hg.comp_of_eq (hH 0) hH0
    let q := pullbackEquivOfEq H 0 (hH 0) (hHi _) hH0
    have hq : IsRelPrime (q (ofAnalyticAt f hf)) (q (ofAnalyticAt g hg)) :=
      IsRelPrime.of_map q.symm (by simpa only [AlgEquiv.symm_apply_apply] using h)
    have hHrel : IsRelPrime (ofAnalyticAt (f ∘ H) hfH) (ofAnalyticAt (g ∘ H) hgH) := by
      simpa only [q, pullbackEquivOfEq_ofAnalyticAt] using hq
    have hp := eventually_isRelPrime_ofAnalyticAt_prod hfH hgH hHrel
    simpa only [hH0] using eventually_isRelPrime_of_comp_homeomorph H hH hHi hp

/-- The locus where two functions are analytic and their germs are relatively prime is open. -/
theorem isOpen_isRelPrime_locus (f g : E → ℂ) :
    IsOpen {x | ∃ (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x),
      IsRelPrime (ofAnalyticAt f hf) (ofAnalyticAt g hg)} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨hf, hg, h⟩
  exact eventually_isRelPrime_ofAnalyticAt hf hg h

end SeveralComplexVariables.AnalyticGerm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
