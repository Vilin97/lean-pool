/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Germs of local biholomorphisms

This file packages the small amount of local-coordinate infrastructure needed by
the holomorphic constant-rank theorem.  A `LocalBiholomorphAt E F a b` consists of
analytic maps in both directions, carrying `a` to `b`, whose two composites agree
with the identity on neighborhoods of the relevant base points.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- An analytic isomorphism between neighborhoods of `a` and `b`.

The maps are globally defined representatives.  The inverse identities are germ
identities, which is the appropriate local notion and avoids choosing particular
open neighborhoods in the structure. -/
structure LocalBiholomorphAt
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (a : E) (b : F) where
  /-- The forward map representing the local biholomorphism. -/
  toFun : E → F
  /-- The inverse map representing the local biholomorphism. -/
  invFun : F → E
  map_source : toFun a = b
  map_target : invFun b = a
  analyticAt_toFun : AnalyticAt ℂ toFun a
  analyticAt_invFun : AnalyticAt ℂ invFun b
  left_inv : (fun x ↦ invFun (toFun x)) =ᶠ[𝓝 a] fun x ↦ x
  right_inv : (fun y ↦ toFun (invFun y)) =ᶠ[𝓝 b] fun y ↦ y

namespace LocalBiholomorphAt

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  {a : E} {b : F} {c : G}

@[simp]
theorem toFun_source (e : LocalBiholomorphAt E F a b) : e.toFun a = b :=
  e.map_source

@[simp]
theorem invFun_target (e : LocalBiholomorphAt E F a b) : e.invFun b = a :=
  e.map_target

/-- The forward representative tends to the target base point. -/
theorem toFun_tendsto (e : LocalBiholomorphAt E F a b) :
    Tendsto e.toFun (𝓝 a) (𝓝 b) := by
  have h := e.analyticAt_toFun.continuousAt
  change Tendsto e.toFun (𝓝 a) (𝓝 (e.toFun a)) at h
  simpa only [e.map_source] using h

/-- The inverse representative tends to the source base point. -/
theorem invFun_tendsto (e : LocalBiholomorphAt E F a b) :
    Tendsto e.invFun (𝓝 b) (𝓝 a) := by
  have h := e.analyticAt_invFun.continuousAt
  change Tendsto e.invFun (𝓝 b) (𝓝 (e.invFun b)) at h
  simpa only [e.map_target] using h

/-- A target neighborhood contains the forward image eventually. -/
theorem eventually_toFun_mem (e : LocalBiholomorphAt E F a b)
    {s : Set F} (hs : s ∈ 𝓝 b) :
    ∀ᶠ x in 𝓝 a, e.toFun x ∈ s :=
  e.toFun_tendsto hs

/-- A source neighborhood contains the inverse image eventually. -/
theorem eventually_invFun_mem (e : LocalBiholomorphAt E F a b)
    {s : Set E} (hs : s ∈ 𝓝 a) :
    ∀ᶠ y in 𝓝 b, e.invFun y ∈ s :=
  e.invFun_tendsto hs

/-- The forward representative is injective on some neighborhood of its source. -/
theorem exists_mem_nhds_injOn (e : LocalBiholomorphAt E F a b) :
    ∃ s ∈ 𝓝 a, Set.InjOn e.toFun s := by
  let s : Set E := {x | e.invFun (e.toFun x) = x}
  have hs : s ∈ 𝓝 a := e.left_inv
  refine ⟨s, hs, ?_⟩
  intro x hx y hy hxy
  calc
    x = e.invFun (e.toFun x) := (show e.invFun (e.toFun x) = x from hx).symm
    _ = e.invFun (e.toFun y) := congrArg e.invFun hxy
    _ = y := hy

/-- The derivative of a local biholomorphism is eventually a linear
isomorphism.  The conclusion is stated as bijectivity so it does not require
choosing continuous-linear equivalences at every nearby point. -/
theorem eventually_bijective_fderiv_toFun [CompleteSpace E] [CompleteSpace F]
    (e : LocalBiholomorphAt E F a b) :
    ∀ᶠ x in nhds a, Function.Bijective (fderiv ℂ e.toFun x) := by
  have hleft : ∀ᶠ x in nhds a,
      (fun z ↦ e.invFun (e.toFun z)) =ᶠ[nhds x] fun z ↦ z :=
    eventually_eventuallyEq_nhds.mpr e.left_inv
  have hrightTarget : ∀ᶠ y in nhds b,
      (e.toFun ∘ e.invFun) =ᶠ[nhds y] fun z ↦ z :=
    eventually_eventuallyEq_nhds.mpr <|
      e.right_inv.mono fun _ hz ↦ hz
  have hright := e.toFun_tendsto hrightTarget
  have hto := e.analyticAt_toFun.eventually_analyticAt
  have hinv := e.toFun_tendsto e.analyticAt_invFun.eventually_analyticAt
  filter_upwards [hleft, hright, hto, hinv] with x hl hr hta hia
  have hx : e.invFun (e.toFun x) = x := hl.self_of_nhds
  let B : E →L[ℂ] F := fderiv ℂ e.toFun x
  let C : F →L[ℂ] E := fderiv ℂ e.invFun (e.toFun x)
  have hCBderiv : HasFDerivAt (fun z ↦ e.invFun (e.toFun z)) (C.comp B) x := by
    exact hia.hasStrictFDerivAt.hasFDerivAt.comp x
      hta.hasStrictFDerivAt.hasFDerivAt
  have hCBatId : HasFDerivAt (fun z : E ↦ z) (C.comp B) x :=
    hCBderiv.congr_of_eventuallyEq hl.symm
  have hCB : C.comp B = ContinuousLinearMap.id ℂ E :=
    hCBatId.unique (hasFDerivAt_id x)
  have hta' : AnalyticAt ℂ e.toFun (e.invFun (e.toFun x)) := by
    simpa only [hx] using hta
  have hBCderiv : HasFDerivAt (e.toFun ∘ e.invFun) (B.comp C) (e.toFun x) := by
    simpa only [Function.comp_apply, B, C, hx] using
      hta'.hasStrictFDerivAt.hasFDerivAt.comp (e.toFun x)
        hia.hasStrictFDerivAt.hasFDerivAt
  have hBCatId : HasFDerivAt (fun z : F ↦ z) (B.comp C) (e.toFun x) :=
    hBCderiv.congr_of_eventuallyEq hr.symm
  have hBC : B.comp C = ContinuousLinearMap.id ℂ F :=
    hBCatId.unique (hasFDerivAt_id (e.toFun x))
  refine ⟨?_, ?_⟩
  · apply Function.LeftInverse.injective (g := C)
    intro v
    exact DFunLike.congr_fun hCB v
  · apply Function.RightInverse.surjective (g := C)
    intro w
    exact DFunLike.congr_fun hBC w

/-- The identity germ is a local biholomorphism. -/
def refl (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (a : E) :
    LocalBiholomorphAt E E a a where
  toFun := fun x ↦ x
  invFun := fun x ↦ x
  map_source := rfl
  map_target := rfl
  analyticAt_toFun := analyticAt_id
  analyticAt_invFun := analyticAt_id
  left_inv := Filter.Eventually.of_forall fun _ ↦ rfl
  right_inv := Filter.Eventually.of_forall fun _ ↦ rfl

/-- Reverse a local biholomorphism. -/
def symm (e : LocalBiholomorphAt E F a b) :
    LocalBiholomorphAt F E b a where
  toFun := e.invFun
  invFun := e.toFun
  map_source := e.map_target
  map_target := e.map_source
  analyticAt_toFun := e.analyticAt_invFun
  analyticAt_invFun := e.analyticAt_toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- The derivative of the inverse representative is eventually bijective. -/
theorem eventually_bijective_fderiv_invFun [CompleteSpace E] [CompleteSpace F]
    (e : LocalBiholomorphAt E F a b) :
    ∀ᶠ y in nhds b, Function.Bijective (fderiv ℂ e.invFun y) :=
  e.symm.eventually_bijective_fderiv_toFun

/-- Compose two local biholomorphisms with matching middle base point. -/
def trans (e : LocalBiholomorphAt E F a b)
    (h : LocalBiholomorphAt F G b c) :
    LocalBiholomorphAt E G a c where
  toFun := h.toFun ∘ e.toFun
  invFun := e.invFun ∘ h.invFun
  map_source := by simp
  map_target := by simp
  analyticAt_toFun :=
    h.analyticAt_toFun.comp_of_eq e.analyticAt_toFun e.map_source
  analyticAt_invFun :=
    e.analyticAt_invFun.comp_of_eq h.analyticAt_invFun h.map_target
  left_inv := by
    have hh := h.left_inv.comp_tendsto e.toFun_tendsto
    filter_upwards [e.left_inv, hh] with x hex hhx
    change e.invFun (h.invFun (h.toFun (e.toFun x))) = x
    have hhx' : h.invFun (h.toFun (e.toFun x)) = e.toFun x := by
      simpa only [Function.comp_apply] using hhx
    rw [hhx', hex]
  right_inv := by
    have he := e.right_inv.comp_tendsto h.invFun_tendsto
    filter_upwards [h.right_inv, he] with y hhy hey
    change h.toFun (e.toFun (e.invFun (h.invFun y))) = y
    have hey' : e.toFun (e.invFun (h.invFun y)) = h.invFun y := by
      simpa only [Function.comp_apply] using hey
    rw [hey', hhy]

/-- A continuous complex-linear equivalence, based at an arbitrary point. -/
def ofContinuousLinearEquiv (e : E ≃L[ℂ] F) (a : E) :
    LocalBiholomorphAt E F a (e a) where
  toFun := e
  invFun := e.symm
  map_source := rfl
  map_target := e.symm_apply_apply a
  analyticAt_toFun := e.toContinuousLinearMap.analyticAt a
  analyticAt_invFun := e.symm.toContinuousLinearMap.analyticAt (e a)
  left_inv := Filter.Eventually.of_forall e.symm_apply_apply
  right_inv := Filter.Eventually.of_forall e.apply_symm_apply

/-- A continuous complex-linear equivalence regarded as a biholomorphic germ
at the origin in both spaces. -/
def ofContinuousLinearEquivAtZero (e : E ≃L[ℂ] F) :
    LocalBiholomorphAt E F 0 0 where
  toFun := e
  invFun := e.symm
  map_source := map_zero e
  map_target := map_zero e.symm
  analyticAt_toFun := e.toContinuousLinearMap.analyticAt 0
  analyticAt_invFun := e.symm.toContinuousLinearMap.analyticAt 0
  left_inv := Filter.Eventually.of_forall e.symm_apply_apply
  right_inv := Filter.Eventually.of_forall e.apply_symm_apply

/-- The affine biholomorphism with linear part `e` sending `a` to `b`. -/
def affine (e : E ≃L[ℂ] F) (a : E) (b : F) :
    LocalBiholomorphAt E F a b where
  toFun := fun x ↦ e (x - a) + b
  invFun := fun y ↦ e.symm (y - b) + a
  map_source := by simp
  map_target := by simp
  analyticAt_toFun := by
    have hsub : AnalyticAt ℂ (fun x : E ↦ x - a) a :=
      analyticAt_id.sub analyticAt_const
    have he : AnalyticAt ℂ (fun x : E ↦ e (x - a)) a :=
      (e.toContinuousLinearMap.analyticAt 0).comp_of_eq hsub (by simp)
    exact he.add analyticAt_const
  analyticAt_invFun := by
    have hsub : AnalyticAt ℂ (fun y : F ↦ y - b) b :=
      analyticAt_id.sub analyticAt_const
    have he : AnalyticAt ℂ (fun y : F ↦ e.symm (y - b)) b :=
      (e.symm.toContinuousLinearMap.analyticAt 0).comp_of_eq hsub (by simp)
    exact he.add analyticAt_const
  left_inv := Filter.Eventually.of_forall fun x ↦ by simp
  right_inv := Filter.Eventually.of_forall fun y ↦ by simp

/-- Translation carrying `a` to `b`. -/
def translation (a b : E) : LocalBiholomorphAt E E a b :=
  affine (ContinuousLinearEquiv.refl ℂ E) a b

/-- A triangular analytic change of coordinates on a product, subtracting an
analytic function from the second coordinate. -/
def fiberShearAtZero
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (h : X → Y) (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 0) :
    LocalBiholomorphAt (X × Y) (X × Y) 0 0 where
  toFun := fun p ↦ (p.1, p.2 - h p.1)
  invFun := fun p ↦ (p.1, p.2 + h p.1)
  map_source := by ext <;> simp [h0]
  map_target := by ext <;> simp [h0]
  analyticAt_toFun := by
    have hc : AnalyticAt ℂ (fun p : X × Y ↦ h p.1) 0 :=
      hh.comp_of_eq analyticAt_fst (by simp)
    exact analyticAt_fst.prod (analyticAt_snd.sub hc)
  analyticAt_invFun := by
    have hc : AnalyticAt ℂ (fun p : X × Y ↦ h p.1) 0 :=
      hh.comp_of_eq analyticAt_fst (by simp)
    exact analyticAt_fst.prod (analyticAt_snd.add hc)
  left_inv := Filter.Eventually.of_forall fun p ↦ by
    ext <;> simp
  right_inv := Filter.Eventually.of_forall fun p ↦ by
    ext <;> simp

/-- An analytic map with an explicitly invertible derivative is locally biholomorphic. -/
def ofAnalyticAtOfFDerivEquiv [CompleteSpace E]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (e : E ≃L[ℂ] F) (he : fderiv ℂ f a = (e : E →L[ℂ] F)) :
    LocalBiholomorphAt E F a (f a) := by
  have hs : HasStrictFDerivAt f (e : E →L[ℂ] F) a := by
    simpa only [he] using hf.hasStrictFDerivAt
  let R : OpenPartialHomeomorph E F := hs.toOpenPartialHomeomorph f
  have hR_source : a ∈ R.source := hs.mem_toOpenPartialHomeomorph_source
  have hR_analytic : AnalyticAt ℂ (R : E → F) a := by
    simpa only [R, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hf
  have hR_fderiv : fderiv ℂ (R : E → F) a = (e : E →L[ℂ] F) := by
    simpa only [R, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using he
  refine
    { toFun := f
      invFun := hs.localInverse f e a
      map_source := rfl
      map_target := hs.localInverse_apply_image
      analyticAt_toFun := hf
      analyticAt_invFun := ?_
      left_inv := hs.eventually_left_inverse
      right_inv := hs.eventually_right_inverse }
  change AnalyticAt ℂ (R.symm : F → E) (R a)
  exact R.analyticAt_symm' hR_source hR_analytic hR_fderiv

/-- An analytic map with bijective derivative is locally biholomorphic. -/
def ofAnalyticAtOfBijectiveFDeriv [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (hbij : Function.Bijective (fderiv ℂ f a)) :
    LocalBiholomorphAt E F a (f a) := by
  let e : E ≃L[ℂ] F := ContinuousLinearEquiv.ofBijective (fderiv ℂ f a)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  apply ofAnalyticAtOfFDerivEquiv hf e
  rfl

/-- The normalized inverse-function-theorem chart, sending `a` to the origin. -/
def ofAnalyticAtOfBijectiveFDerivToZero [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (hbij : Function.Bijective (fderiv ℂ f a)) :
    LocalBiholomorphAt E F a 0 :=
  (ofAnalyticAtOfBijectiveFDeriv hf hbij).trans (translation (f a) 0)

/-- The fully centered inverse-function-theorem chart.  Its forward
representative is locally the map `x ↦ f (x + a) - f a`, so both marked
base points are the origin. -/
def ofAnalyticAtOfBijectiveFDerivCentered [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (hbij : Function.Bijective (fderiv ℂ f a)) :
    LocalBiholomorphAt E F 0 0 :=
  (translation 0 a).trans
    ((ofAnalyticAtOfBijectiveFDeriv hf hbij).trans (translation (f a) 0))

end LocalBiholomorphAt

end

end LocalComplexGeometry
