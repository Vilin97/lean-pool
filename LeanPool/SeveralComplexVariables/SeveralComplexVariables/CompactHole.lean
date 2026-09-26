/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CauchyTransform

/-!
# Hartogs' compact-hole extension theorem in a product space

Ehrenpreis' proof of Hartogs' extension theorem. Let `D ⊆ ℂ × G` be open with `G` a nontrivial
finite-dimensional complex normed space, `K ⊆ D` compact with `D \ K` connected, and `f`
holomorphic on `D \ K`. A smooth cutoff `φ` equal to one near `K` with compact support in `D`
gives the smooth function `F₀ = (1 - φ) f`, extended by zero across `K`. Its antiholomorphic
derivatives `∂F₀/∂\bar z` along every direction are compactly supported, and their symmetry,
from the symmetry of the second derivative of `F₀`, shows that the Cauchy transform `u` in the
first variable of `∂F₀/∂\bar z₁` has the same antiholomorphic derivatives as `F₀`. Hence `F₀ -
u` is holomorphic on `D`. On the open set of points of `D` whose second coordinate lies outside
the projection of the support of `φ`, both `F₀ = f` and `u = 0`; this set is nonempty because
the projection of `D` cannot be compact, and the identity principle on `D \ K` finishes the
proof.

References: [Hörmander][Hormander1973] (1973), Theorem 2.3.2;
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Theorem 4.2.5; [Boas][Boas2013] (2013), Section
2.4.

## Main results

* `exists_analyticOnNhd_extension_of_isCompact_prod`: **Hartogs' compact-hole extension theorem in a
  product space.** For an open set `D ⊆ ℂ × G` with `G` a nontrivial finite-dimensional complex
  normed space, a compact `K ⊆ D` with `D \ K` connected, and `f` holomorphic on `D \ K`, there is a
  holomorphic function on `D` agreeing with `f` on `D \ K`.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Complex MeasureTheory Set Filter Metric Function
open scoped Topology

namespace SeveralComplexVariables

section Symmetry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The antiholomorphic derivatives of a `C²` function commute: the antiholomorphic part along `v'`
of the derivative of `∂F₀/∂\bar z_v` equals the antiholomorphic part along `v` of the derivative
of `∂F₀/∂\bar z_{v'}`. -/
theorem dbarAlong_fderiv_dbarAlong_fderiv_symm {F₀ : E → F} {x : E} (hF : ContDiffAt ℝ 2 F₀ x)
    (v v' : E) :
    dbarAlong (fderiv ℝ (fun y => dbarAlong (fderiv ℝ F₀ y) v) x) v' =
      dbarAlong (fderiv ℝ (fun y => dbarAlong (fderiv ℝ F₀ y) v') x) v := by
  have hsymm : IsSymmSndFDerivAt ℝ F₀ x := hF.isSymmSndFDerivAt (by simp)
  have hd : HasFDerivAt (fderiv ℝ F₀) (fderiv ℝ (fderiv ℝ F₀) x) x :=
    ((hF.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  set D2 := fderiv ℝ (fderiv ℝ F₀) x with hD2
  have key : ∀ u : E, HasFDerivAt (fun y => dbarAlong (fderiv ℝ F₀ y) u)
      ((2 : ℂ)⁻¹ • (D2.flip u + I • D2.flip (I • u))) x := by
    intro u
    have h1 : HasFDerivAt (fun y => fderiv ℝ F₀ y u) (D2.flip u) x := by
      have := hd.clm_apply (hasFDerivAt_const u x)
      simpa using this
    have h2 : HasFDerivAt (fun y => fderiv ℝ F₀ y (I • u)) (D2.flip (I • u)) x := by
      have := hd.clm_apply (hasFDerivAt_const (I • u) x)
      simpa using this
    exact (h1.add (h2.const_smul I)).const_smul (2 : ℂ)⁻¹
  rw [(key v).fderiv, (key v').fderiv]
  simp only [dbarAlong, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply,
    ContinuousLinearMap.flip_apply]
  rw [hsymm v' v, hsymm v' (I • v), hsymm (I • v') v, hsymm (I • v') (I • v)]
  module

end Symmetry

section Cutoff

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

open scoped ContDiff

/-- Cutoff data for a compact hole `K` in an open set `D`: a smooth function equal to one on an open
neighborhood of `K`, with open support `s` whose closure is compact in `D`. -/
private structure HoleCutoffData (D K : Set (ℂ × G)) where
  /-- The cutoff function. -/
  φ : ℂ × G → ℝ
  /-- An open neighborhood of `K` on which the cutoff equals one. -/
  neighborhood : Set (ℂ × G)
  /-- The support of the cutoff. -/
  s : Set (ℂ × G)
  /-- The cutoff is smooth. -/
  contDiff : ContDiff ℝ ∞ φ
  /-- The neighborhood on which the cutoff equals one is open. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The neighborhood contains the hole. -/
  subset_neighborhood : K ⊆ neighborhood
  /-- The cutoff equals one on the neighborhood of the hole. -/
  eq_one : ∀ x ∈ neighborhood, φ x = 1
  /-- The support is open. -/
  isOpen_s : IsOpen s
  /-- The specified support is the nonzero locus of the cutoff. -/
  support_eq : support φ = s
  /-- The support has compact closure. -/
  isCompact_closure : IsCompact (closure s)
  /-- The closure of the support lies in the original domain. -/
  closure_subset : closure s ⊆ D

omit [NormedSpace ℂ F] [CompleteSpace F] in
/-- Existence of cutoff data, from a smooth Urysohn function on thickenings of `K`. -/
private theorem nonempty_holeCutoffData {D K : Set (ℂ × G)} (hD : IsOpen D) (hK : IsCompact K)
    (hKD : K ⊆ D) : Nonempty (HoleCutoffData D K) := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open hD hKD
  obtain ⟨φ, hφ, -, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤) (E := ℂ × G)
    (isOpen_thickening (δ := δ / 2) (E := K)) (isClosed_cthickening (δ := δ / 4) (E := K))
    (cthickening_subset_thickening' (by positivity) (by linarith) K)
  refine ⟨⟨φ, thickening (δ / 4) K, thickening (δ / 2) K, hφ, isOpen_thickening,
    self_subset_thickening (by positivity) K,
    fun x hx => (hone x).mp (thickening_subset_cthickening _ _ hx), isOpen_thickening, hsupp,
    ?_, ?_⟩⟩
  · exact (hK.cthickening (r := δ / 2)).of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening _ _)
  · exact (closure_thickening_subset_cthickening _ _).trans
      ((cthickening_mono (by linarith) K).trans hδD)

omit [FiniteDimensional ℂ G] [NormedSpace ℂ F] [CompleteSpace F] in
/-- The hole lies in the support of the cutoff. -/
private theorem HoleCutoffData.subset_s {D K : Set (ℂ × G)} (h : HoleCutoffData D K) : K ⊆ h.s :=
  fun x hx => by
    rw [← h.support_eq, mem_support, h.eq_one x (h.subset_neighborhood hx)]
    exact one_ne_zero

omit [FiniteDimensional ℂ G] [NormedSpace ℂ F] [CompleteSpace F] in
/-- The cutoff vanishes outside its support. -/
private theorem HoleCutoffData.eq_zero_of_notMem {D K : Set (ℂ × G)} (h : HoleCutoffData D K)
    {x : ℂ × G} (hx : x ∉ h.s) : h.φ x = 0 := by
  rw [← h.support_eq] at hx
  exact notMem_support.mp hx

omit [FiniteDimensional ℂ G] [NormedSpace ℂ F] [CompleteSpace F] in
/-- Points outside the closure of the support are outside the hole. -/
private theorem HoleCutoffData.notMem_hole_of_notMem_closure {D K : Set (ℂ × G)}
    (h : HoleCutoffData D K)
    {x : ℂ × G} (hx : x ∉ closure h.s) : x ∉ K :=
  fun hxK => hx (subset_closure (h.subset_s hxK))

open scoped Classical in
/-- The modification `(1 - φ) • f`, set to zero on the hole. -/
private def holeCutoff (K : Set (ℂ × G)) (φ : ℂ × G → ℝ) (f : ℂ × G → F) (x : ℂ × G) : F :=
  if x ∈ K then 0 else (1 - φ x) • f x

omit [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace F] in
/-- The modified function vanishes where the cutoff equals one. -/
private theorem holeCutoff_eq_zero_of_one {K : Set (ℂ × G)} {φ : ℂ × G → ℝ} {f : ℂ × G → F}
    {x : ℂ × G}
    (hx : φ x = 1) : holeCutoff K φ f x = 0 := by
  unfold holeCutoff
  split_ifs <;> simp [hx]

omit [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace F] in
/-- Off the hole and off the support of the cutoff, the modified function is `f`. -/
private theorem holeCutoff_eq_of_zero {K : Set (ℂ × G)} {φ : ℂ × G → ℝ} {f : ℂ × G → F} {x : ℂ × G}
    (hxK : x ∉ K) (hx : φ x = 0) : holeCutoff K φ f x = f x := by
  simp [holeCutoff, hxK, hx]

variable {D K : Set (ℂ × G)} {f : ℂ × G → F}

omit [FiniteDimensional ℂ G] in
/-- The modified function is `C²` on `D`. -/
private theorem contDiffAt_holeCutoff (h : HoleCutoffData D K) (hD : IsOpen D) (hKc : IsClosed K)
    (hf : AnalyticOnNhd ℂ f (D \ K)) {x : ℂ × G} (hx : x ∈ D) :
    ContDiffAt ℝ 2 (holeCutoff K h.φ f) x := by
  by_cases hxU : x ∈ h.neighborhood
  · have heq : holeCutoff K h.φ f =ᶠ[𝓝 x] fun _ => (0 : F) :=
      eventuallyEq_of_mem (h.isOpen_neighborhood.mem_nhds hxU) fun y hy =>
        holeCutoff_eq_zero_of_one (h.eq_one y hy)
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hxK : x ∉ K := fun hxK => hxU (h.subset_neighborhood hxK)
    have hmem : x ∈ D \ K := ⟨hx, hxK⟩
    have heq : holeCutoff K h.φ f =ᶠ[𝓝 x] fun y => (1 - h.φ y) • f y :=
      eventuallyEq_of_mem ((hD.sdiff hKc).mem_nhds hmem) fun y hy => by
        simp [holeCutoff, hy.2]
    have hfc : ContDiffAt ℝ 2 f x := (hf x hmem).contDiffAt.restrict_scalars ℝ
    have hφc : ContDiffAt ℝ 2 h.φ x := h.contDiff.contDiffAt.of_le (by simp)
    exact ((contDiffAt_const.sub hφc).smul hfc).congr_of_eventuallyEq heq

omit [FiniteDimensional ℂ G] [CompleteSpace F] in
/-- Away from the closure of the support of the cutoff, the modified function is `f`. -/
private theorem holeCutoff_eventuallyEq (h : HoleCutoffData D K) (x : ℂ × G) (hx : x ∉ closure h.s)
    :
    holeCutoff K h.φ f =ᶠ[𝓝 x] f :=
  eventuallyEq_of_mem (isClosed_closure.isOpen_compl.mem_nhds hx) fun _ hy =>
    holeCutoff_eq_of_zero (h.notMem_hole_of_notMem_closure hy)
      (h.eq_zero_of_notMem fun hs => hy (subset_closure hs))

open scoped Classical in
/-- The antiholomorphic derivative of a function on `D` along a direction, extended by zero. -/
private def dbarExt (D : Set (ℂ × G)) (F₀ : ℂ × G → F) (v : ℂ × G) (x : ℂ × G) : F :=
  if x ∈ D then dbarAlong (fderiv ℝ F₀ x) v else 0

omit [FiniteDimensional ℂ G] [CompleteSpace F] in
/-- On `D`, the extended derivative is the antiholomorphic derivative. -/
private theorem dbarExt_eventuallyEq (hD : IsOpen D) {F₀ : ℂ × G → F} {v x : ℂ × G} (hx : x ∈ D) :
    dbarExt D F₀ v =ᶠ[𝓝 x] fun y => dbarAlong (fderiv ℝ F₀ y) v :=
  eventuallyEq_of_mem (hD.mem_nhds hx) fun y hy => by simp [dbarExt, hy]

omit [FiniteDimensional ℂ G] [CompleteSpace F] in
/-- The value of the extended derivative at a point of `D`. -/
private theorem dbarExt_of_mem {F₀ : ℂ × G → F} {v x : ℂ × G} (hx : x ∈ D) :
    dbarExt D F₀ v x = dbarAlong (fderiv ℝ F₀ x) v := by simp [dbarExt, hx]

omit [FiniteDimensional ℂ G] [CompleteSpace F] in
/-- The extended antiholomorphic derivatives vanish outside the closure of the support. -/
private theorem dbarExt_holeCutoff_eq_zero (h : HoleCutoffData D K)
    (hf : AnalyticOnNhd ℂ f (D \ K)) (v : ℂ × G) {x : ℂ × G}
    (hx : x ∉ closure h.s) : dbarExt D (holeCutoff K h.φ f) v x = 0 := by
  by_cases hxD : x ∈ D
  · rw [dbarExt_of_mem hxD, (holeCutoff_eventuallyEq h (f := f) x hx).fderiv_eq,
      (hf x ⟨hxD, h.notMem_hole_of_notMem_closure hx⟩).differentiableAt.fderiv_restrictScalars ℝ,
      dbarAlong_restrictScalars]
  · simp [dbarExt, hxD]

omit [FiniteDimensional ℂ G] in
/-- The extended antiholomorphic derivatives of the modified function are `C¹`. -/
private theorem contDiff_dbarExt_holeCutoff (h : HoleCutoffData D K) (hD : IsOpen D)
    (hKc : IsClosed K)
    (hf : AnalyticOnNhd ℂ f (D \ K)) (v : ℂ × G) :
    ContDiff ℝ 1 (dbarExt D (holeCutoff K h.φ f) v) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ D
  · have hfd : ContDiffAt ℝ 1 (fderiv ℝ (holeCutoff K h.φ f)) x :=
      (contDiffAt_holeCutoff h hD hKc hf hx).fderiv_right (m := 1) le_rfl
    have : ContDiffAt ℝ 1 (fun y => dbarAlong (fderiv ℝ (holeCutoff K h.φ f) y) v) x := by
      unfold dbarAlong
      exact contDiffAt_const.smul ((hfd.clm_apply contDiffAt_const).add
        (contDiffAt_const.smul (hfd.clm_apply contDiffAt_const)))
    exact this.congr_of_eventuallyEq (dbarExt_eventuallyEq hD hx)
  · have hxs : x ∉ closure h.s := fun hc => hx (h.closure_subset hc)
    have heq : dbarExt D (holeCutoff K h.φ f) v =ᶠ[𝓝 x] fun _ => (0 : F) :=
      eventuallyEq_of_mem (isClosed_closure.isOpen_compl.mem_nhds hxs) fun y hy =>
        dbarExt_holeCutoff_eq_zero h hf v hy
    exact contDiffAt_const.congr_of_eventuallyEq heq

omit [FiniteDimensional ℂ G] [CompleteSpace F] in
/-- The extended antiholomorphic derivatives of the modified function have compact support. -/
private theorem hasCompactSupport_dbarExt_holeCutoff (h : HoleCutoffData D K)
    (hf : AnalyticOnNhd ℂ f (D \ K)) (v : ℂ × G) :
    HasCompactSupport (dbarExt D (holeCutoff K h.φ f) v) :=
  HasCompactSupport.intro h.isCompact_closure fun _ hx => dbarExt_holeCutoff_eq_zero h hf v hx

omit [FiniteDimensional ℂ G] in
/-- Symmetry of the extended antiholomorphic derivatives. -/
private theorem dbarAlong_fderiv_dbarExt_holeCutoff_symm (h : HoleCutoffData D K) (hD : IsOpen D)
    (hKc : IsClosed K)
    (hf : AnalyticOnNhd ℂ f (D \ K)) (y v v' : ℂ × G) :
    dbarAlong (fderiv ℝ (dbarExt D (holeCutoff K h.φ f) v) y) v' =
      dbarAlong (fderiv ℝ (dbarExt D (holeCutoff K h.φ f) v') y) v := by
  by_cases hy : y ∈ D
  · rw [(dbarExt_eventuallyEq hD hy).fderiv_eq, (dbarExt_eventuallyEq hD hy).fderiv_eq]
    exact dbarAlong_fderiv_dbarAlong_fderiv_symm (contDiffAt_holeCutoff h hD hKc hf hy) v v'
  · have hys : y ∉ closure h.s := fun hc => hy (h.closure_subset hc)
    have hz : ∀ u : ℂ × G, fderiv ℝ (dbarExt D (holeCutoff K h.φ f) u) y = 0 := by
      intro u
      have heq : dbarExt D (holeCutoff K h.φ f) u =ᶠ[𝓝 y] fun _ => (0 : F) :=
        eventuallyEq_of_mem (isClosed_closure.isOpen_compl.mem_nhds hys) fun z hz =>
          dbarExt_holeCutoff_eq_zero h hf u hz
      rw [heq.fderiv_eq, fderiv_const_apply]
    rw [hz, hz, dbarAlong_zero, dbarAlong_zero]

end Cutoff

section Main

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Nontrivial G] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Hartogs' compact-hole extension theorem in a product space.** For an open set
`D ⊆ ℂ × G` with `G` a nontrivial finite-dimensional complex normed space, a compact `K ⊆ D`
with `D \ K` connected, and `f` holomorphic on `D \ K`, there is a holomorphic function on `D`
agreeing with `f` on `D \ K`. -/
theorem exists_analyticOnNhd_extension_of_isCompact_prod {D K : Set (ℂ × G)} (hD : IsOpen D)
    (hK : IsCompact K) (hKD : K ⊆ D) (hconn : IsPreconnected (D \ K)) {f : ℂ × G → F}
    (hf : AnalyticOnNhd ℂ f (D \ K)) :
    ∃ g : ℂ × G → F, AnalyticOnNhd ℂ g D ∧ EqOn g f (D \ K) := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    exact ⟨f, by simpa using hf, fun x _ => rfl⟩
  obtain ⟨h⟩ := nonempty_holeCutoffData hD hK hKD
  have hKc : IsClosed K := hK.isClosed
  set F₀ := holeCutoff K h.φ f with hF₀
  set e₁ : ℂ × G := ((1 : ℂ), (0 : G)) with he₁
  have hg1 : ∀ v, ContDiff ℝ 1 (dbarExt D F₀ v) := contDiff_dbarExt_holeCutoff h hD hKc hf
  have hgs : ∀ v, HasCompactSupport (dbarExt D F₀ v) := hasCompactSupport_dbarExt_holeCutoff h hf
  set u := cauchyTransformFst (dbarExt D F₀ e₁) with hu
  set g : ℂ × G → F := fun x => F₀ x - u x with hg
  have hdiff : DifferentiableOn ℂ g D := by
    intro x hx
    have hF₀d : HasFDerivAt F₀ (fderiv ℝ F₀ x) x :=
      ((contDiffAt_holeCutoff h hD hKc hf hx).differentiableAt (by norm_num)).hasFDerivAt
    have hud : HasFDerivAt u (fderiv ℝ u x) x :=
      (hasFDerivAt_cauchyTransformFst (hg1 e₁) (hgs e₁) x).differentiableAt.hasFDerivAt
    have hL : HasFDerivAt g (fderiv ℝ F₀ x - fderiv ℝ u x) x := hF₀d.sub hud
    have hdbar : ∀ v, dbarAlong (fderiv ℝ F₀ x - fderiv ℝ u x) v = 0 := by
      intro v
      rw [dbarAlong_sub, dbarAlong_fderiv_cauchyTransformFst (hg1 e₁) (hgs e₁) x v]
      have hsym : ∀ w : ℂ, dbarAlong (fderiv ℝ (dbarExt D F₀ e₁) (x - (w, 0))) v =
          dbarAlong (fderiv ℝ (dbarExt D F₀ v) (x - (w, 0))) e₁ := fun w =>
        dbarAlong_fderiv_dbarExt_holeCutoff_symm h hD hKc hf _ e₁ v
      simp_rw [hsym]
      rw [integral_inv_smul_dbarAlong_fderiv_sub (hg1 v) (hgs v) x, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast Real.pi_ne_zero), one_smul, dbarExt_of_mem hx,
        sub_self]
    exact (hasFDerivAt_of_restrictScalars ℝ hL
      (restrictScalars_complexLinearOfDbar _ hdbar)).differentiableAt.differentiableWithinAt
  have hga : AnalyticOnNhd ℂ g D := hdiff.analyticOnNhd_of_finiteDimensional hD
  set T := Prod.snd '' closure h.s with hT
  have hTc : IsCompact T := h.isCompact_closure.image continuous_snd
  set V := D ∩ Prod.snd ⁻¹' Tᶜ with hV
  have hVo : IsOpen V := hD.inter (hTc.isClosed.isOpen_compl.preimage continuous_snd)
  have hVsub : V ⊆ D \ K := fun x hx =>
    ⟨hx.1, fun hxK => hx.2 (mem_image_of_mem _ (subset_closure (h.subset_s hxK)))⟩
  have hVne : V.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have h1 : Prod.snd '' D ⊆ T := by
      rintro _ ⟨x, hx, rfl⟩
      by_contra hxT
      exact (eq_empty_iff_forall_notMem.mp hemp) x ⟨hx, hxT⟩
    have h2 : T ⊆ Prod.snd '' D := image_mono h.closure_subset
    have heq : Prod.snd '' D = T := Subset.antisymm h1 h2
    have hopen : IsOpen (Prod.snd '' D) := isOpenMap_snd D hD
    have hne : (Prod.snd '' D).Nonempty := (hKne.mono hKD).image _
    have hclopen : IsClopen (Prod.snd '' D) := ⟨by rw [heq]; exact hTc.isClosed, hopen⟩
    have huniv := hclopen.eq_univ hne
    have hcpt : IsCompact (univ : Set G) := by
      rw [← huniv, heq]
      exact hTc
    exact NoncompactSpace.noncompact_univ hcpt
  obtain ⟨x₀, hx₀⟩ := hVne
  have hgf : EqOn g f V := by
    intro x hx
    have hxs : x ∉ closure h.s := fun hc => hx.2 (mem_image_of_mem _ hc)
    have hF : F₀ x = f x :=
      holeCutoff_eq_of_zero (h.notMem_hole_of_notMem_closure hxs)
        (h.eq_zero_of_notMem fun hs => hxs (subset_closure hs))
    have hu0 : u x = 0 := by
      have hz : ∀ z : ℂ, dbarExt D F₀ e₁ (z, x.2) = 0 := fun z =>
        dbarExt_holeCutoff_eq_zero h hf e₁ fun hc => hx.2 ⟨(z, x.2), hc, rfl⟩
      have := cauchyTransformFst_eq_zero hz x.1
      simpa using this
    change F₀ x - u x = f x
    rw [hF, hu0, sub_zero]
  refine ⟨g, hga, ?_⟩
  exact (hga.mono sdiff_subset).eqOn_of_preconnected_of_eventuallyEq hf hconn (hVsub hx₀)
    (eventuallyEq_of_mem (hVo.mem_nhds hx₀) hgf)

end Main

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
