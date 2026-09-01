/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Analytic.ConstantRank

/-!
# Regular holomorphic level sets

A surjective derivative at one point gives a local analytic parametrization of
the corresponding fiber.  The parameter space has the expected complex
dimension `n - m`.  Besides the analytic parameter map, the interface exposes
an analytic ambient fiber-coordinate map and eventual two-sided inverse laws,
so the conclusion is stronger than a dimension count.
-/


open Filter
open scoped Topology

namespace LocalComplexGeometry

noncomputable section

/-- An explicit local analytic parametrization of the fiber
`F⁻¹(F a)` by `ℂ^(n-m)`.

The parameter and fiber-coordinate maps are analytic at their marked points.
They are locally inverse on the parameter space and on the level set, and the
parameter map lands in the level set on a neighborhood of the origin. -/
structure IsLocalLevelSetParametrization
    {n m : ℕ}
    (F : ComplexEuclidean n → ComplexEuclidean m)
    (a : ComplexEuclidean n)
    (parameter : ComplexEuclidean (n - m) → ComplexEuclidean n)
    (fiberCoordinate : ComplexEuclidean n → ComplexEuclidean (n - m)) :
    Prop where
  parameter_zero : parameter 0 = a
  fiberCoordinate_base : fiberCoordinate a = 0
  analyticAt_parameter : AnalyticAt ℂ parameter 0
  analyticAt_fiberCoordinate : AnalyticAt ℂ fiberCoordinate a
  left_inv :
    (fun u ↦ fiberCoordinate (parameter u)) =ᶠ[𝓝 0] fun u ↦ u
  parameter_mem_fiber :
    (fun u ↦ F (parameter u)) =ᶠ[𝓝 0] fun _ ↦ F a
  right_inv_on_fiber :
    ∀ᶠ x in 𝓝 a, F x = F a → parameter (fiberCoordinate x) = x

namespace IsLocalLevelSetParametrization

/-- Near the base point, membership in the regular level set is exactly
recovery by the local parameter/fiber-coordinate pair. -/
theorem eventually_mem_fiber_iff
    {n m : ℕ}
    {F : ComplexEuclidean n → ComplexEuclidean m}
    {a : ComplexEuclidean n}
    {parameter : ComplexEuclidean (n - m) → ComplexEuclidean n}
    {fiberCoordinate : ComplexEuclidean n → ComplexEuclidean (n - m)}
    (h : IsLocalLevelSetParametrization F a parameter fiberCoordinate) :
    ∀ᶠ x in 𝓝 a,
      (F x = F a ↔ parameter (fiberCoordinate x) = x) := by
  have hcoord : Tendsto fiberCoordinate (𝓝 a) (𝓝 0) := by
    have hc := h.analyticAt_fiberCoordinate.continuousAt
    change Tendsto fiberCoordinate (𝓝 a) (𝓝 (fiberCoordinate a)) at hc
    simpa only [h.fiberCoordinate_base] using hc
  have hparameterFiber := hcoord h.parameter_mem_fiber
  filter_upwards [h.right_inv_on_fiber, hparameterFiber] with x hright hparam
  constructor
  · exact hright
  · intro hx
    change F (parameter (fiberCoordinate x)) = F a at hparam
    rw [hx] at hparam
    exact hparam

/-- The parameter map is injective on some neighborhood of the origin. -/
theorem exists_mem_nhds_parameter_injOn
    {n m : ℕ}
    {F : ComplexEuclidean n → ComplexEuclidean m}
    {a : ComplexEuclidean n}
    {parameter : ComplexEuclidean (n - m) → ComplexEuclidean n}
    {fiberCoordinate : ComplexEuclidean n → ComplexEuclidean (n - m)}
    (h : IsLocalLevelSetParametrization F a parameter fiberCoordinate) :
    ∃ s ∈ 𝓝 (0 : ComplexEuclidean (n - m)), Set.InjOn parameter s := by
  let s : Set (ComplexEuclidean (n - m)) :=
    {u | fiberCoordinate (parameter u) = u}
  have hs : s ∈ 𝓝 (0 : ComplexEuclidean (n - m)) := h.left_inv
  refine ⟨s, hs, ?_⟩
  intro u hu v hv huv
  calc
    u = fiberCoordinate (parameter u) := hu.symm
    _ = fiberCoordinate (parameter v) := congrArg fiberCoordinate huv
    _ = v := hv

end IsLocalLevelSetParametrization

/-- **Holomorphic regular level-set theorem.**  If the derivative of a
holomorphic map is surjective at `a`, then the local fiber through `a` is
analytically parametrized by a neighborhood of the origin in `ℂ^(n-m)`, with
an analytic local inverse defined on the ambient source.

Only surjectivity at the marked point is assumed; no separate neighborhood
constant-rank hypothesis is needed. -/
theorem holomorphic_regularLevelSet_parametrization
    {n m : ℕ}
    {F : ComplexEuclidean n → ComplexEuclidean m}
    {a : ComplexEuclidean n}
    (hF : AnalyticAt ℂ F a)
    (hsurj : Function.Surjective (fderiv ℂ F a)) :
    ∃ (parameter : ComplexEuclidean (n - m) → ComplexEuclidean n)
      (fiberCoordinate : ComplexEuclidean n → ComplexEuclidean (n - m)),
      IsLocalLevelSetParametrization F a parameter fiberCoordinate := by
  let A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m := fderiv ℂ F a
  let K : Submodule ℂ (ComplexEuclidean n) :=
    LinearMap.ker A.toLinearMap
  let : CompleteSpace K := FiniteDimensional.complete ℂ K
  obtain ⟨L, hKL⟩ := Submodule.exists_isCompl K
  have hKLtop : Submodule.IsTopCompl K L :=
    Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hKL
      K.closed_of_finiteDimensional
  let kproj : ComplexEuclidean n →L[ℂ] K :=
    K.projectionOntoL L hKLtop
  have hkerCompl : IsCompl (LinearMap.ker A.toLinearMap)
      (LinearMap.ker kproj.toLinearMap) := by
    simpa [K, kproj] using hKL
  let eLin : ComplexEuclidean n ≃ₗ[ℂ] ComplexEuclidean m × K :=
    LinearMap.equivProdOfSurjectiveOfIsCompl A.toLinearMap kproj.toLinearMap
      (LinearMap.range_eq_top.mpr hsurj)
      (Submodule.range_projectionOntoL hKLtop)
      hkerCompl
  let eDeriv : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m × K :=
    eLin.toContinuousLinearEquiv
  let H : ComplexEuclidean n → ComplexEuclidean m × K :=
    fun x ↦ (F x - F a, kproj (x - a))
  have hkAnalytic : AnalyticAt ℂ (fun x ↦ kproj (x - a)) a := by
    exact (kproj.analyticAt 0).comp_of_eq
      (analyticAt_id.sub analyticAt_const) (by simp)
  have hHAnalytic : AnalyticAt ℂ H a := by
    exact (hF.sub analyticAt_const).prod hkAnalytic
  have hfirstDeriv :
      HasFDerivAt (fun x ↦ F x - F a) A a := by
    simpa only [A] using
      hF.hasStrictFDerivAt.hasFDerivAt.sub_const (F a)
  have hkDeriv : HasFDerivAt (fun x ↦ kproj (x - a)) kproj a := by
    have hc : HasFDerivAt (kproj ∘ fun x ↦ x - a) kproj a := by
      simpa only [id_eq, ContinuousLinearMap.comp_id] using
        kproj.hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const a)
    exact hc.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun _ ↦ rfl
  have hHDeriv : HasFDerivAt H (A.prod kproj) a := by
    exact hfirstDeriv.prodMk hkDeriv
  have hHfderiv : fderiv ℂ H a = (eDeriv : _ →L[ℂ] _) := by
    rw [hHDeriv.fderiv]
    ext x <;> rfl
  let chiRaw := LocalBiholomorphAt.ofAnalyticAtOfFDerivEquiv
    hHAnalytic eDeriv hHfderiv
  have hHcenter : H a = (0, 0) := by
    simp [H]
  let chi : LocalBiholomorphAt
      (ComplexEuclidean n) (ComplexEuclidean m × K) a (0, 0) :=
    { toFun := H
      invFun := chiRaw.invFun
      map_source := hHcenter
      map_target := by
        rw [← hHcenter]
        exact chiRaw.map_target
      analyticAt_toFun := hHAnalytic
      analyticAt_invFun := by
        simpa only [hHcenter] using chiRaw.analyticAt_invFun
      left_inv := chiRaw.left_inv
      right_inv := by
        have h :
            (fun y ↦ chiRaw.toFun (chiRaw.invFun y)) =ᶠ[𝓝 (0, 0)]
              fun y ↦ y := by
          simpa only [hHcenter] using chiRaw.right_inv
        exact h.mono fun y hy ↦ by
          change H (chiRaw.invFun y) = y at hy
          exact hy }
  have hKrank : Module.finrank ℂ K = n - m := by
    have hdim := LinearMap.finrank_range_add_finrank_ker A.toLinearMap
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
      Module.finrank_fin_fun, Module.finrank_fin_fun] at hdim
    change Module.finrank ℂ (LinearMap.ker A.toLinearMap) = n - m
    omega
  let kernelCoord : K ≃L[ℂ] ComplexEuclidean (n - m) :=
    ContinuousLinearEquiv.ofFinrankEq <| by
      simpa only [Module.finrank_fin_fun] using hKrank
  let parameter : ComplexEuclidean (n - m) → ComplexEuclidean n :=
    fun u ↦ chi.invFun (0, kernelCoord.symm u)
  let fiberCoordinate : ComplexEuclidean n → ComplexEuclidean (n - m) :=
    fun x ↦ kernelCoord (chi.toFun x).2
  refine ⟨parameter, fiberCoordinate, {
    parameter_zero := ?_
    fiberCoordinate_base := ?_
    analyticAt_parameter := ?_
    analyticAt_fiberCoordinate := ?_
    left_inv := ?_
    parameter_mem_fiber := ?_
    right_inv_on_fiber := ?_ }⟩
  · change chi.invFun (0, kernelCoord.symm 0) = a
    simpa only [map_zero] using chi.map_target
  · change kernelCoord (chi.toFun a).2 = 0
    rw [chi.map_source]
    exact map_zero kernelCoord
  · have hj : AnalyticAt ℂ
        (fun u : ComplexEuclidean (n - m) ↦
          ((0 : ComplexEuclidean m), kernelCoord.symm u)) 0 :=
      analyticAt_const.prod
        (kernelCoord.symm.toContinuousLinearMap.analyticAt 0)
    simpa [parameter, Function.comp_def] using
      chi.analyticAt_invFun.comp_of_eq hj (by simp)
  · have hsnd : AnalyticAt ℂ (fun x ↦ (chi.toFun x).2) a :=
      analyticAt_snd.comp chi.analyticAt_toFun
    have hout :
        AnalyticAt ℂ kernelCoord (chi.toFun a).2 :=
      kernelCoord.toContinuousLinearMap.analyticAt _
    have hcomp :
        AnalyticAt ℂ
          (fun x ↦ kernelCoord (chi.toFun x).2) a :=
      AnalyticAt.comp
        (g := fun y : K ↦ kernelCoord y)
        (f := fun x ↦ (chi.toFun x).2) hout hsnd
    simpa only [fiberCoordinate] using hcomp
  · have hjTendsto :
        Tendsto
          (fun u : ComplexEuclidean (n - m) ↦
            ((0 : ComplexEuclidean m), kernelCoord.symm u))
          (𝓝 0) (𝓝 (0, 0)) := by
      have hcont :
          Continuous
            (fun u : ComplexEuclidean (n - m) ↦
              ((0 : ComplexEuclidean m), kernelCoord.symm u)) := by
        fun_prop
      have hzero :
          ((0 : ComplexEuclidean m), kernelCoord.symm
            (0 : ComplexEuclidean (n - m))) = (0, 0) := by
        simp
      rw [← hzero]
      exact hcont.continuousAt
    have hright := hjTendsto chi.right_inv
    have hleft :
        (fun u ↦ fiberCoordinate (parameter u)) =ᶠ[𝓝 0] fun u ↦ u := by
      filter_upwards [hright] with u hu
      change kernelCoord (chi.toFun (chi.invFun
        (0, kernelCoord.symm u))).2 = u
      rw [hu]
      simp
    exact hleft
  · have hjTendsto :
        Tendsto
          (fun u : ComplexEuclidean (n - m) ↦
            ((0 : ComplexEuclidean m), kernelCoord.symm u))
          (𝓝 0) (𝓝 (0, 0)) := by
      have hcont :
          Continuous
            (fun u : ComplexEuclidean (n - m) ↦
              ((0 : ComplexEuclidean m), kernelCoord.symm u)) := by
        fun_prop
      have hzero :
          ((0 : ComplexEuclidean m), kernelCoord.symm
            (0 : ComplexEuclidean (n - m))) = (0, 0) := by
        simp
      rw [← hzero]
      exact hcont.continuousAt
    have hright := hjTendsto chi.right_inv
    filter_upwards [hright] with u hu
    have hfirst := congrArg Prod.fst hu
    change F (chi.invFun (0, kernelCoord.symm u)) - F a = 0 at hfirst
    exact sub_eq_zero.mp hfirst
  · filter_upwards [chi.left_inv] with x hx
    intro hFx
    change chi.invFun
        (0, kernelCoord.symm (kernelCoord (chi.toFun x).2)) = x
    rw [kernelCoord.symm_apply_apply]
    have hfirst : (chi.toFun x).1 = 0 := by
      change F x - F a = 0
      exact sub_eq_zero.mpr hFx
    have hpair :
        ((0 : ComplexEuclidean m), (chi.toFun x).2) = chi.toFun x := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    calc
      chi.invFun (0, (chi.toFun x).2) =
          chi.invFun (chi.toFun x) := congrArg chi.invFun hpair
      _ = x := hx

end

end LocalComplexGeometry
