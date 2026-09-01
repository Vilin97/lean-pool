/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Analytic.ConstantRankLinear
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Holomorphic constant-rank theorem

This file proves the local analytic normal form for a holomorphic map of
constant complex rank.  The proof uses the analytic inverse-function theorem,
finite-dimensional complements, and the mean-value theorem on the kernel
factor.
-/


open Filter Metric
open scoped Topology

namespace LocalComplexGeometry

noncomputable section

/-- Once the first component of an analytic map is the first projection and
the derivative has the minimal possible rank, the second component is locally
independent of the second input variable. -/
theorem eventually_snd_eq_slice_of_rank
    {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℂ U]
    [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace W]
    {P : U × V → U × W}
    (hP : AnalyticAt ℂ P 0)
    (hfst : (fun z ↦ (P z).1) =ᶠ[nhds 0] fun z ↦ z.1)
    (hrank : ∀ᶠ z in nhds 0,
      complexLinearRank (fderiv ℂ P z) = Module.finrank ℂ U) :
    (fun z ↦ (P z).2) =ᶠ[nhds 0] fun z ↦ (P (z.1, 0)).2 := by
  have hfstLocal : ∀ᶠ z in nhds 0,
      (fun w ↦ (P w).1) =ᶠ[nhds z] fun w ↦ w.1 :=
    eventually_eventuallyEq_nhds.mpr hfst
  have hgood : ∀ᶠ z in nhds 0,
      AnalyticAt ℂ P z ∧
        ∀ v : V, fderiv ℂ P z (0, v) = 0 := by
    filter_upwards [hP.eventually_analyticAt, hfstLocal, hrank] with z hPz hloc hrz
    let D : U × V →L[ℂ] U × W := fderiv ℂ P z
    have hD : HasFDerivAt P D z := hPz.hasStrictFDerivAt.hasFDerivAt
    have hfstD : HasFDerivAt (fun w ↦ (P w).1)
        ((ContinuousLinearMap.fst ℂ U W).comp D) z :=
      (ContinuousLinearMap.fst ℂ U W).hasFDerivAt.comp z hD
    have hfstD' : HasFDerivAt (fun w : U × V ↦ w.1)
        ((ContinuousLinearMap.fst ℂ U W).comp D) z :=
      hfstD.congr_of_eventuallyEq hloc.symm
    have hfstEq : (ContinuousLinearMap.fst ℂ U W).comp D =
        ContinuousLinearMap.fst ℂ U V :=
      hfstD'.unique (ContinuousLinearMap.fst ℂ U V).hasFDerivAt
    refine ⟨hPz, fun v ↦ ?_⟩
    exact apply_zero_prod_eq_zero_of_rank_eq D hfstEq hrz v
  rcases Metric.mem_nhds_iff.mp hgood with ⟨ε, hε, hball⟩
  apply Filter.Eventually.mono (Metric.ball_mem_nhds (0 : U × V) hε)
  rintro z hz
  have hzNorm : ‖z‖ < ε := by
    simpa [Metric.mem_ball] using hz
  have hzu : z.1 ∈ Metric.ball (0 : U) ε := by
    simp only [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_fst_le z) hzNorm
  have hzv : z.2 ∈ Metric.ball (0 : V) ε := by
    simp only [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_snd_le z) hzNorm
  let q : V → W := fun v ↦ (P (z.1, v)).2
  have hqDiff : DifferentiableOn ℂ q (Metric.ball (0 : V) ε) := by
    intro v hv
    have huv : (z.1, v) ∈ Metric.ball (0 : U × V) ε := by
      simp only [Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero,
        max_lt_iff]
      exact ⟨by simpa [Metric.mem_ball] using hzu,
        by simpa [Metric.mem_ball] using hv⟩
    have hPa := (hball huv).1
    have hins : AnalyticAt ℂ (fun v : V ↦ (z.1, v)) v :=
      analyticAt_const.prod analyticAt_id
    exact (analyticAt_snd.comp (hPa.comp hins)).differentiableAt.differentiableWithinAt
  have hqDeriv : ∀ v ∈ Metric.ball (0 : V) ε, fderiv ℂ q v = 0 := by
    intro v hv
    have huv : (z.1, v) ∈ Metric.ball (0 : U × V) ε := by
      simp only [Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero,
        max_lt_iff]
      exact ⟨by simpa [Metric.mem_ball] using hzu,
        by simpa [Metric.mem_ball] using hv⟩
    have hvert := (hball huv).2
    let D : U × V →L[ℂ] U × W := fderiv ℂ P (z.1, v)
    let inr : V →L[ℂ] U × V :=
      (0 : V →L[ℂ] U).prod (ContinuousLinearMap.id ℂ V)
    let snd : U × W →L[ℂ] W := ContinuousLinearMap.snd ℂ U W
    have hins : HasFDerivAt (fun w : V ↦ (z.1, w)) inr v := by
      simpa only [inr, id_eq] using
        (hasFDerivAt_const (x := v) (c := z.1)).prodMk (hasFDerivAt_id v)
    have hcomp : HasFDerivAt q (snd.comp (D.comp inr)) v := by
      exact snd.hasFDerivAt.comp v
        ((hball huv).1.hasStrictFDerivAt.hasFDerivAt.comp v hins)
    rw [hcomp.fderiv]
    ext w
    change (fderiv ℂ P (z.1, v) (0, w)).2 = 0
    rw [hvert w]
    rfl
  exact (convex_ball (0 : V) ε).is_const_of_fderivWithin_eq_zero
    hqDiff
    (fun v hv ↦ by
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hv, hqDeriv v hv])
    hzv (Metric.mem_ball_self hε)

private theorem rangeProjection_comp_surjective {n m : ℕ}
    (A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (Q : Submodule ℂ (ComplexEuclidean m))
    (h : Submodule.IsTopCompl (LinearMap.range A.toLinearMap) Q) :
    Function.Surjective
      (((LinearMap.range A.toLinearMap).projectionOntoL Q h).comp A) := by
  intro y
  rcases y.property with ⟨x, hx⟩
  refine ⟨x, Subtype.ext ?_⟩
  change (((LinearMap.range A.toLinearMap).projectionOntoL Q h) (A x) :
    ComplexEuclidean m) = y
  rw [show A x = (y : ComplexEuclidean m) from hx]
  exact congrArg Subtype.val (Submodule.projectionOntoL_apply_left h y)

private theorem eventually_complexLinearRank_affineConjugate
    {n m r : ℕ}
    {F : ComplexEuclidean n → ComplexEuclidean m}
    {a : ComplexEuclidean n}
    {R Q : Submodule ℂ (ComplexEuclidean m)}
    {K : Submodule ℂ (ComplexEuclidean n)}
    [CompleteSpace R] [CompleteSpace K]
    (hF : AnalyticAt ℂ F a)
    (chi : LocalBiholomorphAt (ComplexEuclidean n) (R × K) a 0)
    (targetDecomp : ComplexEuclidean m ≃L[ℂ] R × Q)
    (hconst : ∀ᶠ x in nhds a, complexRank (fderiv ℂ F x) = r)
    (P : R × K → R × Q)
    (hP : P = fun z ↦ targetDecomp (F (chi.invFun z) - F a)) :
    ∀ᶠ z in nhds 0, complexLinearRank (fderiv ℂ P z) = r := by
  subst P
  have hconst' := chi.invFun_tendsto hconst
  have hF' := chi.invFun_tendsto hF.eventually_analyticAt
  have hchi' := chi.analyticAt_invFun.eventually_analyticAt
  have hbij' := chi.eventually_bijective_fderiv_invFun
  filter_upwards [hconst', hF', hchi', hbij'] with z hrz hFz hchiz hbijz
  change complexRank (fderiv ℂ F (chi.invFun z)) = r at hrz
  let DF := fderiv ℂ F (chi.invFun z)
  let DC := fderiv ℂ chi.invFun z
  have hinner : HasFDerivAt
      (fun w ↦ F (chi.invFun w) - F a) (DF.comp DC) z := by
    exact (hFz.hasStrictFDerivAt.hasFDerivAt.comp z
      hchiz.hasStrictFDerivAt.hasFDerivAt).sub_const (F a)
  have hderiv : HasFDerivAt
      (fun w ↦ targetDecomp (F (chi.invFun w) - F a))
      (targetDecomp.toContinuousLinearMap.comp (DF.comp DC)) z :=
    targetDecomp.toContinuousLinearMap.hasFDerivAt.comp z hinner
  rw [hderiv.fderiv]
  calc
    complexLinearRank
        (targetDecomp.toContinuousLinearMap.comp (DF.comp DC)) =
        complexLinearRank (DF.comp DC) :=
      complexLinearRank_comp_of_injective_left _ _ targetDecomp.injective
    _ = complexLinearRank DF :=
      complexLinearRank_comp_of_surjective_right _ _ hbijz.2
    _ = r := by simpa only [DF, complexLinearRank_eq_complexRank] using hrz

/-- **Holomorphic constant-rank theorem.**  A holomorphic map whose complex
rank is locally constant is locally equivalent, through biholomorphic source
and target coordinates centered at the origin, to the standard coordinate
map of that rank. -/
theorem holomorphic_constant_rank
    {n m r : ℕ}
    {F : ComplexEuclidean n → ComplexEuclidean m}
    {a : ComplexEuclidean n}
    (hF : AnalyticAt ℂ F a)
    (hrn : r ≤ n)
    (hrm : r ≤ m)
    (hconst : ∀ᶠ x in nhds a, complexRank (fderiv ℂ F x) = r) :
    ∃ (phi : LocalBiholomorphAt
          (ComplexEuclidean n) (ComplexEuclidean n) a 0)
      (psi : LocalBiholomorphAt
          (ComplexEuclidean m) (ComplexEuclidean m) (F a) 0),
      (fun x ↦ psi.toFun (F (phi.invFun x))) =ᶠ[nhds 0]
        standardRankMap n m r := by
  obtain ⟨n', hn⟩ := Nat.exists_eq_add_of_le hrn
  obtain ⟨m', hm⟩ := Nat.exists_eq_add_of_le hrm
  subst n
  subst m
  let A : ComplexEuclidean (r + n') →L[ℂ] ComplexEuclidean (r + m') :=
    fderiv ℂ F a
  let R : Submodule ℂ (ComplexEuclidean (r + m')) :=
    LinearMap.range A.toLinearMap
  have hRankR : Module.finrank ℂ R = r := by
    have ha := hconst.self_of_nhds
    simpa [complexRank, A, R] using ha
  obtain ⟨Q, hRQ⟩ := Submodule.exists_isCompl R
  have hRQtop : Submodule.IsTopCompl R Q :=
    Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hRQ
      R.closed_of_finiteDimensional
  let : CompleteSpace R := FiniteDimensional.complete ℂ R
  let : CompleteSpace Q := FiniteDimensional.complete ℂ Q
  let pR : ComplexEuclidean (r + m') →L[ℂ] R :=
    R.projectionOntoL Q hRQtop
  let pQ : ComplexEuclidean (r + m') →L[ℂ] Q :=
    Q.projectionOntoL R hRQtop.symm
  let targetDecomp : ComplexEuclidean (r + m') ≃L[ℂ] R × Q :=
    (Submodule.prodEquivOfIsTopCompl R Q hRQtop).symm
  have targetDecomp_apply (y : ComplexEuclidean (r + m')) :
      targetDecomp y = (pR y, pQ y) := by
    simp [targetDecomp, pR, pQ]
  let g : ComplexEuclidean (r + n') → R :=
    fun x ↦ pR (F x - F a)
  let g' : ComplexEuclidean (r + n') →L[ℂ] R := pR.comp A
  have hcenter : AnalyticAt ℂ (fun x ↦ F x - F a) a :=
    hF.sub analyticAt_const
  have hg : AnalyticAt ℂ g a := by
    exact (pR.analyticAt 0).comp_of_eq hcenter (by simp)
  have hgDeriv : HasFDerivAt g g' a := by
    have hc : HasFDerivAt
        (pR ∘ fun x ↦ F x - F a) g' a := by
      simpa only [g', A] using
        pR.hasFDerivAt.comp a
          (hF.hasStrictFDerivAt.hasFDerivAt.sub_const (F a))
    exact hc.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun _ ↦ rfl
  have hgSurj : Function.Surjective g' := by
    simpa only [g', pR, R] using rangeProjection_comp_surjective A Q hRQtop
  let K : Submodule ℂ (ComplexEuclidean (r + n')) :=
    LinearMap.ker g'.toLinearMap
  let : CompleteSpace K := FiniteDimensional.complete ℂ K
  obtain ⟨L, hKL⟩ := Submodule.exists_isCompl K
  have hKLtop : Submodule.IsTopCompl K L :=
    Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hKL
      K.closed_of_finiteDimensional
  let kproj : ComplexEuclidean (r + n') →L[ℂ] K :=
    K.projectionOntoL L hKLtop
  have hkerCompl : IsCompl (LinearMap.ker g'.toLinearMap)
      (LinearMap.ker kproj.toLinearMap) := by
    simpa [K, kproj] using hKL
  let eLin : ComplexEuclidean (r + n') ≃ₗ[ℂ] R × K :=
    LinearMap.equivProdOfSurjectiveOfIsCompl g'.toLinearMap kproj.toLinearMap
      (LinearMap.range_eq_top.mpr hgSurj)
      (Submodule.range_projectionOntoL hKLtop)
      hkerCompl
  let eDeriv : ComplexEuclidean (r + n') ≃L[ℂ] R × K :=
    eLin.toContinuousLinearEquiv
  let H : ComplexEuclidean (r + n') → R × K :=
    fun x ↦ (g x, kproj (x - a))
  have hkAnalytic : AnalyticAt ℂ (fun x ↦ kproj (x - a)) a := by
    exact (kproj.analyticAt 0).comp_of_eq
      (analyticAt_id.sub analyticAt_const) (by simp)
  have hHAnalytic : AnalyticAt ℂ H a := hg.prod hkAnalytic
  have hkDeriv : HasFDerivAt (fun x ↦ kproj (x - a)) kproj a := by
    have hc : HasFDerivAt (kproj ∘ fun x ↦ x - a) kproj a := by
      simpa only [id_eq, ContinuousLinearMap.comp_id] using
        kproj.hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const a)
    exact hc.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun _ ↦ rfl
  have hHDeriv : HasFDerivAt H (g'.prod kproj) a :=
    hgDeriv.prodMk hkDeriv
  have hHfderiv : fderiv ℂ H a = (eDeriv : _ →L[ℂ] _) := by
    rw [hHDeriv.fderiv]
    ext x <;> rfl
  let chiRaw := LocalBiholomorphAt.ofAnalyticAtOfFDerivEquiv
    hHAnalytic eDeriv hHfderiv
  have hHcenter : H a = (0, 0) := by
    simp [H, g]
  let chi : LocalBiholomorphAt
      (ComplexEuclidean (r + n')) (R × K) a (0, 0) :=
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
        have h : (fun y ↦ chiRaw.toFun (chiRaw.invFun y)) =ᶠ[nhds (0, 0)]
            fun y ↦ y := by
          simpa only [hHcenter] using chiRaw.right_inv
        exact h.mono fun y hy ↦ by
          change H (chiRaw.invFun y) = y at hy
          exact hy }
  have hKrank : Module.finrank ℂ K = n' := by
    have hdim := LinearMap.finrank_range_add_finrank_ker g'.toLinearMap
    rw [LinearMap.range_eq_top.mpr hgSurj, finrank_top,
      hRankR, Module.finrank_fin_fun] at hdim
    change Module.finrank ℂ (LinearMap.ker g'.toLinearMap) = n'
    omega
  have hQrank : Module.finrank ℂ Q = m' := by
    have hdim := Submodule.finrank_add_eq_of_isCompl hRQ
    rw [hRankR, Module.finrank_fin_fun] at hdim
    omega
  let P : R × K → R × Q := fun z ↦
    targetDecomp (F (chi.invFun z) - F a)
  have hPAnalytic : AnalyticAt ℂ P 0 := by
    have hinner : AnalyticAt ℂ (fun z ↦ F (chi.invFun z) - F a) 0 :=
      (hF.comp_of_eq chi.analyticAt_invFun chi.map_target).sub analyticAt_const
    exact (targetDecomp.toContinuousLinearMap.analyticAt 0).comp_of_eq
      hinner (by
        change F (chi.invFun (0, 0)) - F a = 0
        rw [chi.map_target, sub_self])
  have hPfst : (fun z ↦ (P z).1) =ᶠ[nhds 0] fun z ↦ z.1 := by
    filter_upwards [chi.right_inv] with z hz
    have hz' := congrArg Prod.fst hz
    change g (chi.invFun z) = z.1 at hz'
    simpa only [P, targetDecomp_apply, g] using hz'
  have hPrank : ∀ᶠ z in nhds 0,
      complexLinearRank (fderiv ℂ P z) = Module.finrank ℂ R := by
    filter_upwards [eventually_complexLinearRank_affineConjugate
      hF chi targetDecomp hconst P rfl] with z hz
    exact hz.trans hRankR.symm
  have hPslice := eventually_snd_eq_slice_of_rank
    hPAnalytic hPfst hPrank
  let q₀ : R → Q := fun u ↦ (P (u, 0)).2
  have hq₀Analytic : AnalyticAt ℂ q₀ 0 := by
    have hins : AnalyticAt ℂ (fun u : R ↦ (u, (0 : K))) 0 :=
      analyticAt_id.prod analyticAt_const
    have hcomp : AnalyticAt ℂ (fun u : R ↦ P (u, (0 : K))) 0 :=
      hPAnalytic.comp_of_eq hins (by simp)
    exact analyticAt_snd.comp hcomp
  have hPzero : P (0, 0) = (0, 0) := by
    change targetDecomp (F (chi.invFun (0, 0)) - F a) = (0, 0)
    rw [chi.map_target, sub_self, map_zero]
    rfl
  have hq₀zero : q₀ 0 = 0 := by
    exact congrArg Prod.snd hPzero
  let shear : LocalBiholomorphAt (R × Q) (R × Q) 0 0 :=
    LocalBiholomorphAt.fiberShearAtZero q₀ hq₀Analytic hq₀zero
  have hNormal : (fun z ↦ shear.toFun (P z)) =ᶠ[nhds 0]
      fun z : R × K ↦ (z.1, (0 : Q)) := by
    filter_upwards [hPfst, hPslice] with z hfirst hsecond
    change ((P z).1, (P z).2 - q₀ (P z).1) = (z.1, 0)
    rw [hfirst, hsecond]
    simp only [q₀, sub_self]
  let eR : R ≃L[ℂ] ComplexEuclidean r :=
    ContinuousLinearEquiv.ofFinrankEq <| by
      simpa only [Module.finrank_fin_fun] using hRankR
  let eK : K ≃L[ℂ] ComplexEuclidean n' :=
    ContinuousLinearEquiv.ofFinrankEq <| by
      simpa only [Module.finrank_fin_fun] using hKrank
  let eQ : Q ≃L[ℂ] ComplexEuclidean m' :=
    ContinuousLinearEquiv.ofFinrankEq <| by
      simpa only [Module.finrank_fin_fun] using hQrank
  let eSource : (R × K) ≃L[ℂ] ComplexEuclidean (r + n') :=
    (eR.prodCongr eK).trans (finProdContinuousLinearEquiv r n')
  let eTarget : (R × Q) ≃L[ℂ] ComplexEuclidean (r + m') :=
    (eR.prodCongr eQ).trans (finProdContinuousLinearEquiv r m')
  let sourceCoord : LocalBiholomorphAt
      (R × K) (ComplexEuclidean (r + n')) 0 0 :=
    LocalBiholomorphAt.ofContinuousLinearEquivAtZero eSource
  let targetCoord : LocalBiholomorphAt
      (R × Q) (ComplexEuclidean (r + m')) 0 0 :=
    LocalBiholomorphAt.ofContinuousLinearEquivAtZero eTarget
  let centeredTarget : LocalBiholomorphAt
      (ComplexEuclidean (r + m')) (R × Q) (F a) 0 :=
    LocalBiholomorphAt.affine targetDecomp (F a) 0
  let phi := chi.trans sourceCoord
  let psi := centeredTarget.trans (shear.trans targetCoord)
  refine ⟨phi, psi, ?_⟩
  have heSource : Tendsto (fun x ↦ eSource.symm x) (nhds 0) (nhds 0) := by
    have h : Tendsto (fun x : ComplexEuclidean (r + n') ↦ eSource.symm x)
        (nhds 0) (nhds (eSource.symm 0)) := eSource.symm.continuousAt
    simpa only [map_zero] using h
  have hNormal' := heSource hNormal
  filter_upwards [hNormal'] with x hx
  change shear.toFun (P (eSource.symm x)) =
      ((eSource.symm x).1, (0 : Q)) at hx
  calc
    psi.toFun (F (phi.invFun x)) =
        eTarget (shear.toFun (P (eSource.symm x))) := by
      simp only [phi, psi, centeredTarget, sourceCoord, targetCoord,
        LocalBiholomorphAt.trans, LocalBiholomorphAt.affine,
        LocalBiholomorphAt.ofContinuousLinearEquivAtZero,
        Function.comp_apply, add_zero, P]
    _ = eTarget ((eSource.symm x).1, (0 : Q)) := congrArg eTarget hx
    _ = standardRankMap (r + n') (r + m') r x :=
      productEquiv_fst_zero_eq_standardRankMap
        r n' m' eR eK eQ x

/-- Audited public spelling of `holomorphic_constant_rank`. -/
theorem holomorphic_constantRank_normalForm_core
    {n m r : ℕ}
    {F : ComplexEuclidean n → ComplexEuclidean m}
    {a : ComplexEuclidean n}
    (hF : AnalyticAt ℂ F a)
    (hrn : r ≤ n)
    (hrm : r ≤ m)
    (hconst : ∀ᶠ x in nhds a, complexRank (fderiv ℂ F x) = r) :
    ∃ (phi : LocalBiholomorphAt
          (ComplexEuclidean n) (ComplexEuclidean n) a 0)
      (psi : LocalBiholomorphAt
          (ComplexEuclidean m) (ComplexEuclidean m) (F a) 0),
      (fun x ↦ psi.toFun (F (phi.invFun x))) =ᶠ[nhds 0]
        standardRankMap n m r :=
  holomorphic_constant_rank hF hrn hrm hconst

/-- A holomorphic map with locally surjective derivative has the standard
submersion normal form.  The necessary inequality `m ≤ n` is a consequence,
not an extra hypothesis. -/
theorem holomorphic_submersion_normalForm
    {n m : ℕ}
    {F : ComplexEuclidean n → ComplexEuclidean m}
    {a : ComplexEuclidean n}
    (hF : AnalyticAt ℂ F a)
    (hsurj : ∀ᶠ x in nhds a,
      Function.Surjective (fderiv ℂ F x)) :
    ∃ (phi : LocalBiholomorphAt
          (ComplexEuclidean n) (ComplexEuclidean n) a 0)
      (psi : LocalBiholomorphAt
          (ComplexEuclidean m) (ComplexEuclidean m) (F a) 0),
      (fun x ↦ psi.toFun (F (phi.invFun x))) =ᶠ[nhds 0]
        standardRankMap n m m := by
  have hrank : ∀ᶠ x in nhds a, complexRank (fderiv ℂ F x) = m := by
    filter_upwards [hsurj] with x hx
    unfold complexRank
    rw [LinearMap.range_eq_top.mpr hx, finrank_top,
      Module.finrank_fin_fun]
  have hmn : m ≤ n := by
    have ha := hrank.self_of_nhds
    rw [← ha]
    exact complexRank_le_source (fderiv ℂ F a)
  exact holomorphic_constant_rank hF hmn le_rfl hrank

/-- A holomorphic map with locally injective derivative has the standard
immersion normal form.  The necessary inequality `n ≤ m` is a consequence,
not an extra hypothesis. -/
theorem holomorphic_immersion_normalForm
    {n m : ℕ}
    {F : ComplexEuclidean n → ComplexEuclidean m}
    {a : ComplexEuclidean n}
    (hF : AnalyticAt ℂ F a)
    (hinj : ∀ᶠ x in nhds a,
      Function.Injective (fderiv ℂ F x)) :
    ∃ (phi : LocalBiholomorphAt
          (ComplexEuclidean n) (ComplexEuclidean n) a 0)
      (psi : LocalBiholomorphAt
          (ComplexEuclidean m) (ComplexEuclidean m) (F a) 0),
      (fun x ↦ psi.toFun (F (phi.invFun x))) =ᶠ[nhds 0]
        standardRankMap n m n := by
  have hrank : ∀ᶠ x in nhds a, complexRank (fderiv ℂ F x) = n := by
    filter_upwards [hinj] with x hx
    unfold complexRank
    rw [LinearMap.finrank_range_of_inj hx, Module.finrank_fin_fun]
  have hnm : n ≤ m := by
    have ha := hrank.self_of_nhds
    rw [← ha]
    exact complexRank_le_target (fderiv ℂ F a)
  exact holomorphic_constant_rank hF le_rfl hnm hrank

end

end LocalComplexGeometry
