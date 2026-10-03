/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! A reusable joint `C¹` criterion from time and parameter derivatives. -/

@[expose] public section

open Filter
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Joint `C¹` regularity follows when the time derivative and strict
parameter derivative exist on their slices and vary continuously together. -/
theorem contDiff_one_of_time_and_parameter_derivatives
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ × P → G)
    (dtime : ℝ × P → G)
    (dparam : ℝ × P → P →L[ℝ] G)
    (hTime : ∀ t z, HasDerivAt (fun r => f (r, z)) (dtime (t, z)) t)
    (hParam : ∀ t z, HasStrictFDerivAt (fun w => f (t, w)) (dparam (t, z)) z)
    (hTimeCont : Continuous dtime)
    (hParamCont : Continuous dparam) :
    ContDiff ℝ 1 f := by
  let dtimeCLM : ℝ × P → ℝ →L[ℝ] G := fun q =>
    ContinuousLinearMap.toSpanSingleton ℝ (dtime q)
  have hdtimeCLM : Continuous dtimeCLM :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).continuous.comp hTimeCont
  have hF (t : ℝ) (z : P) :
    HasFDerivAt f ((dtimeCLM (t, z)).coprod (dparam (t, z))) (t, z) := by
    exact (hasStrictFDerivAt_uncurry_coprod
      (f := fun t z => f (t, z))
      (f₁ := fun t z => dtimeCLM (t, z))
      (f₂ := fun t z => dparam (t, z))
      (Filter.Eventually.of_forall fun q => (hTime q.1 q.2).hasFDerivAt)
      (Filter.Eventually.of_forall fun q => (hParam q.1 q.2).hasFDerivAt)
      (by
        change ContinuousAt (fun q : ℝ × P => dtimeCLM q) (t, z)
        exact hdtimeCLM.continuousAt)
      (by
        change ContinuousAt (fun q : ℝ × P => dparam q) (t, z)
        exact hParamCont.continuousAt)).hasFDerivAt
  rw [contDiff_one_iff_fderiv]
  constructor
  · intro q
    rcases q with ⟨t, z⟩
    exact (hF t z).differentiableAt
  · have hPair : Continuous (fun q : ℝ × P => (dtimeCLM q, dparam q)) :=
      hdtimeCLM.prodMk hParamCont
    have hTotal : Continuous (fun q : ℝ × P => (dtimeCLM q).coprod (dparam q)) :=
      (ContinuousLinearMap.coprodEquivL (S := ℝ) (E := ℝ)
        (F := P) (G := G)).continuous.comp hPair
    have hderiv : fderiv ℝ f = fun q => (dtimeCLM q).coprod (dparam q) := by
      funext q
      rcases q with ⟨t, z⟩
      exact (hF t z).fderiv
    rw [hderiv]
    exact hTotal

/-- Continuous linear time-direction map associated with a prescribed time derivative. -/
noncomputable def JointC1Core.jointTimeDerivativeCLM
    {P G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (dtime : ℝ × P → G) (q : ℝ × P) : ℝ →L[ℝ] G :=
  ContinuousLinearMap.toSpanSingleton ℝ (dtime q)

/-- Pointwise joint derivative on an open region, assembled from the two
coordinate-slice derivatives. -/
theorem JointC1Core.jointFDerivAt_on_open
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ × P → G) (s : Set (ℝ × P)) (hs : IsOpen s)
    (dtime : ℝ × P → G) (dparam : ℝ × P → P →L[ℝ] G)
    (hTime : ∀ t z, (t, z) ∈ s →
      HasDerivAt (fun r => f (r, z)) (dtime (t, z)) t)
    (hParam : ∀ t z, (t, z) ∈ s →
      HasStrictFDerivAt (fun w => f (t, w)) (dparam (t, z)) z)
    (hTimeCont : ContinuousOn dtime s) (hParamCont : ContinuousOn dparam s)
    (q : ℝ × P) (hq : q ∈ s) :
    HasFDerivAt f
      ((JointC1Core.jointTimeDerivativeCLM dtime q).coprod (dparam q)) q := by
  rcases q with ⟨t, z⟩
  have htimeCLM : ContinuousOn (JointC1Core.jointTimeDerivativeCLM dtime) s :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).continuous.comp_continuousOn
      hTimeCont
  have hTimeEv : ∀ᶠ q in 𝓝 (t, z),
      HasFDerivAt (fun r => f (r, q.2))
        (JointC1Core.jointTimeDerivativeCLM dtime (q.1, q.2)) q.1 := by
    filter_upwards [hs.mem_nhds hq] with q hqs
    exact (hTime q.1 q.2 hqs).hasFDerivAt
  have hParamEv : ∀ᶠ q in 𝓝 (t, z),
      HasFDerivAt (fun w => f (q.1, w)) (dparam (q.1, q.2)) q.2 := by
    filter_upwards [hs.mem_nhds hq] with q hqs
    exact (hParam q.1 q.2 hqs).hasFDerivAt
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun t z => f (t, z))
    (f₁ := fun t z => JointC1Core.jointTimeDerivativeCLM dtime (t, z))
    (f₂ := fun t z => dparam (t, z))
    hTimeEv hParamEv
    (by
      change ContinuousAt (fun q : ℝ × P => JointC1Core.jointTimeDerivativeCLM dtime q) (t, z)
      exact htimeCLM.continuousAt (hs.mem_nhds hq))
    (by
      change ContinuousAt (fun q : ℝ × P => dparam q) (t, z)
      exact hParamCont.continuousAt (hs.mem_nhds hq))).hasFDerivAt

theorem JointC1Core.jointFDerivAt_family_on_open
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ × P → G) (s : Set (ℝ × P)) (hs : IsOpen s)
    (dtime : ℝ × P → G) (dparam : ℝ × P → P →L[ℝ] G)
    (hTime : ∀ t z, (t, z) ∈ s →
      HasDerivAt (fun r => f (r, z)) (dtime (t, z)) t)
    (hParam : ∀ t z, (t, z) ∈ s →
      HasStrictFDerivAt (fun w => f (t, w)) (dparam (t, z)) z)
    (hTimeCont : ContinuousOn dtime s) (hParamCont : ContinuousOn dparam s) :
    ∀ q, q ∈ s → HasFDerivAt f
      ((JointC1Core.jointTimeDerivativeCLM dtime q).coprod (dparam q)) q := by
  intro q hq
  exact JointC1Core.jointFDerivAt_on_open f s hs dtime dparam hTime hParam
    hTimeCont hParamCont q hq

/-- Pointwise total derivative assembled from a time derivative and a
parameter derivative whose families are continuous. -/
theorem hasFDerivAt_of_time_and_parameter_derivatives
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ × P → G) (dtime : ℝ × P → G)
    (dparam : ℝ × P → P →L[ℝ] G)
    (hTime : ∀ t z, HasDerivAt (fun r => f (r, z)) (dtime (t, z)) t)
    (hParam : ∀ t z, HasStrictFDerivAt (fun w => f (t, w)) (dparam (t, z)) z)
    (hTimeCont : Continuous dtime) (hParamCont : Continuous dparam)
    (q : ℝ × P) :
    HasFDerivAt f
      ((ContinuousLinearMap.toSpanSingleton ℝ (dtime q)).coprod (dparam q)) q := by
  rcases q with ⟨t, z⟩
  have h := JointC1Core.jointFDerivAt_on_open f Set.univ isOpen_univ dtime dparam
    (fun t z _ => hTime t z) (fun t z _ => hParam t z)
    hTimeCont.continuousOn hParamCont.continuousOn (t, z) (Set.mem_univ _)
  simpa [JointC1Core.jointTimeDerivativeCLM] using h

theorem JointC1Core.jointDerivative_continuousOn
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
    (dtime : ℝ × P → G) (dparam : ℝ × P → P →L[ℝ] G)
    (s : Set (ℝ × P)) (hTimeCont : ContinuousOn dtime s)
    (hParamCont : ContinuousOn dparam s) :
    ContinuousOn
      (fun q : ℝ × P => (JointC1Core.jointTimeDerivativeCLM dtime q).coprod (dparam q)) s := by
  have hTimeCLM : ContinuousOn (JointC1Core.jointTimeDerivativeCLM dtime) s :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).continuous.comp_continuousOn
      hTimeCont
  exact hTimeCLM.continuousLinearMapCoprod hParamCont

/-- Convert a continuous family of total derivatives into `ContDiffOn C¹` on
an open set. -/
theorem JointC1Core.contDiffOn_one_of_continuous_derivative_on_open
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ × P → G) (s : Set (ℝ × P)) (hs : IsOpen s)
    (D : ℝ × P → (ℝ × P) →L[ℝ] G)
    (hF : ∀ q, q ∈ s → HasFDerivAt f (D q) q)
    (hD : ContinuousOn D s) : ContDiffOn ℝ 1 f s := by
  rw [show (1 : ℕ∞ω) = (0 : ℕ∞ω) + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact (hF q hq).differentiableAt.differentiableWithinAt
  · intro h
    norm_num at h
  · rw [contDiffOn_zero]
    apply hD.congr
    intro q hq
    exact (hF q hq).fderiv

/-- The open-set version of the joint `C¹` criterion, used on forward-time
regions of augmented flows. -/
theorem contDiffOn_one_of_time_and_parameter_derivatives
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ × P → G) (s : Set (ℝ × P)) (hs : IsOpen s)
    (dtime : ℝ × P → G) (dparam : ℝ × P → P →L[ℝ] G)
    (hTime : ∀ t z, (t, z) ∈ s →
      HasDerivAt (fun r => f (r, z)) (dtime (t, z)) t)
    (hParam : ∀ t z, (t, z) ∈ s →
      HasStrictFDerivAt (fun w => f (t, w)) (dparam (t, z)) z)
    (hTimeCont : ContinuousOn dtime s) (hParamCont : ContinuousOn dparam s) :
    ContDiffOn ℝ 1 f s := by
  have hF := JointC1Core.jointFDerivAt_family_on_open f s hs dtime dparam
    hTime hParam hTimeCont hParamCont
  have hD := JointC1Core.jointDerivative_continuousOn dtime dparam s hTimeCont hParamCont
  exact JointC1Core.contDiffOn_one_of_continuous_derivative_on_open f s hs
    (fun q => (JointC1Core.jointTimeDerivativeCLM dtime q).coprod (dparam q)) hF hD

end

end AVenhance.Infra.Flow
