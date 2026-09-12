/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.EvenSmoothDescent
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Joint smoothness of even descent

This module treats a real auxiliary parameter and a real radial coordinate.
The full derivative on the closed half-plane is proved before any higher-order
regularity is inferred. Separate smoothness is not used as a substitute for
joint smoothness.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.ParametricEvenDescent

universe u

/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Even radial, given by `∀ p, Function.Even (fun r => F (p, r))`. -/
noncomputable def EvenRadial (F : Plane → E) : Prop :=
  ∀ p, Function.Even (fun r => F (p, r))

/-- Parameter partial, given by `deriv (fun p => F (p, q.2)) q.1`. -/
noncomputable def parameterPartial (F : Plane → E) (q : Plane) : E :=
  deriv (fun p => F (p, q.2)) q.1

/-- Radial partial, given by `deriv (fun r => F (q.1, r)) q.2`. -/
noncomputable def radialPartial (F : Plane → E) (q : Plane) : E :=
  deriv (fun r => F (q.1, r)) q.2

/-- Radial reduce, given by `EvenSmoothDescent.radialDerivative (fun r => F (q.1, r)) q.2`. -/
noncomputable def radialReduce (F : Plane → E) (q : Plane) : E :=
  EvenSmoothDescent.radialDerivative (fun r => F (q.1, r)) q.2

/-- Descend, given by `F (q.1, Real.sqrt q.2)`. -/
noncomputable def descend (F : Plane → E) (q : Plane) : E :=
  F (q.1, Real.sqrt q.2)

/-- Plane derivative, given by `(ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (parameterPartial F q)
+ (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (radialReduce F q)`. -/
noncomputable def planeDerivative (F : Plane → E) (q : Plane) : Plane →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (parameterPartial F q) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (radialReduce F q)

omit [CompleteSpace E] in
theorem parameterPartial_eq_fderiv {F : Plane → E} (hF : ContDiff ℝ ∞ F) (q : Plane) :
    parameterPartial F q = fderiv ℝ F q (1, 0) := by
  have h := ((contDiff_infty_iff_fderiv.mp hF).1 q).hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  exact h.deriv

omit [CompleteSpace E] in
theorem radialPartial_eq_fderiv {F : Plane → E} (hF : ContDiff ℝ ∞ F) (q : Plane) :
    radialPartial F q = fderiv ℝ F q (0, 1) := by
  have h := ((contDiff_infty_iff_fderiv.mp hF).1 q).hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  exact h.deriv

omit [CompleteSpace E] in
theorem fderiv_decompose {F : Plane → E} (hF : ContDiff ℝ ∞ F) (q v : Plane) :
    fderiv ℝ F q v = v.1 • parameterPartial F q + v.2 • radialPartial F q := by
  rw [parameterPartial_eq_fderiv hF, radialPartial_eq_fderiv hF]
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

omit [CompleteSpace E] in
theorem contDiff_parameterPartial {F : Plane → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterPartial F) := by
  have hEq : parameterPartial F = fun q => fderiv ℝ F q (1, 0) :=
    funext (parameterPartial_eq_fderiv hF)
  rw [hEq]
  exact (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

omit [CompleteSpace E] in
theorem contDiff_radialPartial {F : Plane → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialPartial F) := by
  have hEq : radialPartial F = fun q => fderiv ℝ F q (0, 1) :=
    funext (radialPartial_eq_fderiv hF)
  rw [hEq]
  exact (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

omit [CompleteSpace E] in
theorem radialReduce_integral (F : Plane → E) (q : Plane) :
    radialReduce F q = (1 / 2 : ℝ) •
      ∫ t in (0 : ℝ)..1, radialPartial (radialPartial F) (q.1, t * q.2) := by
  simp only [radialReduce, EvenSmoothDescent.radialDerivative, EvenSmoothDescent.average,
    radialPartial, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ]
  simp only [iteratedDeriv_zero]

omit [CompleteSpace E] in
theorem contDiff_radialReduce {F : Plane → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialReduce F) := by
  let K : Plane × ℝ → E := fun z => radialPartial (radialPartial F) (z.1.1, z.2 * z.1.2)
  have hK : ContDiff ℝ ∞ K :=
    (contDiff_radialPartial (contDiff_radialPartial hF)).comp
      (contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd))
  have hi := ParametricRephase.intervalIntegral_contDiffOn_of_joint K univ isOpen_univ
    hK.contDiffOn 0 1 zero_le_one
  have hi' : ContDiff ℝ ∞ (fun q : Plane => ∫ t in (0 : ℝ)..1, K (q, t)) :=
    contDiffOn_univ.mp hi
  have hEq : radialReduce F = fun q => (1 / 2 : ℝ) • ∫ t in (0 : ℝ)..1, K (q, t) :=
    funext (radialReduce_integral F)
  rw [hEq]
  exact hi'.const_smul (1 / 2 : ℝ)

omit [CompleteSpace E] in
theorem even_parameterPartial {F : Plane → E} (hEven : EvenRadial F) :
    EvenRadial (parameterPartial F) := by
  intro p r
  have hEq : (fun p => F (p, -r)) = fun p => F (p, r) :=
    funext fun p => hEven p r
  exact congrArg (fun f : ℝ → E => deriv f p) hEq

omit [CompleteSpace E] in
theorem even_radialReduce {F : Plane → E} (hEven : EvenRadial F) :
    EvenRadial (radialReduce F) := by
  intro p r
  exact EvenSmoothDescent.even_radialDerivative (hEven p) r

omit [CompleteSpace E] in
theorem contDiff_planeDerivative {F : Plane → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (planeDerivative F) :=
  (contDiff_const.smulRight (contDiff_parameterPartial hF)).add
    (contDiff_const.smulRight (contDiff_radialReduce hF))

omit [CompleteSpace E] in
theorem even_planeDerivative {F : Plane → E} (hEven : EvenRadial F) :
    EvenRadial (planeDerivative F) := by
  intro p r
  simp only [planeDerivative, even_parameterPartial hEven p r, even_radialReduce hEven p r]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_descend {F : Plane → E} (hF : Continuous F) : Continuous (descend F) :=
  hF.comp (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd))

theorem radialPartial_identity {F : Plane → E} (hF : ContDiff ℝ ∞ F)
    (hEven : EvenRadial F) (q : Plane) :
    radialPartial F q = (2 * q.2) • radialReduce F q := by
  have hs : ContDiff ℝ ∞ (fun r => F (q.1, r)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  exact (EvenSmoothDescent.radialDerivative_identity hs (hEven q.1) q.2).symm

theorem hasFDerivAt_descend_pos {F : Plane → E} (hF : ContDiff ℝ ∞ F)
    (hEven : EvenRadial F) {q : Plane} (hq : 0 < q.2) :
    HasFDerivAt (descend F) (descend (planeDerivative F) q) q := by
  have hs := (Real.hasDerivAt_sqrt hq.ne').comp_hasFDerivAt q
    (hasFDerivAt_snd : HasFDerivAt (fun z : Plane => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) q)
  have hp := (hasFDerivAt_fst : HasFDerivAt (fun z : Plane => z.1)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) q).prodMk hs
  have h := ((contDiff_infty_iff_fderiv.mp hF).1 (q.1, Real.sqrt q.2)).hasFDerivAt.comp q hp
  have hL : descend (planeDerivative F) q =
      (fderiv ℝ F (q.1, Real.sqrt q.2)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          ((1 / (2 * Real.sqrt q.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    apply ContinuousLinearMap.ext
    intro v
    change v.1 • parameterPartial F (q.1, Real.sqrt q.2) +
        v.2 • radialReduce F (q.1, Real.sqrt q.2) =
      fderiv ℝ F (q.1, Real.sqrt q.2) (v.1, (1 / (2 * Real.sqrt q.2)) * v.2)
    rw [fderiv_decompose hF, radialPartial_identity hF hEven, smul_smul]
    congr 1
    congr 1
    have hn : Real.sqrt q.2 ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    field_simp
  rw [hL]
  exact h

/-- The full Fréchet derivative extends to the boundary of the half-plane. -/
theorem hasFDerivWithinAt_descend {F : Plane → E} (hF : ContDiff ℝ ∞ F)
    (hEven : EvenRadial F) (q : Plane) :
    HasFDerivWithinAt (descend F) (descend (planeDerivative F) q)
      (univ ×ˢ Ici (0 : ℝ)) q := by
  let s : Set Plane := univ ×ˢ Ioi (0 : ℝ)
  have hd : DifferentiableOn ℝ (descend F) s :=
    fun z hz => (hasFDerivAt_descend_pos hF hEven hz.2).differentiableAt.differentiableWithinAt
  have heq : fderiv ℝ (descend F) =ᶠ[𝓝[s] q] descend (planeDerivative F) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hasFDerivAt_descend_pos hF hEven hz.2).fderiv
  have ht : Tendsto (descend (planeDerivative F)) (𝓝[s] q)
      (𝓝 (descend (planeDerivative F) q)) :=
    ((continuous_descend (contDiff_planeDerivative hF).continuous).tendsto q).mono_left
      nhdsWithin_le_nhds
  have h := hasFDerivWithinAt_closure_of_tendsto_fderiv hd
    (convex_univ.prod (convex_Ioi 0)) (isOpen_univ.prod isOpen_Ioi)
    (fun _ _ => (continuous_descend hF.continuous).continuousAt.continuousWithinAt)
    (ht.congr' heq.symm)
  simpa only [s, closure_prod_eq, closure_univ, closure_Ioi] using h

private theorem contDiffOn_descend_nat (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (F : Plane → V), ContDiff ℝ ∞ F → EvenRadial F →
        ContDiffOn ℝ n (descend F) (univ ×ˢ Ici (0 : ℝ)) := by
  induction n with
  | zero =>
    intro V _ _ _ F hF hEven
    exact contDiffOn_zero.mpr (continuous_descend hF.continuous).continuousOn
  | succ n ih =>
    intro V _ _ _ F hF hEven
    have hJ := ih (Plane →L[ℝ] V) (planeDerivative F)
      (contDiff_planeDerivative hF) (even_planeDerivative hEven)
    have hu : UniqueDiffOn ℝ (univ ×ˢ Ici (0 : ℝ) : Set Plane) :=
      uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)
    have hd := hasFDerivWithinAt_descend hF hEven
    have hactual : ContDiffOn ℝ n
        (fderivWithin ℝ (descend F) (univ ×ˢ Ici (0 : ℝ)))
        (univ ×ˢ Ici (0 : ℝ)) :=
      hJ.congr fun q hq => (hd q).fderivWithin (hu q hq)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (contDiffOn_succ_of_fderivWithin
        (fun q _ => (hd q).differentiableWithinAt) (by simp) hactual)

/-- Joint smoothness in the auxiliary parameter and the squared radial variable. -/
theorem contDiffOn_descend {F : Plane → E} (hF : ContDiff ℝ ∞ F)
    (hEven : EvenRadial F) :
    ContDiffOn ℝ ∞ (descend F) (univ ×ˢ Ici (0 : ℝ)) :=
  contDiffOn_infty.mpr fun n => contDiffOn_descend_nat n E F hF hEven

/-- Localized, given by `(EvenSmoothDescent.evenCutoff A (q.1 - a) *
EvenSmoothDescent.evenCutoff R q.2) • F q`. -/
noncomputable def localized (a A R : ℝ) (F : Plane → E) (q : Plane) : E :=
  (EvenSmoothDescent.evenCutoff A (q.1 - a) *
    EvenSmoothDescent.evenCutoff R q.2) • F q

private theorem cutoff_eventually_zero {R x : ℝ} (hR : 0 < R) (hx : R ≤ |x|) :
    EvenSmoothDescent.evenCutoff R =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [EvenSmoothDescent.localized_eventually_zero hR hx (fun _ => (1 : ℝ))]
    with y hy
  change EvenSmoothDescent.evenCutoff R y * 1 = 0 at hy
  simpa only [mul_one] using hy

omit [CompleteSpace E] in
theorem localized_eventually_zero_parameter {a A R : ℝ} (hA : 0 < A)
    {q : Plane} (hq : A ≤ |q.1 - a|) (F : Plane → E) :
    localized a A R F =ᶠ[𝓝 q] (fun _ => 0) := by
  have h := (cutoff_eventually_zero hA hq).comp_tendsto
    ((continuous_fst.fun_sub continuous_const).tendsto q)
  filter_upwards [h] with z hz
  change EvenSmoothDescent.evenCutoff A (z.1 - a) = 0 at hz
  simp only [localized, hz, zero_mul, zero_smul]

omit [CompleteSpace E] in
theorem localized_eventually_zero_radial {a A R : ℝ} (hR : 0 < R)
    {q : Plane} (hq : R ≤ |q.2|) (F : Plane → E) :
    localized a A R F =ᶠ[𝓝 q] (fun _ => 0) := by
  have h := (cutoff_eventually_zero hR hq).comp_tendsto (continuous_snd.tendsto q)
  filter_upwards [h] with z hz
  change EvenSmoothDescent.evenCutoff R z.2 = 0 at hz
  simp only [localized, hz, mul_zero, zero_smul]

omit [CompleteSpace E] in
theorem contDiff_localized {a A R : ℝ} (hA : 0 < A) (hR : 0 < R) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (Ioo (a - A) (a + A) ×ˢ Ioo (-R) R)) :
    ContDiff ℝ ∞ (localized a A R F) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hp : |q.1 - a| < A
  · by_cases hr : |q.2| < R
    · have hmem : q ∈ Ioo (a - A) (a + A) ×ˢ Ioo (-R) R := by
        constructor
        · rcases abs_lt.mp hp with ⟨h1, h2⟩
          constructor <;> linarith
        · exact abs_lt.mp hr
      exact (((EvenSmoothDescent.contDiff_evenCutoff A).comp
          (contDiff_fst.sub contDiff_const)).mul
        ((EvenSmoothDescent.contDiff_evenCutoff R).comp contDiff_snd)).contDiffAt.smul
          (hF.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem))
    · exact contDiffAt_const.congr_of_eventuallyEq
        (localized_eventually_zero_radial hR (le_of_not_gt hr) F)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (localized_eventually_zero_parameter hA (le_of_not_gt hp) F)

omit [CompleteSpace E] in
theorem even_localized {a A R : ℝ} (hA : 0 < A) (hR : 0 < R) {F : Plane → E}
    (he : ∀ p ∈ Ioo (a - A) (a + A), ∀ r ∈ Ioo (-R) R, F (p, -r) = F (p, r)) :
    EvenRadial (localized a A R F) := by
  intro p r
  change localized a A R F (p, -r) = localized a A R F (p, r)
  by_cases hp : |p - a| < A
  · by_cases hr : |r| < R
    · have hpmem : p ∈ Ioo (a - A) (a + A) := by
        rcases abs_lt.mp hp with ⟨h1, h2⟩
        constructor <;> linarith
      change (EvenSmoothDescent.evenCutoff A (p - a) *
          EvenSmoothDescent.evenCutoff R (-r)) • F (p, -r) = _
      rw [EvenSmoothDescent.even_evenCutoff R r, he p hpmem r (abs_lt.mp hr)]
      rfl
    · have hr' : R ≤ |r| := le_of_not_gt hr
      have hnr : R ≤ |-r| := by simpa only [abs_neg] using hr'
      rw [(localized_eventually_zero_radial hR (q := (p, -r)) hnr F).eq_of_nhds,
        (localized_eventually_zero_radial hR (q := (p, r)) hr' F).eq_of_nhds]
  · have hp' : A ≤ |p - a| := le_of_not_gt hp
    rw [(localized_eventually_zero_parameter hA (q := (p, -r)) hp' F).eq_of_nhds,
      (localized_eventually_zero_parameter hA (q := (p, r)) hp' F).eq_of_nhds]

omit [CompleteSpace E] in
theorem localized_eventuallyEq (a A R : ℝ) (F : Plane → E) :
    localized a A R F =ᶠ[𝓝 (a, 0)] F := by
  have hp : (fun q : Plane => EvenSmoothDescent.evenCutoff A (q.1 - a))
      =ᶠ[𝓝 (a, 0)] (fun _ => 1) :=
    (EvenSmoothDescent.evenCutoff_eventually_one A).comp_tendsto
      (by simpa only [sub_self] using
        ((continuous_fst.fun_sub (continuous_const : Continuous (fun _ : Plane => a))).tendsto
          (a, (0 : ℝ))))
  have hr : (fun q : Plane => EvenSmoothDescent.evenCutoff R q.2)
      =ᶠ[𝓝 (a, 0)] (fun _ => 1) :=
    (EvenSmoothDescent.evenCutoff_eventually_one R).comp_tendsto
      (continuous_snd.tendsto (a, (0 : ℝ)))
  filter_upwards [hp, hr] with q hq1 hq2
  simp only [localized, hq1, hq2, one_mul, one_smul]

omit [CompleteSpace E] in
theorem descend_localized_eventuallyEq (a A R : ℝ) (F : Plane → E) :
    descend (localized a A R F) =ᶠ[𝓝 (a, 0)] descend F :=
  (localized_eventuallyEq a A R F).comp_tendsto (by
    simpa only [Function.comp_apply, Real.sqrt_zero] using
      (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd)).tendsto
        (a, (0 : ℝ)))

/-- Joint smoothness at the axis uses only an actual smooth, radially even germ. -/
theorem contDiffWithinAt_descend_axis_local {a A R : ℝ} (hA : 0 < A) (hR : 0 < R)
    {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (Ioo (a - A) (a + A) ×ˢ Ioo (-R) R))
    (he : ∀ p ∈ Ioo (a - A) (a + A), ∀ r ∈ Ioo (-R) R, F (p, -r) = F (p, r)) :
    ContDiffWithinAt ℝ ∞ (descend F) (univ ×ˢ Ici (0 : ℝ)) (a, 0) := by
  have hg := contDiffOn_descend (contDiff_localized hA hR hF) (even_localized hA hR he)
  have hEq := descend_localized_eventuallyEq a A R F
  exact (hg (a, 0) (by simp)).congr_of_eventuallyEq
    (hEq.symm.filter_mono nhdsWithin_le_nhds) hEq.eq_of_nhds.symm

/-- Local joint smoothness on an open parameter set and a closed radial half-interval. -/
theorem contDiffOn_descend_local {U : Set ℝ} (hU : IsOpen U) {R : ℝ} (hR : 0 < R)
    {F : Plane → E} (hF : ContDiffOn ℝ ∞ F (U ×ˢ Ioo (-R) R))
    (he : ∀ p ∈ U, ∀ r ∈ Ioo (-R) R, F (p, -r) = F (p, r)) :
    ContDiffOn ℝ ∞ (descend F) (U ×ˢ Ico 0 (R ^ 2)) := by
  intro q hq
  rcases q with ⟨p, X⟩
  by_cases hz : X = 0
  · subst X
    rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hq.1) with ⟨A, hA, hsub⟩
    have hs : Ioo (p - A) (p + A) ⊆ U := by
      simpa only [Real.ball_eq_Ioo] using hsub
    have hFlocal : ContDiffOn ℝ ∞ F (Ioo (p - A) (p + A) ×ˢ Ioo (-R) R) :=
      hF.mono (Set.prod_mono hs (Subset.refl _))
    have heLocal : ∀ a ∈ Ioo (p - A) (p + A), ∀ r ∈ Ioo (-R) R,
        F (a, -r) = F (a, r) := fun a ha r hr => he a (hs ha) r hr
    exact (contDiffWithinAt_descend_axis_local hA hR hFlocal heLocal).mono
      (Set.prod_mono (subset_univ _) Ico_subset_Ici_self)
  · have hpos : 0 < X := lt_of_le_of_ne hq.2.1 (Ne.symm hz)
    have hsqrt : Real.sqrt X ∈ Ioo (-R) R := by
      constructor
      · linarith [Real.sqrt_nonneg X]
      · nlinarith [Real.sq_sqrt hq.2.1, Real.sqrt_nonneg X, hq.2.2]
    have hmem : (p, Real.sqrt X) ∈ U ×ˢ Ioo (-R) R := ⟨hq.1, hsqrt⟩
    have hFAt : ContDiffAt ℝ ∞ F (p, Real.sqrt X) :=
      hF.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hmem)
    have hc := hFAt.comp (p, X)
      (contDiffAt_fst.prodMk ((Real.contDiffAt_sqrt hz).comp (p, X) contDiffAt_snd))
    exact hc.contDiffWithinAt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
/-- Exact recovery of the original radial field after substituting a square. -/
theorem descend_square_local {U : Set ℝ} {R : ℝ} {F : Plane → E}
    (he : ∀ p ∈ U, ∀ r ∈ Ioo (-R) R, F (p, -r) = F (p, r))
    {p r : ℝ} (hp : p ∈ U) (hr : r ∈ Ioo (-R) R) :
    descend F (p, r ^ 2) = F (p, r) :=
  EvenSmoothDescent.descent_square_local (f := fun r => F (p, r)) (he p hp) hr

/-- The radial right jets in the joint descent are the exact even radial jets. -/
theorem iteratedDerivWithin_descend_axis_local {U : Set ℝ} {R : ℝ} (hR : 0 < R)
    {F : Plane → E} (hF : ContDiffOn ℝ ∞ F (U ×ˢ Ioo (-R) R))
    (he : ∀ p ∈ U, ∀ r ∈ Ioo (-R) R, F (p, -r) = F (p, r))
    {p : ℝ} (hp : p ∈ U) (n : ℕ) :
    iteratedDerivWithin n (fun X => descend F (p, X)) (Ici 0) 0 =
      ((n.factorial : ℝ) / ((2 * n).factorial : ℝ)) •
        iteratedDeriv (2 * n) (fun r => F (p, r)) 0 := by
  apply EvenSmoothDescent.iteratedDerivWithin_descent_zero_local (f := fun r => F (p, r)) hR
  · exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun r hr => ⟨hp, hr⟩)
  · exact he p hp

end NavierStokes.ParametricEvenDescent
