/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothPathFamily

@[expose] public section

/-!
# Joint parameter and current-time smoothness for linear ODE solutions

A fixed-interval solution is reparametrized from `[a,t]` onto `[0,1]`, with
`(p,t)` as its parameter. Evaluation at the fixed endpoint `1` is bounded
linear on the path space. A compact tube argument supplies genuinely open
coefficient neighborhoods, including when `t` is an original endpoint.

The reparametrized solution is a locally smooth extension of the original
solution on the prescribed closed interval. We do not assert smoothness of
the original clamped extension outside that interval.
-/

namespace NavierStokes.JointODE

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

universe u

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ}

/-- The actual extension constructed by the Volterra inverse, jointly indexed. -/
noncomputable def actualSolution (hab : a ≤ b) (A : P × ℝ → E →L[ℝ] E)
    (x₀ : P → E) (f : P × ℝ → E) (z : P × ℝ) : E :=
  ParametricODE.solutionExtension hab (SmoothPathFamily.pathFamily A z.1) (x₀ z.1)
    (SmoothPathFamily.pathFamily f z.1) z.2

/-- The affine time change from the unit interval to `[a,t]`. -/
noncomputable def affineTime (a t s : ℝ) : ℝ := a + s * (t - a)

@[simp] theorem affineTime_zero (a t : ℝ) : affineTime a t 0 = a := by
  simp [affineTime]

@[simp] theorem affineTime_one (a t : ℝ) : affineTime a t 1 = t := by
  simp [affineTime]

theorem affineTime_mem {t s : ℝ} (ht : t ∈ Icc a b) (hs : s ∈ Icc (0 : ℝ) 1) :
    affineTime a t s ∈ Icc a b := by
  have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
  have hlo : 0 ≤ s * (t - a) := mul_nonneg hs.1 hta
  have hhi : s * (t - a) ≤ t - a := mul_le_of_le_one_left hta hs.2
  unfold affineTime
  constructor <;> linarith [ht.2]

theorem hasDerivAt_affineTime (a t s : ℝ) :
    HasDerivAt (affineTime a t) (t - a) s := by
  change HasDerivAt (fun r : ℝ => a + r * (t - a)) (t - a) s
  simpa using ((hasDerivAt_id s).mul_const (t - a)).const_add a

/-- `(p,t,s)` is sent to the original coefficient argument `(p,a+s(t-a))`. -/
noncomputable def timeMap (a : ℝ) (w : (P × ℝ) × ℝ) : P × ℝ :=
  (w.1.1, affineTime a w.1.2 w.2)

theorem contDiff_timeMap (a : ℝ) : ContDiff ℝ ∞ (timeMap (P := P) a) :=
  contDiff_fst.fst.prodMk
    (contDiff_const.add (contDiff_snd.mul (contDiff_fst.snd.sub contDiff_const)))

variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Both the linear coefficient and the source acquire the time-change factor. -/
noncomputable def rescale (a : ℝ) (F : P × ℝ → W) (w : (P × ℝ) × ℝ) : W :=
  (w.1.2 - a) • F (timeMap a w)

theorem rescale_contDiffOn {U : Set P} {V : Set ℝ}
    {Q : Set (P × ℝ)} {S : Set ℝ} (F : P × ℝ → W)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    (hmap : MapsTo (timeMap a) (Q ×ˢ S) (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (rescale a F) (Q ×ˢ S) :=
  (contDiff_fst.snd.sub contDiff_const).contDiffOn.smul
    (hF.comp (contDiff_timeMap a).contDiffOn hmap)

omit [NormedSpace ℝ P] in
theorem rescale_slice_continuousOn {U : Set P} (F : P × ℝ → W)
    (hF : ContinuousOn F (U ×ˢ Icc a b)) {z : P × ℝ} (hz : z ∈ U ×ˢ Icc a b) :
    ContinuousOn (fun s => rescale a F (z, s)) (Icc (0 : ℝ) 1) := by
  have ht : Continuous (affineTime a z.2) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have hc : ContinuousOn (fun s : ℝ => F (z.1, affineTime a z.2 s)) (Icc (0 : ℝ) 1) :=
    hF.comp (continuousOn_const.prodMk ht.continuousOn)
      (fun s hs => ⟨hz.1, affineTime_mem hz.2 hs⟩)
  exact (continuousOn_const (c := z.2 - a)).smul hc

/-- A new solution on the fixed unit interval, evaluated at its fixed right endpoint. -/
noncomputable def reparamSolution (a : ℝ) (A : P × ℝ → E →L[ℝ] E)
    (x₀ : P → E) (f : P × ℝ → E) (z : P × ℝ) : E :=
  SmoothPathFamily.odeFamily (a := 0) (b := 1) zero_le_one
    (rescale a A) (fun q => x₀ q.1) (rescale a f) z ⟨1, zero_le_one, le_rfl⟩

/-- This representative is smooth on a genuine open neighborhood of every
point of the original closed parameter/time domain. -/
theorem reparamSolution_contDiffAt (U : Set P) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) {z : P × ℝ} (hz : z ∈ U ×ˢ Icc a b) :
    ContDiffAt ℝ ∞ (reparamSolution a A x₀ f) z := by
  let Ω : Set ((P × ℝ) × ℝ) := (timeMap a) ⁻¹' (U ×ˢ V)
  have hΩ : IsOpen Ω := (hU.prod hV).preimage (contDiff_timeMap a).continuous
  have hsubset : ({z} : Set (P × ℝ)) ×ˢ Icc (0 : ℝ) 1 ⊆ Ω := by
    rintro ⟨q, s⟩ ⟨hq, hs⟩
    have hqz : q = z := mem_singleton_iff.mp hq
    subst q
    exact ⟨hz.1, hI (affineTime_mem hz.2 hs)⟩
  obtain ⟨Q, S, hQ, hS, hzQ, hIS, hQS⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hΩ hsubset
  have hzQ' : z ∈ Q := hzQ (mem_singleton z)
  have hmap : MapsTo (timeMap a) (Q ×ˢ S) (U ×ˢ V) := hQS
  have hinit : ContDiffOn ℝ ∞ (fun q : P × ℝ => x₀ q.1) Q := by
    apply hx₀.comp contDiffOn_fst
    intro q hq
    exact (hmap (show (q, (0 : ℝ)) ∈ Q ×ˢ S from
      ⟨hq, hIS ⟨le_rfl, zero_le_one⟩⟩)).1
  have hpath := SmoothPathFamily.contDiffOn_odeFamily_of_joint
    (a := 0) (b := 1) zero_le_one Q S hQ hS hIS
    (rescale a A) (fun q => x₀ q.1) (rescale a f)
    (rescale_contDiffOn A hA hmap) hinit (rescale_contDiffOn f hf hmap)
  have hev := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (ContinuousMap.evalCLM ℝ (⟨1, zero_le_one, le_rfl⟩ : Icc (0 : ℝ) 1))).comp_contDiffOn hpath
  exact (hev z hzQ').contDiffAt (hQ.mem_nhds hzQ')

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem actualSolution_initial (hab : a ≤ b) (A : P × ℝ → E →L[ℝ] E)
    (x₀ : P → E) (f : P × ℝ → E) (p : P) :
    actualSolution hab A x₀ f (p, a) = x₀ p := by
  simp only [actualSolution, ParametricODE.solutionExtension,
    intervalIntegral.integral_same, add_zero]

omit [NormedSpace ℝ P] in
/-- The actual extension solves the original ODE at every point of the closed interval. -/
theorem actualSolution_hasDerivAt (hab : a ≤ b) {U : Set P}
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContinuousOn A (U ×ˢ Icc a b)) (hf : ContinuousOn f (U ×ˢ Icc a b))
    {p : P} (hp : p ∈ U) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivAt (fun s => actualSolution hab A x₀ f (p, s))
      (A (p, t) (actualSolution hab A x₀ f (p, t)) + f (p, t)) t := by
  have hAc := SmoothPathFamily.slice_continuous hA hp
  have hfc := SmoothPathFamily.slice_continuous hf hp
  have hd := ParametricODE.solutionExtension_hasDerivAt hab
    (SmoothPathFamily.pathFamily A p) (x₀ p) (SmoothPathFamily.pathFamily f p) ⟨t, ht⟩
  unfold actualSolution
  simpa only [SmoothPathFamily.pathFamily_apply A p hAc,
    SmoothPathFamily.pathFamily_apply f p hfc] using hd

omit [NormedSpace ℝ P] in
/-- Uniqueness identifies the fixed-unit-interval construction with the actual
Volterra solution at every parameter and every time in the closed interval. -/
theorem reparamSolution_eq_actualSolution (hab : a ≤ b) {U : Set P}
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContinuousOn A (U ×ˢ Icc a b)) (hf : ContinuousOn f (U ×ˢ Icc a b))
    {z : P × ℝ} (hz : z ∈ U ×ˢ Icc a b) :
    reparamSolution a A x₀ f z = actualSolution hab A x₀ f z := by
  let B : ℝ → E →L[ℝ] E := fun s => rescale a A (z, s)
  let g : ℝ → E := fun s => rescale a f (z, s)
  let y : ℝ → E := ParametricODE.solutionExtension (a := 0) (b := 1) zero_le_one
    (SmoothPathFamily.pathFamily (rescale a A) z) (x₀ z.1)
    (SmoothPathFamily.pathFamily (rescale a f) z)
  let w : ℝ → E := fun s => actualSolution hab A x₀ f (z.1, affineTime a z.2 s)
  have hB : ContinuousOn B (Icc (0 : ℝ) 1) := rescale_slice_continuousOn A hA hz
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := rescale_slice_continuousOn f hf hz
  have hBc : Continuous (fun s : Icc (0 : ℝ) 1 => rescale a A (z, s)) := hB.domRestrict
  have hgc : Continuous (fun s : Icc (0 : ℝ) 1 => rescale a f (z, s)) := hg.domRestrict
  have hy : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt y (B s (y s) + g s) s := by
    intro s hs
    have hd := ParametricODE.solutionExtension_hasDerivAt (a := 0) (b := 1) zero_le_one
      (SmoothPathFamily.pathFamily (rescale a A) z) (x₀ z.1)
      (SmoothPathFamily.pathFamily (rescale a f) z) ⟨s, hs⟩
    simpa only [SmoothPathFamily.pathFamily_apply (rescale a A) z hBc,
      SmoothPathFamily.pathFamily_apply (rescale a f) z hgc] using hd
  have hw : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt w (B s (w s) + g s) s := by
    intro s hs
    have hd := (actualSolution_hasDerivAt hab A x₀ f hA hf hz.1
      (affineTime_mem hz.2 hs)).scomp s (hasDerivAt_affineTime a z.2 s)
    simpa only [w, B, g, rescale, timeMap, Function.comp_def,
      _root_.smul_apply, smul_add] using hd
  have hinit : y 0 = w 0 := by
    change x₀ z.1 + (∫ s in (0 : ℝ)..0,
      ParametricODE.extend zero_le_one
        (ParametricODE.applyCoefficient (SmoothPathFamily.pathFamily (rescale a A) z)
          (ParametricODE.solution zero_le_one
            (SmoothPathFamily.pathFamily (rescale a A) z) (x₀ z.1)
            (SmoothPathFamily.pathFamily (rescale a f) z)) +
          SmoothPathFamily.pathFamily (rescale a f) z) s) = w 0
    simp only [intervalIntegral.integral_same, add_zero, w, affineTime_zero,
      actualSolution_initial]
  have heq := TangentODE.linear_solution_unique zero_le_one B g hB hy hw hinit
  have h1 := heq (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  have hy1 : y 1 = reparamSolution a A x₀ f z :=
    ParametricODE.solutionExtension_coe zero_le_one _ _ _ ⟨1, zero_le_one, le_rfl⟩
  rw [hy1] at h1
  simpa only [w, affineTime_one, Prod.mk.eta] using h1

/-- Genuine joint parameter/current-time C∞ for the actual solution on the
closed interval, including its endpoints in the relative smoothness sense. -/
theorem contDiffOn_solutionExtension_joint (hab : a ≤ b) (U : Set P) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞
      (fun z : P × ℝ => ParametricODE.solutionExtension hab
        (SmoothPathFamily.pathFamily A z.1) (x₀ z.1)
        (SmoothPathFamily.pathFamily f z.1) z.2) (U ×ˢ Icc a b) := by
  have hs : ContDiffOn ℝ ∞ (reparamSolution a A x₀ f) (U ×ˢ Icc a b) :=
    fun z hz => (reparamSolution_contDiffAt U V hU hV hI A x₀ f hA hx₀ hf hz).contDiffWithinAt
  apply hs.congr
  intro z hz
  exact (reparamSolution_eq_actualSolution hab A x₀ f
    (hA.continuousOn.mono (prod_mono Subset.rfl hI))
    (hf.continuousOn.mono (prod_mono Subset.rfl hI)) hz).symm

/-- The interior form used when localizing a solution inside the slot. -/
theorem contDiffOn_solutionExtension_joint_interior (hab : a ≤ b) (U : Set P) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞
      (fun z : P × ℝ => ParametricODE.solutionExtension hab
        (SmoothPathFamily.pathFamily A z.1) (x₀ z.1)
        (SmoothPathFamily.pathFamily f z.1) z.2) (U ×ˢ Ioo a b) :=
  (contDiffOn_solutionExtension_joint hab U V hU hV hI A x₀ f hA hx₀ hf).mono
    (prod_mono Subset.rfl Ioo_subset_Icc_self)

end

end NavierStokes.JointODE
