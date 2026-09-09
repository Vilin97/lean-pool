/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionState
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveInteractionBounds

@[expose] public section

/-!
# Exact angular averages of the lifted correction residual

Angular integration is over the actual circle variable. All differentiation
uses Fréchet derivatives on an open lifted strip; the graph operators are
instantiated from `CorrectionState.Context.operators`.
-/

namespace NavierStokes.LiftedMeanResidual

noncomputable section

open Set Filter MeasureTheory HarmonicCalculus
open scoped ContDiff Topology BigOperators

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def cylinder (U : Set D) : Set (D × ℝ) := U ×ˢ univ

omit [NormedSpace ℝ D] in
theorem cylinder_open {U : Set D} (hU : IsOpen U) : IsOpen (cylinder U) :=
  hU.prod isOpen_univ

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem continuous_slice {U : Set D} (hU : IsOpen U) {f : D × ℝ → E}
    (hf : ContinuousOn f (cylinder U)) {x : D} (hx : x ∈ U) :
    Continuous (fun θ : ℝ => f (x, θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact ((hf (x, θ) ⟨hx, mem_univ θ⟩).continuousAt
    ((cylinder_open hU).mem_nhds ⟨hx, mem_univ θ⟩)).comp
    (continuous_const.prodMk continuous_id).continuousAt

theorem constant_mul_continuous (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun t => c * f t) := continuous_const.mul hf

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem uniform_local_bound {U : Set D} (hU : IsOpen U) {f : D × ℝ → E}
    (hf : ContinuousOn f (cylinder U)) {x : D} (hx : x ∈ U) (a b : ℝ) :
    ∃ η > 0, ∃ C : ℝ, Metric.ball x η ⊆ U ∧
      ∀ y ∈ Metric.ball x η, ∀ θ ∈ uIcc a b, ‖f (y, θ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (continuous_slice hU hf hx).continuousOn
  let W : Set (D × ℝ) := cylinder U ∩ {p | ‖f p‖ < C + 1}
  have hW : IsOpen W := hf.norm.isOpen_inter_preimage (cylinder_open hU) isOpen_Iio
  have hsub : ({x} : Set D) ×ˢ uIcc a b ⊆ W := by
    rintro ⟨y, θ⟩ ⟨hy, hθ⟩
    simp only [mem_singleton_iff] at hy
    subst y
    exact ⟨⟨hx, mem_univ θ⟩, lt_of_le_of_lt (hC θ hθ) (lt_add_one C)⟩
  obtain ⟨V, Wθ, hV, _, hxV, hθW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hW hsub
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp
    ((hV.inter hU).mem_nhds ⟨hxV (mem_singleton x), hx⟩)
  refine ⟨η, hη, C + 1, fun y hy => (hball hy).2, ?_⟩
  intro y hy θ hθ
  exact (hVW ⟨(hball hy).1, hθW hθ⟩).2.le

theorem parameterDerivative_smooth {U : Set D} (hU : IsOpen U) {f : D × ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) :
    ContDiffOn ℝ ∞ (TransportPrimitive.parameterDerivative f) (cylinder U) :=
  (hf.fderiv_of_isOpen (cylinder_open hU) (by simp)).clm_comp contDiffOn_const

theorem parameter_hasFDerivAt {U : Set D} (hU : IsOpen U) {f : D × ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) {x : D} (hx : x ∈ U) (θ : ℝ) :
    HasFDerivAt (fun y => f (y, θ)) (TransportPrimitive.parameterDerivative f (x, θ)) x := by
  exact (((hf.contDiffAt ((cylinder_open hU).mem_nhds ⟨hx, mem_univ θ⟩)).differentiableAt
    (by simp)).hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const θ x)))

theorem parameterIntegral_hasFDerivAt {U : Set D} (hU : IsOpen U) {f : D × ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) (a b : ℝ) {x : D} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ θ in a..b, f (y, θ))
      (∫ θ in a..b, TransportPrimitive.parameterDerivative f (x, θ)) x := by
  have hdf := (parameterDerivative_smooth hU hf).continuousOn
  obtain ⟨η, hη, C, hball, hC⟩ := uniform_local_bound hU hdf hx a b
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y θ => TransportPrimitive.parameterDerivative f (y, θ)) (bound := fun _ => C)
    (Metric.ball_mem_nhds x hη)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (continuous_slice hU hf.continuousOn hy).aestronglyMeasurable
  · exact (continuous_slice hU hf.continuousOn hx).intervalIntegrable a b
  · exact (continuous_slice hU hdf hx).aestronglyMeasurable
  · exact Eventually.of_forall fun θ hθ y hy => hC y hy θ (uIoc_subset_uIcc hθ)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun θ _ y hy => parameter_hasFDerivAt hU hf (hball hy) θ

theorem parameterIntegral_smooth_nat {U : Set D} (hU : IsOpen U) (m : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {f : D × ℝ → E}, ContDiffOn ℝ ∞ f (cylinder U) → ∀ a b : ℝ,
      ContDiffOn ℝ (m : ℕ∞) (fun x => ∫ θ in a..b, f (x, θ)) U := by
  induction m with
  | zero =>
    intro E _ _ _ f hf a b
    apply contDiffOn_zero.mpr
    intro x hx
    exact (parameterIntegral_hasFDerivAt hU hf a b hx).continuousAt.continuousWithinAt
  | succ m ih =>
    intro E _ _ _ f hf a b
    rw [show (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by simp]
    apply (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr
    refine ⟨fun x hx => (parameterIntegral_hasFDerivAt hU hf a b
      hx).differentiableAt.differentiableWithinAt,
      (by simp), ?_⟩
    exact (ih (parameterDerivative_smooth hU hf) a b).congr
      (fun x hx => (parameterIntegral_hasFDerivAt hU hf a b hx).fderiv)

theorem parameterIntegral_smooth [CompleteSpace E] {U : Set D} (hU : IsOpen U)
    {f : D × ℝ → E} (hf : ContDiffOn ℝ ∞ f (cylinder U)) (a b : ℝ) :
    ContDiffOn ℝ ∞ (fun x => ∫ θ in a..b, f (x, θ)) U :=
  contDiffOn_infty.mpr (fun m => parameterIntegral_smooth_nat hU m hf a b)

noncomputable def period : ℝ := 2 * Real.pi

theorem period_ne : period ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero

noncomputable def avg (f : D × ℝ → ℝ) (x : D) : ℝ :=
  (∫ θ in (0 : ℝ)..period, f (x, θ)) / period

noncomputable def liftDirection (V : D → D) (p : D × ℝ) : D × ℝ := (V p.1, 0)

noncomputable def angularDirection (_p : D × ℝ) : D × ℝ := (0, 1)

noncomputable def liftScalar (f : D → ℝ) (p : D × ℝ) : ℝ := f p.1

theorem liftDirection_smooth {U : Set D} {V : D → D} (hV : ContDiffOn ℝ ∞ V U) :
    ContDiffOn ℝ ∞ (liftDirection V) (cylinder U) :=
  (hV.comp contDiffOn_fst (fun _ h => h.1)).prodMk contDiffOn_const

theorem liftScalar_smooth {U : Set D} {f : D → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (liftScalar f) (cylinder U) :=
  hf.comp contDiffOn_fst (fun _ h => h.1)

theorem avg_smooth {U : Set D} (hU : IsOpen U) {f : D × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) : ContDiffOn ℝ ∞ (avg f) U :=
  (parameterIntegral_smooth hU hf 0 period).div_const period

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_lift (f : D → ℝ) : avg (liftScalar f) = f := by
  funext x
  simp [avg, liftScalar, period_ne]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_add {f g : D × ℝ → ℝ} {x : D}
    (hf : Continuous (fun θ : ℝ => f (x, θ))) (hg : Continuous (fun θ : ℝ => g (x, θ))) :
    avg (fun p => f p + g p) x = avg f x + avg g x := by
  rw [avg, intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    add_div]
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_sub {f g : D × ℝ → ℝ} {x : D}
    (hf : Continuous (fun θ : ℝ => f (x, θ))) (hg : Continuous (fun θ : ℝ => g (x, θ))) :
    avg (fun p => f p - g p) x = avg f x - avg g x := by
  rw [avg, intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    sub_div]
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_mul_left (a : D → ℝ) (f : D × ℝ → ℝ) (x : D) :
    avg (fun p => a p.1 * f p) x = a x * avg f x := by
  simp only [avg, intervalIntegral.integral_const_mul]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_mul_right (f : D × ℝ → ℝ) (a : D → ℝ) (x : D) :
    avg (fun p => f p * a p.1) x = avg f x * a x := by
  simp only [avg, intervalIntegral.integral_mul_const]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_congr {U : Set D} {f g : D × ℝ → ℝ} (hfg : EqOn f g (cylinder U))
    {x : D} (hx : x ∈ U) : avg f x = avg g x := by
  unfold avg
  congr 1
  exact intervalIntegral.integral_congr (fun θ _ => hfg ⟨hx, mem_univ θ⟩)

theorem along_avg {U : Set D} (hU : IsOpen U) {f : D × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) (V : D → D) {x : D} (hx : x ∈ U) :
    along V (avg f) x = avg (along (liftDirection V) f) x := by
  have hI := parameterIntegral_hasFDerivAt hU hf 0 period hx
  have hI' := hI.mul_const period⁻¹
  unfold along avg
  simp only [div_eq_mul_inv]
  rw [hI'.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [mul_comm period⁻¹]
  congr 1
  rw [ContinuousLinearMap.intervalIntegral_apply]
  · rfl
  · exact (continuous_slice hU (parameterDerivative_smooth hU hf).continuousOn
    hx).intervalIntegrable _ _

theorem avg_along_twice {U : Set D} (hU : IsOpen U) {f : D × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) {V : D → D} (hV : ContDiffOn ℝ ∞ V U)
    {x : D} (hx : x ∈ U) :
    avg (along (liftDirection V) (along (liftDirection V) f)) x =
      along V (along V (avg f)) x := by
  rw [← along_avg hU (contDiffOn_along (cylinder_open hU) (liftDirection_smooth hV) hf) V hx]
  exact along_congr hU (fun y hy => (along_avg hU hf V hy).symm) hx

def PeriodicOn (U : Set D) (f : D × ℝ → E) : Prop :=
  ∀ x ∈ U, ∀ θ : ℝ, f (x, θ + period) = f (x, θ)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem PeriodicOn.add {U : Set D} {f g : D × ℝ → E}
    (hf : PeriodicOn U f) (hg : PeriodicOn U g) : PeriodicOn U (fun p => f p + g p) := by
  intro x hx θ
  dsimp only
  rw [hf x hx θ, hg x hx θ]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem PeriodicOn.mul {U : Set D} {f g : D × ℝ → ℝ}
    (hf : PeriodicOn U f) (hg : PeriodicOn U g) : PeriodicOn U (fun p => f p * g p) := by
  intro x hx θ
  dsimp only
  rw [hf x hx θ, hg x hx θ]

theorem PeriodicOn.theta {U : Set D} (hU : IsOpen U) {f : D × ℝ → E}
    (hf : PeriodicOn U f) : PeriodicOn U (along angularDirection f) := by
  intro x hx θ
  have he : (fun p : D × ℝ => f (p + (0, period))) =ᶠ[𝓝 (x, θ)] f := by
    filter_upwards [(cylinder_open hU).mem_nhds ⟨hx, mem_univ θ⟩] with p hp
    change f (p.1 + 0, p.2 + period) = f (p.1, p.2)
    simpa only [add_zero] using hf p.1 hp.1 p.2
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_add_right] at hd
  change fderiv ℝ f (x + 0, θ + period) = fderiv ℝ f (x, θ) at hd
  simp only [add_zero] at hd
  exact congrArg (fun L : D × ℝ →L[ℝ] E => L (0, 1)) hd

theorem hasDerivAt_theta {U : Set D} (hU : IsOpen U) {f : D × ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) {x : D} (hx : x ∈ U) (θ : ℝ) :
    HasDerivAt (fun a : ℝ => f (x, a)) (along angularDirection f (x, θ)) θ := by
  exact (((hf.contDiffAt ((cylinder_open hU).mem_nhds ⟨hx, mem_univ θ⟩)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt θ
      ((hasDerivAt_const θ x).prodMk (hasDerivAt_id θ)))

theorem avg_theta_zero {U : Set D} (hU : IsOpen U) {f : D × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) (hp : PeriodicOn U f)
    {x : D} (hx : x ∈ U) : avg (along angularDirection f) x = 0 := by
  have hs : ContDiffOn ℝ ∞ (along angularDirection f) (cylinder U) :=
    contDiffOn_along (cylinder_open hU) contDiffOn_const hf
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_theta hU hf hx θ)
    ((continuous_slice hU hs.continuousOn hx).intervalIntegrable 0 period)
  have hb : f (x, period) = f (x, 0) := by simpa using hp x hx 0
  rw [hb, sub_self] at hi
  simp only [avg, hi, zero_div]

theorem avg_theta_twice_zero {U : Set D} (hU : IsOpen U) {f : D × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) (hp : PeriodicOn U f)
    {x : D} (hx : x ∈ U) : avg (along angularDirection (along angularDirection f)) x = 0 :=
  avg_theta_zero hU (contDiffOn_along (cylinder_open hU) contDiffOn_const hf) (hp.theta hU) hx

theorem along_lift {f : D → ℝ} {x : D} (hf : DifferentiableAt ℝ f x)
    (V : D → D) (θ : ℝ) :
    along (liftDirection V) (liftScalar f) (x, θ) = along V f x := by
  unfold along liftScalar
  have hd : HasFDerivAt (fun p : D × ℝ => f p.1)
      ((fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ D ℝ)) (x, θ) :=
    hf.hasFDerivAt.comp (x, θ) hasFDerivAt_fst
  rw [hd.fderiv]
  rfl

theorem theta_lift_zero {f : D → ℝ} {x : D} (hf : DifferentiableAt ℝ f x) (θ : ℝ) :
    along angularDirection (liftScalar f) (x, θ) = 0 := by
  unfold along liftScalar
  have hd : HasFDerivAt (fun p : D × ℝ => f p.1)
      ((fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ D ℝ)) (x, θ) :=
    hf.hasFDerivAt.comp (x, θ) hasFDerivAt_fst
  rw [hd.fderiv]
  change fderiv ℝ f x 0 = 0
  exact map_zero _

noncomputable def radialVector (o : MeanIncrementBounds.Operators D) (n : ℕ) (x : D) : D :=
  o.eR + (o.radialFrequency n * o.radialProfile x) • o.vR

noncomputable def axialVector (o : MeanIncrementBounds.Operators D) (n : ℕ) (_x : D) : D :=
  o.epsilon n • o.eZ

noncomputable def temporalVector (o : MeanIncrementBounds.Operators D) (n : ℕ) (_x : D) : D :=
  o.fastCoefficient n • o.vT - o.epsilon n • o.eT

noncomputable def radialDirection (c : CorrectionState.Context D) (n : ℕ) : D × ℝ → D × ℝ :=
  liftDirection (radialVector c.operators n)

noncomputable def axialDirection (c : CorrectionState.Context D) (n : ℕ) : D × ℝ → D × ℝ :=
  liftDirection (axialVector c.operators n)

noncomputable def timeDirection (c : CorrectionState.Context D) (n : ℕ) : D × ℝ → D × ℝ :=
  liftDirection (temporalVector c.operators n)

noncomputable def complexBase (c : CorrectionState.Context D) (n : ℕ) (x : D × ℝ) : ComplexVector :=
  ![(c.base.radial n x.1 : ℂ), (c.base.angular n x.1 : ℂ), (c.base.axial n x.1 : ℂ)]

noncomputable def complexPerturbation (u : CorrectionState.State D) (n : ℕ) (x : D × ℝ) :
  ComplexVector :=
  ![(u.mean.radial n x.1 + u.oscillation n x 0 : ℝ),
    (u.mean.angular n x.1 + u.oscillation n x 1 : ℝ),
    (u.mean.axial n x.1 + u.oscillation n x 2 : ℝ)]

noncomputable def complexPressure (u : CorrectionState.State D) (n : ℕ) (x : D × ℝ) : ℂ :=
  (u.totalPressureIncrement n x : ℝ)

noncomputable def virtualDivergence (c : CorrectionState.Context D) (n : ℕ) (x : D × ℝ) : Fin 3 → ℝ
  :=
  ![0, -(c.operators.radialDiv 2 c.virtualTheta n x.1),
    -(c.operators.radialDiv 1 c.virtualAxial n x.1)]

noncomputable def nonlinearResidual (ε : ℝ) (R : (D × ℝ) → ℝ)
    (Vr Vθ Vz Vt : D × ℝ → D × ℝ) (B a : D × ℝ → ComplexVector)
    (p : D × ℝ → ℂ) (x : D × ℝ) : ComplexVector :=
  LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B a p x +
    LinearWaveResidual.transport R Vr Vθ Vz a a x

noncomputable def fullResidual (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    CorrectionState.Oscillation D := fun n x i =>
  (nonlinearResidual (c.operators.epsilon n) (fun y : D × ℝ => c.operators.radius y.1)
    (radialDirection c n) angularDirection (axialDirection c n) (timeDirection c n)
    (complexBase c n) (complexPerturbation u n) (complexPressure u n) x i).re +
      virtualDivergence c n x i + u.errors.base n x i

noncomputable def fullGoodResidual (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    CorrectionState.Oscillation D := fullResidual c u - u.errors.total

noncomputable def angularMeanVector (f : CorrectionState.Oscillation D) :
  CorrectionState.MeanVector D :=
  fun n x i => CorrectionState.angularAverage (fun k p => f k p i) n x

noncomputable def realDivergence (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    (a : D × ℝ → Fin 3 → ℝ) (p : D × ℝ) : ℝ :=
  along Vr (fun y => a y 0) p + a p 0 / R p +
    along Vθ (fun y => a y 1) p / R p + along Vz (fun y => a y 2) p

noncomputable def quadraticFlux (B a : D × ℝ → Fin 3 → ℝ) (i j : Fin 3) (p : D × ℝ) : ℝ :=
  B p i * a p j + a p i * B p j + a p i * a p j

noncomputable def advectionIncrement (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    (B a : D × ℝ → Fin 3 → ℝ) (p : D × ℝ) : Fin 3 → ℝ :=
  LinearWaveResidual.realTransport R Vr Vθ Vz B a p +
    LinearWaveResidual.realTransport R Vr Vθ Vz a B p +
    LinearWaveResidual.realTransport R Vr Vθ Vz a a p

noncomputable def conservativeFlux (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    (J : Fin 3 → Fin 3 → D × ℝ → ℝ) (p : D × ℝ) : Fin 3 → ℝ :=
  ![along Vr (J 0 0) p + J 0 0 p / R p + along Vθ (J 1 0) p / R p +
      along Vz (J 2 0) p - J 1 1 p / R p,
    along Vr (J 0 1) p + 2 * J 0 1 p / R p + along Vθ (J 1 1) p / R p +
      along Vz (J 2 1) p,
    along Vr (J 0 2) p + J 0 2 p / R p + along Vθ (J 1 2) p / R p +
      along Vz (J 2 2) p]

/-- The conservative quadratic identity is derived before taking an average.
The two divergence errors display exactly which solenoidality is needed. -/
theorem advectionIncrement_conservative (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    {B a : D × ℝ → Fin 3 → ℝ} {p : D × ℝ}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) p)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) p) (i : Fin 3) :
    advectionIncrement R Vr Vθ Vz B a p i =
      conservativeFlux R Vr Vθ Vz (quadraticFlux B a) p i -
        realDivergence R Vr Vθ Vz B p * a p i -
        realDivergence R Vr Vθ Vz a p * (B p i + a p i) := by
  have hd (V : D × ℝ → D × ℝ) (j k : Fin 3) :
      along V (quadraticFlux B a j k) p =
        (along V (fun y => B y j) p * a p k + B p j * along V (fun y => a y k) p) +
        (along V (fun y => a y j) p * B p k + a p j * along V (fun y => B y k) p) +
        (along V (fun y => a y j) p * a p k + a p j * along V (fun y => a y k) p) := by
    unfold quadraticFlux
    rw [along_add V (((hB j).fun_mul (ha k)).fun_add ((ha j).fun_mul (hB k))) ((ha j).fun_mul (ha
      k)),
      along_add V ((hB j).fun_mul (ha k)) ((ha j).fun_mul (hB k)),
      LinearWaveResidual.along_mul_real V (hB j) (ha k),
      LinearWaveResidual.along_mul_real V (ha j) (hB k),
      LinearWaveResidual.along_mul_real V (ha j) (ha k)]
  fin_cases i <;>
    simp [advectionIncrement, LinearWaveResidual.realTransport,
      LinearWaveResidual.realAngularGenerator,
      conservativeFlux, realDivergence, hd, quadraticFlux] <;> ring

theorem advectionIncrement_eq_conservative (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    {B a : D × ℝ → Fin 3 → ℝ} {p : D × ℝ}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) p)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) p)
    (hBd : realDivergence R Vr Vθ Vz B p = 0)
    (had : realDivergence R Vr Vθ Vz a p = 0) :
    advectionIncrement R Vr Vθ Vz B a p = conservativeFlux R Vr Vθ Vz (quadraticFlux B a) p := by
  funext i
  rw [advectionIncrement_conservative R Vr Vθ Vz hB ha i, hBd, had]
  ring

structure Regular (U : Set D) (R : D → ℝ) (Vr Vz Vt : D → D) : Prop where
  isOpen : IsOpen U
  radius_smooth : ContDiffOn ℝ ∞ R U
  radius_ne : ∀ x ∈ U, R x ≠ 0
  radial_smooth : ContDiffOn ℝ ∞ Vr U
  axial_smooth : ContDiffOn ℝ ∞ Vz U
  time_smooth : ContDiffOn ℝ ∞ Vt U

theorem quadraticFlux_smooth {U : Set D} {B a : D × ℝ → Fin 3 → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) (cylinder U))
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) (cylinder U)) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (quadraticFlux B a i j) (cylinder U) :=
  (((hB i).mul (ha j)).add ((ha i).mul (hB j))).add ((ha i).mul (ha j))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem quadraticFlux_periodic {U : Set D} {B a : D × ℝ → Fin 3 → ℝ}
    (hB : ∀ i, PeriodicOn U (fun y => B y i))
    (ha : ∀ i, PeriodicOn U (fun y => a y i)) (i j : Fin 3) :
    PeriodicOn U (quadraticFlux B a i j) :=
  (((hB i).mul (ha j)).add ((ha i).mul (hB j))).add ((ha i).mul (ha j))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_div (f : D × ℝ → ℝ) (a : D → ℝ) (x : D) :
    avg (fun p => f p / a p.1) x = avg f x / a x := by
  simpa only [div_eq_mul_inv] using avg_mul_right f (fun y => (a y)⁻¹) x

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_const_mul (c : ℝ) (f : D × ℝ → ℝ) (x : D) :
    avg (fun p => c * f p) x = c * avg f x := avg_mul_left (fun _ => c) f x

noncomputable def meanConservativeFlux (R : D → ℝ) (Vr Vz : D → D)
    (J : Fin 3 → Fin 3 → D → ℝ) (x : D) : Fin 3 → ℝ :=
  ![along Vr (J 0 0) x + J 0 0 x / R x + along Vz (J 2 0) x - J 1 1 x / R x,
    along Vr (J 0 1) x + 2 * J 0 1 x / R x + along Vz (J 2 1) x,
    along Vr (J 0 2) x + J 0 2 x / R x + along Vz (J 2 2) x]

theorem avg_conservativeFlux {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) {J : Fin 3 → Fin 3 → D × ℝ → ℝ}
    (hJ : ∀ i j, ContDiffOn ℝ ∞ (J i j) (cylinder U))
    (hp : ∀ i j, PeriodicOn U (J i j)) {x : D} (hx : x ∈ U) (i : Fin 3) :
    avg (fun p => conservativeFlux (liftScalar R) (liftDirection Vr) angularDirection
      (liftDirection Vz) J p i) x =
      meanConservativeFlux R Vr Vz (fun i j => avg (J i j)) x i := by
  have hJc j k := continuous_slice G.isOpen (hJ j k).continuousOn hx
  have hrc j k := continuous_slice G.isOpen
    (contDiffOn_along (cylinder_open G.isOpen) (liftDirection_smooth G.radial_smooth) (hJ j
      k)).continuousOn hx
  have hzc j k := continuous_slice G.isOpen
    (contDiffOn_along (cylinder_open G.isOpen) (liftDirection_smooth G.axial_smooth) (hJ j
      k)).continuousOn hx
  have hθc j k : Continuous (fun θ => along angularDirection (J j k) (x, θ)) :=
    continuous_slice G.isOpen
      (contDiffOn_along (cylinder_open G.isOpen) contDiffOn_const (hJ j k)).continuousOn hx
  have hr j k := (along_avg G.isOpen (hJ j k) Vr hx).symm
  have hz j k := (along_avg G.isOpen (hJ j k) Vz hx).symm
  have hθ j k := avg_theta_zero G.isOpen (hJ j k) (hp j k) hx
  have hcorec j (c : ℝ) : Continuous (fun θ =>
      along (liftDirection Vr) (J 0 j) (x, θ) + c * J 0 j (x, θ) / R x +
        along angularDirection (J 1 j) (x, θ) / R x + along (liftDirection Vz) (J 2 j) (x, θ)) :=
    (((hrc 0 j).add ((continuous_const.mul (hJc 0 j)).div_const (R x))).add
      ((hθc 1 j).div_const (R x))).add (hzc 2 j)
  have hcore j (c : ℝ) : avg (fun p =>
      along (liftDirection Vr) (J 0 j) p + c * J 0 j p / R p.1 +
        along angularDirection (J 1 j) p / R p.1 + along (liftDirection Vz) (J 2 j) p) x =
      along Vr (avg (J 0 j)) x + c * avg (J 0 j) x / R x + along Vz (avg (J 2 j)) x := by
    rw [avg_add (((hrc 0 j).add ((continuous_const.mul (hJc 0 j)).div_const (R x))).add
        ((hθc 1 j).div_const (R x))) (hzc 2 j),
      avg_add ((hrc 0 j).add ((continuous_const.mul (hJc 0 j)).div_const (R x)))
        ((hθc 1 j).div_const (R x)),
      avg_add (hrc 0 j) ((continuous_const.mul (hJc 0 j)).div_const (R x)),
      avg_div, avg_div, avg_const_mul, hr, hz, hθ]
    simp
  fin_cases i
  · have hs := avg_sub (x := x)
      (f := fun p => along (liftDirection Vr) (J 0 0) p + 1 * J 0 0 p / R p.1 +
        along angularDirection (J 1 0) p / R p.1 + along (liftDirection Vz) (J 2 0) p)
      (g := fun p => J 1 1 p / R p.1) (hcorec 0 1) ((hJc 1 1).div_const (R x))
    rw [hcore, avg_div] at hs
    simp only [conservativeFlux, meanConservativeFlux, liftScalar, one_mul] at hs ⊢
    exact hs
  · exact hcore 1 2
  · have h := hcore 2 1
    simp only [one_mul] at h
    exact h

noncomputable def meanScalarLaplacian (R : D → ℝ) (Vr Vz : D → D) (f : D → ℝ) (x : D) : ℝ :=
  along Vr (along Vr f) x + (R x)⁻¹ * along Vr f x + along Vz (along Vz f) x

theorem avg_scalarLaplacian {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) {f : D × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) (hp : PeriodicOn U f)
    {x : D} (hx : x ∈ U) :
    avg (cylindricalLaplacian (liftScalar R) (liftDirection Vr) angularDirection (liftDirection Vz)
      f) x =
      meanScalarLaplacian R Vr Vz (avg f) x := by
  have hVr := liftDirection_smooth G.radial_smooth
  have hVz := liftDirection_smooth G.axial_smooth
  have hr := contDiffOn_along (cylinder_open G.isOpen) hVr hf
  have hz := contDiffOn_along (cylinder_open G.isOpen) hVz hf
  have hθ : ContDiffOn ℝ ∞ (along angularDirection f) (cylinder U) :=
    contDiffOn_along (cylinder_open G.isOpen) contDiffOn_const hf
  have hrc := continuous_slice G.isOpen hr.continuousOn hx
  have hrrc := continuous_slice G.isOpen
    (contDiffOn_along (cylinder_open G.isOpen) hVr hr).continuousOn hx
  have hzzc := continuous_slice G.isOpen
    (contDiffOn_along (cylinder_open G.isOpen) hVz hz).continuousOn hx
  have hθθc : Continuous (fun θ => along angularDirection (along angularDirection f) (x, θ)) :=
    continuous_slice G.isOpen
      (contDiffOn_along (cylinder_open G.isOpen) contDiffOn_const hθ).continuousOn hx
  change avg (fun p => along (liftDirection Vr) (along (liftDirection Vr) f) p +
    (R p.1)⁻¹ * along (liftDirection Vr) f p + (R p.1 ^ 2)⁻¹ *
      along angularDirection (along angularDirection f) p +
      along (liftDirection Vz) (along (liftDirection Vz) f) p) x = _
  rw [avg_add ((hrrc.add (constant_mul_continuous ((R x)⁻¹) hrc)).add
      (constant_mul_continuous ((R x ^ 2)⁻¹) hθθc)) hzzc,
    avg_add (hrrc.add (constant_mul_continuous ((R x)⁻¹) hrc))
      (constant_mul_continuous ((R x ^ 2)⁻¹) hθθc),
    avg_add hrrc (constant_mul_continuous ((R x)⁻¹) hrc),
    avg_mul_left (fun y => (R y)⁻¹) _ x, avg_mul_left (fun y => (R y ^ 2)⁻¹) _ x,
    avg_along_twice G.isOpen hf G.radial_smooth hx,
    avg_along_twice G.isOpen hf G.axial_smooth hx, avg_theta_twice_zero G.isOpen hf hp hx,
    ← along_avg G.isOpen hf Vr hx]
  simp [meanScalarLaplacian]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_neg (f : D × ℝ → ℝ) (x : D) : avg (fun p => -f p) x = -avg f x := by
  simp only [avg, intervalIntegral.integral_neg, neg_div]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_zero (x : D) : avg (fun _ : D × ℝ => 0) x = 0 := by simp [avg]

theorem Regular.scalarLaplacian_smooth {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) {f : D × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cylinder U)) :
    ContDiffOn ℝ ∞
      (cylindricalLaplacian (liftScalar R) (liftDirection Vr) angularDirection (liftDirection Vz) f)
      (cylinder U) := by
  have hu := cylinder_open G.isOpen
  have hVr := liftDirection_smooth G.radial_smooth
  have hVz := liftDirection_smooth G.axial_smooth
  have hr := contDiffOn_along hu hVr hf
  have hz := contDiffOn_along hu hVz hf
  have hθ : ContDiffOn ℝ ∞ (along angularDirection f) (cylinder U) :=
    contDiffOn_along hu contDiffOn_const hf
  have hR := liftScalar_smooth G.radius_smooth
  have hRne : ∀ p ∈ cylinder U, liftScalar R p ≠ 0 := fun p hp => G.radius_ne p.1 hp.1
  exact (((contDiffOn_along hu hVr hr).add ((hR.inv hRne).smul hr)).add
    (((hR.pow 2).inv (fun p hp => pow_ne_zero 2 (hRne p hp))).smul
      (contDiffOn_along hu contDiffOn_const hθ))).add (contDiffOn_along hu hVz hz)

theorem Regular.frameLaplacian_smooth {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) {a : D × ℝ → Fin 3 → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun p => a p i) (cylinder U)) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p => LinearWaveResidual.realFrameLaplacian (liftScalar R)
      (liftDirection Vr) angularDirection (liftDirection Vz) a p i) (cylinder U) := by
  have hθ (j : Fin 3) : ContDiffOn ℝ ∞ (along angularDirection (fun p => a p j)) (cylinder U) :=
    contDiffOn_along (cylinder_open G.isOpen) contDiffOn_const (ha j)
  have hj : ∀ j, ContDiffOn ℝ ∞ (fun p => LinearWaveResidual.realAngularGenerator
      (fun k => along angularDirection (fun y => a y k) p) j) (cylinder U) := by
    intro j
    fin_cases j
    · exact (hθ 1).neg
    · exact hθ 0
    · exact contDiffOn_const
  have hjj : ∀ j, ContDiffOn ℝ ∞ (fun p => LinearWaveResidual.realAngularGenerator
      (LinearWaveResidual.realAngularGenerator (a p)) j) (cylinder U) := by
    intro j
    fin_cases j
    · exact (ha 0).neg
    · exact (ha 1).neg
    · exact contDiffOn_const
  have hr := ((liftScalar_smooth G.radius_smooth).pow 2).inv
    (fun p hp => pow_ne_zero 2 (G.radius_ne p.1 hp.1))
  exact (G.scalarLaplacian_smooth (ha i)).add
    (hr.mul (((hj i).const_smul (2 : ℝ)).add (hjj i)))

noncomputable def meanFrameLaplacian (R : D → ℝ) (Vr Vz : D → D)
    (a : D → Fin 3 → ℝ) (x : D) (i : Fin 3) : ℝ :=
  meanScalarLaplacian R Vr Vz (fun y => a y i) x + (R x ^ 2)⁻¹ *
    LinearWaveResidual.realAngularGenerator (LinearWaveResidual.realAngularGenerator (a x)) i

theorem avg_frameLaplacian {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) {a : D × ℝ → Fin 3 → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun p => a p i) (cylinder U))
    (hp : ∀ i, PeriodicOn U (fun p => a p i)) {x : D} (hx : x ∈ U) (i : Fin 3) :
    avg (fun p => LinearWaveResidual.realFrameLaplacian (liftScalar R)
      (liftDirection Vr) angularDirection (liftDirection Vz) a p i) x =
      meanFrameLaplacian R Vr Vz (fun y j => avg (fun p => a p j) y) x i := by
  have hL j := continuous_slice G.isOpen (G.scalarLaplacian_smooth (ha j)).continuousOn hx
  have hθc j : Continuous (fun θ => along angularDirection (fun p => a p j) (x, θ)) :=
    continuous_slice G.isOpen
      (contDiffOn_along (cylinder_open G.isOpen) contDiffOn_const (ha j)).continuousOn hx
  have hac j := continuous_slice G.isOpen (ha j).continuousOn hx
  have hθ j := avg_theta_zero G.isOpen (ha j) (hp j) hx
  have hLap j := avg_scalarLaplacian G (ha j) (hp j) hx
  fin_cases i
  · change avg (fun p => cylindricalLaplacian (liftScalar R) (liftDirection Vr) angularDirection
      (liftDirection Vz) (fun y => a y 0) p + (R p.1 ^ 2)⁻¹ *
        (2 * (-along angularDirection (fun y => a y 1) p) + -a p 0)) x = _
    rw [avg_add (hL 0) (constant_mul_continuous ((R x ^ 2)⁻¹)
      ((constant_mul_continuous 2 (hθc 1).neg).add (hac 0).neg)),
      avg_mul_left (fun y => (R y ^ 2)⁻¹) _ x,
      avg_add (constant_mul_continuous 2 (hθc 1).neg) (hac 0).neg,
      avg_const_mul, avg_neg, avg_neg, hθ, hLap]
    simp [meanFrameLaplacian, LinearWaveResidual.realAngularGenerator]
  · change avg (fun p => cylindricalLaplacian (liftScalar R) (liftDirection Vr) angularDirection
      (liftDirection Vz) (fun y => a y 1) p + (R p.1 ^ 2)⁻¹ *
        (2 * along angularDirection (fun y => a y 0) p + -a p 1)) x = _
    rw [avg_add (hL 1) (constant_mul_continuous ((R x ^ 2)⁻¹)
      ((constant_mul_continuous 2 (hθc 0)).add (hac 1).neg)),
      avg_mul_left (fun y => (R y ^ 2)⁻¹) _ x,
      avg_add (constant_mul_continuous 2 (hθc 0)) (hac 1).neg,
      avg_const_mul, avg_neg, hθ, hLap]
    simp [meanFrameLaplacian, LinearWaveResidual.realAngularGenerator]
  · simpa [LinearWaveResidual.realFrameLaplacian, meanFrameLaplacian,
      LinearWaveResidual.realAngularGenerator] using hLap 2

theorem Regular.conservativeFlux_smooth {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) {J : Fin 3 → Fin 3 → D × ℝ → ℝ}
    (hJ : ∀ i j, ContDiffOn ℝ ∞ (J i j) (cylinder U)) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p => conservativeFlux (liftScalar R) (liftDirection Vr)
      angularDirection (liftDirection Vz) J p i) (cylinder U) := by
  have hr j k := contDiffOn_along (cylinder_open G.isOpen) (liftDirection_smooth G.radial_smooth)
    (hJ j k)
  have hz j k := contDiffOn_along (cylinder_open G.isOpen) (liftDirection_smooth G.axial_smooth)
    (hJ j k)
  have hθ j k : ContDiffOn ℝ ∞ (along angularDirection (J j k)) (cylinder U) :=
    contDiffOn_along (cylinder_open G.isOpen) contDiffOn_const (hJ j k)
  have hR := liftScalar_smooth G.radius_smooth
  have hn : ∀ p ∈ cylinder U, liftScalar R p ≠ 0 := fun p hp => G.radius_ne p.1 hp.1
  fin_cases i
  · exact ((((hr 0 0).add ((hJ 0 0).div hR hn)).add ((hθ 1 0).div hR hn)).add
      (hz 2 0)).sub ((hJ 1 1).div hR hn)
  · exact (((hr 0 1).add (((hJ 0 1).const_smul (2 : ℝ)).div hR hn)).add
      ((hθ 1 1).div hR hn)).add (hz 2 1)
  · exact (((hr 0 2).add ((hJ 0 2).div hR hn)).add ((hθ 1 2).div hR hn)).add (hz 2 2)

noncomputable def realGradient (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    (p : D × ℝ → ℝ) (x : D × ℝ) : Fin 3 → ℝ :=
  ![along Vr p x, (R x)⁻¹ * along Vθ p x, along Vz p x]

noncomputable def meanGradient (Vr Vz : D → D) (p : D → ℝ) (x : D) : Fin 3 → ℝ :=
  ![along Vr p x, 0, along Vz p x]

theorem Regular.gradient_smooth {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) {p : D × ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ p (cylinder U)) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => realGradient (liftScalar R) (liftDirection Vr)
      angularDirection (liftDirection Vz) p x i) (cylinder U) := by
  fin_cases i
  · exact contDiffOn_along (cylinder_open G.isOpen) (liftDirection_smooth G.radial_smooth) hp
  · exact ((liftScalar_smooth G.radius_smooth).inv
      (fun x hx => G.radius_ne x.1 hx.1)).mul
        (contDiffOn_along (cylinder_open G.isOpen) contDiffOn_const hp)
  · exact contDiffOn_along (cylinder_open G.isOpen) (liftDirection_smooth G.axial_smooth) hp

theorem avg_gradient {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) {p : D × ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ p (cylinder U)) (hper : PeriodicOn U p)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    avg (fun y => realGradient (liftScalar R) (liftDirection Vr) angularDirection
      (liftDirection Vz) p y i) x = meanGradient Vr Vz (avg p) x i := by
  fin_cases i
  · exact (along_avg G.isOpen hp Vr hx).symm
  · change avg (fun y => (R y.1)⁻¹ * along angularDirection p y) x = 0
    rw [avg_mul_left (fun y => (R y)⁻¹) _ x, avg_theta_zero G.isOpen hp hper hx, mul_zero]
  · exact (along_avg G.isOpen hp Vz hx).symm

noncomputable def realNonlinearResidual (ε : ℝ) (R : D × ℝ → ℝ)
    (Vr Vθ Vz Vt : D × ℝ → D × ℝ) (B a : D × ℝ → Fin 3 → ℝ)
    (p : D × ℝ → ℝ) (x : D × ℝ) : Fin 3 → ℝ :=
  LinearWaveResidual.realComponentLinearResidual ε R Vr Vθ Vz Vt B a p x +
    LinearWaveResidual.realTransport R Vr Vθ Vz a a x

theorem nonlinearResidual_realLift {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) (ε : ℝ) {B a : D × ℝ → Fin 3 → ℝ} {p : D × ℝ → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) (cylinder U))
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) (cylinder U))
    (hp : ContDiffOn ℝ ∞ p (cylinder U)) {x : D × ℝ} (hx : x ∈ cylinder U) (i : Fin 3) :
    (nonlinearResidual ε (liftScalar R) (liftDirection Vr) angularDirection (liftDirection Vz)
      (liftDirection Vt) (LinearWaveResidual.realLift B) (LinearWaveResidual.realLift a)
      (fun y => (p y : ℂ)) x i).re =
      realNonlinearResidual ε (liftScalar R) (liftDirection Vr) angularDirection (liftDirection Vz)
        (liftDirection Vt) B a p x i := by
  have ho := cylinder_open G.isOpen
  have haC j : ContDiffOn ℝ ∞ (fun y => (a y j : ℂ)) (cylinder U) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (ha j)
  have hpC : ContDiffOn ℝ ∞ (fun y => (p y : ℂ)) (cylinder U) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hp
  have db j := ((hB j).contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)
  have da j := ((ha j).contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)
  have hl := congrFun (LinearWaveResidual.realMap_linearResidual Complex.reCLM ε (liftScalar R)
    (liftDirection Vt) (B := B) (a := LinearWaveResidual.realLift a) (p := fun y => (p y : ℂ))
    (Vθ := angularDirection)
    ho (liftDirection_smooth G.radial_smooth) contDiffOn_const (liftDirection_smooth G.axial_smooth)
    haC db ((hpC.contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)) hx) i
  have ht := WaveInteractionBounds.transport_realLift (liftScalar R) (liftDirection Vr)
    angularDirection (liftDirection Vz) a da i
  simp only [nonlinearResidual, Pi.add_apply, Complex.add_re, ht, Complex.ofReal_re,
    realNonlinearResidual]
  congr 1

theorem realNonlinearResidual_conservative (ε : ℝ) (R : D × ℝ → ℝ)
    (Vr Vθ Vz Vt : D × ℝ → D × ℝ) {B a : D × ℝ → Fin 3 → ℝ} (p : D × ℝ → ℝ)
    {x : D × ℝ} (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hBd : realDivergence R Vr Vθ Vz B x = 0)
    (had : realDivergence R Vr Vθ Vz a x = 0) (i : Fin 3) :
    realNonlinearResidual ε R Vr Vθ Vz Vt B a p x i =
      along Vt (fun y => a y i) x + conservativeFlux R Vr Vθ Vz (quadraticFlux B a) x i +
      realGradient R Vr Vθ Vz p x i - ε * LinearWaveResidual.realFrameLaplacian R Vr Vθ Vz a x i :=
        by
  rw [← congrFun (advectionIncrement_eq_conservative R Vr Vθ Vz hB ha hBd had) i]
  simp only [realNonlinearResidual, LinearWaveResidual.realComponentLinearResidual,
    advectionIncrement, realGradient, Pi.add_apply]
  ring

noncomputable def meanExpression (ε : ℝ) (R : D → ℝ) (Vr Vz Vt : D → D)
    (a : D → Fin 3 → ℝ) (p : D → ℝ) (J : Fin 3 → Fin 3 → D → ℝ)
    (x : D) (i : Fin 3) : ℝ :=
  along Vt (fun y => a y i) x + meanConservativeFlux R Vr Vz J x i +
    meanGradient Vr Vz p x i - ε * meanFrameLaplacian R Vr Vz a x i

/-- Reynolds averaging for the full real lifted nonlinear residual. -/
theorem avg_realNonlinearResidual {U : Set D} {R : D → ℝ} {Vr Vz Vt : D → D}
    (G : Regular U R Vr Vz Vt) (ε : ℝ) {B a : D × ℝ → Fin 3 → ℝ} {p : D × ℝ → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) (cylinder U))
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) (cylinder U))
    (hp : ContDiffOn ℝ ∞ p (cylinder U))
    (hBper : ∀ i, PeriodicOn U (fun y => B y i))
    (haper : ∀ i, PeriodicOn U (fun y => a y i)) (hpper : PeriodicOn U p)
    (hBd : ∀ y ∈ cylinder U, realDivergence (liftScalar R) (liftDirection Vr)
      angularDirection (liftDirection Vz) B y = 0)
    (had : ∀ y ∈ cylinder U, realDivergence (liftScalar R) (liftDirection Vr)
      angularDirection (liftDirection Vz) a y = 0)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    avg (fun y => realNonlinearResidual ε (liftScalar R) (liftDirection Vr) angularDirection
      (liftDirection Vz) (liftDirection Vt) B a p y i) x =
      meanExpression ε R Vr Vz Vt (fun y j => avg (fun p => a p j) y) (avg p)
        (fun j k => avg (quadraticFlux B a j k)) x i := by
  have hu := cylinder_open G.isOpen
  have hJ j k := quadraticFlux_smooth hB ha j k
  have hJper j k := quadraticFlux_periodic hBper haper j k
  have hc := continuous_slice G.isOpen (G.conservativeFlux_smooth hJ i).continuousOn hx
  have ht := continuous_slice G.isOpen
    (contDiffOn_along hu (liftDirection_smooth G.time_smooth) (ha i)).continuousOn hx
  have hg := continuous_slice G.isOpen (G.gradient_smooth hp i).continuousOn hx
  have hl := continuous_slice G.isOpen (G.frameLaplacian_smooth ha i).continuousOn hx
  have he : EqOn (fun y => realNonlinearResidual ε (liftScalar R) (liftDirection Vr)
    angularDirection
      (liftDirection Vz) (liftDirection Vt) B a p y i)
      (fun y => along (liftDirection Vt) (fun z => a z i) y +
        conservativeFlux (liftScalar R) (liftDirection Vr) angularDirection (liftDirection Vz)
          (quadraticFlux B a) y i +
        realGradient (liftScalar R) (liftDirection Vr) angularDirection (liftDirection Vz) p y i -
        ε * LinearWaveResidual.realFrameLaplacian (liftScalar R) (liftDirection Vr)
          angularDirection (liftDirection Vz) a y i) (cylinder U) := by
    intro y hy
    exact realNonlinearResidual_conservative ε _ _ _ _ _ p
      (fun j => ((hB j).contDiffAt (hu.mem_nhds hy)).differentiableAt (by simp))
      (fun j => ((ha j).contDiffAt (hu.mem_nhds hy)).differentiableAt (by simp))
      (hBd y hy) (had y hy) i
  rw [avg_congr he hx, avg_sub ((ht.add hc).add hg) (constant_mul_continuous ε hl),
    avg_add (ht.add hc) hg, avg_add ht hc, avg_const_mul,
    avg_conservativeFlux G hJ hJper hx, avg_gradient G hp hpper hx,
    avg_frameLaplacian G ha haper hx, ← along_avg G.isOpen (ha i) Vt hx]
  rfl

theorem dr_eq_along (o : MeanIncrementBounds.Operators D) (f : MeanIncrementBounds.Field D)
    (n : ℕ) (x : D) : o.dr f n x = along (radialVector o n) (f n) x := by
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    radialVector, along, map_add, map_smul, smul_eq_mul]
  ring

theorem dz_eq_along (o : MeanIncrementBounds.Operators D) (f : MeanIncrementBounds.Field D)
    (n : ℕ) (x : D) : o.dz f n x = along (axialVector o n) (f n) x := by
  simp only [MeanIncrementBounds.Operators.dz, axialVector, along, map_smul, smul_eq_mul]

theorem time_eq_along (o : MeanIncrementBounds.Operators D) (f : MeanIncrementBounds.Field D)
    (n : ℕ) (x : D) : o.time f n x = along (temporalVector o n) (f n) x := by
  simp only [MeanIncrementBounds.Operators.time, MeanIncrementBounds.Operators.fastTime,
    MeanIncrementBounds.Operators.slowTime, temporalVector, along, map_sub, map_smul,
    Pi.add_apply, smul_eq_mul]
  ring

theorem radialDiv_eq (o : MeanIncrementBounds.Operators D) (c : ℝ)
    (f : MeanIncrementBounds.Field D) (n : ℕ) (x : D) :
    o.radialDiv c f n x = along (radialVector o n) (f n) x + c * f n x / o.radius x := by
  simp only [MeanIncrementBounds.Operators.radialDiv, dr_eq_along, Pi.add_apply,
    Pi.smul_apply, Pi.mul_apply, MeanIncrementBounds.Operators.invRadius, smul_eq_mul]
  ring

theorem viscosity_eq (o : MeanIncrementBounds.Operators D) (c : ℝ)
    (f : MeanIncrementBounds.Field D) (n : ℕ) (x : D) :
    o.viscosity c f n x = o.epsilon n *
      (meanScalarLaplacian o.radius (radialVector o n) (axialVector o n) (f n) x -
        c * (o.radius x ^ 2)⁻¹ * f n x) := by
  have hr : (fun y => o.dr f n y) = along (radialVector o n) (f n) := funext (dr_eq_along o f n)
  have hz : (fun y => o.dz f n y) = along (axialVector o n) (f n) := funext (dz_eq_along o f n)
  simp only [MeanIncrementBounds.Operators.viscosity, dr_eq_along, dz_eq_along,
    MeanIncrementBounds.Operators.invRadius, hr, hz, meanScalarLaplacian]
  ring

noncomputable def tripleVector (m : MeanIncrementBounds.Triple D) (n : ℕ) (x : D) : Fin 3 → ℝ :=
  ![m.radial n x, m.angular n x, m.axial n x]

noncomputable def baseLift (c : CorrectionState.Context D) (n : ℕ) (p : D × ℝ) : Fin 3 → ℝ :=
  tripleVector c.base n p.1

noncomputable def perturbation (u : CorrectionState.State D) (n : ℕ) (p : D × ℝ) : Fin 3 → ℝ :=
  tripleVector u.mean n p.1 + u.oscillation n p

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem complexBase_eq (c : CorrectionState.Context D) (n : ℕ) :
    complexBase c n = LinearWaveResidual.realLift (baseLift c n) := by
  funext p i
  fin_cases i <;> rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem complexPerturbation_eq (u : CorrectionState.State D) (n : ℕ) :
    complexPerturbation u n = LinearWaveResidual.realLift (perturbation u n) := by
  funext p i
  fin_cases i <;> rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem totalVelocity_eq (c : CorrectionState.Context D) (u : CorrectionState.State D) (n : ℕ) :
    u.totalVelocity c n = fun p => baseLift c n p + perturbation u n p := by
  funext p i
  fin_cases i <;> simp [CorrectionState.State.totalVelocity, baseLift, perturbation, tripleVector,
    Matrix.vecHead, Matrix.vecTail] <;> ring

theorem tripleVector_smooth {U : Set D} {m : MeanIncrementBounds.Triple D}
    (hm : MeanIncrementBounds.SmoothTriple U m) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => tripleVector m n x i) U := by
  fin_cases i
  · exact hm.radial n
  · exact hm.angular n
  · exact hm.axial n

/-- Primitive hypotheses on the actual state. The mean-PDE identity is a
conclusion, and is not a field of this structure. -/
structure MeanHypotheses (U : Set D) (c : CorrectionState.Context D) (u : CorrectionState.State D)
  : Prop where
  isOpen : IsOpen U
  radius_smooth : ContDiffOn ℝ ∞ c.operators.radius U
  radius_ne : ∀ x ∈ U, c.operators.radius x ≠ 0
  profile_smooth : ContDiffOn ℝ ∞ c.operators.radialProfile U
  base_smooth : MeanIncrementBounds.SmoothTriple U c.base
  mean_smooth : MeanIncrementBounds.SmoothTriple U u.mean
  pressure_smooth : MeanIncrementBounds.SmoothOn U u.pressure
  oscillation_smooth : ∀ n i, ContDiffOn ℝ ∞ (fun p => u.oscillation n p i) (cylinder U)
  oscillatoryPressure_smooth : ∀ n, ContDiffOn ℝ ∞ (u.oscillatoryPressure n) (cylinder U)
  oscillation_periodic : ∀ n i, PeriodicOn U (fun p => u.oscillation n p i)
  oscillatoryPressure_periodic : ∀ n, PeriodicOn U (u.oscillatoryPressure n)
  oscillation_mean_zero : ∀ n x, x ∈ U → ∀ i,
    CorrectionState.angularAverage (fun k p => u.oscillation k p i) n x = 0
  oscillatoryPressure_mean_zero : ∀ n x, x ∈ U → CorrectionState.angularAverage
    u.oscillatoryPressure n x = 0
  base_divergence : ∀ n p, p ∈ cylinder U → realDivergence
    (liftScalar c.operators.radius) (radialDirection c n) angularDirection (axialDirection c n)
      (baseLift c n) p = 0
  total_divergence : ∀ n p, p ∈ cylinder U → realDivergence
    (liftScalar c.operators.radius) (radialDirection c n) angularDirection (axialDirection c n)
      (u.totalVelocity c n) p = 0
  base_error_continuous : ∀ n x, x ∈ U → ∀ i, Continuous (fun θ : ℝ => u.errors.base n (x, θ) i)
  excluded_continuous : ∀ n x, x ∈ U → ∀ i, Continuous (fun θ : ℝ => u.errors.total n (x, θ) i)

theorem MeanHypotheses.regular {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) :
    Regular U c.operators.radius (radialVector c.operators n) (axialVector c.operators n)
      (temporalVector c.operators n) where
  isOpen := H.isOpen
  radius_smooth := H.radius_smooth
  radius_ne := H.radius_ne
  radial_smooth := contDiffOn_const.add
    ((H.profile_smooth.const_smul (c.operators.radialFrequency n)).smul contDiffOn_const)
  axial_smooth := contDiffOn_const
  time_smooth := contDiffOn_const

theorem MeanHypotheses.baseLift_smooth {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p => baseLift c n p i) (cylinder U) :=
  liftScalar_smooth (tripleVector_smooth H.base_smooth n i)

theorem MeanHypotheses.perturbation_smooth {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p => perturbation u n p i) (cylinder U) :=
  (liftScalar_smooth (tripleVector_smooth H.mean_smooth n i)).add (H.oscillation_smooth n i)

theorem MeanHypotheses.pressureIncrement_smooth {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) :
    ContDiffOn ℝ ∞ (u.totalPressureIncrement n) (cylinder U) :=
  (liftScalar_smooth (H.pressure_smooth n)).add (H.oscillatoryPressure_smooth n)

theorem realDivergence_add (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    {a b : D × ℝ → Fin 3 → ℝ} {p : D × ℝ}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) p)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) p) :
    realDivergence R Vr Vθ Vz (fun y => a y + b y) p =
      realDivergence R Vr Vθ Vz a p + realDivergence R Vr Vθ Vz b p := by
  simp only [realDivergence, Pi.add_apply, along_add _ (ha 0) (hb 0),
    along_add _ (ha 1) (hb 1), along_add _ (ha 2) (hb 2)]
  ring

theorem MeanHypotheses.perturbation_divergence {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {p : D × ℝ} (hp : p ∈ cylinder U) :
    realDivergence (liftScalar c.operators.radius) (radialDirection c n) angularDirection
      (axialDirection c n) (perturbation u n) p = 0 := by
  have hd := H.total_divergence n p hp
  rw [totalVelocity_eq, realDivergence_add _ _ _ _
    (fun i => ((H.baseLift_smooth n i).contDiffAt ((cylinder_open H.isOpen).mem_nhds
      hp)).differentiableAt (by simp))
    (fun i => ((H.perturbation_smooth n i).contDiffAt ((cylinder_open H.isOpen).mem_nhds
      hp)).differentiableAt (by simp)),
    H.base_divergence n p hp, zero_add] at hd
  exact hd

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem periodic_lift (U : Set D) (f : D → ℝ) : PeriodicOn U (liftScalar f) :=
  fun _ _ _ => rfl

theorem MeanHypotheses.baseLift_periodic {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (_H : MeanHypotheses U c u) (n : ℕ) (i : Fin 3) : PeriodicOn U (fun p => baseLift c n p i) :=
  periodic_lift U (fun x => tripleVector c.base n x i)

theorem MeanHypotheses.perturbation_periodic {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) (i : Fin 3) : PeriodicOn U (fun p => perturbation u n p i) :=
  (periodic_lift U (fun x => tripleVector u.mean n x i)).add (H.oscillation_periodic n i)

theorem MeanHypotheses.pressureIncrement_periodic {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) : PeriodicOn U (u.totalPressureIncrement n) :=
  (periodic_lift U (u.pressure n)).add (H.oscillatoryPressure_periodic n)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_affine (a : D → ℝ) {f : D × ℝ → ℝ} {x : D}
    (hf : Continuous (fun θ : ℝ => f (x, θ))) (hz : avg f x = 0) :
    avg (fun p => a p.1 + f p) x = a x := by
  rw [avg_add (continuous_const : Continuous (fun _ : ℝ => a x)) hf,
    show (fun p : D × ℝ => a p.1) = liftScalar a from rfl,
    avg_lift, hz, add_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem avg_affine_product (a b : D → ℝ) {f g : D × ℝ → ℝ} {x : D}
    (hf : Continuous (fun θ : ℝ => f (x, θ))) (hg : Continuous (fun θ : ℝ => g (x, θ)))
    (hf0 : avg f x = 0) (hg0 : avg g x = 0) :
    avg (fun p => (a p.1 + f p) * (b p.1 + g p)) x = a x * b x + avg (fun p => f p * g p) x := by
  have he : (fun p : D × ℝ => (a p.1 + f p) * (b p.1 + g p)) =
      (fun p => a p.1 * b p.1 + a p.1 * g p + b p.1 * f p + f p * g p) := by
    funext p
    ring
  have hab : Continuous (fun _ : ℝ => a x * b x) := continuous_const
  have habavg : avg (fun p : D × ℝ => a p.1 * b p.1) x = a x * b x :=
    congrFun (avg_lift (fun y => a y * b y)) x
  rw [he, avg_add ((hab.add (constant_mul_continuous (a x) hg)).add
      (constant_mul_continuous (b x) hf)) (hf.mul hg),
    avg_add (hab.add (constant_mul_continuous (a x) hg)) (constant_mul_continuous (b x) hf),
    avg_add hab (constant_mul_continuous (a x) hg),
    habavg,
    avg_mul_left a g x, avg_mul_left b f x, hf0, hg0]
  ring

theorem MeanHypotheses.avg_perturbation {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) (i : Fin 3) :
    avg (fun p => perturbation u n p i) x = tripleVector u.mean n x i := by
  exact avg_affine (fun y => tripleVector u.mean n y i) (f := fun p => u.oscillation n p i)
    (x := x) (continuous_slice H.isOpen (H.oscillation_smooth n i).continuousOn hx)
    (H.oscillation_mean_zero n x hx i)

theorem MeanHypotheses.avg_pressureIncrement {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) :
    avg (u.totalPressureIncrement n) x = u.pressure n x := by
  exact avg_affine (u.pressure n) (f := u.oscillatoryPressure n) (x := x)
    (continuous_slice H.isOpen (H.oscillatoryPressure_smooth n).continuousOn hx)
    (H.oscillatoryPressure_mean_zero n x hx)

noncomputable def stateFlux (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (i j : Fin 3) (n : ℕ) (x : D) : ℝ :=
  tripleVector c.base n x i * tripleVector u.mean n x j +
    tripleVector u.mean n x i * tripleVector c.base n x j +
    tripleVector u.mean n x i * tripleVector u.mean n x j + u.covariance i j n x

theorem MeanHypotheses.avg_quadraticFlux {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) (i j : Fin 3) :
    avg (quadraticFlux (baseLift c n) (perturbation u n) i j) x = stateFlux c u i j n x := by
  have hac k := continuous_slice H.isOpen (H.perturbation_smooth n k).continuousOn hx
  have hoc k := continuous_slice H.isOpen (H.oscillation_smooth n k).continuousOn hx
  have hprod : avg (fun p => perturbation u n p i * perturbation u n p j) x =
      tripleVector u.mean n x i * tripleVector u.mean n x j + u.covariance i j n x :=
    avg_affine_product (fun y => tripleVector u.mean n y i) (fun y => tripleVector u.mean n y j)
      (f := fun p => u.oscillation n p i) (g := fun p => u.oscillation n p j) (x := x) (hoc i) (hoc
        j)
      (H.oscillation_mean_zero n x hx i) (H.oscillation_mean_zero n x hx j)
  change avg (fun p => tripleVector c.base n p.1 i * perturbation u n p j +
      perturbation u n p i * tripleVector c.base n p.1 j +
      perturbation u n p i * perturbation u n p j) x = _
  rw [avg_add ((constant_mul_continuous (tripleVector c.base n x i) (hac j)).add
      ((hac i).mul (continuous_const : Continuous (fun _ : ℝ => tripleVector c.base n x j))))
      ((hac i).mul (hac j)),
    avg_add (constant_mul_continuous (tripleVector c.base n x i) (hac j))
      ((hac i).mul (continuous_const : Continuous (fun _ : ℝ => tripleVector c.base n x j))),
    avg_mul_left (fun y => tripleVector c.base n y i) _ x,
    avg_mul_right _ (fun y => tripleVector c.base n y j) x,
    H.avg_perturbation n hx i, H.avg_perturbation n hx j, hprod]
  simp only [stateFlux]
  ring

theorem MeanHypotheses.covariance_smooth {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (i j : Fin 3) : MeanIncrementBounds.SmoothOn U (u.covariance i j) :=
      by
  intro n
  exact avg_smooth H.isOpen ((H.oscillation_smooth n i).mul (H.oscillation_smooth n j))

theorem MeanHypotheses.stateFlux_smooth {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (i j : Fin 3) : MeanIncrementBounds.SmoothOn U (stateFlux c u i j)
      := by
  intro n
  have hb k := tripleVector_smooth H.base_smooth n k
  have hm k := tripleVector_smooth H.mean_smooth n k
  exact ((((hb i).mul (hm j)).add ((hm i).mul (hb j))).add ((hm i).mul (hm j))).add
    (H.covariance_smooth i j n)

theorem meanExpression_congr {U : Set D} (hU : IsOpen U) (ε : ℝ) (R : D → ℝ)
    (Vr Vz Vt : D → D) {a b : D → Fin 3 → ℝ} {p q : D → ℝ}
    {J K : Fin 3 → Fin 3 → D → ℝ}
    (hab : ∀ i, EqOn (fun x => a x i) (fun x => b x i) U)
    (hpq : EqOn p q U) (hJK : ∀ i j, EqOn (J i j) (K i j) U)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    meanExpression ε R Vr Vz Vt a p J x i = meanExpression ε R Vr Vz Vt b q K x i := by
  have hd (V : D → D) (j : Fin 3) := along_congr hU (hab j) hx (V := V)
  have hdd (V : D → D) (j : Fin 3) :
      along V (along V (fun y => a y j)) x = along V (along V (fun y => b y j)) x :=
    along_congr hU (fun y hy => along_congr hU (hab j) hy) hx
  have hj (V : D → D) (j k : Fin 3) := along_congr hU (hJK j k) hx (V := V)
  have hp (V : D → D) := along_congr hU hpq hx (V := V)
  have hv (j : Fin 3) := hab j hx
  have hjv (j k : Fin 3) := hJK j k hx
  fin_cases i <;>
    simp [meanExpression, meanConservativeFlux, meanGradient, meanFrameLaplacian,
      meanScalarLaplacian, LinearWaveResidual.realAngularGenerator, hd, hdd, hj, hp, hv, hjv]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem stateFlux_00 (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    stateFlux c u 0 0 = MeanIncrementBounds.radialRadial c.base u.mean + u.covariance 0 0 := by
  funext n x
  simp [stateFlux, tripleVector, MeanIncrementBounds.radialRadial]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem stateFlux_01 (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    stateFlux c u 0 1 = MeanIncrementBounds.thetaRadial c.base u.mean + u.covariance 0 1 := by
  funext n x
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem stateFlux_02 (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    stateFlux c u 0 2 = MeanIncrementBounds.axialRadial c.base u.mean + u.covariance 0 2 := by
  funext n x
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem stateFlux_11 (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    stateFlux c u 1 1 = MeanIncrementBounds.radialAngular c.base u.mean + u.covariance 1 1 := by
  funext n x
  simp [stateFlux, tripleVector, MeanIncrementBounds.radialAngular]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem stateFlux_20 (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    stateFlux c u 2 0 = MeanIncrementBounds.axialRadial c.base u.mean + u.covariance 2 0 := by
  funext n x
  simp [stateFlux, tripleVector, MeanIncrementBounds.axialRadial]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem stateFlux_21 (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    stateFlux c u 2 1 = MeanIncrementBounds.thetaAxial c.base u.mean + u.covariance 2 1 := by
  funext n x
  simp [stateFlux, tripleVector, MeanIncrementBounds.thetaAxial]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem stateFlux_22 (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    stateFlux c u 2 2 = MeanIncrementBounds.axialAxial c.base u.mean + u.covariance 2 2 := by
  funext n x
  simp [stateFlux, tripleVector, MeanIncrementBounds.axialAxial]
  ring

theorem meanExpression_state {U : Set D} {c : CorrectionState.Context D} {u : CorrectionState.State
  D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) (i : Fin 3) :
    meanExpression (c.operators.epsilon n) c.operators.radius (radialVector c.operators n)
      (axialVector c.operators n) (temporalVector c.operators n) (tripleVector u.mean n)
      (u.pressure n) (fun j k => stateFlux c u j k n) x i + virtualDivergence c n (x, 0) i =
        u.reducedMeanResidual c n x i := by
  have hz := c.operators.dz_add H.isOpen (H.stateFlux_smooth 2 2) H.pressure_smooth n hx
  have h11 := congrFun (congrFun (stateFlux_11 c u) n) x
  simp only [Pi.add_apply] at h11
  fin_cases i
  · simp [CorrectionState.State.reducedMeanResidual, CorrectionState.State.radialResidual,
      CorrectionState.State.gr, MeanIncrementBounds.gr, Matrix.cons_val_zero, Pi.sub_apply,
        Pi.add_apply, Pi.mul_apply]
    rw [← stateFlux_00, ← stateFlux_20, ← h11]
    simp [time_eq_along, radialDiv_eq, dz_eq_along, viscosity_eq, dr_eq_along,
      meanExpression, meanConservativeFlux, meanGradient, meanFrameLaplacian, tripleVector,
      virtualDivergence, LinearWaveResidual.realAngularGenerator,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      MeanIncrementBounds.Operators.invRadius]
    ring

  · simp [CorrectionState.State.reducedMeanResidual, CorrectionState.State.thetaResidual,
      MeanIncrementBounds.thetaResidual, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply,
        Pi.add_apply]
    rw [← stateFlux_01, ← stateFlux_21]
    simp [time_eq_along, radialDiv_eq, dz_eq_along, viscosity_eq,
      meanExpression, meanConservativeFlux, meanGradient, meanFrameLaplacian, tripleVector,
      virtualDivergence, LinearWaveResidual.realAngularGenerator,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp [CorrectionState.State.reducedMeanResidual, CorrectionState.State.axialResidual,
      MeanIncrementBounds.axialResidual, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.sub_apply, Pi.add_apply]
    rw [← stateFlux_02, ← stateFlux_22, hz]
    simp [time_eq_along, radialDiv_eq, dz_eq_along, viscosity_eq,
      meanExpression, meanConservativeFlux, meanGradient, meanFrameLaplacian, tripleVector,
      virtualDivergence, LinearWaveResidual.realAngularGenerator,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons,
      zero_mul, mul_zero, sub_zero, add_zero]
    ring

noncomputable def nonlinearField (c : CorrectionState.Context D) (u : CorrectionState.State D) :
    CorrectionState.Oscillation D := fun n p i =>
  (nonlinearResidual (c.operators.epsilon n) (liftScalar c.operators.radius)
    (radialDirection c n) angularDirection (axialDirection c n) (timeDirection c n)
    (complexBase c n) (complexPerturbation u n) (complexPressure u n) p i).re

theorem MeanHypotheses.nonlinearField_eq_real {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {p : D × ℝ} (hp : p ∈ cylinder U) (i : Fin 3) :
    nonlinearField c u n p i =
      realNonlinearResidual (c.operators.epsilon n) (liftScalar c.operators.radius)
        (radialDirection c n) angularDirection (axialDirection c n) (timeDirection c n)
        (baseLift c n) (perturbation u n) (u.totalPressureIncrement n) p i := by
  unfold nonlinearField
  rw [complexBase_eq, complexPerturbation_eq]
  exact nonlinearResidual_realLift (H.regular n) _ (H.baseLift_smooth n)
    (H.perturbation_smooth n) (H.pressureIncrement_smooth n) hp i

theorem MeanHypotheses.nonlinearField_continuous {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) (i : Fin 3) :
    Continuous (fun θ : ℝ => nonlinearField c u n (x, θ) i) := by
  let G := H.regular n
  have hJ := quadraticFlux_smooth (H.baseLift_smooth n) (H.perturbation_smooth n)
  have hc := continuous_slice H.isOpen (G.conservativeFlux_smooth hJ i).continuousOn hx
  have ht := continuous_slice H.isOpen
    (contDiffOn_along (cylinder_open H.isOpen) (liftDirection_smooth G.time_smooth)
      (H.perturbation_smooth n i)).continuousOn hx
  have hg := continuous_slice H.isOpen (G.gradient_smooth (H.pressureIncrement_smooth n)
    i).continuousOn hx
  have hl := continuous_slice H.isOpen (G.frameLaplacian_smooth (H.perturbation_smooth n)
    i).continuousOn hx
  have he : (fun θ : ℝ => nonlinearField c u n (x, θ) i) = fun θ =>
      along (timeDirection c n) (fun y => perturbation u n y i) (x, θ) +
      conservativeFlux (liftScalar c.operators.radius) (radialDirection c n) angularDirection
        (axialDirection c n) (quadraticFlux (baseLift c n) (perturbation u n)) (x, θ) i +
      realGradient (liftScalar c.operators.radius) (radialDirection c n) angularDirection
        (axialDirection c n) (u.totalPressureIncrement n) (x, θ) i -
      c.operators.epsilon n * LinearWaveResidual.realFrameLaplacian (liftScalar c.operators.radius)
        (radialDirection c n) angularDirection (axialDirection c n) (perturbation u n) (x, θ) i :=
          by
    funext θ
    have hp : (x, θ) ∈ cylinder U := ⟨hx, mem_univ θ⟩
    rw [H.nonlinearField_eq_real n hp i]
    exact realNonlinearResidual_conservative _ _ _ _ _ _ _
      (fun j => ((H.baseLift_smooth n j).contDiffAt ((cylinder_open H.isOpen).mem_nhds
        hp)).differentiableAt (by simp))
      (fun j => ((H.perturbation_smooth n j).contDiffAt ((cylinder_open H.isOpen).mem_nhds
        hp)).differentiableAt (by simp))
      (H.base_divergence n (x, θ) hp) (H.perturbation_divergence n hp) i
  rw [he]
  exact ((ht.add hc).add hg).sub (constant_mul_continuous (c.operators.epsilon n) hl)

theorem MeanHypotheses.avg_nonlinearField {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) (i : Fin 3) :
    avg (fun p => nonlinearField c u n p i) x =
      meanExpression (c.operators.epsilon n) c.operators.radius (radialVector c.operators n)
        (axialVector c.operators n) (temporalVector c.operators n) (tripleVector u.mean n)
        (u.pressure n) (fun j k => stateFlux c u j k n) x i := by
  calc
    _ = avg (fun p => realNonlinearResidual (c.operators.epsilon n) (liftScalar c.operators.radius)
        (radialDirection c n) angularDirection (axialDirection c n) (timeDirection c n)
        (baseLift c n) (perturbation u n) (u.totalPressureIncrement n) p i) x :=
      avg_congr (fun p hp => H.nonlinearField_eq_real n hp i) hx
    _ = meanExpression (c.operators.epsilon n) c.operators.radius (radialVector c.operators n)
        (axialVector c.operators n) (temporalVector c.operators n)
        (fun y j => avg (fun p => perturbation u n p j) y) (avg (u.totalPressureIncrement n))
        (fun j k => avg (quadraticFlux (baseLift c n) (perturbation u n) j k)) x i :=
      avg_realNonlinearResidual (H.regular n) _ (H.baseLift_smooth n) (H.perturbation_smooth n)
        (H.pressureIncrement_smooth n) (H.baseLift_periodic n) (H.perturbation_periodic n)
        (H.pressureIncrement_periodic n) (H.base_divergence n)
        (fun p hp => H.perturbation_divergence n hp) hx i
    _ = _ := meanExpression_congr H.isOpen _ _ _ _ _
      (fun j y hy => H.avg_perturbation n hy j)
      (fun y hy => H.avg_pressureIncrement n hy)
      (fun j k y hy => H.avg_quadraticFlux n hy j k) hx i

theorem avg_virtualDivergence (c : CorrectionState.Context D) (n : ℕ) (x : D) (i : Fin 3) :
    avg (fun p => virtualDivergence c n p i) x = virtualDivergence c n (x, 0) i :=
  congrFun (avg_lift (fun y => virtualDivergence c n (y, 0) i)) x

/-- The actual full residual averages to equation (32) plus exactly the
stored base error. -/
theorem angularMean_fullResidual {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) (i : Fin 3) :
    angularMeanVector (fullResidual c u) n x i = u.meanResidual c n x i := by
  have hv : Continuous (fun θ : ℝ => virtualDivergence c n (x, θ) i) := by
    change Continuous (fun _ : ℝ => virtualDivergence c n (x, 0) i)
    exact continuous_const
  change avg (fun p => nonlinearField c u n p i + virtualDivergence c n p i + u.errors.base n p i)
    x = _
  rw [avg_add ((H.nonlinearField_continuous n hx i).add hv) (H.base_error_continuous n x hx i),
    avg_add (H.nonlinearField_continuous n hx i) hv,
    H.avg_nonlinearField n hx i, avg_virtualDivergence, meanExpression_state H n hx i]
  rfl

/-- No Gaussian or alias term is silently discarded: the exact angular mean
of the explicitly subtracted total is removed on both sides. -/
theorem angularMean_fullGoodResidual {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) (i : Fin 3) :
    angularMeanVector (fullGoodResidual c u) n x i = u.meanGoodResidual c n x i := by
  have hv : Continuous (fun θ : ℝ => virtualDivergence c n (x, θ) i) := by
    change Continuous (fun _ : ℝ => virtualDivergence c n (x, 0) i)
    exact continuous_const
  change avg (fun p => nonlinearField c u n p i + virtualDivergence c n p i + u.errors.base n p i -
    u.errors.total n p i) x = _
  rw [avg_sub (((H.nonlinearField_continuous n hx i).add hv).add (H.base_error_continuous n x hx i))
      (H.excluded_continuous n x hx i),
    avg_add ((H.nonlinearField_continuous n hx i).add hv) (H.base_error_continuous n x hx i),
    avg_add (H.nonlinearField_continuous n hx i) hv,
    H.avg_nonlinearField n hx i, avg_virtualDivergence, meanExpression_state H n hx i]
  rfl

theorem meanGoodResidual_errors (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (n : ℕ) (x : D) (i : Fin 3)
    (hb : Continuous (fun θ : ℝ => u.errors.base n (x, θ) i))
    (hg : Continuous (fun θ : ℝ => u.errors.gaussian n (x, θ) i))
    (ha : Continuous (fun θ : ℝ => u.errors.aliasError n (x, θ) i)) :
    u.meanGoodResidual c n x i = u.reducedMeanResidual c n x i -
      CorrectionState.angularAverage (fun k p => u.errors.gaussian k p i) n x -
      CorrectionState.angularAverage (fun k p => u.errors.aliasError k p i) n x := by
  change u.reducedMeanResidual c n x i + avg (fun p => u.errors.base n p i) x -
    avg (fun p => u.errors.base n p i + u.errors.gaussian n p i + u.errors.aliasError n p i) x =
      u.reducedMeanResidual c n x i - avg (fun p => u.errors.gaussian n p i) x -
        avg (fun p => u.errors.aliasError n p i) x
  rw [avg_add (hb.add hg) ha, avg_add hb hg]
  ring

theorem angularMean_fullGoodResidual_errors {U : Set D} {c : CorrectionState.Context D} {u :
  CorrectionState.State D}
    (H : MeanHypotheses U c u) (n : ℕ) {x : D} (hx : x ∈ U) (i : Fin 3)
    (hg : Continuous (fun θ : ℝ => u.errors.gaussian n (x, θ) i))
    (ha : Continuous (fun θ : ℝ => u.errors.aliasError n (x, θ) i)) :
    angularMeanVector (fullGoodResidual c u) n x i = u.reducedMeanResidual c n x i -
      CorrectionState.angularAverage (fun k p => u.errors.gaussian k p i) n x -
      CorrectionState.angularAverage (fun k p => u.errors.aliasError k p i) n x := by
  rw [angularMean_fullGoodResidual H n hx i]
  exact meanGoodResidual_errors c u n x i (H.base_error_continuous n x hx i) hg ha

section CanonicalGraph

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The actual power-graph profile is smooth on every positive radial strip. -/
theorem graphOperators_profile_smooth (r : CorrectionState.ReconstructionData)
    (epsilon fast : ℕ → ℝ) (axial slowTime : S × PressureStream.Plane) (temporal :
      PressureStream.Plane)
    {U : Set (PressureStream.Lift S)} (hpos : ∀ x ∈ U, 0 < x.1) :
    ContDiffOn ℝ ∞
      (CorrectionState.graphOperators r epsilon fast axial slowTime temporal).radialProfile U := by
  change ContDiffOn ℝ ∞ (fun x : PressureStream.Lift S => r.exponent * x.1 ^ (r.exponent - 1)) U
  exact contDiffOn_const.mul (contDiffOn_fst.rpow_const_of_ne (fun x hx => (hpos x hx).ne'))

/-- Direct instantiation by the genuine graph operators used by the state. -/
theorem graphOperators_regular (r : CorrectionState.ReconstructionData)
    (epsilon fast : ℕ → ℝ) (axial slowTime : S × PressureStream.Plane) (temporal :
      PressureStream.Plane)
    {U : Set (PressureStream.Lift S)} (hU : IsOpen U) (hpos : ∀ x ∈ U, 0 < x.1) (n : ℕ) :
    let o := CorrectionState.graphOperators r epsilon fast axial slowTime temporal
    Regular U o.radius (radialVector o n) (axialVector o n) (temporalVector o n) := by
  let o := CorrectionState.graphOperators r epsilon fast axial slowTime temporal
  have hp : ContDiffOn ℝ ∞ o.radialProfile U :=
    graphOperators_profile_smooth r epsilon fast axial slowTime temporal hpos
  refine ⟨hU, contDiffOn_fst, fun x hx => (hpos x hx).ne', ?_, contDiffOn_const, contDiffOn_const⟩
  exact contDiffOn_const.add ((hp.const_smul (o.radialFrequency n)).smul contDiffOn_const)

end CanonicalGraph

end

end NavierStokes.LiftedMeanResidual
