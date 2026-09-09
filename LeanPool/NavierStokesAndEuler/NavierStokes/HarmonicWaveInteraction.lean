/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicMeanInteraction

/-!
# Actual harmonic wave-update interactions

The nonlinear terms are finite convolutions of actual differentiated fields.
All-jet classes are lifted and restricted by proved norm-one linear pullbacks
before applying the full cylindrical divergence cancellation.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.HarmonicWaveInteraction

open Set Filter Function HarmonicCalculus HarmonicFields WeightedClasses WaveInteractionBounds
open HarmonicMeanInteraction
open scoped Topology ContDiff BigOperators ComplexConjugate


variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback strip, bundling `domain`, `isOpen_domain`, `epsilon`, `epsilon_pos` and the
required compatibility proofs. -/
noncomputable def pullbackStrip (s : StripData D) (L : E →L[ℝ] D) : StripData E where
  domain := L ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage L.continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta := fun x => s.delta (L x)
  delta_pos := fun x hx => s.delta_pos (L x) hx
  zeta := fun x => s.zeta (L x)
  zeta_smooth := s.zeta_smooth.comp L.contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg := fun x hx => s.zeta_nonneg (L x) hx

theorem norm_jet_comp_linear {f : D → F} {U : Set D} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (L : E →L[ℝ] D) {x : E} (hx : L x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ m f (L x)‖ * ‖L‖ ^ m := by
  have hpre := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hx
    (i := m) (show (m : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen m hpre hx, iteratedFDerivWithin_of_isOpen m hU hx] at he
  rw [he]
  simpa using (iteratedFDeriv ℝ m f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

theorem class_pullback {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D → F}
    (hf : MemClass s w α f) (L : E →L[ℝ] D) (hL : ‖L‖ ≤ 1) :
    MemClass (pullbackStrip s L) (fun n x => w n (L x)) α (fun n x => f n (L x)) := by
  refine ⟨fun n x hx => hf.weight_nonneg n (L x) hx,
    fun n => (hf.smooth n).comp L.contDiff.contDiffOn (fun _ hx => hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have hc := norm_jet_comp_linear s.isOpen_domain (hf.smooth n) L hx j
  have hpow : ‖L‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg L) hL
  exact (hc.trans (mul_le_of_le_one_right (norm_nonneg _) hpow)).trans (hb n (L x) hx j hj)

/-- Projection, given by `ContinuousLinearMap.fst ℝ D ℝ`. -/
noncomputable def projection : D × ℝ →L[ℝ] D := ContinuousLinearMap.fst ℝ D ℝ
/-- Inclusion, given by `(ContinuousLinearMap.id ℝ D).prod (0 : D →L[ℝ] ℝ)`. -/
noncomputable def inclusion : D →L[ℝ] D × ℝ :=
  (ContinuousLinearMap.id ℝ D).prod (0 : D →L[ℝ] ℝ)

theorem projection_norm : ‖projection (D := D)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.1‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using norm_fst_le x

theorem inclusion_norm : ‖inclusion (D := D)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [inclusion, Prod.norm_def]

/-- Product strip, given by `pullbackStrip s projection`. -/
noncomputable def productStrip (s : StripData D) : StripData (D × ℝ) := pullbackStrip s projection

theorem class_lift {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D → F}
    (hf : MemClass s w α f) :
    MemClass (productStrip s) (fun n p => w n p.1) α (fun n p => f n p.1) :=
  class_pullback hf projection projection_norm

theorem class_slice {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D × ℝ → F}
    (hf : MemClass (productStrip s) (fun n p => w n p.1) α f) :
    MemClass s w α (fun n x => f n (x, 0)) := by
  have hh := class_pullback hf inclusion inclusion_norm
  have he : pullbackStrip (productStrip s) (inclusion (D := D)) = s := by
    cases s
    rfl
  rw [he] at hh
  exact hh

/-- Lifted geometry, bundling `radius`, `radial`, `angular`, `axial` and the required
compatibility proofs. -/
noncomputable def liftedGeometry {s : StripData D} {κ : ℝ} (G : Geometry s κ) :
    Geometry (productStrip s) κ where
  radius := fun n p => G.radius n p.1
  radial := fun n p => (G.radial n p.1, 0)
  angular := fun _ _ => (0, 1)
  axial := fun n p => (G.axial n p.1, 0)
  radius_pos := fun n p hp => G.radius_pos n p.1 hp
  radial_class := (class_lift G.radial_class).map inclusion
  axial_class := (class_lift G.axial_class).map inclusion
  inverse_radius_class := class_lift G.inverse_radius_class

/-- Full phase, given by `b.phase n p.1 + ((b.angularFrequency n : ℝ) / b.frequency n) * p.2`. -/
noncomputable def fullPhase (b : CorrectionState.HarmonicBlock D) (n : ℕ) (p : D × ℝ) : ℝ :=
  b.phase n p.1 + ((b.angularFrequency n : ℝ) / b.frequency n) * p.2

theorem fullPhase_smooth {s : StripData D} (b : CorrectionState.HarmonicBlock D)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (b.phase n) s.domain) (n : ℕ) :
    ContDiffOn ℝ ∞ (fullPhase b n) (productStrip s).domain :=
  ((hΦ n).comp contDiffOn_fst (fun _ hx => hx)).add (contDiffOn_const.mul contDiffOn_snd)

/-- Amplitude, defined pointwise by `blockAmplitude b n i j x`. -/
noncomputable def amplitude (b : CorrectionState.HarmonicBlock D) (j : ℤ)
    (n : ℕ) (x : D) : ComplexVector := fun i => blockAmplitude b n i j x

/-- Single mode, constructed using `HarmonicResidual.vectorField`. -/
noncomputable def singleMode (b : CorrectionState.HarmonicBlock D) (j : ℤ)
    (n : ℕ) (p : D × ℝ) : ComplexVector :=
  HarmonicResidual.vectorField (fun i => AddMonoidAlgebra.single j (fun x => amplitude b j n x i))
    (b.frequency n) (b.phase n) (b.angularFrequency n) p

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem singleMode_eq (b : CorrectionState.HarmonicBlock D) (j : ℤ) (n : ℕ)
    (hk : b.frequency n ≠ 0) :
    singleMode b j n = vectorMode (b.frequency n * (j : ℝ)) (fullPhase b n)
      (fun p => amplitude b j n p.1) := by
  ext p i
  simp only [singleMode, HarmonicResidual.vectorField, field, evaluate_single,
    vectorMode, mode, character, carrier, phaseFactor, fullPhase]
  congr 1
  congr 1
  have hkc : (b.frequency n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  push_cast
  field_simp

/-- The primitive divergence condition is imposed on each actual harmonic field. -/
def ModeSolenoidal (s : StripData D) (c : CorrectionState.Context D)
    (b : CorrectionState.HarmonicBlock D) : Prop :=
  ∀ j : ℤ, j ≠ 0 → ∀ n p, p.1 ∈ s.domain →
    cylindricalDivergence (fun q => c.operators.radius q.1)
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
      HarmonicResidual.angularDirection
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
      (singleMode b j n) p = 0

theorem lifted_amplitude_angularIndependent {s : StripData D} {κ α : ℝ} {P : ℕ → D → ℝ}
    (G : Geometry s κ) {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α)
    {j : ℤ} (hj : j ≠ 0) :
    AngularIndependent (liftedGeometry G) (fun n p => amplitude b j n p.1) := by
  intro n i p hp
  rcases p with ⟨x, θ⟩
  have hs := class_lift (blockAmplitude_class hb hj i)
  have hd := ((hs.smooth n).contDiffAt ((productStrip s).isOpen_domain.mem_nhds
      hp)).differentiableAt (by
      simp)
  change DifferentiableAt ℝ (fun q : D × ℝ => amplitude b j n q.1 i) (x, θ) at hd
  change along HarmonicResidual.angularDirection (fun q => amplitude b j n q.1 i) (x, θ) = 0
  rw [HarmonicResidual.along_angularDirection hd]
  simp

theorem along_fst (V : D → D) {f : D → F} {p : D × ℝ}
    (hf : DifferentiableAt ℝ f p.1) :
    along (HarmonicResidual.liftDirection V) (fun q => f q.1) p = along V f p.1 := by
  have hd := hf.hasFDerivAt.comp p (projection (D := D)).hasFDerivAt
  change HasFDerivAt (fun q : D × ℝ => f q.1) ((fderiv ℝ f p.1).comp projection) p at hd
  simp only [along, hd.fderiv]
  rfl

theorem fullPhase_hasFDerivAt (b : CorrectionState.HarmonicBlock D) (n : ℕ) {p : D × ℝ}
    (hΦ : DifferentiableAt ℝ (b.phase n) p.1) :
    HasFDerivAt (fullPhase b n)
      ((fderiv ℝ (b.phase n) p.1).comp projection +
        ((b.angularFrequency n : ℝ) / b.frequency n) • ContinuousLinearMap.snd ℝ D ℝ) p := by
  exact (hΦ.hasFDerivAt.comp p (projection (D := D)).hasFDerivAt).add
    ((ContinuousLinearMap.snd ℝ D ℝ).hasFDerivAt.const_mul _)

theorem along_fullPhase_lift (b : CorrectionState.HarmonicBlock D) (n : ℕ) (V : D → D)
    {p : D × ℝ} (hΦ : DifferentiableAt ℝ (b.phase n) p.1) :
    along (HarmonicResidual.liftDirection V) (fullPhase b n) p = along V (b.phase n) p.1 := by
  simp only [along, (fullPhase_hasFDerivAt b n hΦ).fderiv,
    _root_.add_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply]
  change (fderiv ℝ (b.phase n) p.1) (V p.1) + ((b.angularFrequency n : ℝ) / b.frequency n) * 0 = _
  ring

theorem along_fullPhase_angular (b : CorrectionState.HarmonicBlock D) (n : ℕ)
    {p : D × ℝ} (hΦ : DifferentiableAt ℝ (b.phase n) p.1) :
    along HarmonicResidual.angularDirection (fullPhase b n) p =
      (b.angularFrequency n : ℝ) / b.frequency n := by
  simp only [along, (fullPhase_hasFDerivAt b n hΦ).fderiv,
    _root_.add_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply]
  change (fderiv ℝ (b.phase n) p.1) 0 + ((b.angularFrequency n : ℝ) / b.frequency n) * 1 = _
  simp

/-- The exact ordered coefficient from harmonic `j` advecting harmonic `l`.
The first index is carried by the first input function; `l` enters the derivatives. -/
noncomputable def orderedKernel (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp l : ℤ)
    (a b : D → ComplexVector) (x : D) (i : Fin 3) : ℂ :=
  a x 0 * derivativeCoefficient g.radial k Φ l (fun y => b y i) x +
    (a x 1 / (g.radius x : ℂ)) *
      ((((l * kp : ℤ) : ℂ) * Complex.I) * b x i + angularGenerator (b x) i) +
    a x 2 * derivativeCoefficient g.axial k Φ l (fun y => b y i) x

theorem orderedKernel_eq_fullCoefficient {s : StripData D} {κ : ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (carrierData : CorrectionState.HarmonicBlock D) (a b : Family D) (l : ℤ) (n : ℕ)
    {x : D} (hx : x ∈ s.domain) (hk : carrierData.frequency n ≠ 0)
    (hΦ : DifferentiableAt ℝ (carrierData.phase n) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b n y i) x) (i : Fin 3) :
    orderedKernel (HarmonicResidual.contextFrame c n) (carrierData.frequency n)
      (carrierData.phase n) (carrierData.angularFrequency n) l (a n) (b n) x i =
    sameCoefficient (liftedGeometry (slowGeometry c ho hR)) (fullPhase carrierData)
      (fun n => carrierData.frequency n * (l : ℝ))
      (fun n p => a n p.1) (fun n p => b n p.1) n (x, 0) i := by
  have hp (V : D → D) := along_fullPhase_lift carrierData n V (p := (x, 0)) hΦ
  have hθ := along_fullPhase_angular carrierData n (p := (x, 0)) hΦ
  have hd (V : D → D) (j : Fin 3) := along_fst V (p := (x, 0)) (hb j)
  simp only [sameCoefficient, strippedTransport, liftedGeometry, slowGeometry, normalDot,
      phaseNormal]
  change orderedKernel _ _ _ _ _ _ _ _ _ =
    a n x 0 * along (HarmonicResidual.liftDirection _) (fun p => b n p.1 i) (x, 0) +
    (a n x 1 / (c.operators.radius x : ℂ)) * angularGenerator (b n x) i +
    a n x 2 * along (HarmonicResidual.liftDirection _) (fun p => b n p.1 i) (x, 0) +
    phaseFactor (carrierData.frequency n * (l : ℝ)) *
      (normalDot (phaseNormal (fun p => c.operators.radius p.1)
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
        HarmonicResidual.angularDirection
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
        (fullPhase carrierData n) (x, 0)) (a n x)) * b n x i
  simp only [normalDot, phaseNormal, hp, hθ, hd, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons,
    orderedKernel, derivativeCoefficient, HarmonicResidual.contextFrame,
    phaseFactor, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast, Int.cast_mul]
  have hkc : (carrierData.frequency n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hrc : (c.operators.radius x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hR x hx).ne'
  field_simp; ring

/-- The first harmonic is used only through its genuine divergence equation.
Its carrier cancels against the second harmonic with a bounded integer ratio. -/
theorem orderedKernel_raw_class {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hdiv : ModeSolenoidal s c a)
    {j l : ℤ} (hj : j ≠ 0) (hl : l ≠ 0) (i : Fin 3) :
    MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ)
      (fun n x => orderedKernel (HarmonicResidual.contextFrame c n) (a.frequency n)
        (a.phase n) (a.angularFrequency n) l (amplitude a j n) (amplitude b l n) x i) := by
  let G := liftedGeometry (slowGeometry c ho hR)
  have ha' : WaveVector (productStrip s) (fun n p => P n p.1) α
      (fun n p => amplitude a j n p.1) := fun r => class_lift (blockAmplitude_class ha hj r)
  have hb' : WaveVector (productStrip s) (fun n p => P n p.1) β
      (fun n p => amplitude b l n p.1) := fun r => class_lift (blockAmplitude_class hb hl r)
  have hd : ∀ n p, p ∈ (productStrip s).domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (vectorMode (a.frequency n * (j : ℝ)) (fullPhase a n)
        (fun q => amplitude a j n q.1)) p = 0 := by
    intro n p hp
    have hh := hdiv j hj n p hp
    rw [singleMode_eq a j n (hk n)] at hh
    exact hh
  have hh := same_label_raw_bound G ho.kappa_nonneg ha' hb'
    (fullPhase_smooth a hΦ)
    (fun n => mul_ne_zero (hk n) (by exact_mod_cast hj))
    (bandBound_frequency_ratio (productStrip s) hk (fun _ => hj)
      (abs_nonneg (l : ℝ)) (fun _ => le_rfl))
    (lifted_amplitude_angularIndependent (slowGeometry c ho hR) ha hj) hd i
  have hs := class_slice (s := s) (w := fun n x =>
    (Real.sqrt (s.zeta x) * P n x) * (Real.sqrt (s.zeta x) * P n x)) hh
  apply class_congr hs
  intro n x hx
  exact (orderedKernel_eq_fullCoefficient c ho hR a (amplitude a j) (amplitude b l)
    l n hx (hk n)
    (((hΦ n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
    (fun r => ((((blockAmplitude_class hb hl r).smooth n).contDiffAt
      (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))) i).symm

/-- Oscillatory input blocks have no stored velocity at harmonic zero. -/
def ZeroMode (b : CorrectionState.HarmonicBlock D) : Prop :=
  ∀ n i, b.velocity n i 0 = 0

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem amplitude_zero {b : CorrectionState.HarmonicBlock D} (hb : ZeroMode b) (n : ℕ) :
    amplitude b 0 n = 0 := by
  ext x i
  have hzero := hb n i
  simp [amplitude, blockAmplitude, HarmonicResidual.realCoefficients_apply, hzero]

theorem orderedKernel_zero_left (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ)
    (kp l : ℤ) (b : D → ComplexVector) (x : D) (i : Fin 3) :
    orderedKernel g k Φ kp l 0 b x i = 0 := by
  simp [orderedKernel]

theorem orderedKernel_zero_right (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ)
    (kp l : ℤ) (a : D → ComplexVector) (x : D) (i : Fin 3) :
    orderedKernel g k Φ kp l a 0 x i = 0 := by
  simp only [orderedKernel, Pi.zero_apply, mul_zero]
  fin_cases i <;> simp [angularGenerator, derivativeCoefficient, along]

theorem orderedKernel_raw_class_all {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ZeroMode a) (hb0 : ZeroMode b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hdiv : ModeSolenoidal s c a)
    (j l : ℤ) (i : Fin 3) :
    MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ)
      (fun n x => orderedKernel (HarmonicResidual.contextFrame c n) (a.frequency n)
        (a.phase n) (a.angularFrequency n) l (amplitude a j n) (amplitude b l n) x i) := by
  by_cases hj : j = 0
  · subst j
    simpa only [amplitude_zero ha0, orderedKernel_zero_left] using
      (MemClass.zero (s := s) (α := α + β - κ) (E := ℂ)
        (fun n x _ => mul_self_nonneg (Real.sqrt (s.zeta x) * P n x)))
  by_cases hl : l = 0
  · subst l
    simpa only [amplitude_zero hb0, orderedKernel_zero_right] using
      (MemClass.zero (s := s) (α := α + β - κ) (E := ℂ)
        (fun n x _ => mul_self_nonneg (Real.sqrt (s.zeta x) * P n x)))
  exact orderedKernel_raw_class c ho hR ha hb hΦ hk hdiv hj hl i

/-- A common finite range is fixed for the whole family, not chosen anew on
each band. This is the finiteness needed by the uniform class estimates. -/
noncomputable def harmonicRange (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_support_range {a : Coefficients D} {N : ℕ} (ha : BandLimited a N) :
    a.support ⊆ harmonicRange N := by
  intro j hj
  have hh := ha j hj
  simp only [harmonicRange, Finset.mem_Icc]
  omega

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem convolution_apply_finset (a b : Coefficients D) (K : Finset ℤ)
    (ha : a.support ⊆ K) (m : ℤ) (x : D) :
    (a * b) m x = ∑ j ∈ K, a j x * b (m - j) x := by
  rw [convolution_apply]
  apply Finset.sum_subset ha
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj]
  simp

theorem transport_convolution (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (a b : HarmonicResidual.VectorCoefficients D) (K : Finset ℤ)
    (ha : ∀ i, (a i).support ⊆ K) (m : ℤ) (x : D) (i : Fin 3) :
    HarmonicResidual.transport g k Φ kp a b i m x =
      ∑ j ∈ K, orderedKernel g k Φ kp (m - j)
        (fun y r => a r j y) (fun y r => b r (m - j) y) x i := by
  simp only [HarmonicResidual.transport, coeff_add]
  rw [mul_assoc, convolution_apply_finset _ _ K (ha 0),
    convolution_apply_finset _ _ K (ha 1), convolution_apply_finset _ _ K (ha 2),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [orderedKernel, constant_mul, coeff_add, angularDifferentiate_apply,
    differentiate_apply, rotate_apply, div_eq_mul_inv]
  ring

theorem transport_raw_class {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D} {N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ZeroMode a) (hb0 : ZeroMode b) (hN : a.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hdiv : ModeSolenoidal s c a)
    (m : ℤ) (i : Fin 3) :
    MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ)
      (fun n x => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
        (a.frequency n) (a.phase n) (a.angularFrequency n)
        (blockAmplitude a n) (blockAmplitude b n) i m x) := by
  have hh := MemClass.sum (harmonicRange N)
    (fun j n x => orderedKernel (HarmonicResidual.contextFrame c n) (a.frequency n)
      (a.phase n) (a.angularFrequency n) (m - j) (amplitude a j n)
      (amplitude b (m - j) n) x i)
    (fun n x _ => mul_self_nonneg (Real.sqrt (s.zeta x) * P n x))
    (fun j _ => orderedKernel_raw_class_all c ho hR ha hb ha0 hb0 hΦ hk hdiv j (m - j) i)
  apply class_congr hh
  intro n x _
  exact (transport_convolution _ _ _ _ _ _ (harmonicRange N)
    (fun r => band_support_range (HarmonicResidual.band_realCoefficients (hN.1 n r))) m x i).symm

theorem transport_wave_class {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D} {N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ZeroMode a) (hb0 : ZeroMode b) (hN : a.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hdiv : ModeSolenoidal s c a)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (m : ℤ) (i : Fin 3) :
    WaveClass s P (α + β - κ)
      (fun n x => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
        (a.frequency n) (a.phase n) (a.angularFrequency n)
        (blockAmplitude a n) (blockAmplitude b n) i m x) :=
  wave_square_weight_wave
    (transport_raw_class c ho hR ha hb ha0 hb0 hN hΦ hk hdiv m i)
    ho.weight_le_one hP0 hP1

theorem transport_mean_class {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D} {N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ZeroMode a) (hb0 : ZeroMode b) (hN : a.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hdiv : ModeSolenoidal s c a)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (m : ℤ) (i : Fin 3) :
    MeanClass s (α + β - κ)
      (fun n x => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
        (a.frequency n) (a.phase n) (a.angularFrequency n)
        (blockAmplitude a n) (blockAmplitude b n) i m x) :=
  wave_square_weight_mean
    (transport_raw_class c ho hR ha hb ha0 hb0 hN hΦ hk hdiv m i) hP0 hP1

/-- Coefficients evaluated using the original label's carrier. -/
noncomputable def withCarrier (carrierData b : CorrectionState.HarmonicBlock D) :
    CorrectionState.HarmonicBlock D where
  velocity := b.velocity
  pressure := b.pressure
  frequency := carrierData.frequency
  phase := carrierData.phase
  angularFrequency := carrierData.angularFrequency

/-- The updated label retains its carrier, including its angular frequency. -/
noncomputable def addBlock (a b : CorrectionState.HarmonicBlock D) :
    CorrectionState.HarmonicBlock D where
  velocity := fun n i => a.velocity n i + b.velocity n i
  pressure := fun n => a.pressure n + b.pressure n
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_oscillation (a b : CorrectionState.HarmonicBlock D) (n : ℕ)
    (p : D × ℝ) (i : Fin 3) :
    (addBlock a b).oscillation n p i = a.oscillation n p i +
      (withCarrier a b).oscillation n p i := by
  simp only [addBlock, withCarrier, CorrectionState.HarmonicBlock.oscillation,
    HarmonicResidual.field_add, Complex.add_re]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_pressure (a b : CorrectionState.HarmonicBlock D) (n : ℕ) (p : D × ℝ) :
    (addBlock a b).oscillatoryPressure n p = a.oscillatoryPressure n p +
      (withCarrier a b).oscillatoryPressure n p := by
  simp only [addBlock, withCarrier, CorrectionState.HarmonicBlock.oscillatoryPressure,
    HarmonicResidual.field_add, Complex.add_re]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem blockAmplitude_addBlock (a b : CorrectionState.HarmonicBlock D) (n : ℕ) :
    blockAmplitude (addBlock a b) n = blockAmplitude a n + blockAmplitude b n := by
  funext i
  exact realCoefficients_add _ _

/-- Block transport as an element of `HarmonicResidual.BlockCoefficients D`. -/
noncomputable def blockTransport (c : CorrectionState.Context D)
    (carrierData a b : CorrectionState.HarmonicBlock D) : HarmonicResidual.BlockCoefficients D :=
  fun n => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
    (carrierData.frequency n) (carrierData.phase n) (carrierData.angularFrequency n)
    (blockAmplitude a n) (blockAmplitude b n)

/-- All three actual quadratic terms introduced by adding one wave block. -/
noncomputable def nonlinearCoefficients (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) : HarmonicResidual.BlockCoefficients D :=
  blockTransport c a a b + blockTransport c a b a + blockTransport c a b b

theorem mixed_wave_class {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ZeroMode a) (hb0 : ZeroMode b) (hM : a.BandLimited M) (hN : b.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain) (hk : ∀ n, a.frequency n ≠ 0)
    (hda : ModeSolenoidal s c a) (hdb : ModeSolenoidal s c (withCarrier a b))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (j : ℤ) (i : Fin 3) :
    WaveClass s P (α + β - κ) (fun n x =>
      blockTransport c a a b n i j x + blockTransport c a b a n i j x) := by
  have hab := transport_wave_class c ho hR ha hb ha0 hb0 hM hΦ hk hda hP0 hP1 j i
  have hba := transport_wave_class c ho hR (a := withCarrier a b) hb ha hb0 ha0 hN
    hΦ hk hdb hP0 hP1 j i
  have hba' : WaveClass s P (α + β - κ)
      (fun n x => blockTransport c a b a n i j x) := by
    simp only [blockTransport, withCarrier, add_comm β α] at hba ⊢
    exact hba
  exact hab.add hba'

theorem square_wave_class {s : StripData D} {κ β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (a : CorrectionState.HarmonicBlock D) {b : CorrectionState.HarmonicBlock D} {N : ℕ}
    (hb : b.WaveBounds s P β) (hb0 : ZeroMode b) (hN : b.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain) (hk : ∀ n, a.frequency n ≠ 0)
    (hdb : ModeSolenoidal s c (withCarrier a b))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (j : ℤ) (i : Fin 3) :
    WaveClass s P (β + β - κ) (fun n x => blockTransport c a b b n i j x) :=
  transport_wave_class c ho hR (a := withCarrier a b) hb hb hb0 hb0 hN
    hΦ hk hdb hP0 hP1 j i

theorem nonlinearCoefficients_wave_class {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ZeroMode a) (hb0 : ZeroMode b) (hM : a.BandLimited M) (hN : b.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain) (hk : ∀ n, a.frequency n ≠ 0)
    (hda : ModeSolenoidal s c a) (hdb : ModeSolenoidal s c (withCarrier a b))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (j : ℤ) (i : Fin 3) :
    WaveClass s P (min (α + β - κ) (β + β - κ))
      (fun n x => nonlinearCoefficients c a b n i j x) := by
  exact ((mixed_wave_class c ho hR ha hb ha0 hb0 hM hN hΦ hk hda hdb hP0 hP1 j i).mono_exponent
    (min_le_left _ _)).add ((square_wave_class c ho hR a hb hb0 hN hΦ hk hdb hP0 hP1 j
        i).mono_exponent
      (min_le_right _ _))

/-- Nonlinear error block, bundling `velocity`, `pressure`, `frequency`, `phase` and the
required compatibility proofs. -/
noncomputable def nonlinearErrorBlock (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) : CorrectionState.HarmonicBlock D where
  velocity := fun n i => HarmonicResidual.nonconstant
    (HarmonicResidual.realCoefficients (nonlinearCoefficients c a b n i))
  pressure := fun _ => 0
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

theorem nonlinearErrorBlock_class {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ZeroMode a) (hb0 : ZeroMode b) (hM : a.BandLimited M) (hN : b.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain) (hk : ∀ n, a.frequency n ≠ 0)
    (hda : ModeSolenoidal s c a) (hdb : ModeSolenoidal s c (withCarrier a b))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    (nonlinearErrorBlock c a b).WaveBounds s P (min (α + β - κ) (β + β - κ)) := by
  intro i j hj
  have hh m := nonlinearCoefficients_wave_class c ho hR ha hb ha0 hb0 hM hN hΦ hk hda hdb hP0 hP1 m
      i
  have hr := realCoefficient_class (fun n => nonlinearCoefficients c a b n i) j (hh j) (hh (-j))
  apply class_congr hr
  intro n x _
  exact (nonconstant_apply_of_ne _ hj x).symm

theorem nonlinearErrorBlock_band (c : CorrectionState.Context D)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.BandLimited M) (hb : b.BandLimited N) :
    (nonlinearErrorBlock c a b).BandLimited (max (M + N) (N + N)) := by
  refine ⟨fun n i => ?_, fun _ => HarmonicResidual.band_zero _⟩
  apply HarmonicResidual.band_nonconstant
  apply HarmonicResidual.band_realCoefficients
  have ha' r := HarmonicResidual.band_realCoefficients (ha.1 n r)
  have hb' r := HarmonicResidual.band_realCoefficients (hb.1 n r)
  have hab := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) ha' hb' i
  have hba := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) hb' ha' i
  have hbb := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) hb' hb' i
  exact ((hab.mono (le_max_left _ _)).add (hba.mono (by omega))).add
    (hbb.mono (le_max_right _ _))

theorem nonlinearErrorBlock_conjugate (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) (n : ℕ) (i : Fin 3) :
    ConjugateSymmetric ((nonlinearErrorBlock c a b).velocity n i) :=
  HarmonicResidual.nonconstant_conjugate (HarmonicResidual.realCoefficients_conjugate _)

theorem nonlinearErrorBlock_zero (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) : ZeroMode (nonlinearErrorBlock c a b) := by
  intro n i
  simp [nonlinearErrorBlock, HarmonicResidual.nonconstant]

/-! ## Identification with the actual differentiated residual -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficient_eq_of_field_eq_at (a b : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (j : ℤ) (x : D)
    (he : ∀ θ, field a k Φ kp (x, θ) = field b k Φ kp (x, θ)) : a j x = b j x := by
  rw [← HarmonicResidual.extract_field a k Φ hkp j x,
    ← HarmonicResidual.extract_field b k Φ hkp j x]
  unfold HarmonicResidual.extract
  congr 1
  funext θ
  rw [he θ]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem vectorField_add (a b : HarmonicResidual.VectorCoefficients D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) :
    HarmonicResidual.vectorField (a + b) k Φ kp =
      HarmonicResidual.vectorField a k Φ kp + HarmonicResidual.vectorField b k Φ kp := by
  ext p i
  exact HarmonicResidual.field_add (a i) (b i) k Φ kp p

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem scalarField_add (a b : Coefficients D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ) :
    field (a + b) k Φ kp = field a k Φ kp + field b k Φ kp := by
  ext p
  exact HarmonicResidual.field_add a b k Φ kp p

/-- The coefficient identity is extracted from the proved product rules for
the actual cylindrical differential operators. -/
theorem nonlinear_update_coefficients {U : Set D} (hU : IsOpen U)
    (g : HarmonicResidual.Frame D) (hr : ContDiffOn ℝ ∞ g.radial U)
    (hz : ContDiffOn ℝ ∞ g.axial U) (k : ℝ) {Φ : D → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ U) {kp : ℤ} (hkp : kp ≠ 0)
    (B a b : HarmonicResidual.VectorCoefficients D) (p q : Coefficients D)
    (hB : ∀ i, HarmonicResidual.SmoothCoefficients U (B i))
    (ha : ∀ i, HarmonicResidual.SmoothCoefficients U (a i))
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b i))
    (hp : HarmonicResidual.SmoothCoefficients U p) (hq : HarmonicResidual.SmoothCoefficients U q)
    {x : D} (hx : x ∈ U) (j : ℤ) (i : Fin 3) :
    HarmonicResidual.nonlinearResidual g k Φ kp B (a + b) (p + q) i j x -
      HarmonicResidual.nonlinearResidual g k Φ kp B a p i j x =
      HarmonicResidual.linearResidual g k Φ kp B b q i j x +
        HarmonicResidual.transport g k Φ kp a b i j x +
        HarmonicResidual.transport g k Φ kp b a i j x +
        HarmonicResidual.transport g k Φ kp b b i j x := by
  change (HarmonicResidual.nonlinearResidual g k Φ kp B (a + b) (p + q) i -
    HarmonicResidual.nonlinearResidual g k Φ kp B a p i) j x =
    (HarmonicResidual.linearResidual g k Φ kp B b q i +
      HarmonicResidual.transport g k Φ kp a b i +
      HarmonicResidual.transport g k Φ kp b a i +
      HarmonicResidual.transport g k Φ kp b b i) j x
  apply coefficient_eq_of_field_eq_at _ _ k Φ hkp j x
  intro θ
  have hxθ : (x, θ) ∈ HarmonicResidual.liftDomain U := ⟨hx, trivial⟩
  have hnew := HarmonicResidual.field_nonlinearResidual hU g hr hz (a := a + b) hB
    (fun r => (ha r).add (hb r)) (hp.add hq) hΦ k kp hxθ
  have hold := HarmonicResidual.field_nonlinearResidual hU g hr hz hB ha hp hΦ k kp hxθ
  have hlin := HarmonicResidual.field_linearResidual hU g hr hz hB hb hq hΦ k kp hxθ
  have hab := HarmonicResidual.field_transport hU g a hb hΦ k kp hxθ
  have hba := HarmonicResidual.field_transport hU g b ha hΦ k kp hxθ
  have hbb := HarmonicResidual.field_transport hU g b hb hΦ k kp hxθ
  simp only [HarmonicResidual.field_sub, HarmonicResidual.field_add]
  change (HarmonicResidual.vectorField _ k Φ kp (x, θ)) i -
    (HarmonicResidual.vectorField _ k Φ kp (x, θ)) i =
    (HarmonicResidual.vectorField _ k Φ kp (x, θ)) i +
    (HarmonicResidual.vectorField _ k Φ kp (x, θ)) i +
    (HarmonicResidual.vectorField _ k Φ kp (x, θ)) i +
    (HarmonicResidual.vectorField _ k Φ kp (x, θ)) i
  rw [hnew, hold, hlin, hab, hba, hbb, vectorField_add, scalarField_add]
  have he := HarmonicResidual.Actual.nonlinearResidual_add_sub (Vθ :=
      HarmonicResidual.angularDirection)
    (HarmonicResidual.liftDomain_open hU) g.viscosity (fun y => g.radius y.1)
    (HarmonicResidual.liftDirection g.time) (HarmonicResidual.liftDirection_smooth hr)
    contDiffOn_const (HarmonicResidual.liftDirection_smooth hz)
    (HarmonicResidual.vectorField B k Φ kp) (HarmonicResidual.vectorField a k Φ kp)
    (HarmonicResidual.vectorField b k Φ kp) (field p k Φ kp) (field q k Φ kp)
    (fun r => HarmonicResidual.field_smoothOn (ha r) hΦ k kp)
    (fun r => HarmonicResidual.field_smoothOn (hb r) hΦ k kp)
    (HarmonicResidual.field_smoothOn hp hΦ k kp) (HarmonicResidual.field_smoothOn hq hΦ k kp) hxθ
  exact congrFun he i

theorem linear_mean_difference (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (B m : D → ComplexVector) (a : HarmonicResidual.VectorCoefficients D) (p : Coefficients D) {x :
        D}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hm : ∀ i, DifferentiableAt ℝ (fun y => m y i) x) (j : ℤ) (i : Fin 3) :
    HarmonicResidual.linearResidual g k Φ kp (HarmonicResidual.constantVector (B + m)) a p i j x -
      HarmonicResidual.linearResidual g k Φ kp (HarmonicResidual.constantVector B) a p i j x =
        crossCoefficients g k Φ kp m a i j x := by
  simp only [HarmonicResidual.linearResidual, crossCoefficients, coeff_add, coeff_sub,
    transport_constant_left, transport_constant_right, Pi.add_apply,
    along_add _ (hB i) (hm i), HarmonicResidual.Actual.angularGenerator_add]
  ring

theorem nonlinear_update_with_mean {U : Set D} (hU : IsOpen U)
    (g : HarmonicResidual.Frame D) (hr : ContDiffOn ℝ ∞ g.radial U)
    (hz : ContDiffOn ℝ ∞ g.axial U) (k : ℝ) {Φ : D → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ U) {kp : ℤ} (hkp : kp ≠ 0)
    (B M : D → ComplexVector) (a b : HarmonicResidual.VectorCoefficients D)
    (p q : Coefficients D) (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U)
    (ha : ∀ i, HarmonicResidual.SmoothCoefficients U (a i))
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b i))
    (hp : HarmonicResidual.SmoothCoefficients U p) (hq : HarmonicResidual.SmoothCoefficients U q)
    {x : D} (hx : x ∈ U) (j : ℤ) (i : Fin 3) :
    HarmonicResidual.nonlinearResidual g k Φ kp (HarmonicResidual.constantVector (B + M))
        (a + b) (p + q) i j x -
      HarmonicResidual.nonlinearResidual g k Φ kp (HarmonicResidual.constantVector (B + M)) a p i j
          x =
      HarmonicResidual.linearResidual g k Φ kp (HarmonicResidual.constantVector B) b q i j x +
        crossCoefficients g k Φ kp M b i j x +
        HarmonicResidual.transport g k Φ kp a b i j x +
        HarmonicResidual.transport g k Φ kp b a i j x +
        HarmonicResidual.transport g k Φ kp b b i j x := by
  have hn := nonlinear_update_coefficients hU g hr hz k hΦ hkp
    (HarmonicResidual.constantVector (B + M)) a b p q
    (fun r => HarmonicResidual.smoothCoefficients_constant ((hB r).add (hM r))) ha hb hp hq hx j i
  have hm := linear_mean_difference g k Φ kp B M b q
    (fun r => ((hB r).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (fun r => ((hM r).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) j i
  linear_combination hn + hm

/-- Linear coefficients as an element of `HarmonicResidual.BlockCoefficients D`. -/
noncomputable def linearCoefficients (c : CorrectionState.Context D)
    (carrierData b : CorrectionState.HarmonicBlock D) : HarmonicResidual.BlockCoefficients D :=
  fun n => HarmonicResidual.linearResidual (HarmonicResidual.contextFrame c n)
    (carrierData.frequency n) (carrierData.phase n) (carrierData.angularFrequency n)
    (HarmonicResidual.constantVector (HarmonicResidual.contextBase c n))
    (blockAmplitude b n) (HarmonicResidual.realCoefficients (b.pressure n))

/-- The complete wave change before removing its zero mode. The Gaussian
increment and the alias difference remain literal coefficient fields. -/
noncomputable def waveChangeCoefficients (c : CorrectionState.Context D) (u : CorrectionState.State
    D)
    (a b : CorrectionState.HarmonicBlock D) (g A₀ A₁ : HarmonicResidual.BlockCoefficients D) :
    HarmonicResidual.BlockCoefficients D :=
  linearCoefficients c a b + meanCross c u.mean (withCarrier a b) + nonlinearCoefficients c a b -
    g - (A₁ - A₀)

theorem residualCoefficients_wave_update {U : Set D} (hU : IsOpen U)
    (c : CorrectionState.Context D) (u₀ u₁ : CorrectionState.State D) (he : u₁.mean = u₀.mean)
    (a b : CorrectionState.HarmonicBlock D) (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (n : ℕ) (hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial U)
    (hz : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial U)
    (hΦ : ContDiffOn ℝ ∞ (a.phase n) U) (hkp : a.angularFrequency n ≠ 0)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.contextBase c n y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.stateMean u₀ n y i) U)
    (ha : ∀ i, HarmonicResidual.SmoothCoefficients U (a.velocity n i))
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (hp : HarmonicResidual.SmoothCoefficients U (a.pressure n))
    (hq : HarmonicResidual.SmoothCoefficients U (b.pressure n))
    {x : D} (hx : x ∈ U) (j : ℤ) (i : Fin 3) :
    (HarmonicResidual.ofBlock (addBlock a b) (G + g) A₁ n).residualCoefficients
        (HarmonicResidual.contextFrame c n) (HarmonicResidual.contextBase c n)
        (HarmonicResidual.stateMean u₁ n) i j x -
      (HarmonicResidual.ofBlock a G A₀ n).residualCoefficients
        (HarmonicResidual.contextFrame c n) (HarmonicResidual.contextBase c n)
        (HarmonicResidual.stateMean u₀ n) i j x =
      HarmonicResidual.realCoefficients (waveChangeCoefficients c u₀ a b g A₀ A₁ n i) j x := by
  have hstate : HarmonicResidual.stateMean u₁ n = HarmonicResidual.stateMean u₀ n := by
    change tripleField u₁.mean n = tripleField u₀.mean n
    rw [he]
  let N₀ := HarmonicResidual.nonlinearResidual (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n)
    (HarmonicResidual.constantVector (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean
        u₀ n))
    (blockAmplitude a n) (HarmonicResidual.realCoefficients (a.pressure n))
  let N₁ := HarmonicResidual.nonlinearResidual (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n)
    (HarmonicResidual.constantVector (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean
        u₀ n))
    (blockAmplitude a n + blockAmplitude b n)
    (HarmonicResidual.realCoefficients (a.pressure n) + HarmonicResidual.realCoefficients
        (b.pressure n))
  have hd (m : ℤ) : N₁ i m x - N₀ i m x =
      linearCoefficients c a b n i m x + meanCross c u₀.mean (withCarrier a b) n i m x +
        nonlinearCoefficients c a b n i m x := by
    have hh := nonlinear_update_with_mean hU (HarmonicResidual.contextFrame c n) hr hz
      (a.frequency n) hΦ hkp (HarmonicResidual.contextBase c n) (HarmonicResidual.stateMean u₀ n)
      (blockAmplitude a n) (blockAmplitude b n) (HarmonicResidual.realCoefficients (a.pressure n))
      (HarmonicResidual.realCoefficients (b.pressure n)) hB hM
      (fun r => (ha r).realCoefficients) (fun r => (hb r).realCoefficients)
      hp.realCoefficients hq.realCoefficients hx m i
    change N₁ i m x - N₀ i m x = _ at hh
    change N₁ i m x - N₀ i m x = _
    simp only [linearCoefficients, meanCross, withCarrier, nonlinearCoefficients,
      blockTransport, Pi.add_apply, coeff_add, add_assoc] at hh ⊢
    exact hh
  simp only [HarmonicResidual.LabelData.residualCoefficients, HarmonicResidual.ofBlock,
    addBlock, realCoefficients_add, hstate]
  change HarmonicResidual.realCoefficients (N₁ i - (G n i + g n i) - A₁ n i) j x -
    HarmonicResidual.realCoefficients (N₀ i - G n i - A₀ n i) j x = _
  rw [← coeff_sub, ← realCoefficients_sub]
  have hdiff (m : ℤ) : ((N₁ i - (G n i + g n i) - A₁ n i) -
      (N₀ i - G n i - A₀ n i)) m x = waveChangeCoefficients c u₀ a b g A₀ A₁ n i m x := by
    simp only [waveChangeCoefficients, Pi.sub_apply, Pi.add_apply, coeff_sub, coeff_add]
    linear_combination hd m
  simp only [HarmonicResidual.realCoefficients_apply, hdiff]

theorem residualBlock_wave_update {U : Set D} (hU : IsOpen U)
    (c : CorrectionState.Context D) (u₀ u₁ : CorrectionState.State D) (he : u₁.mean = u₀.mean)
    (a b : CorrectionState.HarmonicBlock D) (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (n : ℕ) (hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial U)
    (hz : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial U)
    (hΦ : ContDiffOn ℝ ∞ (a.phase n) U) (hkp : a.angularFrequency n ≠ 0)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.contextBase c n y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.stateMean u₀ n y i) U)
    (ha : ∀ i, HarmonicResidual.SmoothCoefficients U (a.velocity n i))
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (hp : HarmonicResidual.SmoothCoefficients U (a.pressure n))
    (hq : HarmonicResidual.SmoothCoefficients U (b.pressure n))
    {x : D} (hx : x ∈ U) (j : ℤ) (i : Fin 3) :
    (HarmonicResidual.residualBlock c u₁ (addBlock a b) (G + g) A₁).velocity n i j x -
      (HarmonicResidual.residualBlock c u₀ a G A₀).velocity n i j x =
      HarmonicResidual.nonconstant
        (HarmonicResidual.realCoefficients (waveChangeCoefficients c u₀ a b g A₀ A₁ n i)) j x := by
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.residualBlock_zero_mode, HarmonicResidual.nonconstant]
  change HarmonicResidual.nonconstant _ j x - HarmonicResidual.nonconstant _ j x = _
  simp only [nonconstant_apply_of_ne _ hj]
  exact residualCoefficients_wave_update hU c u₀ u₁ he a b G g A₀ A₁ n hr hz hΦ hkp
    hB hM ha hb hp hq hx j i

/-- Interaction coefficients, given by `meanCross c u.mean (withCarrier a b) +
nonlinearCoefficients c a b`. -/
noncomputable def interactionCoefficients (c : CorrectionState.Context D) (u :
    CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) : HarmonicResidual.BlockCoefficients D :=
  meanCross c u.mean (withCarrier a b) + nonlinearCoefficients c a b

/-- Interaction block, bundling `velocity`, `pressure`, `frequency`, `phase` and the required
compatibility proofs. -/
noncomputable def interactionBlock (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) : CorrectionState.HarmonicBlock D where
  velocity := fun n i => HarmonicResidual.nonconstant
    (HarmonicResidual.realCoefficients (interactionCoefficients c u a b n i))
  pressure := fun _ => 0
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

/-- Linear good block, bundling `velocity`, `pressure`, `frequency`, `phase` and the required
compatibility proofs. -/
noncomputable def linearGoodBlock (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) (g : HarmonicResidual.BlockCoefficients D) :
    CorrectionState.HarmonicBlock D where
  velocity := fun n i => HarmonicResidual.nonconstant
    (HarmonicResidual.realCoefficients (linearCoefficients c a b n i - g n i))
  pressure := fun _ => 0
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant_add (a b : Coefficients D) :
    HarmonicResidual.nonconstant (a + b) =
      HarmonicResidual.nonconstant a + HarmonicResidual.nonconstant b := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.nonconstant]
  simp only [nonconstant_apply_of_ne _ hj, coeff_add]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The zero-mode alias remains in the complete residual but vanishes under
the actual nonconstant projection. -/
theorem nonconstant_real_sub_axisymmetric (a b : Coefficients D) (hb : BandLimited b 0) :
    HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients (a - b)) =
      HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients a) := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.nonconstant]
  simp only [nonconstant_apply_of_ne _ hj, HarmonicResidual.realCoefficients_apply,
    coeff_sub, band_zero_coefficient hb hj, band_zero_coefficient hb (neg_ne_zero.mpr hj),
    Pi.zero_apply, sub_zero]

theorem waveChange_projection_split (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) (g A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.nonconstant
        (HarmonicResidual.realCoefficients (waveChangeCoefficients c u a b g A₀ A₁ n i)) =
      (linearGoodBlock c a b g).velocity n i + (interactionBlock c u a b).velocity n i := by
  change HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients
      ((linearCoefficients c a b n i + meanCross c u.mean (withCarrier a b) n i +
        nonlinearCoefficients c a b n i - g n i) - (A₁ n i - A₀ n i))) = _
  rw [nonconstant_real_sub_axisymmetric _ _ (hA n i)]
  have he : linearCoefficients c a b n i + meanCross c u.mean (withCarrier a b) n i +
      nonlinearCoefficients c a b n i - g n i =
      (linearCoefficients c a b n i - g n i) + interactionCoefficients c u a b n i := by
    simp only [interactionCoefficients, Pi.add_apply]
    abel
  rw [he, realCoefficients_add, nonconstant_add]
  rfl

theorem residualBlock_wave_update_split {U : Set D} (hU : IsOpen U)
    (c : CorrectionState.Context D) (u₀ u₁ : CorrectionState.State D) (he : u₁.mean = u₀.mean)
    (a b : CorrectionState.HarmonicBlock D) (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0)
    (n : ℕ) (hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial U)
    (hz : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial U)
    (hΦ : ContDiffOn ℝ ∞ (a.phase n) U) (hkp : a.angularFrequency n ≠ 0)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.contextBase c n y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.stateMean u₀ n y i) U)
    (ha : ∀ i, HarmonicResidual.SmoothCoefficients U (a.velocity n i))
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (hp : HarmonicResidual.SmoothCoefficients U (a.pressure n))
    (hq : HarmonicResidual.SmoothCoefficients U (b.pressure n))
    {x : D} (hx : x ∈ U) (j : ℤ) (i : Fin 3) :
    (HarmonicResidual.residualBlock c u₁ (addBlock a b) (G + g) A₁).velocity n i j x -
      (HarmonicResidual.residualBlock c u₀ a G A₀).velocity n i j x =
      (linearGoodBlock c a b g).velocity n i j x + (interactionBlock c u₀ a b).velocity n i j x :=
          by
  rw [residualBlock_wave_update hU c u₀ u₁ he a b G g A₀ A₁ n hr hz hΦ hkp hB hM ha hb hp hq hx j i,
    waveChange_projection_split c u₀ a b g A₀ A₁ hA n i]
  rfl

/-- Mean-wave and wave-wave terms retain their separate gains until the
final minimum. No class hypothesis is imposed on their output. -/
theorem interactionBlock_class {s : StripData D} {κ α β H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {u : CorrectionState.State D} (hm : MeanIncrementBounds.IncrementBounds s H u.mean)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ZeroMode a) (hb0 : ZeroMode b) (hM : a.BandLimited M) (hN : b.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain) (hk : ∀ n, a.frequency n ≠ 0)
    (hda : ModeSolenoidal s c a) (hdb : ModeSolenoidal s c (withCarrier a b))
    (hNormal : ∀ i, UnweightedClass s 0 (fun n x => slowNormal c ho hR a.phase n x i))
    (hFreq : BandBound s (-(1 / 2)) a.frequency)
    (hAng : BandBound s (-(1 / 2)) (fun n => (a.angularFrequency n : ℝ)))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    (interactionBlock c u a b).WaveBounds s P
      (min (β + H - 1 / 2) (min (α + β - κ) (β + β - κ))) := by
  intro i j hj
  have hmean := realMeanCross_class c ho hκ hR hm (b := withCarrier a b) hb hNormal hFreq hAng hP0
      hj i
  have hnon m := nonlinearCoefficients_wave_class c ho hR ha hb ha0 hb0 hM hN hΦ hk hda hdb hP0 hP1
      m i
  have hn := realCoefficient_class (fun n => nonlinearCoefficients c a b n i) j (hnon j) (hnon (-j))
  apply class_congr ((hmean.mono_exponent (min_le_left _ _)).add
    (hn.mono_exponent (min_le_right _ _)))
  intro n x _
  change _ = HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients
    (meanCross c u.mean (withCarrier a b) n i + nonlinearCoefficients c a b n i)) j x
  rw [nonconstant_apply_of_ne _ hj, realCoefficients_add]
  rfl

/-! ## Extracting the actual divergence condition -/

/-- Divergence coefficients, constructed using `differentiate`. -/
noncomputable def divergenceCoefficients (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (a : HarmonicResidual.VectorCoefficients D) : Coefficients D :=
  differentiate g.radial k Φ (a 0) +
    constantCoefficient (fun x => ((g.radius x)⁻¹ : ℝ) : D → ℂ) * a 0 +
    constantCoefficient (fun x => ((g.radius x)⁻¹ : ℝ) : D → ℂ) * angularDifferentiate kp (a 1) +
    differentiate g.axial k Φ (a 2)

theorem field_divergenceCoefficients {U : Set D} (hU : IsOpen U)
    (g : HarmonicResidual.Frame D) (k : ℝ) {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    (kp : ℤ) (a : HarmonicResidual.VectorCoefficients D)
    (ha : ∀ i, HarmonicResidual.SmoothCoefficients U (a i))
    {p : D × ℝ} (hp : p ∈ HarmonicResidual.liftDomain U) :
    field (divergenceCoefficients g k Φ kp a) k Φ kp p =
      cylindricalDivergence (fun y => g.radius y.1) (HarmonicResidual.liftDirection g.radial)
        HarmonicResidual.angularDirection (HarmonicResidual.liftDirection g.axial)
        (HarmonicResidual.vectorField a k Φ kp) p := by
  simp only [divergenceCoefficients, HarmonicResidual.field_add, field_mul,
    HarmonicResidual.field_constant,
    HarmonicResidual.field_differentiate hU (ha 0) hΦ g.radial k kp hp,
    HarmonicResidual.field_differentiate hU (ha 2) hΦ g.axial k kp hp,
    HarmonicResidual.field_angularDifferentiate hU (ha 1) hΦ k kp hp,
    cylindricalDivergence, HarmonicResidual.vectorField, Complex.real_smul]

theorem divergenceCoefficients_single (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (a : HarmonicResidual.VectorCoefficients D) (j : ℤ) :
    divergenceCoefficients g k Φ kp (fun i => AddMonoidAlgebra.single j (a i j)) =
      AddMonoidAlgebra.single j (divergenceCoefficients g k Φ kp a j) := by
  ext m x
  by_cases hm : m = j
  · subst m
    simp [divergenceCoefficients, constantCoefficient]
  · simp [divergenceCoefficients, constantCoefficient, hm,
      derivativeCoefficient, along]

theorem smoothCoefficients_single {U : Set D} {f : D → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (j : ℤ) :
    HarmonicResidual.SmoothCoefficients U (AddMonoidAlgebra.single j f) := by
  intro l
  change ContDiffOn ℝ ∞ ((Finsupp.single j f) l) U
  by_cases hl : l = j
  · subst l
    simpa only [Finsupp.single_eq_same] using hf
  · rw [Finsupp.single_eq_of_ne hl]
    exact contDiffOn_const

theorem modeSolenoidal_of_full {s : StripData D} (c : CorrectionState.Context D)
    (b : CorrectionState.HarmonicBlock D)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (b.phase n) s.domain)
    (hkp : ∀ n, b.angularFrequency n ≠ 0)
    (hb : ∀ n i, HarmonicResidual.SmoothCoefficients s.domain (b.velocity n i))
    (hdiv : ∀ n p, p.1 ∈ s.domain →
      cylindricalDivergence (fun q => c.operators.radius q.1)
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
        HarmonicResidual.angularDirection
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
        (fun q i => (b.oscillation n q i : ℂ)) p = 0) : ModeSolenoidal s c b := by
  intro j _ n p hp
  have hp' : p ∈ HarmonicResidual.liftDomain s.domain := ⟨hp, trivial⟩
  have hb' i := (hb n i).realCoefficients
  have hfield : HarmonicResidual.vectorField (blockAmplitude b n)
      (b.frequency n) (b.phase n) (b.angularFrequency n) = fun q i => (b.oscillation n q i : ℂ) :=
          by
    ext q i
    exact HarmonicResidual.field_realCoefficients _ _ _ _ _
  have hz : divergenceCoefficients (HarmonicResidual.contextFrame c n)
      (b.frequency n) (b.phase n) (b.angularFrequency n) (blockAmplitude b n) j p.1 = 0 := by
    have he := coefficient_eq_of_field_eq_at
      (divergenceCoefficients (HarmonicResidual.contextFrame c n)
        (b.frequency n) (b.phase n) (b.angularFrequency n) (blockAmplitude b n))
      0 (b.frequency n) (b.phase n) (hkp n) j p.1
    apply he
    intro θ
    rw [field_divergenceCoefficients s.isOpen_domain (HarmonicResidual.contextFrame c n)
        (b.frequency n) (hΦ n) (b.angularFrequency n) (blockAmplitude b n) hb'
        (p := (p.1, θ)) ⟨hp, trivial⟩,
      hfield, HarmonicResidual.field_zero]
    exact hdiv n (p.1, θ) hp
  change cylindricalDivergence (fun q => (HarmonicResidual.contextFrame c n).radius q.1)
    (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
    HarmonicResidual.angularDirection
    (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
    (HarmonicResidual.vectorField
      (fun i => AddMonoidAlgebra.single j (blockAmplitude b n i j))
      (b.frequency n) (b.phase n) (b.angularFrequency n)) p = 0
  rw [← field_divergenceCoefficients s.isOpen_domain (HarmonicResidual.contextFrame c n)
      (b.frequency n) (hΦ n) (b.angularFrequency n)
      (fun i => AddMonoidAlgebra.single j (blockAmplitude b n i j))
      (fun i => smoothCoefficients_single (hb' i j) j) hp', divergenceCoefficients_single]
  simp only [field, evaluate_single, hz, zero_mul]

theorem waveBounds_smooth {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α) (h0 : ZeroMode b)
    (n : ℕ) (i : Fin 3) : HarmonicResidual.SmoothCoefficients s.domain (b.velocity n i) := by
  intro j
  by_cases hj : j = 0
  · subst j
    rw [h0 n i]
    exact contDiffOn_const
  exact (hb i j hj).smooth n

/-! ## Finite harmonic values, realness, and actual label reconstruction -/

theorem nonlinearCoefficients_band (c : CorrectionState.Context D)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.BandLimited M) (hb : b.BandLimited N) (n : ℕ) (i : Fin 3) :
    BandLimited (nonlinearCoefficients c a b n i) (max (M + N) (N + N)) := by
  have ha' r := HarmonicResidual.band_realCoefficients (ha.1 n r)
  have hb' r := HarmonicResidual.band_realCoefficients (hb.1 n r)
  have hab := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) ha' hb' i
  have hba := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) hb' ha' i
  have hbb := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) hb' hb' i
  exact ((hab.mono (le_max_left _ _)).add (hba.mono (by omega))).add
    (hbb.mono (le_max_right _ _))

theorem crossCoefficients_band (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (m : D → ComplexVector)
    {a : HarmonicResidual.VectorCoefficients D} {N : ℕ}
    (ha : ∀ i, BandLimited (a i) N) (i : Fin 3) :
    BandLimited (crossCoefficients g k Φ kp m a i) N := by
  have hleft : BandLimited (HarmonicResidual.transport g k Φ kp
      (HarmonicResidual.constantVector m) a i) N := by
    have h := HarmonicResidual.band_transport g k Φ kp
      (fun j => band_constantCoefficient (fun x => m x j)) ha i
    simp only [zero_add] at h
    exact h
  have hright : BandLimited (HarmonicResidual.transport g k Φ kp a
      (HarmonicResidual.constantVector m) i) N := by
    have h := HarmonicResidual.band_transport g k Φ kp
      ha (fun j => band_constantCoefficient (fun x => m x j)) i
    simp only [add_zero] at h
    exact h
  exact hleft.add hright

theorem interactionBlock_band (c : CorrectionState.Context D) (u : CorrectionState.State D)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.BandLimited M) (hb : b.BandLimited N) :
    (interactionBlock c u a b).BandLimited (max (M + N) (N + N)) := by
  refine ⟨fun n i => ?_, fun _ => HarmonicResidual.band_zero _⟩
  apply HarmonicResidual.band_nonconstant
  apply HarmonicResidual.band_realCoefficients
  have hcross := crossCoefficients_band (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) (tripleField u.mean n)
    (fun r => HarmonicResidual.band_realCoefficients (hb.1 n r)) i
  exact (hcross.mono (by omega)).add (nonlinearCoefficients_band c ha hb n i)

theorem interactionBlock_conjugate (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) (n : ℕ) (i : Fin 3) :
    ConjugateSymmetric ((interactionBlock c u a b).velocity n i) :=
  HarmonicResidual.nonconstant_conjugate (HarmonicResidual.realCoefficients_conjugate _)

theorem interactionBlock_zero (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) : ZeroMode (interactionBlock c u a b) := by
  intro n i
  simp [interactionBlock, HarmonicResidual.nonconstant]

theorem linearGoodBlock_band (c : CorrectionState.Context D) (a : CorrectionState.HarmonicBlock D)
    {b : CorrectionState.HarmonicBlock D} {g : HarmonicResidual.BlockCoefficients D} {N E : ℕ}
    (hb : b.BandLimited N) (hg : ∀ n i, BandLimited (g n i) E) :
    (linearGoodBlock c a b g).BandLimited (max N E) := by
  refine ⟨fun n i => ?_, fun _ => HarmonicResidual.band_zero _⟩
  apply HarmonicResidual.band_nonconstant
  apply HarmonicResidual.band_realCoefficients
  have hlin := HarmonicResidual.band_linearResidual (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n)
    (B := HarmonicResidual.constantVector (HarmonicResidual.contextBase c n))
    (fun _ => band_constantCoefficient _)
    (fun r => HarmonicResidual.band_realCoefficients (hb.1 n r))
    (HarmonicResidual.band_realCoefficients (hb.2 n)) i
  exact HarmonicResidual.band_sub (hlin.mono (le_max_left _ _)) ((hg n i).mono (le_max_right _ _))

theorem linearGoodBlock_conjugate (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) (g : HarmonicResidual.BlockCoefficients D) (n : ℕ) (i :
        Fin 3) :
    ConjugateSymmetric ((linearGoodBlock c a b g).velocity n i) :=
  HarmonicResidual.nonconstant_conjugate (HarmonicResidual.realCoefficients_conjugate _)

theorem linearGoodBlock_zero (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) (g : HarmonicResidual.BlockCoefficients D) :
    ZeroMode (linearGoodBlock c a b g) := by
  intro n i
  simp [linearGoodBlock, HarmonicResidual.nonconstant]

/-- Wave residual difference block, bundling `velocity`, `pressure`, `frequency`, `phase` and
the required compatibility proofs. -/
noncomputable def waveResidualDifferenceBlock (c : CorrectionState.Context D)
    (u₀ u₁ : CorrectionState.State D) (a b : CorrectionState.HarmonicBlock D)
    (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D) : CorrectionState.HarmonicBlock D where
  velocity := fun n i => (HarmonicResidual.residualBlock c u₁ (addBlock a b) (G + g) A₁).velocity n
      i -
    (HarmonicResidual.residualBlock c u₀ a G A₀).velocity n i
  pressure := fun _ => 0
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

theorem waveResidualDifferenceBlock_field (c : CorrectionState.Context D)
    (u₀ u₁ : CorrectionState.State D) (a b : CorrectionState.HarmonicBlock D)
    (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (waveResidualDifferenceBlock c u₀ u₁ a b G g A₀ A₁).oscillation n x i =
      (HarmonicResidual.residualBlock c u₁ (addBlock a b) (G + g) A₁).oscillation n x i -
      (HarmonicResidual.residualBlock c u₀ a G A₀).oscillation n x i := by
  simp only [waveResidualDifferenceBlock, CorrectionState.HarmonicBlock.oscillation,
    HarmonicResidual.field_sub, Complex.sub_re]
  rfl

/-- The grouped difference is the change in the actual good nonconstant PDE
residual. Cross-label products vanish by the disjoint supports contained in
`ExtractionRegular`; finite sums alone are not used as uniform estimates. -/
theorem grouped_wave_change {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : CorrectionState.Context D} {u₀ u₁ : CorrectionState.State D}
    {labels : ℕ → Finset ι} {a b : ι → CorrectionState.HarmonicBlock D}
    {G g A₀ A₁ : ι → HarmonicResidual.BlockCoefficients D}
    (hrep₀ : HarmonicResidual.BlockRepresentation labels a G A₀ u₀)
    (hrep₁ : HarmonicResidual.BlockRepresentation labels (fun l => addBlock (a l) (b l))
      (fun l => G l + g l) A₁ u₁) {n : ℕ}
    (h₀ : HarmonicResidual.ExtractionRegular U c u₀ labels a G A₀ n)
    (h₁ : HarmonicResidual.ExtractionRegular U c u₁ labels (fun l => addBlock (a l) (b l))
      (fun l => G l + g l) A₁ n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    HarmonicResidual.stateGoodWaveResidual c u₁ n x i -
      HarmonicResidual.stateGoodWaveResidual c u₀ n x i =
      ∑ l ∈ labels n, (waveResidualDifferenceBlock c u₀ u₁ (a l) (b l)
        (G l) (g l) (A₀ l) (A₁ l)).oscillation n x i := by
  rw [HarmonicResidual.stateGoodWaveResidual_grouped hU hrep₁ h₁ hx i,
    HarmonicResidual.stateGoodWaveResidual_grouped hU hrep₀ h₀ hx i]
  simp only [waveResidualDifferenceBlock_field, Finset.sum_sub_distrib]

end NavierStokes.HarmonicWaveInteraction
