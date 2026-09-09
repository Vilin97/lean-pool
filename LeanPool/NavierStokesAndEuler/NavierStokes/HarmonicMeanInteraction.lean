/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveInteractionBounds

@[expose] public section

/-!
# Actual harmonic residual changes under a mean increment

The wave and its pressure are held fixed.  Every coefficient below belongs to
the actual differential residual in `HarmonicResidual`; excluded errors are
kept as separate additive differences.
-/

noncomputable section

namespace NavierStokes.HarmonicMeanInteraction

open Set Filter Function HarmonicCalculus HarmonicFields WeightedClasses
open WaveInteractionBounds
open scoped Topology ContDiff BigOperators ComplexConjugate



variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem coeff_add (a b : Coefficients D) (j : ℤ) (x : D) :
    (a + b) j x = a j x + b j x := rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem coeff_sub (a b : Coefficients D) (j : ℤ) (x : D) :
    (a - b) j x = a j x - b j x := rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem coeff_neg (a : Coefficients D) (j : ℤ) (x : D) : (-a) j x = -a j x := rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem coeff_zero (j : ℤ) (x : D) : (0 : Coefficients D) j x = 0 := rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem constant_mul (f : D → ℂ) (a : Coefficients D) (j : ℤ) (x : D) :
    (constantCoefficient f * a) j x = f x * a j x := by
  rw [constantCoefficient, AddMonoidAlgebra.coeff_single_zero_mul]
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem mul_constant (a : Coefficients D) (f : D → ℂ) (j : ℤ) (x : D) :
    (a * constantCoefficient f) j x = a j x * f x := by
  rw [constantCoefficient, AddMonoidAlgebra.coeff_mul_single_zero]
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem constant_mul_constant (f g : D → ℂ) :
    constantCoefficient f * constantCoefficient g = constantCoefficient (fun x => f x * g x) := by
  ext j x
  rw [constant_mul]
  by_cases hj : j = 0
  · simp [hj, constantCoefficient]
  · simp [constantCoefficient, hj]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem constant_add (f g : D → ℂ) :
    constantCoefficient f + constantCoefficient g = constantCoefficient (fun x => f x + g x) := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [constantCoefficient]
  · simp [constantCoefficient, hj]

theorem differentiate_constant (V : D → D) (k : ℝ) (Φ : D → ℝ) (f : D → ℂ) :
    differentiate V k Φ (constantCoefficient f) = constantCoefficient (along V f) := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [differentiate_apply, derivativeCoefficient, constantCoefficient, phaseFactor]
  · have hz : (constantCoefficient f : Coefficients D) j = 0 := by
      simp [constantCoefficient, hj]
    simp [differentiate_apply, derivativeCoefficient_zero, constantCoefficient, hj]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularDifferentiate_constant (kp : ℤ) (f : D → ℂ) :
    angularDifferentiate kp (constantCoefficient f) = 0 := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [angularDifferentiate_apply]
  · simp [angularDifferentiate_apply, constantCoefficient, hj]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem rotate_constant (m : D → ComplexVector) (i : Fin 3) :
    HarmonicResidual.rotate (HarmonicResidual.constantVector m) i = constantCoefficient (fun x =>
      angularGenerator (m x) i) := by
  ext j x
  fin_cases i <;>
    simp [HarmonicResidual.rotate, HarmonicResidual.constantVector, angularGenerator,
      constantCoefficient] <;> split_ifs <;> simp

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem rotate_apply (a : HarmonicResidual.VectorCoefficients D) (j : ℤ) (x : D) (i : Fin 3) :
    HarmonicResidual.rotate a i j x = angularGenerator (fun l => a l j x) i := by
  fin_cases i <;> rfl

theorem transport_constant_left (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (m : D → ComplexVector) (a : HarmonicResidual.VectorCoefficients D) (j : ℤ) (x : D) (i : Fin 3)
      :
    HarmonicResidual.transport g k Φ kp (HarmonicResidual.constantVector m) a i j x =
      m x 0 * derivativeCoefficient g.radial k Φ j (a i j) x +
      (m x 1 / (g.radius x : ℂ)) *
        ((((j * kp : ℤ) : ℂ) * Complex.I) * a i j x + angularGenerator (fun l => a l j x) i) +
      m x 2 * derivativeCoefficient g.axial k Φ j (a i j) x := by
  simp only [HarmonicResidual.transport, HarmonicResidual.constantVector, coeff_add, constant_mul,
    constant_mul_constant, angularDifferentiate_apply, differentiate_apply, rotate_apply,
      div_eq_mul_inv]

theorem transport_constant_right (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (a : HarmonicResidual.VectorCoefficients D) (m : D → ComplexVector) (j : ℤ) (x : D) (i : Fin 3)
      :
    HarmonicResidual.transport g k Φ kp a (HarmonicResidual.constantVector m) i j x =
      a 0 j x * along g.radial (fun y => m y i) x +
      (a 1 j x / (g.radius x : ℂ)) * angularGenerator (m x) i +
      a 2 j x * along g.axial (fun y => m y i) x := by
  simp only [HarmonicResidual.transport, HarmonicResidual.constantVector, coeff_add,
    differentiate_constant, mul_constant,
    angularDifferentiate_constant, zero_add, rotate_constant, div_eq_mul_inv]

/-- The two actual cross-advections at coefficient level, before any zero-mode deletion. -/
noncomputable def crossCoefficients (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (m : D → ComplexVector) (a : HarmonicResidual.VectorCoefficients D) :
      HarmonicResidual.VectorCoefficients D := fun i =>
  HarmonicResidual.transport g k Φ kp (HarmonicResidual.constantVector m) a i +
    HarmonicResidual.transport g k Φ kp a (HarmonicResidual.constantVector m) i

theorem nonlinear_mean_difference (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (B m : D → ComplexVector) (a : HarmonicResidual.VectorCoefficients D) (p : Coefficients D) {x :
      D}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hm : ∀ i, DifferentiableAt ℝ (fun y => m y i) x) (j : ℤ) (i : Fin 3) :
    HarmonicResidual.nonlinearResidual g k Φ kp (HarmonicResidual.constantVector (B + m)) a p i j x
      -
      HarmonicResidual.nonlinearResidual g k Φ kp (HarmonicResidual.constantVector B) a p i j x =
        crossCoefficients g k Φ kp m a i j x := by
  simp only [HarmonicResidual.nonlinearResidual, HarmonicResidual.linearResidual,
    crossCoefficients, coeff_add, coeff_sub,
    transport_constant_left, transport_constant_right, Pi.add_apply,
    along_add _ (hB i) (hm i), HarmonicResidual.Actual.angularGenerator_add]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_sub (a b : Coefficients D) :
    HarmonicResidual.realCoefficients (a - b) = HarmonicResidual.realCoefficients a -
      HarmonicResidual.realCoefficients b := by
  ext j x
  simp only [HarmonicResidual.realCoefficients_apply, coeff_sub, map_sub]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_add (a b : Coefficients D) :
    HarmonicResidual.realCoefficients (a + b) = HarmonicResidual.realCoefficients a +
      HarmonicResidual.realCoefficients b := by
  ext j x
  simp only [HarmonicResidual.realCoefficients_apply, coeff_add, map_add]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_local_congr {U : Set D} {a b : Coefficients D}
    (hab : ∀ j x, x ∈ U → a j x = b j x) (j : ℤ) {x : D} (hx : x ∈ U) :
    HarmonicResidual.realCoefficients a j x = HarmonicResidual.realCoefficients b j x := by
  simp only [HarmonicResidual.realCoefficients_apply, hab j x hx, hab (-j) x hx]

noncomputable def tripleField (h : MeanIncrementBounds.Triple D) (n : ℕ) (x : D) : ComplexVector :=
  ![(h.radial n x : ℂ), (h.angular n x : ℂ), (h.axial n x : ℂ)]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem stateMean_updated (s₀ s₁ : CorrectionState.State D) (h : MeanIncrementBounds.Triple D)
    (he : s₁.mean = MeanIncrementBounds.updated s₀.mean h) (n : ℕ) :
    HarmonicResidual.stateMean s₁ n = HarmonicResidual.stateMean s₀ n + tripleField h n := by
  ext x i
  fin_cases i <;> simp [HarmonicResidual.stateMean, tripleField, he, MeanIncrementBounds.updated]

noncomputable def blockAmplitude (b : CorrectionState.HarmonicBlock D) (n : ℕ) :
  HarmonicResidual.VectorCoefficients D :=
  fun i => HarmonicResidual.realCoefficients (b.velocity n i)

noncomputable def meanCross (c : CorrectionState.Context D) (h : MeanIncrementBounds.Triple D) (b :
  CorrectionState.HarmonicBlock D)
    (n : ℕ) : HarmonicResidual.VectorCoefficients D :=
  crossCoefficients (HarmonicResidual.contextFrame c n) (b.frequency n) (b.phase n)
    (b.angularFrequency n)
    (tripleField h n) (blockAmplitude b n)

/-- General additive error differences are retained, including their zero modes. -/
theorem residualCoefficients_mean_update (c : CorrectionState.Context D) (s₀ s₁ :
  CorrectionState.State D)
    (h : MeanIncrementBounds.Triple D) (he : s₁.mean = MeanIncrementBounds.updated s₀.mean h) (b :
      CorrectionState.HarmonicBlock D)
    (G₀ G₁ A₀ A₁ : HarmonicResidual.BlockCoefficients D) (n : ℕ) {x : D}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => HarmonicResidual.contextBase c n y i) x)
    (hM : ∀ i, DifferentiableAt ℝ (fun y => HarmonicResidual.stateMean s₀ n y i) x)
    (hh : ∀ i, DifferentiableAt ℝ (fun y => tripleField h n y i) x) (j : ℤ) (i : Fin 3) :
    (HarmonicResidual.ofBlock b G₁ A₁ n).residualCoefficients (HarmonicResidual.contextFrame c n)
        (HarmonicResidual.contextBase c n) (HarmonicResidual.stateMean s₁ n) i j x -
      (HarmonicResidual.ofBlock b G₀ A₀ n).residualCoefficients (HarmonicResidual.contextFrame c n)
        (HarmonicResidual.contextBase c n) (HarmonicResidual.stateMean s₀ n) i j x =
      HarmonicResidual.realCoefficients (meanCross c h b n i - (G₁ n i - G₀ n i) - (A₁ n i - A₀ n
        i)) j x := by
  have hsum : HarmonicResidual.contextBase c n + HarmonicResidual.stateMean s₁ n =
      (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean s₀ n) + tripleField h n := by
    rw [stateMean_updated s₀ s₁ h he n]
    abel
  have hdiff (l : ℤ) := nonlinear_mean_difference (HarmonicResidual.contextFrame c n)
    (b.frequency n) (b.phase n) (b.angularFrequency n)
    (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean s₀ n) (tripleField h n)
      (blockAmplitude b n)
    (HarmonicResidual.realCoefficients (b.pressure n)) (fun t => (hB t).add (hM t)) hh l i
  let N₀ := HarmonicResidual.nonlinearResidual (HarmonicResidual.contextFrame c n)
    (b.frequency n) (b.phase n) (b.angularFrequency n)
    (HarmonicResidual.constantVector (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean
      s₀ n))
    (blockAmplitude b n) (HarmonicResidual.realCoefficients (b.pressure n)) i
  let N₁ := HarmonicResidual.nonlinearResidual (HarmonicResidual.contextFrame c n)
    (b.frequency n) (b.phase n) (b.angularFrequency n)
    (HarmonicResidual.constantVector
      ((HarmonicResidual.contextBase c n + HarmonicResidual.stateMean s₀ n) + tripleField h n))
    (blockAmplitude b n) (HarmonicResidual.realCoefficients (b.pressure n)) i
  simp only [HarmonicResidual.LabelData.residualCoefficients, hsum]
  change HarmonicResidual.realCoefficients (N₁ - G₁ n i - A₁ n i) j x -
    HarmonicResidual.realCoefficients (N₀ - G₀ n i - A₀ n i) j x = _
  rw [← coeff_sub, ← realCoefficients_sub]
  simp only [HarmonicResidual.realCoefficients_apply, coeff_sub]
  have hdj := hdiff j
  have hdn := hdiff (-j)
  change N₁ j x - N₀ j x = meanCross c h b n i j x at hdj
  change N₁ (-j) x - N₀ (-j) x = meanCross c h b n i (-j) x at hdn
  rw [← hdj, ← hdn]
  simp only [map_sub]
  ring

/-! ## Bounds on the original coefficient domain -/

/-- The slow coefficient geometry has no artificial angular coordinate.
The actual separate angular carrier is accounted for explicitly below. -/
noncomputable def slowGeometry {s : StripData D} {κ : ℝ} (c : CorrectionState.Context D)
    (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x) : Geometry s κ where
  radius := fun _ => c.operators.radius
  radial := fun n => (HarmonicResidual.contextFrame c n).radial
  angular := fun _ _ => 0
  axial := fun n => (HarmonicResidual.contextFrame c n).axial
  radius_pos := fun _ x hx => hR x hx
  radial_class := by
    convert! graph_vector_class ho.kappa_nonneg ho.radialFrequency ho.radialProfile
      c.operators.eR c.operators.vR using 1
    ext n x
    simp [HarmonicResidual.contextFrame, smul_smul]
  axial_class := by
    simpa only [HarmonicResidual.contextFrame, ho.epsilon_eq] using
      axial_vector_class s c.operators.eZ
  inverse_radius_class := ho.invRadius

noncomputable def slowNormal {s : StripData D} {κ : ℝ} (c : CorrectionState.Context D)
    (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x) (Φ : ℕ → D → ℝ) (n : ℕ) (x : D) :
    EuclideanSpace ℝ (Fin 3) :=
  phaseNormal ((slowGeometry c ho hR).radius n) ((slowGeometry c ho hR).radial n)
    ((slowGeometry c ho hR).angular n) ((slowGeometry c ho hR).axial n) (Φ n) x

theorem tripleField_bound {s : StripData D} {H : ℝ} {h : MeanIncrementBounds.Triple D}
    (hh : MeanIncrementBounds.IncrementBounds s H h) : MeanVector s H (tripleField h) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hh.radial.map Complex.ofRealCLM
  · exact hh.angular.map Complex.ofRealCLM
  · exact hh.axial.map Complex.ofRealCLM

theorem realCoefficient_class {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    (a : ℕ → Coefficients D) (j : ℤ)
    (ha : WaveClass s P α (fun n x => a n j x))
    (han : WaveClass s P α (fun n x => a n (-j) x)) :
    WaveClass s P α (fun n x => HarmonicResidual.realCoefficients (a n) j x) := by
  apply class_congr (class_const_cmul (ha.add (class_conj han)) ((2 : ℂ)⁻¹))
  intro n x _
  exact (HarmonicResidual.realCoefficients_apply (a n) j x).symm

theorem blockAmplitude_class {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α) {j : ℤ} (hj : j ≠ 0) :
    WaveVector s P α (fun n x i => blockAmplitude b n i j x) := by
  intro i
  exact realCoefficient_class (fun n => b.velocity n i) j (hb i j hj)
    (hb i (-j) (neg_ne_zero.mpr hj))

/-- The separate angular phase term has the same carrier loss as the slow phase term. -/
noncomputable def angularCarrierTerm (c : CorrectionState.Context D)
    (b : CorrectionState.HarmonicBlock D) (h : MeanIncrementBounds.Triple D) (j : ℤ)
    (n : ℕ) (x : D) (i : Fin 3) : ℂ :=
  phaseFactor ((b.angularFrequency n : ℝ) * (j : ℝ)) *
    (tripleField h n x 1 / (c.operators.radius x : ℂ)) * blockAmplitude b n i j x

theorem meanCross_eq {s : StripData D} {κ : ℝ} (c : CorrectionState.Context D)
    (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (h : MeanIncrementBounds.Triple D) (b : CorrectionState.HarmonicBlock D)
    (j : ℤ) (n : ℕ) (x : D) (i : Fin 3) :
    meanCross c h b n i j x =
      waveMeanCoefficient (slowGeometry c ho hR) b.phase (fun n => b.frequency n * (j : ℝ))
        (tripleField h) (fun n x i => blockAmplitude b n i j x) n x i +
        angularCarrierTerm c b h j n x i := by
  simp only [meanCross, crossCoefficients, coeff_add, transport_constant_left,
    transport_constant_right,
    derivativeCoefficient, waveMeanCoefficient, strippedTransport, normalDot, phaseNormal,
    slowGeometry, HarmonicResidual.contextFrame, angularCarrierTerm, phaseFactor,
    along, map_zero, zero_mul,
    Complex.ofReal_mul, Complex.ofReal_intCast, Int.cast_mul, div_eq_mul_inv]
  simp only [ Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Complex.ofReal_zero, zero_mul,
      add_zero]
  ring

theorem angularCarrierTerm_class {s : StripData D} {κ α H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {h : MeanIncrementBounds.Triple D} (hh : MeanIncrementBounds.IncrementBounds s H h)
    {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    WaveClass s P (α + H - 1 / 2) (fun n x => angularCarrierTerm c b h j n x i) := by
  have hm := tripleField_bound hh
  have ha := blockAmplitude_class hb hj
  have hν : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ) * (j : ℝ)) :=
    bandBound_frequency hkp (abs_nonneg (j : ℝ)) (fun _ => le_rfl)
  have hf := phaseFactor_class (class_div_radius (slowGeometry c ho hR) hm.2.1) hν
  have he := mean_wave_cmul hf (ha i) ho.weight_le_one
  convert! he using 1
  ring

theorem meanCross_class {s : StripData D} {κ α H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {h : MeanIncrementBounds.Triple D} (hh : MeanIncrementBounds.IncrementBounds s H h)
    {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α)
    (hN : ∀ i, UnweightedClass s 0 (fun n x => slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    WaveClass s P (α + H - 1 / 2) (fun n x => meanCross c h b n i j x) := by
  have hν : BandBound s (-(1 / 2)) (fun n => b.frequency n * (j : ℝ)) :=
    bandBound_frequency hk (abs_nonneg (j : ℝ)) (fun _ => le_rfl)
  have hs := wave_mean_bound (slowGeometry c ho hR) ho.kappa_nonneg hκ
    (tripleField_bound hh) (blockAmplitude_class hb hj) hN hν ho.weight_le_one hP i
  have hθ := angularCarrierTerm_class c ho hR hh hb hkp hj i
  apply class_congr (hs.add hθ)
  intro n x _
  exact (meanCross_eq c ho hR h b j n x i).symm

theorem realMeanCross_class {s : StripData D} {κ α H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {h : MeanIncrementBounds.Triple D} (hh : MeanIncrementBounds.IncrementBounds s H h)
    {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α)
    (hN : ∀ i, UnweightedClass s 0 (fun n x => slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    WaveClass s P (α + H - 1 / 2)
      (fun n x => HarmonicResidual.realCoefficients (meanCross c h b n i) j x) :=
  realCoefficient_class (fun n => meanCross c h b n i) j
    (meanCross_class c ho hκ hR hh hb hN hk hkp hP hj i)
    (meanCross_class c ho hκ hR hh hb hN hk hkp hP (neg_ne_zero.mpr hj) i)

/-! ## The actual output residual blocks -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant_apply_of_ne (a : Coefficients D) {j : ℤ} (hj : j ≠ 0) (x : D) :
    HarmonicResidual.nonconstant a j x = a j x := by
  change a.coeff.erase 0 j x = a.coeff j x
  rw [Finsupp.erase_ne hj]

theorem residualBlock_mean_update (c : CorrectionState.Context D) (s₀ s₁ : CorrectionState.State D)
    (h : MeanIncrementBounds.Triple D) (he : s₁.mean = MeanIncrementBounds.updated s₀.mean h)
    (b : CorrectionState.HarmonicBlock D) (G₀ G₁ A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (n : ℕ) {x : D}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => HarmonicResidual.contextBase c n y i) x)
    (hM : ∀ i, DifferentiableAt ℝ (fun y => HarmonicResidual.stateMean s₀ n y i) x)
    (hh : ∀ i, DifferentiableAt ℝ (fun y => tripleField h n y i) x) (j : ℤ) (i : Fin 3) :
    (HarmonicResidual.residualBlock c s₁ b G₁ A₁).velocity n i j x -
      (HarmonicResidual.residualBlock c s₀ b G₀ A₀).velocity n i j x =
      HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients
        (meanCross c h b n i - (G₁ n i - G₀ n i) - (A₁ n i - A₀ n i))) j x := by
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.residualBlock_zero_mode, HarmonicResidual.nonconstant]
  · change HarmonicResidual.nonconstant _ j x - HarmonicResidual.nonconstant _ j x = _
    simp only [nonconstant_apply_of_ne _ hj]
    exact residualCoefficients_mean_update c s₀ s₁ h he b G₀ G₁ A₀ A₁ n hB hM hh j i

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_zero_coefficient {a : Coefficients D} (ha : BandLimited a 0)
    {j : ℤ} (hj : j ≠ 0) : a j = 0 := by
  have hnj : j ∉ a.support := by
    intro hmem
    exact hj (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero (ha j hmem)))
  exact Finsupp.notMem_support_iff.mp hnj

/-- An axisymmetric alias change has no effect on nonzero harmonics.
The Gaussian field is unchanged, so it cancels without a size assumption. -/
theorem residualBlock_axisymmetric_alias_update
    (c : CorrectionState.Context D) (s₀ s₁ : CorrectionState.State D)
    (h : MeanIncrementBounds.Triple D) (he : s₁.mean = MeanIncrementBounds.updated s₀.mean h)
    (b : CorrectionState.HarmonicBlock D) (G A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0) (n : ℕ) {x : D}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => HarmonicResidual.contextBase c n y i) x)
    (hM : ∀ i, DifferentiableAt ℝ (fun y => HarmonicResidual.stateMean s₀ n y i) x)
    (hh : ∀ i, DifferentiableAt ℝ (fun y => tripleField h n y i) x)
    {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    (HarmonicResidual.residualBlock c s₁ b G A₁).velocity n i j x -
      (HarmonicResidual.residualBlock c s₀ b G A₀).velocity n i j x =
      HarmonicResidual.realCoefficients (meanCross c h b n i) j x := by
  have hzj := congrArg (fun f : D → ℂ => f x) (band_zero_coefficient (hA n i) hj)
  have hzn := congrArg (fun f : D → ℂ => f x) (band_zero_coefficient (hA n i) (neg_ne_zero.mpr hj))
  change A₁ n i j x - A₀ n i j x = 0 at hzj
  change A₁ n i (-j) x - A₀ n i (-j) x = 0 at hzn
  rw [residualBlock_mean_update c s₀ s₁ h he b G G A₀ A₁ n hB hM hh j i,
    nonconstant_apply_of_ne _ hj]
  simp only [sub_self, sub_zero, HarmonicResidual.realCoefficients_apply, coeff_sub,
    hzj, hzn]

theorem tripleField_smooth {U : Set D} {h : MeanIncrementBounds.Triple D}
    (hh : MeanIncrementBounds.SmoothTriple U h) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => tripleField h n x i) U := by
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hh.radial n)
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hh.angular n)
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hh.axial n)

/-- The resulting all-order class is derived for the actual residual-block
coefficient difference, with no estimate assumed for that difference. -/
theorem residualBlock_mean_update_class {s : StripData D} {κ α H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (s₀ s₁ : CorrectionState.State D) (h : MeanIncrementBounds.Triple D)
    (he : s₁.mean = MeanIncrementBounds.updated s₀.mean h)
    (hbase : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hmean : MeanIncrementBounds.SmoothTriple s.domain s₀.mean)
    (hh : MeanIncrementBounds.IncrementBounds s H h)
    (b : CorrectionState.HarmonicBlock D) (hb : b.WaveBounds s P α)
    (hN : ∀ i, UnweightedClass s 0 (fun n x => slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0) {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    WaveClass s P (α + H - 1 / 2) (fun n x =>
      (HarmonicResidual.residualBlock c s₁ b G A₁).velocity n i j x -
      (HarmonicResidual.residualBlock c s₀ b G A₀).velocity n i j x) := by
  apply class_congr (realMeanCross_class c ho hκ hR hh hb hN hk hkp hP hj i)
  intro n x hx
  symm
  apply residualBlock_axisymmetric_alias_update c s₀ s₁ h he b G A₀ A₁ hA n
  · intro t
    exact ((tripleField_smooth hbase n t).contDiffAt (s.isOpen_domain.mem_nhds
      hx)).differentiableAt (by simp)
  · intro t
    exact ((tripleField_smooth hmean n t).contDiffAt (s.isOpen_domain.mem_nhds
      hx)).differentiableAt (by simp)
  · intro t
    exact ((tripleField_smooth hh.smooth n t).contDiffAt (s.isOpen_domain.mem_nhds
      hx)).differentiableAt (by simp)
  · exact hj

noncomputable def residualDifferenceBlock (c : CorrectionState.Context D)
    (s₀ s₁ : CorrectionState.State D) (b : CorrectionState.HarmonicBlock D)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D) : CorrectionState.HarmonicBlock D where
  velocity := fun n i => (HarmonicResidual.residualBlock c s₁ b G A₁).velocity n i -
    (HarmonicResidual.residualBlock c s₀ b G A₀).velocity n i
  pressure := fun _ => 0
  frequency := b.frequency
  phase := b.phase
  angularFrequency := b.angularFrequency

theorem residualDifferenceBlock_field (c : CorrectionState.Context D)
    (s₀ s₁ : CorrectionState.State D) (b : CorrectionState.HarmonicBlock D)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (residualDifferenceBlock c s₀ s₁ b G A₀ A₁).oscillation n x i =
      (HarmonicResidual.residualBlock c s₁ b G A₁).oscillation n x i -
      (HarmonicResidual.residualBlock c s₀ b G A₀).oscillation n x i := by
  simp only [residualDifferenceBlock, CorrectionState.HarmonicBlock.oscillation,
    HarmonicResidual.field_sub, Complex.sub_re]
  rfl

theorem residualDifferenceBlock_class {s : StripData D} {κ α H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (s₀ s₁ : CorrectionState.State D) (h : MeanIncrementBounds.Triple D)
    (he : s₁.mean = MeanIncrementBounds.updated s₀.mean h)
    (hbase : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hmean : MeanIncrementBounds.SmoothTriple s.domain s₀.mean)
    (hh : MeanIncrementBounds.IncrementBounds s H h)
    (b : CorrectionState.HarmonicBlock D) (hb : b.WaveBounds s P α)
    (hN : ∀ i, UnweightedClass s 0 (fun n x => slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0) :
    (residualDifferenceBlock c s₀ s₁ b G A₀ A₁).WaveBounds s P (α + H - 1 / 2) := by
  intro i j hj
  exact residualBlock_mean_update_class c ho hκ hR s₀ s₁ h he hbase hmean hh b hb hN hk hkp hP
    G A₀ A₁ hA hj i

/-! ## Frequency support and physical cross-advection -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant_sub (a b : Coefficients D) :
    HarmonicResidual.nonconstant (a - b) =
      HarmonicResidual.nonconstant a - HarmonicResidual.nonconstant b := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.nonconstant]
  · simp only [nonconstant_apply_of_ne _ hj, coeff_sub]

noncomputable def transportDifference (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (B₀ B₁ : D → ComplexVector)
    (a : HarmonicResidual.VectorCoefficients D) (i : Fin 3) : Coefficients D :=
  (HarmonicResidual.transport g k Φ kp (HarmonicResidual.constantVector B₁) a i -
    HarmonicResidual.transport g k Φ kp (HarmonicResidual.constantVector B₀) a i) +
  (HarmonicResidual.transport g k Φ kp a (HarmonicResidual.constantVector B₁) i -
    HarmonicResidual.transport g k Φ kp a (HarmonicResidual.constantVector B₀) i)

theorem nonlinear_difference_algebra (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (B₀ B₁ : D → ComplexVector)
    (a : HarmonicResidual.VectorCoefficients D) (p : Coefficients D) (i : Fin 3) :
    HarmonicResidual.nonlinearResidual g k Φ kp (HarmonicResidual.constantVector B₁) a p i -
      HarmonicResidual.nonlinearResidual g k Φ kp (HarmonicResidual.constantVector B₀) a p i =
        transportDifference g k Φ kp B₀ B₁ a i := by
  unfold HarmonicResidual.nonlinearResidual HarmonicResidual.linearResidual transportDifference
  abel

theorem transportDifference_band (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (B₀ B₁ : D → ComplexVector)
    {a : HarmonicResidual.VectorCoefficients D} {N : ℕ} (ha : ∀ i, BandLimited (a i) N) (i : Fin 3)
      :
    BandLimited (transportDifference g k Φ kp B₀ B₁ a i) N := by
  have hleft (B : D → ComplexVector) :
      BandLimited (HarmonicResidual.transport g k Φ kp (HarmonicResidual.constantVector B) a i) N
        := by
    have h := HarmonicResidual.band_transport g k Φ kp (fun j => band_constantCoefficient (fun x =>
      B x j)) ha i
    simp only [zero_add] at h
    exact h
  have hright (B : D → ComplexVector) :
      BandLimited (HarmonicResidual.transport g k Φ kp a (HarmonicResidual.constantVector B) i) N
        := by
    have h := HarmonicResidual.band_transport g k Φ kp ha (fun j => band_constantCoefficient (fun x
      => B x j)) i
    simp only [add_zero] at h
    exact h
  exact (HarmonicResidual.band_sub (hleft B₁) (hleft B₀)).add
    (HarmonicResidual.band_sub (hright B₁) (hright B₀))

theorem residualDifferenceBlock_algebra (c : CorrectionState.Context D)
    (s₀ s₁ : CorrectionState.State D) (b : CorrectionState.HarmonicBlock D)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D) (n : ℕ) (i : Fin 3) :
    (residualDifferenceBlock c s₀ s₁ b G A₀ A₁).velocity n i =
      HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients
        (transportDifference (HarmonicResidual.contextFrame c n) (b.frequency n) (b.phase n)
          (b.angularFrequency n)
          (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean s₀ n)
          (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean s₁ n)
          (blockAmplitude b n) i - (A₁ n i - A₀ n i))) := by
  let N₀ := HarmonicResidual.nonlinearResidual (HarmonicResidual.contextFrame c n)
    (b.frequency n) (b.phase n) (b.angularFrequency n)
    (HarmonicResidual.constantVector (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean
      s₀ n))
    (blockAmplitude b n) (HarmonicResidual.realCoefficients (b.pressure n)) i
  let N₁ := HarmonicResidual.nonlinearResidual (HarmonicResidual.contextFrame c n)
    (b.frequency n) (b.phase n) (b.angularFrequency n)
    (HarmonicResidual.constantVector (HarmonicResidual.contextBase c n + HarmonicResidual.stateMean
      s₁ n))
    (blockAmplitude b n) (HarmonicResidual.realCoefficients (b.pressure n)) i
  change HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients (N₁ - G n i - A₁ n i)) -
    HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients (N₀ - G n i - A₀ n i)) = _
  rw [← nonconstant_sub, ← realCoefficients_sub]
  congr 2
  calc
    (N₁ - G n i - A₁ n i) - (N₀ - G n i - A₀ n i) = (N₁ - N₀) - (A₁ n i - A₀ n i) := by abel
    _ = _ := by rw [nonlinear_difference_algebra]

/-- A mean-only update preserves the existing harmonic-value bound. -/
theorem residualDifferenceBlock_band (c : CorrectionState.Context D)
    (s₀ s₁ : CorrectionState.State D) (b : CorrectionState.HarmonicBlock D)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D) {N : ℕ} (hb : b.BandLimited N)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0) :
    (residualDifferenceBlock c s₀ s₁ b G A₀ A₁).BandLimited N := by
  refine ⟨?_, fun _ => HarmonicResidual.band_zero N⟩
  intro n i
  rw [residualDifferenceBlock_algebra]
  exact HarmonicResidual.band_nonconstant (HarmonicResidual.band_realCoefficients
    (HarmonicResidual.band_sub (transportDifference_band _ _ _ _ _ _
      (fun j => HarmonicResidual.band_realCoefficients (hb.1 n j)) i)
      ((hA n i).mono (Nat.zero_le N))))

theorem residualDifferenceBlock_conjugate (c : CorrectionState.Context D)
    (s₀ s₁ : CorrectionState.State D) (b : CorrectionState.HarmonicBlock D)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D) (n : ℕ) (i : Fin 3) :
    ConjugateSymmetric ((residualDifferenceBlock c s₀ s₁ b G A₀ A₁).velocity n i) := by
  intro j x
  simp only [residualDifferenceBlock, coeff_sub,
    HarmonicResidual.residualBlock_conjugate c s₁ b G A₁ n i j x,
    HarmonicResidual.residualBlock_conjugate c s₀ b G A₀ n i j x, map_sub]

theorem residualDifferenceBlock_zero_mode (c : CorrectionState.Context D)
    (s₀ s₁ : CorrectionState.State D) (b : CorrectionState.HarmonicBlock D)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D) (n : ℕ) (i : Fin 3) :
    (residualDifferenceBlock c s₀ s₁ b G A₀ A₁).velocity n i 0 = 0 := by
  change (HarmonicResidual.residualBlock c s₁ b G A₁).velocity n i 0 -
    (HarmonicResidual.residualBlock c s₀ b G A₀).velocity n i 0 = 0
  rw [HarmonicResidual.residualBlock_zero_mode, HarmonicResidual.residualBlock_zero_mode, sub_self]

/-- The same finite coefficients evaluate to the two actual cross-advection fields. -/
theorem crossCoefficients_field {U : Set D} (hU : IsOpen U) (g : HarmonicResidual.Frame D)
    (k : ℝ) {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (kp : ℤ)
    (m : D → ComplexVector) (hm : ∀ i, ContDiffOn ℝ ∞ (fun x => m x i) U)
    (a : HarmonicResidual.VectorCoefficients D) (ha : ∀ i, HarmonicResidual.SmoothCoefficients U (a
      i))
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) :
    HarmonicResidual.vectorField (crossCoefficients g k Φ kp m a) k Φ kp x =
      LinearWaveResidual.transport (fun y => g.radius y.1) (HarmonicResidual.liftDirection g.radial)
        HarmonicResidual.angularDirection (HarmonicResidual.liftDirection g.axial)
        (fun y => m y.1) (HarmonicResidual.vectorField a k Φ kp) x +
      LinearWaveResidual.transport (fun y => g.radius y.1) (HarmonicResidual.liftDirection g.radial)
        HarmonicResidual.angularDirection (HarmonicResidual.liftDirection g.axial)
        (HarmonicResidual.vectorField a k Φ kp) (fun y => m y.1) x := by
  have hm' : ∀ i, HarmonicResidual.SmoothCoefficients U (HarmonicResidual.constantVector m i) :=
    fun i => HarmonicResidual.smoothCoefficients_constant (hm i)
  have hleft := HarmonicResidual.field_transport hU g (HarmonicResidual.constantVector m) ha hΦ k
    kp hx
  have hright := HarmonicResidual.field_transport hU g a hm' hΦ k kp hx
  have he : HarmonicResidual.vectorField (HarmonicResidual.constantVector m) k Φ kp =
      fun y : D × ℝ => m y.1 := by
    funext y
    exact HarmonicResidual.vectorField_constantVector m k Φ kp y
  rw [he] at hleft hright
  ext i
  change field (_ + _) k Φ kp x = _
  rw [HarmonicResidual.field_add]
  exact congrFun (congrArg₂ (· + ·) hleft hright) i

/-- The computed block differences reconstruct the actual change in the good
nonconstant residual. This is an identity, with no uniform sum estimate assumed. -/
theorem grouped_wave_change {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : CorrectionState.Context D} {s₀ s₁ : CorrectionState.State D}
    {labels : ℕ → Finset ι} {blocks : ι → CorrectionState.HarmonicBlock D}
    {G A₀ A₁ : ι → HarmonicResidual.BlockCoefficients D}
    (hrep₀ : HarmonicResidual.BlockRepresentation labels blocks G A₀ s₀)
    (hrep₁ : HarmonicResidual.BlockRepresentation labels blocks G A₁ s₁) {n : ℕ}
    (h₀ : HarmonicResidual.ExtractionRegular U c s₀ labels blocks G A₀ n)
    (h₁ : HarmonicResidual.ExtractionRegular U c s₁ labels blocks G A₁ n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    HarmonicResidual.stateGoodWaveResidual c s₁ n x i -
      HarmonicResidual.stateGoodWaveResidual c s₀ n x i =
      ∑ l ∈ labels n, (residualDifferenceBlock c s₀ s₁ (blocks l) (G l) (A₀ l) (A₁ l)).oscillation
        n x i := by
  rw [HarmonicResidual.stateGoodWaveResidual_grouped hU hrep₁ h₁ hx i,
    HarmonicResidual.stateGoodWaveResidual_grouped hU hrep₀ h₀ hx i]
  simp only [residualDifferenceBlock_field, Finset.sum_sub_distrib]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- A recomputed mean pressure is unrestricted in this application; its
contribution is in the mean residual, not in the fixed label's wave block. -/
theorem stateMean_addIncrement (s₀ : CorrectionState.State D) (h : MeanIncrementBounds.Triple D)
    (δp : CorrectionState.ScalarField D) (δe : CorrectionState.ExcludedErrors D) :
    (s₀.addIncrement h δp 0 0 δe).mean = MeanIncrementBounds.updated s₀.mean h := rfl

end NavierStokes.HarmonicMeanInteraction
