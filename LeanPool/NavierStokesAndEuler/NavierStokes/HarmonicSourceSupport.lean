/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodizedWaveBounds

/-!
# Support of the actual harmonic residual supplied to a copy solve

The support conclusions below are derived from the literal harmonic
derivatives, convolutions, real projection, and removal of the zero mode.
Only nonzero input harmonics need be localized: a spatially global zero
mode, such as an axisymmetric pressure alias, does not create a new slot.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.HarmonicSourceSupport

open Set Function Filter HarmonicFields HarmonicResidual HarmonicCalculus
open scoped Topology ContDiff BigOperators ComplexConjugate

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Every nonzero harmonic vanishes outside the specified spatial set.
The zero coefficient is unrestricted. -/
def NonzeroSupported (K : Set D) (c : HarmonicFields.Coefficients D) : Prop :=
  ∀ j : ℤ, j ≠ 0 → ∀ x : D, x ∉ K → c j x = 0

namespace NonzeroSupported

variable {K : Set D} {c d : HarmonicFields.Coefficients D}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem zero : NonzeroSupported K (0 : HarmonicFields.Coefficients D) := by
  intro j hj x hx
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem mono (hc : NonzeroSupported K c) {L : Set D} (hKL : K ⊆ L) :
    NonzeroSupported L c := fun j hj x hx => hc j hj x (fun hk => hx (hKL hk))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem add (hc : NonzeroSupported K c) (hd : NonzeroSupported K d) :
    NonzeroSupported K (c + d) := by
  intro j hj x hx
  change c j x + d j x = 0
  rw [hc j hj x hx, hd j hj x hx, add_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem neg (hc : NonzeroSupported K c) : NonzeroSupported K (-c) := by
  intro j hj x hx
  change -c j x = 0
  rw [hc j hj x hx, neg_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem sub (hc : NonzeroSupported K c) (hd : NonzeroSupported K d) :
    NonzeroSupported K (c - d) := by
  simpa only [sub_eq_add_neg] using hc.add hd.neg

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- In a nonzero convolution mode, at least one input index is nonzero. -/
theorem mul (hc : NonzeroSupported K c) (hd : NonzeroSupported K d) :
    NonzeroSupported K (c * d) := by
  intro j hj x hx
  rw [HarmonicFields.convolution_apply]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp only [sub_zero, hd j hj x hx, mul_zero]
  · simp only [hc i hi0 x hx, zero_mul]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem boundConstant (f : D → ℂ) : NonzeroSupported K (constantCoefficient f) := by
  intro j hj x hx
  simp [constantCoefficient, hj]

omit [NormedSpace ℝ D] in
theorem coefficient_germ (hc : NonzeroSupported K c) (hK : IsClosed K)
    {j : ℤ} (hj : j ≠ 0) {x : D} (hx : x ∉ K) :
    c j =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
  exact hc j hj y hy

/-- Actual Fréchet differentiation is local, including when no regularity
of the coefficient is assumed on the other side of the support. -/
theorem differentiate (hc : NonzeroSupported K c) (hK : IsClosed K)
    (V : D → D) (k : ℝ) (Φ : D → ℝ) : NonzeroSupported K (HarmonicFields.differentiate V k Φ c) :=
        by
  intro j hj x hx
  have he := hc.coefficient_germ hK hj hx
  simp only [differentiate_apply, derivativeCoefficient, along, he.fderiv_eq,
    fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, hc j hj x hx, mul_zero, add_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angular (hc : NonzeroSupported K c) (kp : ℤ) :
    NonzeroSupported K (angularDifferentiate kp c) := by
  intro j hj x hx
  simp only [angularDifferentiate_apply, hc j hj x hx, mul_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realProjection (hc : NonzeroSupported K c) : NonzeroSupported K (realCoefficients c) := by
  intro j hj x hx
  simp only [realCoefficients_apply, hc j hj x hx, hc (-j) (neg_ne_zero.mpr hj) x hx,
    map_zero, add_zero, mul_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant (hc : NonzeroSupported K c) : NonzeroSupported K (HarmonicResidual.nonconstant
    c) := by
  intro j hj x hx
  simpa only [HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_ne hj]
      using hc j hj x hx

omit [NormedSpace ℝ D] in
theorem tsupport (hc : NonzeroSupported K c) (hK : IsClosed K) {j : ℤ} (hj : j ≠ 0) :
    _root_.tsupport (c j) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (hc j hj x hn)

omit [NormedSpace ℝ D] in
theorem of_tsupport (hc : ∀ j : ℤ, j ≠ 0 → _root_.tsupport (c j) ⊆ K) :
    NonzeroSupported K c := by
  intro j hj x hx
  by_contra hn
  exact hx (hc j hj (subset_tsupport (c j) hn))

end NonzeroSupported

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem rotate_supported {K : Set D} {a : HarmonicResidual.VectorCoefficients D}
    (ha : ∀ i, NonzeroSupported K (a i)) : ∀ i, NonzeroSupported K (rotate a i) := by
  intro i
  fin_cases i
  · exact (ha 1).neg
  · exact ha 0
  · exact NonzeroSupported.zero

theorem scalarLaplacian_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {c : HarmonicFields.Coefficients D} (hc : NonzeroSupported K c) :
    NonzeroSupported K (scalarLaplacian g k Φ kp c) :=
  (((hc.differentiate hK g.radial k Φ).differentiate hK g.radial k Φ).add
    ((NonzeroSupported.boundConstant _).mul (hc.differentiate hK g.radial k Φ))).add
      ((NonzeroSupported.boundConstant _).mul ((hc.angular kp).angular kp)) |>.add
        ((hc.differentiate hK g.axial k Φ).differentiate hK g.axial k Φ)

theorem vectorLaplacian_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {a : HarmonicResidual.VectorCoefficients D} (ha : ∀ i, NonzeroSupported K (a i)) :
    ∀ i, NonzeroSupported K (vectorLaplacian g k Φ kp a i) := fun i =>
  (scalarLaplacian_supported hK g k Φ kp (ha i)).add
    ((NonzeroSupported.boundConstant _).mul (((NonzeroSupported.boundConstant _).mul
      (rotate_supported (fun j => (ha j).angular kp) i)).add (rotate_supported (rotate_supported
          ha) i)))

theorem transport_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {a b : HarmonicResidual.VectorCoefficients D}
    (ha : ∀ i, NonzeroSupported K (a i)) (hb : ∀ i, NonzeroSupported K (b i)) :
    ∀ i, NonzeroSupported K (HarmonicResidual.transport g k Φ kp a b i) := by
  intro i
  exact (((ha 0).mul ((hb i).differentiate hK g.radial k Φ)).add
    (((ha 1).mul (NonzeroSupported.boundConstant _)).mul
      (((hb i).angular kp).add (rotate_supported hb i)))).add
        ((ha 2).mul ((hb i).differentiate hK g.axial k Φ))

theorem gradient_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {p : HarmonicFields.Coefficients D} (hp : NonzeroSupported K p) :
    ∀ i, NonzeroSupported K (HarmonicResidual.gradient g k Φ kp p i) := by
  intro i
  fin_cases i
  · exact hp.differentiate hK g.radial k Φ
  · exact (NonzeroSupported.boundConstant _).mul (hp.angular kp)
  · exact hp.differentiate hK g.axial k Φ

theorem nonlinearResidual_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {B a : HarmonicResidual.VectorCoefficients D} {p : HarmonicFields.Coefficients D}
    (hB : ∀ i, NonzeroSupported K (B i)) (ha : ∀ i, NonzeroSupported K (a i))
    (hp : NonzeroSupported K p) :
    ∀ i, NonzeroSupported K (HarmonicResidual.nonlinearResidual g k Φ kp B a p i) := fun i =>
  (((((ha i).differentiate hK g.time k Φ).add (transport_supported hK g k Φ kp hB ha i)).add
    (transport_supported hK g k Φ kp ha hB i)).add (gradient_supported hK g k Φ kp hp i) |>.sub
      ((NonzeroSupported.boundConstant _).mul (vectorLaplacian_supported hK g k Φ kp ha i))).add
        (transport_supported hK g k Φ kp ha ha i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_sub (c d : HarmonicFields.Coefficients D) :
    realCoefficients (c - d) = realCoefficients c - realCoefficients d := by
  ext j x
  change realCoefficients (c - d) j x = realCoefficients c j x - realCoefficients d j x
  simp only [realCoefficients_apply]
  change (2 : ℂ)⁻¹ * (c j x - d j x + conj (c (-j) x - d (-j) x)) =
    (2 : ℂ)⁻¹ * (c j x + conj (c (-j) x)) -
    (2 : ℂ)⁻¹ * (d j x + conj (d (-j) x))
  rw [map_sub]
  ring

theorem nonlinear_ofBlock_supported {K : Set D} (hK : IsClosed K)
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (b.velocity n i)) (hp : NonzeroSupported K (b.pressure n)) :
    ∀ i, NonzeroSupported K
      (HarmonicResidual.nonlinearResidual (contextFrame c n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (constantVector (contextBase c n + stateMean u n))
        (ofBlock b G A n).velocity (ofBlock b G A n).pressure i) :=
  nonlinearResidual_supported hK _ _ _ _ (fun _ => NonzeroSupported.boundConstant _)
    (fun i => (hv i).realProjection) hp.realProjection

/-- The exact excluded nonzero coefficient.  Its mean part is removed
even when that part is not localized in a native slot. -/
noncomputable def excludedSource (G A : HarmonicResidual.BlockCoefficients D)
    (j : ℤ) (n : ℕ) (x : D) : ComplexVector := fun i =>
  -(nonconstant (realCoefficients (G n i))) j x -
    (nonconstant (realCoefficients (A n i))) j x

theorem residualSource_apply_ne_zero (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {j : ℤ} (hj : j ≠ 0) (n : ℕ) (x : D) (i : Fin 3) :
    ParticularWaveAssembly.residualSource c u b G A j n x i =
      realCoefficients (HarmonicResidual.nonlinearResidual (contextFrame c n)
        (b.frequency n) (b.phase n) (b.angularFrequency n)
        (constantVector (contextBase c n + stateMean u n))
        (ofBlock b G A n).velocity (ofBlock b G A n).pressure i) j x -
      realCoefficients (G n i) j x - realCoefficients (A n i) j x := by
  change nonconstant (realCoefficients (_ - _ - _)) j x = _
  simp only [HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_ne hj,
      realCoefficients_sub,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Pi.sub_apply]
  rfl

/-- Outside the wave and pressure cells, the literal residual source is
exactly the negative excluded nonzero coefficient.  No error is discarded. -/
theorem residualSource_outside (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (b.velocity n i)) (hp : NonzeroSupported K (b.pressure n))
    (j : ℤ) {x : D} (hx : x ∉ K) :
    ParticularWaveAssembly.residualSource c u b G A j n x = excludedSource G A j n x := by
  by_cases hj : j = 0
  · subst j
    rw [ParticularWaveAssembly.residualSource_zero]
    ext i
    simp [excludedSource, HarmonicResidual.nonconstant]
  · ext i
    rw [residualSource_apply_ne_zero c u b G A hj]
    have hn := ((nonlinear_ofBlock_supported hK c u b G A n hv hp i).realProjection) j hj x hx
    simp only [hn, excludedSource, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase,
        Finsupp.erase_ne hj, zero_sub]

theorem residualSource_complement_germ (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (b.velocity n i)) (hp : NonzeroSupported K (b.pressure n))
    (j : ℤ) {x : D} (hx : x ∉ K) :
    ParticularWaveAssembly.residualSource c u b G A j n =ᶠ[𝓝 x] excludedSource G A j n := by
  filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
  exact residualSource_outside c u b G A hK n hv hp j hy

theorem residualSource_support (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (b.velocity n i)) (hp : NonzeroSupported K (b.pressure n))
    (hG : ∀ i, NonzeroSupported K (G n i)) (hA : ∀ i, NonzeroSupported K (A n i)) (j : ℤ) :
    support (ParticularWaveAssembly.residualSource c u b G A j n) ⊆ K := by
  intro x hx
  by_contra hnot
  apply hx
  rw [residualSource_outside c u b G A hK n hv hp j hnot]
  ext i
  by_cases hj : j = 0
  · simp [excludedSource, HarmonicResidual.nonconstant, hj]
  · simp only [excludedSource, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase,
      Finsupp.erase_ne hj,
      (hG i).realProjection j hj x hnot, (hA i).realProjection j hj x hnot, neg_zero, sub_zero,
      Pi.zero_apply]

theorem residualSource_tsupport (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (b.velocity n i)) (hp : NonzeroSupported K (b.pressure n))
    (hG : ∀ i, NonzeroSupported K (G n i)) (hA : ∀ i, NonzeroSupported K (A n i)) (j : ℤ) :
    tsupport (ParticularWaveAssembly.residualSource c u b G A j n) ⊆ K :=
  closure_minimal (residualSource_support c u b G A hK n hv hp hG hA j) hK

/-! ## Support of the actual real fields suffices -/

theorem nonlinear_ofBlock_supported_of_real {K : Set D} (hK : IsClosed K)
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (realCoefficients (b.velocity n i)))
    (hp : NonzeroSupported K (realCoefficients (b.pressure n))) :
    ∀ i, NonzeroSupported K
      (HarmonicResidual.nonlinearResidual (contextFrame c n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (constantVector (contextBase c n + stateMean u n))
        (ofBlock b G A n).velocity (ofBlock b G A n).pressure i) :=
  nonlinearResidual_supported hK _ _ _ _ (fun _ => NonzeroSupported.boundConstant _) hv hp

theorem residualSource_outside_of_real
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (realCoefficients (b.velocity n i)))
    (hp : NonzeroSupported K (realCoefficients (b.pressure n)))
    (j : ℤ) {x : D} (hx : x ∉ K) :
    ParticularWaveAssembly.residualSource c u b G A j n x = excludedSource G A j n x := by
  by_cases hj : j = 0
  · subst j
    rw [ParticularWaveAssembly.residualSource_zero]
    ext i
    simp [excludedSource, HarmonicResidual.nonconstant]
  · ext i
    rw [residualSource_apply_ne_zero c u b G A hj]
    have hn := ((nonlinear_ofBlock_supported_of_real hK c u b G A n hv hp i).realProjection)
      j hj x hx
    simp only [hn, excludedSource, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase,
        Finsupp.erase_ne hj, zero_sub]

theorem residualSource_complement_germ_of_real
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (realCoefficients (b.velocity n i)))
    (hp : NonzeroSupported K (realCoefficients (b.pressure n)))
    (j : ℤ) {x : D} (hx : x ∉ K) :
    ParticularWaveAssembly.residualSource c u b G A j n =ᶠ[𝓝 x] excludedSource G A j n := by
  filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
  exact residualSource_outside_of_real c u b G A hK n hv hp j hy

theorem residualSource_support_of_real
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (realCoefficients (b.velocity n i)))
    (hp : NonzeroSupported K (realCoefficients (b.pressure n)))
    (hG : ∀ i, NonzeroSupported K (realCoefficients (G n i)))
    (hA : ∀ i, NonzeroSupported K (realCoefficients (A n i))) (j : ℤ) :
    support (ParticularWaveAssembly.residualSource c u b G A j n) ⊆ K := by
  intro x hx
  by_contra hnot
  apply hx
  rw [residualSource_outside_of_real c u b G A hK n hv hp j hnot]
  ext i
  by_cases hj : j = 0
  · simp [excludedSource, HarmonicResidual.nonconstant, hj]
  · simp only [excludedSource, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase,
      Finsupp.erase_ne hj,
      hG i j hj x hnot, hA i j hj x hnot, neg_zero, sub_zero, Pi.zero_apply]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficient_eq_zero_of_field
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (j : ℤ) (x : D)
    (hf : ∀ θ, (HarmonicFields.field c k Φ kp (x, θ)).re = 0) :
    realCoefficients c j x = 0 := by
  rw [← extract_field (realCoefficients c) k Φ hkp j x]
  simp only [extract, field_realCoefficients, hf, Complex.ofReal_zero, zero_mul]
  simp [HarmonicFields.angularMean]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Fourier uniqueness transfers support of the evaluated real field to
its actual real-projected coefficients; no coefficient support is assumed. -/
theorem realCoefficients_supported_of_field
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) {K : Set D}
    (hf : ∀ x, x ∉ K → ∀ θ, (HarmonicFields.field c k Φ kp (x, θ)).re = 0) :
    NonzeroSupported K (realCoefficients c) :=
  fun j _ x hx => realCoefficient_eq_zero_of_field c k Φ hkp j x (hf x hx)

omit [NormedSpace ℝ D] in
theorem realCoefficients_tsupport_of_field
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) {K : Set D} (hK : IsClosed K)
    (hf : ∀ x, x ∉ K → ∀ θ, (HarmonicFields.field c k Φ kp (x, θ)).re = 0)
    (j : ℤ) : tsupport (realCoefficients c j) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (realCoefficient_eq_zero_of_field c k Φ hkp j x (hf x hn))

theorem residualSource_support_of_fields
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ) (hkp : b.angularFrequency n ≠ 0)
    (hv : ∀ x, x ∉ K → ∀ θ i, b.oscillation n (x, θ) i = 0)
    (hp : ∀ x, x ∉ K → ∀ θ, b.oscillatoryPressure n (x, θ) = 0)
    (hG : ∀ x, x ∉ K → ∀ θ i,
      (HarmonicResidual.vectorField (G n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (x, θ) i).re = 0)
    (hA : ∀ x, x ∉ K → ∀ θ i,
      (HarmonicResidual.vectorField (A n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (x, θ) i).re = 0) (j : ℤ) :
    support (ParticularWaveAssembly.residualSource c u b G A j n) ⊆ K := by
  apply residualSource_support_of_real c u b G A hK n
  · intro i
    exact realCoefficients_supported_of_field _ _ _ hkp (fun x hx θ => hv x hx θ i)
  · exact realCoefficients_supported_of_field _ _ _ hkp hp
  · intro i
    exact realCoefficients_supported_of_field _ _ _ hkp (fun x hx θ => hG x hx θ i)
  · intro i
    exact realCoefficients_supported_of_field _ _ _ hkp (fun x hx θ => hA x hx θ i)

/-! ## The uncovered source is estimated from its explicit excluded errors -/

theorem residualSource_complementJets
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {I : Type*} (K : PeriodizedWaveBounds.Cells D I)
    (hv : ∀ n i, NonzeroSupported (⋃ a, K.carrier n a) (realCoefficients (b.velocity n i)))
    (hp : ∀ n, NonzeroSupported (⋃ a, K.carrier n a) (realCoefficients (b.pressure n)))
    (j : ℤ) {s : WeightedClasses.StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    (he : WeightedClasses.MemClass s w α (excludedSource G A j)) :
    PeriodizedWaveBounds.ComplementJets s w α K.carrier
      (ParticularWaveAssembly.residualSource c u b G A j) := by
  have hg (n : ℕ) (x : D) (hx : ∀ a, x ∉ K.carrier n a) :
      ParticularWaveAssembly.residualSource c u b G A j n =ᶠ[𝓝 x] excludedSource G A j n :=
    residualSource_complement_germ_of_real c u b G A
      ((K.locallyFinite n).isClosed_iUnion (K.closed n)) n (hv n) (hp n) j (by simpa using hx)
  constructor
  · intro n x hx hK
    exact ((he.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).congr_of_eventuallyEq
      (hg n x hK)
  · intro m
    obtain ⟨C, hC, p, hb⟩ := he.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro n x hx hK a ha
    rw [PeriodizedWaveBounds.jets_eq_of_germ (hg n x hK) a]
    exact hb n x hx a ha

/-! ## Coverage by all actual native copies -/

section NativeCoverage

open CommonCoverSolve TorusInverse TorusAverages

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Native union, given by `⋃ k : Frequency, PeriodizedWaveBounds.nativeCell g K k`. -/
noncomputable def nativeUnion (g : Geometry) (K : Set Plane) : Set (P × Plane) :=
  ⋃ k : Frequency, PeriodizedWaveBounds.nativeCell g K k

omit [NormedSpace ℝ P] in
theorem nativeUnion_closed (g : Geometry) {K : Set Plane} (hK : IsCompact K) :
    IsClosed (nativeUnion (P := P) g K) :=
  (PeriodizedWaveBounds.nativeCell_locallyFinite g hK).isClosed_iUnion
    (PeriodizedWaveBounds.nativeCell_closed g hK.isClosed)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The union of copy-coordinate cells is precisely the periodic lift of
the native cell's actual geometric image. -/
theorem mem_nativeUnion_iff (g : Geometry) (K : Set Plane) (z : P × Plane) :
    z ∈ nativeUnion g K ↔ z.2 ∈ SlotGeometry.liftedSupport g.gap
      ((fun w => g.center + g.basis w) '' K) := by
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    refine ⟨g.center + g.basis (g.coordinates k z.2), ⟨g.coordinates k z.2, hk, rfl⟩, ?_⟩
    have he : coverPower g.gap z.2 - (g.center + g.basis (g.coordinates k z.2)) =
        latticePoint k := by
      rw [ParticularWaveAssembly.native_coordinate_image]
      have hn : latticePoint (-k) = -latticePoint k := by ext <;> simp [latticePoint]
      rw [hn]
      abel
    change (SlotGeometry.cover ^ g.gap) z.2 -
      (g.center + g.basis (g.coordinates k z.2)) ∈ SlotGeometry.lattice
    rw [← coverPower_apply, he]
    exact ⟨⟨k.1, rfl⟩, ⟨k.2, rfl⟩⟩
  · rintro ⟨w, ⟨v, hv, rfl⟩, hz⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
    have he : coverPower g.gap z.2 - (g.center + g.basis v) = latticePoint (a, b) := by
      rw [coverPower_apply]
      exact Prod.ext ha.symm hb.symm
    refine mem_iUnion.mpr ⟨(a, b), ?_⟩
    change g.coordinates (a, b) z.2 ∈ K
    have hc : g.coordinates (a, b) z.2 = v := by
      unfold Geometry.coordinates
      rw [show coverPower g.gap z.2 - g.center - latticePoint (a, b) = g.basis v from by
        rw [(sub_eq_iff_eq_add).mp he]
        abel]
      exact g.basis.symm_apply_apply v
    rwa [hc]

theorem sourceFamily_covered
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane))
    (g : ℕ → Geometry) (K : ℕ → Set Plane) (hK : ∀ n, IsCompact (K n))
    (hv : ∀ n i, NonzeroSupported (nativeUnion (g n) (K n)) (realCoefficients (b.velocity n i)))
    (hp : ∀ n, NonzeroSupported (nativeUnion (g n) (K n)) (realCoefficients (b.pressure n)))
    (hG : ∀ n i, NonzeroSupported (nativeUnion (g n) (K n)) (realCoefficients (G n i)))
    (hA : ∀ n i, NonzeroSupported (nativeUnion (g n) (K n)) (realCoefficients (A n i)))
    (j : ℤ) (n : ℕ) :
    support (ParticularWaveAssembly.sourceFamily c u b G A j n) ⊆
      ⋃ k : Frequency, PeriodizedWaveBounds.nativeCell (P := P × ℝ) (g n) (K n) k := by
  intro x hx
  have hs := residualSource_support_of_real c u b G A (nativeUnion_closed (g n) (hK n)) n
    (hv n) (hp n) (hG n) (hA n) j hx
  obtain ⟨k, hk⟩ := mem_iUnion.mp hs
  exact mem_iUnion.mpr ⟨k, hk⟩

end NativeCoverage

/-! ## Different labels: genuine derivative products vanish on separated slots -/

/-- Pointwise disjoint products on a neighborhood give the zero germ of
the right factor whenever a component of the left factor is nonzero.
This handles boundary points without imposing globally disjoint supports. -/
theorem transport_zero_of_product_germ (R : D → ℝ) (Vr Vθ Vz : D → D)
    {u v : D → ComplexVector} {x : D}
    (hc : ∀ i, ContinuousAt (fun y => u y i) x)
    (hp : ∀ᶠ y in 𝓝 x, ∀ i j, u y i * v y j = 0) :
    LinearWaveResidual.transport R Vr Vθ Vz u v x = 0 := by
  classical
  by_cases hu : u x = 0
  · ext i
    simp [LinearWaveResidual.transport, hu]
  · obtain ⟨i, hi⟩ : ∃ i, u x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    have he : v =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hp, (hc i).eventually_ne hi] with y hy hne
      funext j
      exact (mul_eq_zero.mp (hy i j)).resolve_left hne
    have hv : v x = 0 := he.self_of_nhds
    have hd (j : Fin 3) (V : D → D) : along V (fun y => v y j) x = 0 := by
      have hej : (fun y => v y j) =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
        he.mono (fun _ hy => congrFun hy j)
      simp only [along, hej.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
        _root_.zero_apply]
    ext j
    fin_cases j <;> simp [LinearWaveResidual.transport, hv, hd, angularGenerator]

theorem transport_sum_self_of_product_germs {ι : Type*} (s : Finset ι)
    (R : D → ℝ) (Vr Vθ Vz : D → D) (u : ι → D → ComplexVector) {x : D}
    (hu : ∀ l ∈ s, ∀ i, DifferentiableAt ℝ (fun y => u l y i) x)
    (hp : ∀ l ∈ s, ∀ k ∈ s, l ≠ k →
      ∀ᶠ y in 𝓝 x, ∀ i j, u l y i * u k y j = 0) :
    LinearWaveResidual.transport R Vr Vθ Vz (∑ l ∈ s, u l) (∑ l ∈ s, u l) x =
      ∑ l ∈ s, LinearWaveResidual.transport R Vr Vθ Vz (u l) (u l) x := by
  classical
  rw [Actual.transport_sum_left]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Actual.transport_sum_right s R Vr Vθ Vz (u l) u hu]
  apply Finset.sum_eq_single l
  · intro k hk hkl
    exact transport_zero_of_product_germ R Vr Vθ Vz
      (fun i => (hu l hl i).continuousAt) (hp l hl k hk (Ne.symm hkl))
  · exact fun h => (h hl).elim

section ColoredSlots

open CorrectionState LabelSumBounds

variable {ι : Type*} {d h : ℝ} {vr vt : TorusInverse.Plane}
  {sys : PartitionedCovariance.SlotSystem d h vr vt}
  {label : ℕ → ι → SlotColoring.Label} {χ : ℕ → D → WindowPoint}
  {Y : ℕ → D → TorusInverse.Plane} {U : Set D} {u v : ι → Oscillation D}

omit [NormedSpace ℝ D] in
theorem supported_product_germ (hU : IsOpen U)
    (hu : SupportedOscillations sys label χ Y U u)
    (hv : SupportedOscillations sys label χ Y U v)
    {l k : ι} {n : ℕ} (hl : 1 ≤ (label n l).1) (hk : 1 ≤ (label n k).1)
    (hne : label n l ≠ label n k) {x : D × ℝ} (hx : x.1 ∈ U) :
    ∀ᶠ y in 𝓝 x, ∀ i j,
      LinearWaveResidual.realLift (u l n) y i * LinearWaveResidual.realLift (v k n) y j = 0 := by
  filter_upwards [(liftDomain_open hU).mem_nhds ⟨hx, mem_univ x.2⟩] with y hy
  intro i j
  change (u l n y i : ℂ) * (v k n y j : ℂ) = 0
  rw [← Complex.ofReal_mul,
    supported_cross_product_zero hu hv hl hk hne hy.1 y.2 i j, Complex.ofReal_zero]

/-- The actual colored-slot geometry eliminates cross-label advection,
including every derivative of the right factor in the cylindrical operator. -/
theorem supported_transport_zero (hU : IsOpen U)
    (hu : SupportedOscillations sys label χ Y U u)
    (hv : SupportedOscillations sys label χ Y U v)
    {l k : ι} {n : ℕ} (hl : 1 ≤ (label n l).1) (hk : 1 ≤ (label n k).1)
    (hne : label n l ≠ label n k) {x : D × ℝ} (hx : x.1 ∈ U)
    (hc : ∀ i, ContinuousAt (fun y => u l n y i) x)
    (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ) :
    LinearWaveResidual.transport R Vr Vθ Vz (LinearWaveResidual.realLift (u l n))
      (LinearWaveResidual.realLift (v k n)) x = 0 := by
  apply transport_zero_of_product_germ R Vr Vθ Vz
  · intro i
    exact Complex.continuous_ofReal.continuousAt.comp (hc i)
  · exact supported_product_germ hU hu hv hl hk hne hx

/-- The nonlinear residual of the actual finite sum is the sum of its
same-label residuals.  Cross-label cancellation comes from the geometric
support predicate, not from an assumed PDE cancellation. -/
theorem supported_nonlinearResidual_sum (hU : IsOpen U)
    (hs : SupportedOscillations sys label χ Y U u) (labels : Finset ι) (n : ℕ)
    (hlevel : ∀ l ∈ labels, 1 ≤ (label n l).1)
    (hinj : Set.InjOn (label n) (↑labels : Set ι))
    (ε : ℝ) (R : D × ℝ → ℝ) {Vr Vθ Vz : D × ℝ → D × ℝ}
    (Vt : D × ℝ → D × ℝ)
    (hr : ContDiffOn ℝ ∞ Vr (liftDomain U))
    (hθ : ContDiffOn ℝ ∞ Vθ (liftDomain U))
    (hz : ContDiffOn ℝ ∞ Vz (liftDomain U))
    (B : D × ℝ → ComplexVector) (p : ι → D × ℝ → ℂ)
    (hu : ∀ l ∈ labels, ∀ i, ContDiffOn ℝ ∞ (fun y => u l n y i) (liftDomain U))
    (hp : ∀ l ∈ labels, ContDiffOn ℝ ∞ (p l) (liftDomain U))
    {x : D × ℝ} (hx : x.1 ∈ U) :
    Actual.nonlinearResidual ε R Vr Vθ Vz Vt B
      (∑ l ∈ labels, LinearWaveResidual.realLift (u l n)) (∑ l ∈ labels, p l) x =
        ∑ l ∈ labels, Actual.nonlinearResidual ε R Vr Vθ Vz Vt B
          (LinearWaveResidual.realLift (u l n)) (p l) x := by
  have hcx : x ∈ liftDomain U := ⟨hx, mem_univ x.2⟩
  have hcu (l : ι) (hl : l ∈ labels) (i : Fin 3) :
      ContDiffOn ℝ ∞ (fun y => LinearWaveResidual.realLift (u l n) y i) (liftDomain U) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hu l hl i)
  unfold Actual.nonlinearResidual
  rw [Actual.linearResidual_sum labels (liftDomain_open hU) ε R Vt hr hθ hz B _ p hcu hp hcx,
    transport_sum_self_of_product_germs labels R Vr Vθ Vz _ (fun l hl i =>
      ((hcu l hl i).contDiffAt ((liftDomain_open hU).mem_nhds hcx)).differentiableAt (by simp)),
    Finset.sum_add_distrib]
  intro l hl k hk hne
  exact supported_product_germ hU hs hs (hlevel l hl) (hlevel k hk)
    (fun he => hne (hinj hl hk he)) hx

end ColoredSlots

/-! ## Relative support on the actual open strip -/

/-- Nonzero coefficients are supported in `K` relative to `U`.  Values
outside `U` are not constrained. -/
def NonzeroSupportedOn (U K : Set D) (c : HarmonicFields.Coefficients D) : Prop :=
  ∀ j : ℤ, j ≠ 0 → ∀ x : D, x ∈ U → x ∉ K → c j x = 0

namespace NonzeroSupportedOn

variable {U K : Set D} {c : HarmonicFields.Coefficients D}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem enlarge (hc : NonzeroSupportedOn U K c) : NonzeroSupported (Uᶜ ∪ K) c := by
  intro j hj x hx
  apply hc j hj x
  · by_contra hn
    exact hx (Or.inl hn)
  · exact fun hk => hx (Or.inr hk)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem of_global (hc : NonzeroSupported K c) : NonzeroSupportedOn U K c :=
  fun j hj x _ hx => hc j hj x hx

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem of_enlarge (hc : NonzeroSupported (Uᶜ ∪ K) c) : NonzeroSupportedOn U K c :=
  fun j hj x hx hn => hc j hj x (by simpa using And.intro hx hn)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem add (hc : NonzeroSupportedOn U K c) {d : HarmonicFields.Coefficients D}
    (hd : NonzeroSupportedOn U K d) : NonzeroSupportedOn U K (c + d) :=
  of_enlarge (hc.enlarge.add hd.enlarge)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem sub (hc : NonzeroSupportedOn U K c) {d : HarmonicFields.Coefficients D}
    (hd : NonzeroSupportedOn U K d) : NonzeroSupportedOn U K (c - d) :=
  of_enlarge (hc.enlarge.sub hd.enlarge)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem mul (hc : NonzeroSupportedOn U K c) {d : HarmonicFields.Coefficients D}
    (hd : NonzeroSupportedOn U K d) : NonzeroSupportedOn U K (c * d) :=
  of_enlarge (hc.enlarge.mul hd.enlarge)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem boundConstant (f : D → ℂ) : NonzeroSupportedOn U K (constantCoefficient f) :=
  of_global (NonzeroSupported.boundConstant f)

theorem differentiate (hc : NonzeroSupportedOn U K c) (hU : IsOpen U) (hK : IsClosed K)
    (V : D → D) (k : ℝ) (Φ : D → ℝ) :
    NonzeroSupportedOn U K (HarmonicFields.differentiate V k Φ c) :=
  of_enlarge (hc.enlarge.differentiate (hU.isClosed_compl.union hK) V k Φ)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realProjection (hc : NonzeroSupportedOn U K c) :
    NonzeroSupportedOn U K (realCoefficients c) := by
  intro j hj x hx hn
  simp only [realCoefficients_apply, hc j hj x hx hn, hc (-j) (neg_ne_zero.mpr hj) x hx hn,
    map_zero, add_zero, mul_zero]

end NonzeroSupportedOn

/-- Primitive support data for the incoming block and its two excluded
error families.  There is no assumption about its residual or derivatives. -/
structure InputSupportOn (U : Set D) (K : ℕ → Set D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D) : Prop where
  velocity : ∀ n i, NonzeroSupportedOn U (K n) (realCoefficients (b.velocity n i))
  pressure : ∀ n, NonzeroSupportedOn U (K n) (realCoefficients (b.pressure n))
  gaussian : ∀ n i, NonzeroSupportedOn U (K n) (realCoefficients (G n i))
  aliasError : ∀ n i, NonzeroSupportedOn U (K n) (realCoefficients (A n i))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_supportedOn_of_field
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) {U K : Set D}
    (hf : ∀ x, x ∈ U → x ∉ K → ∀ θ, (HarmonicFields.field c k Φ kp (x, θ)).re = 0) :
    NonzeroSupportedOn U K (realCoefficients c) :=
  fun j _ x hx hn => realCoefficient_eq_zero_of_field c k Φ hkp j x (hf x hx hn)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem InputSupportOn.of_fields
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {U : Set D} {K : ℕ → Set D} (hkp : ∀ n, b.angularFrequency n ≠ 0)
    (hv : ∀ n x, x ∈ U → x ∉ K n → ∀ θ i, b.oscillation n (x, θ) i = 0)
    (hp : ∀ n x, x ∈ U → x ∉ K n → ∀ θ, b.oscillatoryPressure n (x, θ) = 0)
    (hG : ∀ n x, x ∈ U → x ∉ K n → ∀ θ i,
      (HarmonicResidual.vectorField (G n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (x, θ) i).re = 0)
    (hA : ∀ n x, x ∈ U → x ∉ K n → ∀ θ i,
      (HarmonicResidual.vectorField (A n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (x, θ) i).re = 0) :
    InputSupportOn U K b G A := by
  constructor
  · intro n i
    exact realCoefficients_supportedOn_of_field _ _ _ (hkp n)
      (fun x hx hn θ => hv n x hx hn θ i)
  · intro n
    exact realCoefficients_supportedOn_of_field _ _ _ (hkp n) (hp n)
  · intro n i
    exact realCoefficients_supportedOn_of_field _ _ _ (hkp n)
      (fun x hx hn θ => hG n x hx hn θ i)
  · intro n i
    exact realCoefficients_supportedOn_of_field _ _ _ (hkp n)
      (fun x hx hn θ => hA n x hx hn θ i)

theorem residualSource_complement_germ_on
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {U K : Set D} (hU : IsOpen U) (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupportedOn U K (realCoefficients (b.velocity n i)))
    (hp : NonzeroSupportedOn U K (realCoefficients (b.pressure n)))
    (j : ℤ) {x : D} (hx : x ∈ U) (hn : x ∉ K) :
    ParticularWaveAssembly.residualSource c u b G A j n =ᶠ[𝓝 x] excludedSource G A j n :=
  residualSource_complement_germ_of_real c u b G A (hU.isClosed_compl.union hK) n
    (fun i => (hv i).enlarge) hp.enlarge j (by simpa using And.intro hx hn)

/-- The source has a genuine zero neighborhood at every uncovered point
of the open strip.  Only incoming coefficient support on that strip is used. -/
theorem residualSource_zero_germ_on
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {U : Set D} {K : ℕ → Set D} (hU : IsOpen U) (hK : ∀ n, IsClosed (K n))
    (hs : InputSupportOn U K b G A) (j : ℤ) (n : ℕ) {x : D}
    (hx : x ∈ U) (hn : x ∉ K n) :
    ParticularWaveAssembly.residualSource c u b G A j n =ᶠ[𝓝 x] fun _ => 0 := by
  apply PeriodizedWaveBounds.zero_germ_of_support (hU.isClosed_compl.union (hK n))
  · exact residualSource_support_of_real c u b G A (hU.isClosed_compl.union (hK n)) n
      (fun i => (hs.velocity n i).enlarge) (hs.pressure n).enlarge
      (fun i => (hs.gaussian n i).enlarge) (fun i => (hs.aliasError n i).enlarge) j
  · simpa using And.intro hx hn

theorem zero_complementJets_of_germs
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : WeightedClasses.StripData D) (w : ℕ → D → ℝ) (α : ℝ)
    (K : ℕ → I → Set D) (f : ℕ → D → E)
    (hg : ∀ n x, x ∈ s.domain → (∀ i, x ∉ K n i) → f n =ᶠ[𝓝 x] fun _ => 0) :
    PeriodizedWaveBounds.ComplementJets s w α K f := by
  constructor
  · intro n x hx hn
    exact contDiffAt_const.congr_of_eventuallyEq (hg n x hx hn)
  · intro m
    refine ⟨0, le_rfl, 0, ?_⟩
    intro n x hx hn j hj
    rw [PeriodizedWaveBounds.jets_eq_of_germ (hg n x hx hn) j]
    simp [WeightedClasses.majorant]

theorem residualSource_zero_complementJets
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {I : Type*} (K : PeriodizedWaveBounds.Cells D I) (s : WeightedClasses.StripData D)
    (hs : InputSupportOn s.domain (fun n => ⋃ i, K.carrier n i) b G A)
    (j : ℤ) (w : ℕ → D → ℝ) (α : ℝ) :
    PeriodizedWaveBounds.ComplementJets s w α K.carrier
      (ParticularWaveAssembly.residualSource c u b G A j) := by
  apply zero_complementJets_of_germs
  intro n x hx hn
  exact residualSource_zero_germ_on c u b G A s.isOpen_domain
    (fun n => (K.locallyFinite n).isClosed_iUnion (K.closed n)) hs j n hx (by simpa using hn)

/-- If an excluded nonzero tail is present outside the native cells, its
actual class supplies the complement estimate.  The source is not replaced
by zero there. -/
theorem residualSource_complementJets_on
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {I : Type*} (K : PeriodizedWaveBounds.Cells D I) (s : WeightedClasses.StripData D)
    (hv : ∀ n i, NonzeroSupportedOn s.domain (⋃ a, K.carrier n a)
      (realCoefficients (b.velocity n i)))
    (hp : ∀ n, NonzeroSupportedOn s.domain (⋃ a, K.carrier n a)
      (realCoefficients (b.pressure n)))
    (j : ℤ) {w : ℕ → D → ℝ} {α : ℝ}
    (he : WeightedClasses.MemClass s w α (excludedSource G A j)) :
    PeriodizedWaveBounds.ComplementJets s w α K.carrier
      (ParticularWaveAssembly.residualSource c u b G A j) := by
  have hg (n : ℕ) (x : D) (hx : x ∈ s.domain) (hn : ∀ a, x ∉ K.carrier n a) :
      ParticularWaveAssembly.residualSource c u b G A j n =ᶠ[𝓝 x] excludedSource G A j n :=
    residualSource_complement_germ_on c u b G A s.isOpen_domain
      ((K.locallyFinite n).isClosed_iUnion (K.closed n)) n (hv n) (hp n) j hx (by simpa using hn)
  constructor
  · intro n x hx hn
    exact ((he.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).congr_of_eventuallyEq
      (hg n x hx hn)
  · intro m
    obtain ⟨C, hC, p, hb⟩ := he.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro n x hx hn a ha
    rw [PeriodizedWaveBounds.jets_eq_of_germ (hg n x hx hn) a]
    exact hb n x hx a ha

section RelativeNativeCoverage

open CommonCoverSolve TorusInverse

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Angular extraction and the actual coordinate identity transfer support
in a geometric native slot to support in the union of all copy cells. -/
theorem coefficient_nativeSupport_of_field
    (c : HarmonicFields.Coefficients (P × Plane)) (k : ℝ) (Φ : P × Plane → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (g : Geometry) (K : Set Plane)
    {U : Set (P × Plane)} (level : ℕ) (slot : Set Plane) (Y : P × Plane → Plane)
    (hcoord : ∀ x, x ∈ U → coverPower g.gap x.2 = (SlotGeometry.cover ^ level) (Y x))
    (hslot : slot ⊆ (fun v => g.center + g.basis v) '' K)
    (hf : ∀ x, x ∈ U → ∀ θ, (field c k Φ kp (x, θ)).re ≠ 0 →
      Y x ∈ SlotGeometry.liftedSupport level slot) :
    NonzeroSupportedOn U (nativeUnion g K) (realCoefficients c) := by
  apply realCoefficients_supportedOn_of_field c k Φ hkp
  intro x hx hn θ
  by_contra hne
  obtain ⟨v, hv, ht⟩ := hf x hx θ hne
  apply hn
  apply (mem_nativeUnion_iff g K x).mpr
  refine ⟨v, hslot hv, ?_⟩
  change SlotGeometry.torusEq ((SlotGeometry.cover ^ g.gap) x.2) v
  rw [← coverPower_apply, hcoord x hx]
  exact ht

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem block_velocity_nativeSupport
    {ι : Type*} {d h : ℝ} {vr vt : Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    (label : ℕ → ι → SlotColoring.Label)
    (χ : ℕ → P × Plane → LabelSumBounds.WindowPoint) (Y : ℕ → P × Plane → Plane)
    {U : Set (P × Plane)} (b : ι → CorrectionState.HarmonicBlock (P × Plane))
    (hb : LabelSumBounds.SupportedOscillations sys label χ Y U (fun l => (b l).oscillation))
    (l : ι) (n : ℕ) (hkp : (b l).angularFrequency n ≠ 0) (g : Geometry) (K : Set Plane)
    (hcoord : ∀ x, x ∈ U → coverPower g.gap x.2 =
      (SlotGeometry.cover ^ SlotColoring.nativeIndex h (label n l).1) (Y n x))
    (hslot : PartitionedCovariance.slotSet h sys.radius vr vt (label n l) ⊆
      (fun v => g.center + g.basis v) '' K) (i : Fin 3) :
    NonzeroSupportedOn U (nativeUnion g K) (realCoefficients ((b l).velocity n i)) := by
  apply coefficient_nativeSupport_of_field _ _ _ hkp g K _ _ (Y n) hcoord hslot
  · intro x hx θ hn
    exact (hb l n x hx θ i hn).2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem InputSupportOn.of_native_fields
    (b : CorrectionState.HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane))
    (g : ℕ → Geometry) (K : ℕ → Set Plane) {U : Set (P × Plane)}
    (level : ℕ → ℕ) (slot : ℕ → Set Plane) (Y : ℕ → P × Plane → Plane)
    (hkp : ∀ n, b.angularFrequency n ≠ 0)
    (hcoord : ∀ n x, x ∈ U → coverPower (g n).gap x.2 =
      (SlotGeometry.cover ^ level n) (Y n x))
    (hslot : ∀ n, slot n ⊆ (fun v => (g n).center + (g n).basis v) '' K n)
    (hv : ∀ n x, x ∈ U → ∀ θ i, b.oscillation n (x, θ) i ≠ 0 →
      Y n x ∈ SlotGeometry.liftedSupport (level n) (slot n))
    (hp : ∀ n x, x ∈ U → ∀ θ, b.oscillatoryPressure n (x, θ) ≠ 0 →
      Y n x ∈ SlotGeometry.liftedSupport (level n) (slot n))
    (hG : ∀ n x, x ∈ U → ∀ θ i,
      (vectorField (G n) (b.frequency n) (b.phase n) (b.angularFrequency n) (x, θ) i).re ≠ 0 →
      Y n x ∈ SlotGeometry.liftedSupport (level n) (slot n))
    (hA : ∀ n x, x ∈ U → ∀ θ i,
      (vectorField (A n) (b.frequency n) (b.phase n) (b.angularFrequency n) (x, θ) i).re ≠ 0 →
      Y n x ∈ SlotGeometry.liftedSupport (level n) (slot n)) :
    InputSupportOn U (fun n => nativeUnion (g n) (K n)) b G A := by
  constructor
  · intro n i
    exact coefficient_nativeSupport_of_field _ _ _ (hkp n) (g n) (K n) (level n) (slot n)
      (Y n) (hcoord n) (hslot n) (fun x hx θ hn => hv n x hx θ i hn)
  · intro n
    exact coefficient_nativeSupport_of_field _ _ _ (hkp n) (g n) (K n) (level n) (slot n)
      (Y n) (hcoord n) (hslot n) (hp n)
  · intro n i
    exact coefficient_nativeSupport_of_field _ _ _ (hkp n) (g n) (K n) (level n) (slot n)
      (Y n) (hcoord n) (hslot n) (fun x hx θ hn => hG n x hx θ i hn)
  · intro n i
    exact coefficient_nativeSupport_of_field _ _ _ (hkp n) (g n) (K n) (level n) (slot n)
      (Y n) (hcoord n) (hslot n) (fun x hx θ hn => hA n x hx θ i hn)

theorem sourceFamily_zero_germ_on
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane))
    (g : ℕ → Geometry) (K : ℕ → Set Plane) (hK : ∀ n, IsCompact (K n))
    {U : Set (P × Plane)} (hU : IsOpen U)
    (hs : InputSupportOn U (fun n => nativeUnion (g n) (K n)) b G A)
    (j : ℤ) (n : ℕ) {x : (P × ℝ) × Plane}
    (hx : (x.1.1, x.2) ∈ U)
    (hn : ∀ k, x ∉ PeriodizedWaveBounds.nativeCell (g n) (K n) k) :
    ParticularWaveAssembly.sourceFamily c u b G A j n =ᶠ[𝓝 x] fun _ => 0 := by
  have hnot : (x.1.1, x.2) ∉ nativeUnion (g n) (K n) := by
    simp only [nativeUnion, mem_iUnion, not_exists]
    exact hn
  have he := residualSource_zero_germ_on c u b G A hU
    (fun n => nativeUnion_closed (g n) (hK n)) hs j n hx hnot
  have hc : Continuous (fun y : (P × ℝ) × Plane => (y.1.1, y.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  exact he.comp_tendsto hc.continuousAt

/-- This is the source-complement input for the global Gaussian estimate
on the full angular lift.  It has every exponent with constant zero, and
does not assert support or regularity outside the incoming open strip. -/
theorem sourceFamily_zero_complementJets
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane))
    (g : ℕ → Geometry) (K : ℕ → Set Plane) (hK : ∀ n, IsCompact (K n))
    {U : Set (P × Plane)} (hU : IsOpen U)
    (hs : InputSupportOn U (fun n => nativeUnion (g n) (K n)) b G A)
    (s : WeightedClasses.StripData ((P × ℝ) × Plane))
    (hdom : ∀ x, x ∈ s.domain → (x.1.1, x.2) ∈ U)
    (j : ℤ) (w : ℕ → (P × ℝ) × Plane → ℝ) (α : ℝ) :
    PeriodizedWaveBounds.ComplementJets s w α
      (fun n => PeriodizedWaveBounds.nativeCell (g n) (K n))
      (ParticularWaveAssembly.sourceFamily c u b G A j) := by
  apply zero_complementJets_of_germs
  intro n x hx hn
  exact sourceFamily_zero_germ_on c u b G A g K hK hU hs j n (hdom x hx) hn

end RelativeNativeCoverage

/-! ## Unrestricted zero modes and the exact excluded-tail obstruction -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficient_eq_zero_of_field_constant
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) {j : ℤ} (hj : j ≠ 0) (x : D) (m : ℝ)
    (hf : ∀ θ, (field c k Φ kp (x, θ)).re = m) :
    realCoefficients c j x = 0 := by
  rw [← extract_field (realCoefficients c) k Φ hkp j x]
  trans extract (field (constantCoefficient (fun _ : D => (m : ℂ))) k Φ kp) k Φ kp j x
  · unfold extract
    congr 1
    funext θ
    rw [field_realCoefficients, hf θ, field_constant]
  · rw [extract_field _ _ _ hkp]
    simp [constantCoefficient, hj]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Outside the slot, the real field may have any angularly constant
part.  Only its nonzero Fourier modes are constrained. -/
theorem realCoefficients_supportedOn_of_field_constant
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) {U K : Set D}
    (hf : ∀ x, x ∈ U → x ∉ K → ∃ m : ℝ, ∀ θ, (field c k Φ kp (x, θ)).re = m) :
    NonzeroSupportedOn U K (realCoefficients c) := by
  intro j hj x hx hn
  obtain ⟨m, hm⟩ := hf x hx hn
  exact realCoefficient_eq_zero_of_field_constant c k Φ hkp hj x m hm

/-- An explicit obstruction to dropping the excluded-source condition:
even a zero wave and zero pressure leave a nonzero residual if the stored
Gaussian family contains an unlocalized first harmonic. -/
theorem zero_wave_unlocalized_error
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (n : ℕ)
    (hv : ∀ i, b.velocity n i = 0) (hp : b.pressure n = 0) (x : D) :
    ParticularWaveAssembly.residualSource c u b
      (fun _ _ => AddMonoidAlgebra.single (1 : ℤ) (fun _ => (1 : ℂ))) 0 1 n x =
      fun _ => -(2 : ℂ)⁻¹ := by
  rw [residualSource_outside c u b _ _ isClosed_empty n
    (fun i => by rw [hv i]; exact NonzeroSupported.zero)
    (by rw [hp]; exact NonzeroSupported.zero) 1 (Set.notMem_empty x)]
  ext i
  norm_num [excludedSource, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase,
      realCoefficients_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

end NavierStokes.HarmonicSourceSupport
