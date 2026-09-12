/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedWaveUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.CopySolveCompatibility

/-!
# Actual particular-wave assembly

The residual source is the coefficient of `HarmonicResidual.residualBlock`.
All signed nonzero harmonics are retained inside their original spatial
label. A fixed reference solve supplies the compatible band views.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ParticularWaveAssembly

open Set Function HarmonicFields ErrorHarmonics CorrectionState
open HarmonicCalculus WeightedClasses
open scoped BigOperators Topology ContDiff ComplexConjugate

/-- One finite signed harmonic range, without the mean coefficient. -/
noncomputable def modes (N : ℕ) : Finset ℤ := (Finset.Icc (-(N : ℤ)) N).erase 0

@[simp] theorem mem_modes (N : ℕ) (j : ℤ) :
    j ∈ modes N ↔ j ≠ 0 ∧ j.natAbs ≤ N := by
  simp only [modes, Finset.mem_erase, Finset.mem_Icc]
  omega

theorem neg_mem_modes (N : ℕ) (j : ℤ) : -j ∈ modes N ↔ j ∈ modes N := by
  simp only [mem_modes, neg_ne_zero, Int.natAbs_neg]

theorem pair_apply {D : Type} (j m : ℤ) (a : D → ℂ) (x : D) :
    conjugatePair j a m x =
      (if m = j then a x / 2 else 0) + conj (if -m = j then a x / 2 else 0) := by
  classical
  change Finsupp.single j (fun x => a x / 2) m x +
    conj (Finsupp.single j (fun x => a x / 2) (-m) x) = _
  by_cases hm : j = m <;> by_cases hn : j = -m
  · simp only [Finsupp.single_apply, ite_eq_left hm, ite_eq_left hn, ite_eq_left hm.symm,
      ite_eq_left hn.symm]
  · simp only [Finsupp.single_apply, ite_eq_left hm, ite_eq_right hn, ite_eq_left hm.symm,
      ite_eq_right (Ne.symm hn), Pi.zero_apply]
  · simp only [Finsupp.single_apply, ite_eq_right hm, ite_eq_left hn, ite_eq_right (Ne.symm hm),
      ite_eq_left hn.symm, Pi.zero_apply]
  · simp only [Finsupp.single_apply, ite_eq_right hm, ite_eq_right hn, ite_eq_right (Ne.symm hm),
      ite_eq_right (Ne.symm hn), Pi.zero_apply]

/-- Pairing each signed Fourier source introduces no extra factor of two.
Every coefficient is recovered exactly, including the absent mean. -/
theorem signed_pairs_reconstruct {D : Type} (c : Coefficients D) (N : ℕ)
    (hc : ConjugateSymmetric c) (h0 : c 0 = 0) (hN : BandLimited c N) :
    (∑ j ∈ modes N, conjugatePair j (c j)) = c := by
  classical
  ext m x
  have he : (∑ j ∈ modes N, conjugatePair j (c j)) m x =
      (if m ∈ modes N then c m x / 2 else 0) +
        conj (if -m ∈ modes N then c (-m) x / 2 else 0) := by
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
    simp only [pair_apply, Finset.sum_add_distrib]
    congr 1
    · simp []
    · rw [← map_sum]
      simp []
  rw [he]
  simp only [neg_mem_modes]
  by_cases hm : m ∈ modes N
  · simp only [ite_eq_left hm, hc m x, map_div₀, map_ofNat, starRingEnd_self_apply]
    ring
  · have hz : c m = 0 := by
      by_cases hm0 : m = 0
      · simpa [hm0] using h0
      · apply Finsupp.notMem_support_iff.mp
        intro hs
        exact hm ((mem_modes N m).mpr ⟨hm0, hN m hs⟩)
    simp only [ite_eq_right hm, hz, Pi.zero_apply, map_zero, add_zero]

/-- The actual source coefficient, with no convention-dependent scaling. -/
noncomputable def residualSource {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (c : Context D) (u : State D) (b : HarmonicBlock D)
    (G A : HarmonicResidual.BlockCoefficients D) (j : ℤ) (n : ℕ) (x : D) : ComplexVector :=
  fun i => (HarmonicResidual.residualBlock c u b G A).velocity n i j x

theorem residualSource_zero {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (c : Context D) (u : State D) (b : HarmonicBlock D)
    (G A : HarmonicResidual.BlockCoefficients D) (n : ℕ) (x : D) :
    residualSource c u b G A 0 n x = 0 := by
  funext i
  simp only [residualSource, HarmonicResidual.residualBlock_zero_mode, Pi.zero_apply]

theorem residualSource_conjugate {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (c : Context D) (u : State D) (b : HarmonicBlock D)
    (G A : HarmonicResidual.BlockCoefficients D) (j : ℤ) (n : ℕ) (x : D) (i : Fin 3) :
    residualSource c u b G A (-j) n x i = conj (residualSource c u b G A j n x i) :=
  HarmonicResidual.residualBlock_conjugate c u b G A n i j x

/-- A pair at the original label's carrier, for both velocity and pressure. -/
noncomputable def modeBlock {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) : HarmonicBlock D where
  velocity n i := conjugatePair j (fun x => v n x i)
  pressure n := conjugatePair j (p n)
  frequency := k
  phase := Φ
  angularFrequency := kp

theorem modeBlock_band {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    (modeBlock j k Φ kp v p).BandLimited j.natAbs :=
  ⟨fun n i => band_conjugatePair j (fun x => v n x i), fun n => band_conjugatePair j (p n)⟩

theorem modeBlock_real {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    RealBlock (modeBlock j k Φ kp v p) :=
  ⟨fun n i => conjugatePair_symmetric j (fun x => v n x i), fun n => conjugatePair_symmetric j (p
      n)⟩

theorem modeBlock_zero {D : Type} {j : ℤ} (hj : j ≠ 0)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    (∀ n i, (modeBlock j k Φ kp v p).velocity n i 0 = 0) ∧
    (∀ n, (modeBlock j k Φ kp v p).pressure n 0 = 0) := by
  constructor
  · intro n i
    funext x
    simp only [modeBlock, pair_apply, neg_zero, ite_eq_right (Ne.symm hj), map_zero, add_zero,
        Pi.zero_apply]
  · intro n
    funext x
    simp only [modeBlock, pair_apply, neg_zero, ite_eq_right (Ne.symm hj), map_zero, add_zero,
        Pi.zero_apply]

theorem pair_class {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {a : ℕ → D → ℂ}
    (ha : MemClass s w α a) (j m : ℤ) :
    MemClass s w α (fun n x => conjugatePair j (a n) m x) := by
  have hp := LinearWaveBounds.constant_complex_mul ha (1 / 2)
  have hn := hp.map (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have hz := MemClass.zero (s := s) (α := α) (E := ℂ) ha.weight_nonneg
  by_cases hm : m = j <;> by_cases hm' : -m = j
  · have h := hp.add hn
    simp only [pair_apply, ite_eq_left hm, ite_eq_left hm', div_eq_mul_inv, one_mul, mul_comm]
        at h ⊢
    exact h
  · simpa only [pair_apply, ite_eq_left hm, ite_eq_right hm', div_eq_mul_inv, one_mul, mul_comm,
      map_zero, add_zero] using hp
  · simp only [pair_apply, ite_eq_right hm, ite_eq_left hm', div_eq_mul_inv, one_mul, mul_comm,
      zero_add] at hn ⊢
    exact hn
  · simpa only [pair_apply, ite_eq_right hm, ite_eq_right hm', map_zero, add_zero] using hz

theorem modeBlock_classes {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {W : ℕ → D → ℝ} {α γ : ℝ}
    (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    {v : ℕ → D → ComplexVector} {p : ℕ → D → ℂ}
    (hv : WaveClass s W α v) (hp : WaveClass s W γ p) :
    (modeBlock j k Φ kp v p).WaveBounds s W α ∧
      (modeBlock j k Φ kp v p).PressureBounds s W γ :=
  ⟨fun i m _ => pair_class (CurlClassBounds.class_component hv i) j m,
    fun m _ => pair_class hp j m⟩

/-- Assembled block, given by `sumBlock (modes N) k Φ kp (fun j => modeBlock j k Φ kp (v j) (p
j))`. -/
noncomputable def assembledBlock {D : Type} (N : ℕ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℤ → ℕ → D → ComplexVector) (p : ℤ → ℕ → D → ℂ) : HarmonicBlock D :=
  sumBlock (modes N) k Φ kp (fun j => modeBlock j k Φ kp (v j) (p j))

theorem assembledBlock_band {D : Type} (N : ℕ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℤ → ℕ → D → ComplexVector) (p : ℤ → ℕ → D → ℂ) :
    (assembledBlock N k Φ kp v p).BandLimited N := by
  apply sumBlock_band
  intro j hj
  exact ⟨fun n i => ((modeBlock_band j k Φ kp (v j) (p j)).1 n i).mono ((mem_modes N j).mp hj).2,
    fun n => ((modeBlock_band j k Φ kp (v j) (p j)).2 n).mono ((mem_modes N j).mp hj).2⟩

theorem assembledBlock_real {D : Type} (N : ℕ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℤ → ℕ → D → ComplexVector) (p : ℤ → ℕ → D → ℂ) :
    RealBlock (assembledBlock N k Φ kp v p) :=
  sumBlock_real _ _ _ _ _ (fun j _ => modeBlock_real j k Φ kp (v j) (p j))

/-- Reassemble the actual signed residual sources, without changing label,
phase, frequency, or normalization. -/
theorem residualSource_reconstruct {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (c : Context D) (u : State D) (b : HarmonicBlock D)
    (G A : HarmonicResidual.BlockCoefficients D) (N : ℕ)
    (hN : (HarmonicResidual.residualBlock c u b G A).BandLimited N) (n : ℕ) (i : Fin 3) :
    (assembledBlock N b.frequency b.phase b.angularFrequency
      (residualSource c u b G A) (fun _ _ _ => 0)).velocity n i =
      (HarmonicResidual.residualBlock c u b G A).velocity n i :=
  signed_pairs_reconstruct _ N (HarmonicResidual.residualBlock_conjugate c u b G A n i)
    (HarmonicResidual.residualBlock_zero_mode c u b G A n i) (hN.1 n i)

/-! ## A fixed native clock and reference geometry -/

section ReferenceTransport

open CommonCoverSolve TorusInverse

variable {P Q H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Transport only the input data. The physical native clock and anchor
are retained, and the cover is refined by a specified integer power. -/
noncomputable def transportTangent (t : TangentData P H) (φ : Q → P)
    (gap : ℕ) (amplitude : ℝ) : TangentData Q H where
  normal z := t.normal (φ z.1, z.2)
  normalDot z := t.normalDot (φ z.1, z.2)
  action z := t.action (φ z.1, z.2)
  damping z := t.damping (φ z.1, z.2)
  source z := amplitude • t.source (φ z.1, coverPower gap z.2)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [CompleteSpace H] in
theorem transportTangent_linearData (t : TangentData P H) (φ : Q → P)
    (gap : ℕ) (amplitude : ℝ) :
    (transportTangent t φ gap amplitude).linearData =
      CopySolveCompatibility.scaleSource
        (CopySolveCompatibility.transformData t.linearData φ gap) amplitude := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem copySolve_transport (t : TangentData P H) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ) (amplitude : ℝ)
    (copy : Frequency) (q : Q) (Y : Plane) :
    (transportTangent t φ gap amplitude).linearData.copySolve
      (CopySolveCompatibility.refineGeometry g gap) hab copy (q, Y) =
        amplitude • t.linearData.copySolve g hab copy (φ q, coverPower gap Y) := by
  rw [transportTangent_linearData, CopySolveCompatibility.copySolve_scaleSource,
    CopySolveCompatibility.copySolve_transform]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- All transported views equal a pullback of one actual common-cover
Volterra output; no chartwise output is supplied as a hypothesis. -/
theorem commonSolve_transport (t : TangentData P H) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ) (amplitude : ℝ)
    (κ : Plane → ℝ) (q : Q) (Y : Plane) :
    (transportTangent t φ gap amplitude).linearData.commonSolve
      (CopySolveCompatibility.refineGeometry g gap) hab κ (q, Y) =
        amplitude • t.linearData.commonSolve g hab κ (φ q, coverPower gap Y) := by
  rw [transportTangent_linearData, CopySolveCompatibility.commonSolve_scaleSource,
    CopySolveCompatibility.commonSolve_transform]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem copyPressureReal_transport (t : TangentData P H) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ) (amplitude : ℝ)
    (copy : Frequency) (q : Q) (Y : Plane) :
    ParticularWaveBounds.copyPressureReal (transportTangent t φ gap amplitude)
      (CopySolveCompatibility.refineGeometry g gap) hab copy (q, Y) =
        amplitude * ParticularWaveBounds.copyPressureReal t g hab copy (φ q, coverPower gap Y) := by
  simp only [ParticularWaveBounds.copyPressureReal]
  rw [copySolve_transport]
  simp only [transportTangent,
    ParticularWaveBounds.nativePoint, CopySolveCompatibility.coordinates_refine,
    TangentProjection.pressureCoefficient, map_smul, real_inner_smul_right]
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- Pressure transports with its own inverse carrier frequency. -/
theorem copyPressure_transport (t : TangentData P H) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ) (amplitude referenceFrequency frequency : ℝ)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    (copy : Frequency) (q : Q) (Y : Plane) :
    ParticularWaveBounds.copyPressure (transportTangent t φ gap amplitude)
      (CopySolveCompatibility.refineGeometry g gap) hab copy frequency (q, Y) =
        (amplitude * referenceFrequency / frequency) •
          ParticularWaveBounds.copyPressure t g hab copy referenceFrequency (φ q, coverPower gap Y)
              := by
  have hr : (referenceFrequency : ℂ) ≠ 0 := by exact_mod_cast hreference
  have hf : (frequency : ℂ) ≠ 0 := by exact_mod_cast hfrequency
  simp only [ParticularWaveBounds.copyPressure, copyPressureReal_transport,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.real_smul]
  field_simp

end ReferenceTransport

/-! ## Full angular fields and grouped coefficient classes -/

theorem assembledBlock_zero {D : Type} (N : ℕ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℤ → ℕ → D → ComplexVector) (p : ℤ → ℕ → D → ℂ) :
    (∀ n i, (assembledBlock N k Φ kp v p).velocity n i 0 = 0) ∧
    (∀ n, (assembledBlock N k Φ kp v p).pressure n 0 = 0) := by
  constructor
  · intro n i
    change (∑ j ∈ modes N, (modeBlock j k Φ kp (v j) (p j)).velocity n i) 0 = 0
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    exact (modeBlock_zero ((mem_modes N j).mp hj).1 k Φ kp (v j) (p j)).1 n i
  · intro n
    change (∑ j ∈ modes N, (modeBlock j k Φ kp (v j) (p j)).pressure n) 0 = 0
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    exact (modeBlock_zero ((mem_modes N j).mp hj).1 k Φ kp (v j) (p j)).2 n

theorem assembledBlock_classes {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {W : ℕ → D → ℝ} {α γ : ℝ}
    (N : ℕ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    {v : ℤ → ℕ → D → ComplexVector} {p : ℤ → ℕ → D → ℂ}
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hv : ∀ j ∈ modes N, WaveClass s W α (v j))
    (hp : ∀ j ∈ modes N, WaveClass s W γ (p j)) :
    (assembledBlock N k Φ kp v p).WaveBounds s W α ∧
      (assembledBlock N k Φ kp v p).PressureBounds s W γ := by
  have hw : ∀ n x, x ∈ s.domain → 0 ≤ Real.sqrt (s.zeta x) * W n x :=
    fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n x hx)
  constructor
  · intro i m hm
    have hh := MemClass.sum (modes N)
      (fun j n x => (modeBlock j k Φ kp (v j) (p j)).velocity n i m x) hw
      (fun j hj => (modeBlock_classes j k Φ kp (hv j hj) (hp j hj)).1 i m hm)
    have he : (fun (n : ℕ) (x : D) => (assembledBlock N k Φ kp v p).velocity n i m x) =
        (fun n x => ∑ j ∈ modes N, (modeBlock j k Φ kp (v j) (p j)).velocity n i m x) := by
      funext n x
      change (∑ j ∈ modes N, (modeBlock j k Φ kp (v j) (p j)).velocity n i) m x = _
      rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
    change WaveClass s W α (fun n x => (assembledBlock N k Φ kp v p).velocity n i m x)
    rw [he]
    exact hh
  · intro m hm
    have hh := MemClass.sum (modes N)
      (fun j n x => (modeBlock j k Φ kp (v j) (p j)).pressure n m x) hw
      (fun j hj => (modeBlock_classes j k Φ kp (hv j hj) (hp j hj)).2 m hm)
    have he : (fun (n : ℕ) (x : D) => (assembledBlock N k Φ kp v p).pressure n m x) =
        (fun n x => ∑ j ∈ modes N, (modeBlock j k Φ kp (v j) (p j)).pressure n m x) := by
      funext n x
      change (∑ j ∈ modes N, (modeBlock j k Φ kp (v j) (p j)).pressure n) m x = _
      rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
    change WaveClass s W γ (fun n x => (assembledBlock N k Φ kp v p).pressure n m x)
    rw [he]
    exact hh

theorem assembledBlock_mean_zero {D : Type}
    (N : ℕ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℤ → ℕ → D → ComplexVector) (p : ℤ → ℕ → D → ℂ)
    (hkp : ∀ n, kp n ≠ 0) :
    (∀ i, angularAverage (fun n x => (assembledBlock N k Φ kp v p).oscillation n x i) = 0) ∧
      angularAverage (assembledBlock N k Φ kp v p).oscillatoryPressure = 0 := by
  constructor
  · intro i
    funext n x
    change (∫ θ in (0 : ℝ)..2 * Real.pi,
      (field ((assembledBlock N k Φ kp v p).velocity n i) (k n) (Φ n) (kp n) (x,θ)).re) /
      (2 * Real.pi) = 0
    rw [SignedWaveUpdate.angularAverage_re_field, angularMean_field _ _ _ (hkp n),
      (assembledBlock_zero N k Φ kp v p).1 n i]
    rfl
  · funext n x
    change (∫ θ in (0 : ℝ)..2 * Real.pi,
      (field ((assembledBlock N k Φ kp v p).pressure n) (k n) (Φ n) (kp n) (x,θ)).re) /
      (2 * Real.pi) = 0
    rw [SignedWaveUpdate.angularAverage_re_field, angularMean_field _ _ _ (hkp n),
      (assembledBlock_zero N k Φ kp v p).2 n]
    rfl

/-- Full mode block, given by `modeBlock j k Φ kp (fun n x => a.amplitude n (x,0)) (fun n x =>
a.pressure n (x,0))`. -/
noncomputable def fullModeBlock {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) : HarmonicBlock D :=
  modeBlock j k Φ kp (fun n x => a.amplitude n (x,0)) (fun n x => a.pressure n (x,0))

theorem fullModeBlock_represents {D : Type}
    (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (ha : AngleIndependent a.amplitude) (hp : AngleIndependent a.pressure)
    (hphase : ∀ n x θ, a.frequency n * a.phase n (x, θ) =
      (j : ℝ) * (k n * Φ n x + (kp n : ℝ) * θ)) :
    (fullModeBlock j k Φ kp a).oscillation =
      (fun n x i => (vectorMode (a.frequency n) (a.phase n) (a.amplitude n) x i).re) ∧
    (fullModeBlock j k Φ kp a).oscillatoryPressure =
      (fun n x => (mode (a.frequency n) (a.phase n) (a.pressure n) x).re) := by
  have hc (n : ℕ) (x : D) (θ : ℝ) :
      character j (k n * Φ n x + (kp n : ℝ) * θ) = carrier (a.frequency n) (a.phase n) (x,θ) := by
    have he := congrArg Complex.ofReal (hphase n x θ)
    push_cast at he
    unfold character carrier phaseFactor
    congr 1
    push_cast
    rw [← he]
    ring
  constructor
  · funext n x i
    change ((field (conjugatePair j (fun y => a.amplitude n (y,0) i)) (k n) (Φ n) (kp n) x).re) = _
    rw [field_conjugatePair, Complex.ofReal_re, hc]
    simp only [vectorMode, mode, ha n x.1 x.2]
  · funext n x
    change ((field (conjugatePair j (fun y => a.pressure n (y,0))) (k n) (Φ n) (kp n) x).re) = _
    rw [field_conjugatePair, Complex.ofReal_re, hc]
    simp only [mode, hp n x.1 x.2]

theorem fullModeBlock_classes {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData (D × ℝ)} {W : ℕ → D × ℝ → ℝ} {α γ : ℝ}
    (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (ha : WaveClass s W α a.amplitude) (hp : WaveClass s W γ a.pressure) :
    (fullModeBlock j k Φ kp a).WaveBounds (SignedWaveUpdate.sectionStrip s) (fun n x => W n (x,0))
        α ∧
      (fullModeBlock j k Φ kp a).PressureBounds (SignedWaveUpdate.sectionStrip s) (fun n x => W n
          (x,0)) γ :=
  modeBlock_classes j k Φ kp (SignedWaveUpdate.class_zeroSection ha)
      (SignedWaveUpdate.class_zeroSection hp)

/-! ## Complex reference transport, including pressure -/

section ComplexTransport

open CommonCoverSolve TorusInverse ParticularWaveBounds

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Transport source, defined pointwise by `amplitude • f (φ q.1, coverPower gap q.2)`. -/
noncomputable def transportSource (f : P × Plane → ComplexVector) (φ : Q → P)
    (gap : ℕ) (amplitude : ℝ) : Q × Plane → ComplexVector :=
  fun q => amplitude • f (φ q.1, coverPower gap q.2)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem realData_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (φ : Q → P) (gap : ℕ) (amplitude : ℝ) :
    realData (transportTangent t φ gap amplitude) (transportSource f φ gap amplitude) =
      transportTangent (realData t f) φ gap amplitude := by
  unfold realData transportTangent transportSource
  congr 1
  funext q
  exact map_smul realPart amplitude _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem imagData_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (φ : Q → P) (gap : ℕ) (amplitude : ℝ) :
    imagData (transportTangent t φ gap amplitude) (transportSource f φ gap amplitude) =
      transportTangent (imagData t f) φ gap amplitude := by
  unfold imagData transportTangent transportSource
  congr 1
  funext q
  exact map_smul imagPart amplitude _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem copyVelocity_transport (t : TangentData P ProblemStatement.Space) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ) (amplitude : ℝ)
    (copy : Frequency) (q : Q) (Y : Plane) :
    copyVelocity (transportTangent t φ gap amplitude)
      (CopySolveCompatibility.refineGeometry g gap) hab copy (q,Y) =
        amplitude • copyVelocity t g hab copy (φ q, coverPower gap Y) := by
  unfold copyVelocity
  rw [copySolve_transport, map_smul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem complexCopyVelocity_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ) (amplitude : ℝ)
    (copy : Frequency) (q : Q) (Y : Plane) :
    complexCopyVelocity (transportTangent t φ gap amplitude) (transportSource f φ gap amplitude)
      (CopySolveCompatibility.refineGeometry g gap) hab copy (q,Y) =
        amplitude • complexCopyVelocity t f g hab copy (φ q, coverPower gap Y) := by
  simp only [complexCopyVelocity, realData_transport, imagData_transport,
    copyVelocity_transport, smul_add, smul_comm Complex.I amplitude]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem complexCopyPressure_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (amplitude referenceFrequency frequency : ℝ)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    (copy : Frequency) (q : Q) (Y : Plane) :
    complexCopyPressure (transportTangent t φ gap amplitude) (transportSource f φ gap amplitude)
      (CopySolveCompatibility.refineGeometry g gap) hab copy frequency (q,Y) =
        (amplitude * referenceFrequency / frequency) •
          complexCopyPressure t f g hab copy referenceFrequency (φ q, coverPower gap Y) := by
  simp only [complexCopyPressure, realData_transport, imagData_transport,
    copyPressure_transport _ _ _ _ _ _ _ _ hreference hfrequency, smul_add, Complex.real_smul]
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem periodizedCopies_transport {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) (φ : Q → P) (gap : ℕ) (amplitude : ℝ)
    (q : Q) (Y : Plane) :
    periodizedCopies (CopySolveCompatibility.refineGeometry g gap) κ
      (fun k q => amplitude • F k (φ q.1, coverPower gap q.2)) (q,Y) =
        amplitude • periodizedCopies g κ F (φ q, coverPower gap Y) := by
  unfold periodizedCopies
  simp only [CopySolveCompatibility.coordinates_refine, smul_comm _ amplitude]
  exact tsum_const_smul'' amplitude

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem commonVelocity_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ) (amplitude : ℝ)
    (κ : Plane → ℝ) (q : Q) (Y : Plane) :
    commonVelocity (transportTangent t φ gap amplitude) (transportSource f φ gap amplitude)
      (CopySolveCompatibility.refineGeometry g gap) hab κ (q,Y) =
        amplitude • commonVelocity t f g hab κ (φ q, coverPower gap Y) := by
  unfold commonVelocity periodizedCopies
  simp only [complexCopyVelocity_transport, CopySolveCompatibility.coordinates_refine,
    smul_comm _ amplitude]
  exact tsum_const_smul'' amplitude

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem commonPressure_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (φ : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (amplitude referenceFrequency frequency : ℝ)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    (κ : Plane → ℝ) (q : Q) (Y : Plane) :
    commonPressure (transportTangent t φ gap amplitude) (transportSource f φ gap amplitude)
      (CopySolveCompatibility.refineGeometry g gap) hab κ frequency (q,Y) =
        (amplitude * referenceFrequency / frequency) •
          commonPressure t f g hab κ referenceFrequency (φ q, coverPower gap Y) := by
  unfold commonPressure periodizedCopies
  simp only [complexCopyPressure_transport _ _ _ _ _ _ _ _ _ hreference hfrequency,
    CopySolveCompatibility.coordinates_refine, smul_comm _ (amplitude * referenceFrequency /
        frequency)]
  exact tsum_const_smul'' (amplitude * referenceFrequency / frequency)

end ComplexTransport

/-! ## One physical reference for every band view -/

section FixedReference

open CommonCoverSolve TorusInverse ParticularWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The choices are made once for a spatial label. The native interval,
center, cover, and cutoff are shared by all its band views and harmonics. -/
structure Reference (P : Type) where
  /-- Band of `Reference`, of type `ℕ`. -/
  band : ℕ
  /-- Geometry of `Reference`, of type `Geometry`. -/
  geometry : Geometry
  /-- Length of `Reference`, of type `ℝ`. -/
  length : ℝ
  length_pos : 0 < length
  /-- Tangent of `Reference`, of type `ℤ → TangentData P ProblemStatement.Space`. -/
  tangent : ℤ → TangentData P ProblemStatement.Space
  /-- Cutoff of `Reference`, of type `Plane → ℝ`. -/
  cutoff : Plane → ℝ
  cutoff_compact : HasCompactSupport cutoff

/-- Only chart/source input data, never an independently chosen solution. -/
structure BandCharts (P : Type) where
  /-- Parameter of `BandCharts`, of type `ℕ → P → P`. -/
  parameter : ℕ → P → P
  /-- Gap of `BandCharts`, of type `ℕ → ℕ`. -/
  gap : ℕ → ℕ
  /-- Amplitude of `BandCharts`, of type `ℕ → ℝ`. -/
  amplitude : ℕ → ℝ

/-- Reference velocity, given by `commonVelocity (r.tangent j) (residualSource c u b G A j
r.band) r.geometry r.length_pos.le r.cutoff`. -/
noncomputable def referenceVelocity (r : Reference P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) : P × Plane → ComplexVector :=
  commonVelocity (r.tangent j) (residualSource c u b G A j r.band) r.geometry
    r.length_pos.le r.cutoff

/-- Reference pressure, constructed using `commonPressure`. -/
noncomputable def referencePressure (r : Reference P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) : P × Plane → ℂ :=
  commonPressure (r.tangent j) (residualSource c u b G A j r.band) r.geometry
    r.length_pos.le r.cutoff ((j : ℝ) * b.frequency r.band)

/-- Band tangent, given by `transportTangent (r.tangent j) (charts.parameter n) (charts.gap n)
(charts.amplitude n)`. -/
noncomputable def bandTangent (r : Reference P) (charts : BandCharts P) (j : ℤ) (n : ℕ) :
    TangentData P ProblemStatement.Space :=
  transportTangent (r.tangent j) (charts.parameter n) (charts.gap n) (charts.amplitude n)

/-- Band geometry, given by `CopySolveCompatibility.refineGeometry r.geometry (charts.gap n)`. -/
noncomputable def bandGeometry (r : Reference P) (charts : BandCharts P) (n : ℕ) : Geometry :=
  CopySolveCompatibility.refineGeometry r.geometry (charts.gap n)

/-- Actual band velocity, given by `commonVelocity (bandTangent r charts j n) (residualSource c
u b G A j n) (bandGeometry r charts n) r.length_pos.le r.cutoff`. -/
noncomputable def actualBandVelocity (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (n : ℕ) :
    P × Plane → ComplexVector :=
  commonVelocity (bandTangent r charts j n) (residualSource c u b G A j n)
    (bandGeometry r charts n) r.length_pos.le r.cutoff

/-- Actual band pressure, constructed using `commonPressure`. -/
noncomputable def actualBandPressure (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (n : ℕ) : P × Plane → ℂ :=
  commonPressure (bandTangent r charts j n) (residualSource c u b G A j n)
    (bandGeometry r charts n) r.length_pos.le r.cutoff ((j : ℝ) * b.frequency n)

/-- Compatibility is required only of the actual residual source inputs.
Uniqueness of the fixed-reference Volterra construction then gives the
physical output identity. -/
theorem actualBandVelocity_eq_reference (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (n : ℕ)
    (hsource : residualSource c u b G A j n = transportSource
      (residualSource c u b G A j r.band) (charts.parameter n) (charts.gap n) (charts.amplitude n))
    (p : P) (Y : Plane) :
    actualBandVelocity r charts c u b G A j n (p,Y) =
      charts.amplitude n • referenceVelocity r c u b G A j
        (charts.parameter n p, coverPower (charts.gap n) Y) := by
  unfold actualBandVelocity bandTangent bandGeometry referenceVelocity
  rw [hsource, commonVelocity_transport]

theorem actualBandPressure_eq_reference (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) {j : ℤ} (hj : j ≠ 0) (n : ℕ)
    (hfrequency : ∀ n, b.frequency n ≠ 0)
    (hsource : residualSource c u b G A j n = transportSource
      (residualSource c u b G A j r.band) (charts.parameter n) (charts.gap n) (charts.amplitude n))
    (p : P) (Y : Plane) :
    actualBandPressure r charts c u b G A j n (p,Y) =
      (charts.amplitude n * b.frequency r.band / b.frequency n) •
        referencePressure r c u b G A j (charts.parameter n p, coverPower (charts.gap n) Y) := by
  have hjr : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  unfold actualBandPressure bandTangent bandGeometry referencePressure
  rw [hsource, commonPressure_transport _ _ _ _ _ _ _ _ _
    (mul_ne_zero hjr (hfrequency r.band)) (mul_ne_zero hjr (hfrequency n))]
  have he : charts.amplitude n * ((j : ℝ) * b.frequency r.band) /
      ((j : ℝ) * b.frequency n) = charts.amplitude n * b.frequency r.band / b.frequency n := by
    field_simp [hjr, hfrequency n]
  rw [he]

theorem referenceVelocity_finite (r : Reference P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (p : P × Plane) :
    ∃ I : Finset Frequency, referenceVelocity r c u b G A j p = ∑ k ∈ I,
      r.cutoff (r.geometry.coordinates k p.2) •
        complexCopyVelocity (r.tangent j) (residualSource c u b G A j r.band)
          r.geometry r.length_pos.le k p :=
  periodizedCopies_eq_finite_sum r.geometry r.cutoff_compact _ p

theorem referencePressure_finite (r : Reference P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (p : P × Plane) :
    ∃ I : Finset Frequency, referencePressure r c u b G A j p = ∑ k ∈ I,
      r.cutoff (r.geometry.coordinates k p.2) •
        complexCopyPressure (r.tangent j) (residualSource c u b G A j r.band)
          r.geometry r.length_pos.le k ((j : ℝ) * b.frequency r.band) p :=
  periodizedCopies_eq_finite_sum r.geometry r.cutoff_compact _ p

end FixedReference

/-! ## Angular invariance is inherited by the actual complex solve -/

section AngularConstruction

open CommonCoverSolve TorusInverse ParticularWaveBounds CopyAngularInvariance

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem complexCopyVelocity_invariant {θ : P} {t : TangentData P ProblemStatement.Space}
    {source : P × Plane → ComplexVector} (ht : TangentInvariant θ t)
    (hs : Invariant (θ, (0 : Plane)) source) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) : Invariant (θ, (0 : Plane)) (complexCopyVelocity t source g hab k) := by
  have hr : TangentInvariant θ (realData t source) :=
    ⟨ht.normal, ht.normalDot, ht.action, ht.damping, hs.map ParticularWaveBounds.realPart⟩
  have hi : TangentInvariant θ (imagData t source) :=
    ⟨ht.normal, ht.normalDot, ht.action, ht.damping, hs.map imagPart⟩
  exact ((hr.copySolve_invariant g hab k).map CurlClassBounds.complexify).map₂
    ((hi.copySolve_invariant g hab k).map CurlClassBounds.complexify) (fun v w => v + Complex.I • w)

theorem complexCopyPressure_invariant {θ : P} {t : TangentData P ProblemStatement.Space}
    {source : P × Plane → ComplexVector} (ht : TangentInvariant θ t)
    (hs : Invariant (θ, (0 : Plane)) source) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (frequency : ℝ) :
    Invariant (θ, (0 : Plane)) (complexCopyPressure t source g hab k frequency) := by
  have hr : TangentInvariant θ (realData t source) :=
    ⟨ht.normal, ht.normalDot, ht.action, ht.damping, hs.map ParticularWaveBounds.realPart⟩
  have hi : TangentInvariant θ (imagData t source) :=
    ⟨ht.normal, ht.normalDot, ht.action, ht.damping, hs.map imagPart⟩
  exact (hr.copyPressure_invariant g hab k frequency).map₂
    (hi.copyPressure_invariant g hab k frequency) (fun v w => v + Complex.I * w)

theorem commonVelocity_invariant {θ : P} {t : TangentData P ProblemStatement.Space}
    {source : P × Plane → ComplexVector} (ht : TangentInvariant θ t)
    (hs : Invariant (θ, (0 : Plane)) source) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) : Invariant (θ, (0 : Plane)) (ParticularWaveBounds.commonVelocity t source g
        hab κ) := by
  apply Invariant.tsum_invariant
  intro k
  exact (nativeCutoff_invariant θ g κ k).map₂
    (complexCopyVelocity_invariant ht hs g hab k) (fun r v => r • v)

theorem commonPressure_invariant {θ : P} {t : TangentData P ProblemStatement.Space}
    {source : P × Plane → ComplexVector} (ht : TangentInvariant θ t)
    (hs : Invariant (θ, (0 : Plane)) source) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (frequency : ℝ) :
    Invariant (θ, (0 : Plane)) (ParticularWaveBounds.commonPressure t source g hab κ frequency) :=
        by
  apply Invariant.tsum_invariant
  intro k
  exact (nativeCutoff_invariant θ g κ k).map₂
    (complexCopyPressure_invariant ht hs g hab k frequency) (fun r v => r • v)

/-- Angle lift, defined pointwise by `f (z.1.1, z.2)`. -/
noncomputable def angleLift {E : Type} (f : P × Plane → E) : (P × ℝ) × Plane → E :=
  fun z => f (z.1.1, z.2)

theorem angleLift_invariant {E : Type} (f : P × Plane → E) :
    Invariant (((0 : P), (1 : ℝ)), (0 : Plane)) (angleLift f) := by
  rintro ⟨⟨p,θ⟩,Y⟩ t
  simp [angleLift]

/-- Angle tangent, bundling `normal`, `normalDot`, `action`, `damping` and the required
compatibility proofs. -/
noncomputable def angleTangent (t : TangentData P ProblemStatement.Space) :
    TangentData (P × ℝ) ProblemStatement.Space where
  normal := angleLift t.normal
  normalDot := angleLift t.normalDot
  action := angleLift t.action
  damping := angleLift t.damping
  source := angleLift t.source

theorem angleTangent_invariant (t : TangentData P ProblemStatement.Space) :
    TangentInvariant ((0 : P), (1 : ℝ)) (angleTangent t) :=
  ⟨angleLift_invariant _, angleLift_invariant _, angleLift_invariant _,
    angleLift_invariant _, angleLift_invariant _⟩

/-- An isometry retaining the physical angular coordinate, while moving it
into the slow-parameter product used by the Volterra construction. -/
noncomputable def angleShuffle : ((P × Plane) × ℝ) ≃ₗᵢ[ℝ] ((P × ℝ) × Plane) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv := by rintro ⟨⟨p,Y⟩,θ⟩; rfl
  right_inv := by rintro ⟨⟨p,θ⟩,Y⟩; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro r x; rfl
  norm_map' := by
    rintro ⟨⟨p,Y⟩,θ⟩
    change max (max ‖p‖ ‖θ‖) ‖Y‖ = max (max ‖p‖ ‖Y‖) ‖θ‖
    ac_rfl

theorem angleShuffle_apply (x : P × Plane) (θ : ℝ) :
    angleShuffle (x,θ) = ((x.1,θ),x.2) := rfl

theorem invariant_angleShuffle {E : Type} {f : (P × ℝ) × Plane → E}
    (hf : Invariant (((0 : P), (1 : ℝ)), (0 : Plane)) f) (x : P × Plane) (θ : ℝ) :
    f (angleShuffle (x,θ)) = f (angleShuffle (x,0)) := by
  simpa [angleShuffle] using hf (angleShuffle (x,0)) θ

end AngularConstruction

/-! ## Angular invariance of the retained differential error -/

section OperatorInvariance

open CopyAngularInvariance LinearWaveResidual LinearWaveBounds

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {θ : E} {R b F G Φ : E → ℝ} {Vr Vθ Vz Vf Vs : E → E}
variable {a : E → ComplexVector} {p : E → ℂ} {m : ℝ}

theorem principal_invariant (ε K : ℝ) (hR : Invariant θ R)
    (hF : Invariant θ F) (hG : Invariant θ G)
    (hr : Invariant θ Vr) (hθ : Invariant θ Vθ) (hz : Invariant θ Vz)
    (hf : Invariant θ Vf) (hΦ : AffinePhase θ m Φ)
    (ha : Invariant θ a) (hp : Invariant θ p) :
    Invariant θ (principal ε K R F G Vr Vθ Vz Vf Φ a p) := by
  have hN := phaseNormal_invariant hR hr hθ hz hΦ
  intro x t
  have hsh : shear R F G Vr a (x + t • θ) = shear R F G Vr a x := by
    simp only [shear, hF x t, hR x t, ha x t,
      hF.along hr x t, hG.along hr x t]
  funext i
  simp only [principal, hsh, hN x t, ha x t, hp x t, (ha.component i).along hf x t]

theorem remainder_invariant (ε K : ℝ) (hR : Invariant θ R) (hb : Invariant θ b)
    (hF : Invariant θ F) (hG : Invariant θ G)
    (hr : Invariant θ Vr) (hθ : Invariant θ Vθ) (hz : Invariant θ Vz)
    (hf : Invariant θ Vf) (hs : Invariant θ Vs) (hΦ : AffinePhase θ m Φ)
    (ha : Invariant θ a) (hp : Invariant θ p) :
    Invariant θ (remainder ε K R b F G Vr Vθ Vz Vf Vs Φ a p) := by
  have hN := phaseNormal_invariant hR hr hθ hz hΦ
  have hB := base_invariant hR hb hF hG
  have ht : Invariant θ (timeDirection ε Vf Vs) := hf.map₂ hs (fun v w => v - ε • w)
  intro x t
  have hdef : materialPhaseDefect R b F G Vr Vθ Vz (timeDirection ε Vf Vs) Φ (x + t • θ) =
      materialPhaseDefect R b F G Vr Vθ Vz (timeDirection ε Vf Vs) Φ x := by
    simp only [materialPhaseDefect, hb x t, hF x t, hG x t,
      hΦ.along_invariant ht x t, hΦ.along_invariant hr x t,
      hΦ.along_invariant hθ x t, hΦ.along_invariant hz x t]
  have hvis : viscousRemainder R Vr Vθ Vz K Φ a (x + t • θ) =
      viscousRemainder R Vr Vθ Vz K Φ a x := by
    funext i
    simp only [viscousRemainder, hR x t, ha x t, hN x t,
      (ha.component i).along hr x t, (ha.component i).along hz x t,
      ((ha.component i).along hr).along hr x t, ((ha.component i).along hz).along hz x t,
      (hN.map (fun N => N 0)).along hr x t, (hN.map (fun N => N 2)).along hz x t]
  have hder : baseDerivativeRemainder R b F G Vr Vz a (x + t • θ) =
      baseDerivativeRemainder R b F G Vr Vz a x := by
    funext i
    simp only [baseDerivativeRemainder, ha x t, hb x t, hR x t,
      hb.along hr x t, (hB.component i).along hz x t]
  have hslow : slowTransport ε b G Vs Vr Vz a (x + t • θ) =
      slowTransport ε b G Vs Vr Vz a x := by
    funext i
    simp only [slowTransport, hb x t, hG x t, (ha.component i).along hs x t,
      (ha.component i).along hr x t, (ha.component i).along hz x t]
  have hgrad : strippedPressureGradient Vr Vz p (x + t • θ) = strippedPressureGradient Vr Vz p x :=
      by
    simp only [strippedPressureGradient, hp.along hr x t, hp.along hz x t]
  funext i
  simp only [remainder, hslow, hdef, ha x t, hder, hgrad, hvis]

theorem constructedGood_invariant {s : StripData E} {d : GraphDirections E}
    {a : WaveCoefficients E} (ψ : ℕ → E → ℝ)
    (hR : ∀ n, Invariant d.angular (a.radius n))
    (hb : ∀ n, Invariant d.angular (a.radialBase n))
    (hF : ∀ n, Invariant d.angular (a.frequencyBase n))
    (hG : ∀ n, Invariant d.angular (a.axialBase n))
    (hr : ∀ n, Invariant d.angular (d.radialField n))
    (hz : ∀ n, Invariant d.angular (d.axialField s n))
    (hΦ : ∀ n, ∃ m, AffinePhase d.angular m (a.phase n))
    (ha : ∀ n, Invariant d.angular (a.amplitude n))
    (hp : ∀ n, Invariant d.angular (a.pressure n))
    (hψ : ∀ n, Invariant d.angular (ψ n)) (n : ℕ) :
    Invariant d.angular (a.constructedGood s d ψ n) := by
  obtain ⟨m, hm⟩ := hΦ n
  have hcut : Invariant d.angular ((a.withCutoff ψ).amplitude n) :=
    (hψ n).map₂ (ha n) (fun r v => r • v)
  have hcor : Invariant d.angular ((a.withCutoff ψ).curlCorrection s d n) :=
    curlRemainder_invariant (hR n) (hr n) (Invariant.const _) (hz n)
      (coefficient_invariant (hR n) (hr n) (Invariant.const _) (hz n) hm hcut) (a.frequency n)
  have hcorr := corrected_amplitude_invariant ψ hR hr hz hΦ ha hψ n
  have hpcorr := corrected_pressure_invariant (s := s) ψ hp hψ n
  exact (principal_invariant (s.epsilon n) (a.frequency n) (hR n) (hF n) (hG n)
    (hr n) (Invariant.const _) (hz n) (Invariant.const _) hm hcor (Invariant.const 0)).map₂
    (remainder_invariant (s.epsilon n) (a.frequency n) (hR n) (hb n) (hF n) (hG n)
      (hr n) (Invariant.const _) (hz n) (Invariant.const _) (Invariant.const _) hm hcorr hpcorr)
    (fun u v => u + v)

end OperatorInvariance

/-! ## Actual copy localization from an injective padded native chart -/

section NativeLocalization

open CommonCoverSolve TorusInverse TorusAverages ParticularWaveBounds

theorem native_coordinate_image (g : Geometry) (k : Frequency) (Y : Plane) :
    g.center + g.basis (g.coordinates k Y) = latticePoint (-k) + coverPower g.gap Y := by
  simp only [Geometry.coordinates, ContinuousLinearEquiv.apply_symm_apply]
  have hn : latticePoint (-k) = -latticePoint k := by ext <;> simp [latticePoint]
  rw [hn]
  abel

theorem native_copy_unique (g : Geometry) {Ω : Set Plane}
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' Ω))
    {k l : Frequency} {Y : Plane}
    (hk : g.coordinates k Y ∈ Ω) (hl : g.coordinates l Y ∈ Ω) : k = l := by
  have hk' : latticePoint (-k) + coverPower g.gap Y ∈
      (fun z => g.center + g.basis z) '' Ω :=
    ⟨g.coordinates k Y, hk, native_coordinate_image g k Y⟩
  have hl' : latticePoint (-l) + coverPower g.gap Y ∈
      (fun z => g.center + g.basis z) '' Ω :=
    ⟨g.coordinates l Y, hl, native_coordinate_image g l Y⟩
  exact neg_injective (latticeTranslate_unique hinj hk' hl')

variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace H] in
theorem periodizedCopies_eq_weighted_single (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) {Ω : Set Plane}
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' Ω))
    (hsupp : Function.support κ ⊆ Ω) (k : Frequency) (p : P × Plane)
    (hp : g.coordinates k p.2 ∈ Ω) :
    periodizedCopies g κ F p = κ (g.coordinates k p.2) • F k p := by
  unfold periodizedCopies
  apply tsum_eq_single
  intro l hl
  have hz : κ (g.coordinates l p.2) = 0 := by
    by_contra hn
    exact hl (native_copy_unique g hinj (hsupp hn) hp)
  rw [hz, zero_smul]

omit [NormedSpace ℝ P] [CompleteSpace H] in
/-- The derivative of the native cutoff is preserved. No plateau is
assumed for the active copy, so Gaussian edge derivatives are retained. -/
theorem periodizedCopies_germ (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' Ω))
    (hsupp : Function.support κ ⊆ Ω) (k : Frequency) (p : P × Plane)
    (hp : g.coordinates k p.2 ∈ Ω) :
    periodizedCopies g κ F =ᶠ[𝓝 p] (fun q => κ (g.coordinates k q.2) • F k q) := by
  have hc : Continuous (fun q : P × Plane => g.coordinates k q.2) :=
    (g.coordinates_contDiff k).continuous.comp continuous_snd
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)] with q hq
  exact periodizedCopies_eq_weighted_single g κ F hinj hsupp k q hq

omit [CompleteSpace H] in
theorem periodizedCopies_jets (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' Ω))
    (hsupp : Function.support κ ⊆ Ω) (k : Frequency) (p : P × Plane)
    (hp : g.coordinates k p.2 ∈ Ω) (m : ℕ) :
    iteratedFDeriv ℝ m (periodizedCopies g κ F) p =
      iteratedFDeriv ℝ m (fun q => κ (g.coordinates k q.2) • F k q) p := by
  have he := periodizedCopies_germ g κ F hΩ hinj hsupp k p hp
  have hw : periodizedCopies g κ F =ᶠ[𝓝[univ] p]
      (fun q => κ (g.coordinates k q.2) • F k q) := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq he.self_of_nhds m

end NativeLocalization

/-! ## The forced coefficients from the literal residual source -/

section ActualCoefficients

open CommonCoverSolve TorusInverse ParticularWaveBounds CopyAngularInvariance LinearWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem angleTangent_eq_transport (t : TangentData P ProblemStatement.Space) :
    angleTangent t = transportTangent t Prod.fst 0 1 := by
  unfold angleTangent transportTangent angleLift
  congr 1
  funext p
  simp only [coverPower, ContinuousLinearEquiv.refl_apply, one_smul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem angleSource_eq_transport (f : P × Plane → ComplexVector) :
    angleLift f = transportSource f Prod.fst 0 1 := by
  funext p
  simp only [angleLift, transportSource, coverPower, ContinuousLinearEquiv.refl_apply, one_smul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyVelocity_angle (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (copy : Frequency) (p : P) (θ : ℝ) (Y : Plane) :
    complexCopyVelocity (angleTangent t) (angleLift source) g hab copy ((p,θ),Y) =
      complexCopyVelocity t source g hab copy (p,Y) := by
  have he := complexCopyVelocity_transport t source (Prod.fst : P × ℝ → P) g hab 0 1 copy (p,θ) Y
  simpa only [← angleTangent_eq_transport, ← angleSource_eq_transport,
    CopySolveCompatibility.refineGeometry, Nat.add_zero, coverPower,
    ContinuousLinearEquiv.refl_apply, one_smul] using he

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyPressure_angle (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (copy : Frequency) {K : ℝ} (hK : K ≠ 0) (p : P) (θ : ℝ) (Y : Plane) :
    complexCopyPressure (angleTangent t) (angleLift source) g hab copy K ((p,θ),Y) =
      complexCopyPressure t source g hab copy K (p,Y) := by
  have he := complexCopyPressure_transport t source (Prod.fst : P × ℝ → P) g hab 0 1 K K hK hK copy
      (p,θ) Y
  simpa only [← angleTangent_eq_transport, ← angleSource_eq_transport,
    CopySolveCompatibility.refineGeometry, Nat.add_zero, coverPower,
    ContinuousLinearEquiv.refl_apply, one_mul, div_self hK, one_smul] using he

/-- Frequency and phase are constructed from the original residual block.
Only the background fields of `base` are retained. -/
noncomputable def actualCarrier (base : WaveCoefficients ((P × ℝ) × Plane))
    (b : HarmonicBlock (P × Plane)) (j : ℤ) : WaveCoefficients ((P × ℝ) × Plane) :=
  { base with
    phase := fun n z => b.phase n (z.1.1,z.2) + (b.angularFrequency n : ℝ) / b.frequency n * z.1.2
    frequency := fun n => (j : ℝ) * b.frequency n }

theorem actualCarrier_phase (base : WaveCoefficients ((P × ℝ) × Plane))
    (b : HarmonicBlock (P × Plane)) (j : ℤ) (hfrequency : ∀ n, b.frequency n ≠ 0)
    (n : ℕ) (x : P × Plane) (θ : ℝ) :
    (actualCarrier base b j).frequency n * (actualCarrier base b j).phase n (angleShuffle (x,θ)) =
      (j : ℝ) * (b.frequency n * b.phase n x + (b.angularFrequency n : ℝ) * θ) := by
  change ((j : ℝ) * b.frequency n) *
    (b.phase n x + (b.angularFrequency n : ℝ) / b.frequency n * θ) = _
  field_simp [hfrequency n]

theorem actualCarrier_affine (base : WaveCoefficients ((P × ℝ) × Plane))
    (b : HarmonicBlock (P × Plane)) (j : ℤ) (n : ℕ) :
    AffinePhase (((0 : P), (1 : ℝ)), (0 : Plane))
      ((b.angularFrequency n : ℝ) / b.frequency n) ((actualCarrier base b j).phase n) := by
  rintro ⟨⟨p,θ⟩,Y⟩ t
  simp only [actualCarrier, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_zero, add_zero, smul_eq_mul, mul_one]
  ring

/-- Actual copy coefficients, constructed using `complexCopyCoefficients`. -/
noncomputable def actualCopyCoefficients (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (copy : ℕ → Frequency) :
    WaveCoefficients ((P × ℝ) × Plane) :=
  complexCopyCoefficients (actualCarrier base b j)
    (fun n => angleTangent (bandTangent r charts j n))
    (fun n => angleLift (residualSource c u b G A j n))
    (bandGeometry r charts) copy (fun _ => r.length) (fun _ => r.length_pos)

/-- Actual common coefficients as an element of `WaveCoefficients ((P × ℝ) × Plane)`. -/
noncomputable def actualCommonCoefficients (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) : WaveCoefficients ((P × ℝ) × Plane) :=
  { actualCarrier base b j with
    amplitude := fun n => angleLift (actualBandVelocity r charts c u b G A j n)
    pressure := fun n => angleLift (actualBandPressure r charts c u b G A j n) }

theorem actualCopy_amplitude_invariant (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (copy : ℕ → Frequency) (n : ℕ) :
    Invariant (((0 : P), (1 : ℝ)), (0 : Plane))
      ((actualCopyCoefficients r charts c u b G A j base copy).amplitude n) :=
  complexCopyVelocity_invariant (angleTangent_invariant _) (angleLift_invariant _)
    _ r.length_pos.le (copy n)

theorem actualCopy_pressure_invariant (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (copy : ℕ → Frequency) (n : ℕ) :
    Invariant (((0 : P), (1 : ℝ)), (0 : Plane))
      ((actualCopyCoefficients r charts c u b G A j base copy).pressure n) :=
  complexCopyPressure_invariant (angleTangent_invariant _) (angleLift_invariant _)
    _ r.length_pos.le (copy n) _

theorem actualCommon_amplitude_periodization (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (n : ℕ) :
    (actualCommonCoefficients r charts c u b G A j base).amplitude n =
      periodizedCopies (bandGeometry r charts n) r.cutoff
        (fun k => complexCopyVelocity (angleTangent (bandTangent r charts j n))
          (angleLift (residualSource c u b G A j n)) (bandGeometry r charts n) r.length_pos.le k)
              := by
  funext z
  rcases z with ⟨⟨p,θ⟩,Y⟩
  apply tsum_congr
  intro k
  exact congrArg (fun v => r.cutoff ((bandGeometry r charts n).coordinates k Y) • v)
    (complexCopyVelocity_angle (bandTangent r charts j n) (residualSource c u b G A j n)
      (bandGeometry r charts n) r.length_pos.le k p θ Y).symm

theorem actualCommon_pressure_periodization (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) {j : ℤ} (hj : j ≠ 0)
    (hfrequency : ∀ n, b.frequency n ≠ 0)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (n : ℕ) :
    (actualCommonCoefficients r charts c u b G A j base).pressure n =
      periodizedCopies (bandGeometry r charts n) r.cutoff
        (fun k => complexCopyPressure (angleTangent (bandTangent r charts j n))
          (angleLift (residualSource c u b G A j n)) (bandGeometry r charts n) r.length_pos.le k
          ((j : ℝ) * b.frequency n)) := by
  have hK : (j : ℝ) * b.frequency n ≠ 0 := mul_ne_zero (by exact_mod_cast hj) (hfrequency n)
  funext z
  rcases z with ⟨⟨p,θ⟩,Y⟩
  apply tsum_congr
  intro k
  exact congrArg (fun v => r.cutoff ((bandGeometry r charts n).coordinates k Y) • v)
    (complexCopyPressure_angle (bandTangent r charts j n) (residualSource c u b G A j n)
      (bandGeometry r charts n) r.length_pos.le k hK p θ Y).symm

end ActualCoefficients

/-! ## Germ transport through the actual differential operators -/

section DifferentialGerms

open Filter LinearWaveResidual
open CurlClassBounds hiding ComplexVector

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem along_germ {f g : E → F} {x : E} (h : f =ᶠ[𝓝 x] g) (V : E → E) :
    along V f =ᶠ[𝓝 x] along V g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp only [along, hy]

theorem curl_germ {a b : E → ComplexVector} {x : E} (h : a =ᶠ[𝓝 x] b)
    (R : E → ℝ) (Vr Vθ Vz : E → E) :
    cylindricalCurl R Vr Vθ Vz a =ᶠ[𝓝 x] cylindricalCurl R Vr Vθ Vz b := by
  have hr (i : Fin 3) := along_germ (h.fun_comp (fun v => v i)) Vr
  have hθ (i : Fin 3) := along_germ (h.fun_comp (fun v => v i)) Vθ
  have hz (i : Fin 3) := along_germ (h.fun_comp (fun v => v i)) Vz
  filter_upwards [h, Filter.eventually_all.mpr hr, Filter.eventually_all.mpr hθ,
    Filter.eventually_all.mpr hz] with y hy hyr hyθ hyz
  dsimp only [Function.comp_def] at hyr hyθ hyz
  simp only [cylindricalCurl, hyr, hyθ, hyz, hy]

theorem realizedCoefficient_germ {a b : E → ComplexVector} {x : E} (h : a =ᶠ[𝓝 x] b)
    (K : ℝ) (R : E → ℝ) (Vr Vθ Vz : E → E) (Φ : E → ℝ) :
    realizedCoefficient K R Vr Vθ Vz Φ a =ᶠ[𝓝 x]
      realizedCoefficient K R Vr Vθ Vz Φ b := by
  have hc : coefficient R Vr Vθ Vz Φ a =ᶠ[𝓝 x] coefficient R Vr Vθ Vz Φ b := by
    filter_upwards [h] with y hy
    simp only [coefficient, hy]
  filter_upwards [h, curl_germ hc R Vr Vθ Vz] with y hy hcy
  simp only [realizedCoefficient, curlRemainder, hy, hcy]

omit [NormedSpace ℝ E] in
theorem vectorMode_germ {a b : E → ComplexVector} {x : E} (h : a =ᶠ[𝓝 x] b)
    (K : ℝ) (Φ : E → ℝ) : vectorMode K Φ a =ᶠ[𝓝 x] vectorMode K Φ b := by
  filter_upwards [h] with y hy
  funext i
  simp only [vectorMode, mode, hy]

omit [NormedSpace ℝ E] in
theorem mode_germ {p q : E → ℂ} {x : E} (h : p =ᶠ[𝓝 x] q)
    (K : ℝ) (Φ : E → ℝ) : mode K Φ p =ᶠ[𝓝 x] mode K Φ q := by
  filter_upwards [h] with y hy
  simp only [mode, hy]

theorem laplacian_germ {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g)
    (R : E → ℝ) (Vr Vθ Vz : E → E) :
    cylindricalLaplacian R Vr Vθ Vz f =ᶠ[𝓝 x] cylindricalLaplacian R Vr Vθ Vz g := by
  filter_upwards [along_germ (along_germ h Vr) Vr, along_germ h Vr,
    along_germ (along_germ h Vθ) Vθ, along_germ (along_germ h Vz) Vz] with y hrr hr hθθ hzz
  simp only [cylindricalLaplacian, hrr, hr, hθθ, hzz]

theorem vectorLaplacian_germ {a b : E → ComplexVector} {x : E} (h : a =ᶠ[𝓝 x] b)
    (R : E → ℝ) (Vr Vθ Vz : E → E) :
    cylindricalVectorLaplacian R Vr Vθ Vz a =ᶠ[𝓝 x] cylindricalVectorLaplacian R Vr Vθ Vz b := by
  have hl (i : Fin 3) := laplacian_germ (h.fun_comp (fun v => v i)) R Vr Vθ Vz
  have hθ (i : Fin 3) := along_germ (h.fun_comp (fun v => v i)) Vθ
  filter_upwards [h, Filter.eventually_all.mpr hl, Filter.eventually_all.mpr hθ] with y hy hly hyθ
  dsimp only [Function.comp_def] at hly hyθ
  have he : (fun i => along Vθ (fun y => a y i) y) = (fun i => along Vθ (fun y => b y i) y) :=
      funext hyθ
  funext i
  simp only [cylindricalVectorLaplacian, hly, he, hy]

theorem linearResidual_germ {a b : E → ComplexVector} {p q : E → ℂ} {x : E}
    (ha : a =ᶠ[𝓝 x] b) (hp : p =ᶠ[𝓝 x] q)
    (ε : ℝ) (R : E → ℝ) (Vr Vθ Vz Vt : E → E) (B : E → ComplexVector) :
    linearResidual ε R Vr Vθ Vz Vt B a p =ᶠ[𝓝 x] linearResidual ε R Vr Vθ Vz Vt B b q := by
  have hr (i : Fin 3) := along_germ (ha.fun_comp (fun v => v i)) Vr
  have hθ (i : Fin 3) := along_germ (ha.fun_comp (fun v => v i)) Vθ
  have hz (i : Fin 3) := along_germ (ha.fun_comp (fun v => v i)) Vz
  have ht (i : Fin 3) := along_germ (ha.fun_comp (fun v => v i)) Vt
  filter_upwards [ha, Filter.eventually_all.mpr hr, Filter.eventually_all.mpr hθ,
    Filter.eventually_all.mpr hz, Filter.eventually_all.mpr ht,
    along_germ hp Vr, along_germ hp Vθ, along_germ hp Vz,
    vectorLaplacian_germ ha R Vr Vθ Vz] with y hay hry hθy hzy hty hpr hpθ hpz hl
  dsimp only [Function.comp_def] at hry hθy hzy hty
  funext i
  simp only [linearResidual, transport, gradient, hry, hθy, hzy, hty, hay, hpr, hpθ, hpz, hl]

end DifferentialGerms

/-! ## Common physical coefficient and its exact local curl -/

section CommonLocalCurl

open CommonCoverSolve TorusInverse TorusAverages ParticularWaveBounds LinearWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Native cutoff, defined pointwise by `r.cutoff ((bandGeometry r charts n).coordinates (copy
n) z.2)`. -/
noncomputable def nativeCutoff (r : Reference P) (charts : BandCharts P) (copy : ℕ → Frequency) :
    ℕ → (P × ℝ) × Plane → ℝ :=
  fun n z => r.cutoff ((bandGeometry r charts n).coordinates (copy n) z.2)

/-- The common coefficient already contains its single native cutoff.
Its correction is the actual cylindrical curl correction of that coefficient. -/
noncomputable def actualCorrectedCommon (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (s : StripData ((P × ℝ) × Plane))
    (dirs : GraphDirections ((P × ℝ) × Plane)) : WaveCoefficients ((P × ℝ) × Plane) :=
  let a := actualCommonCoefficients r charts c u b G A j base
  a.addAmplitude (a.curlCorrection s dirs)

theorem actualCommon_raw_germ (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) {j : ℤ} (hj : j ≠ 0)
    (hfrequency : ∀ n, b.frequency n ≠ 0)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (copy : ℕ → Frequency)
    (ψ : ℕ → (P × ℝ) × Plane → ℝ) (n : ℕ) (x : (P × ℝ) × Plane)
    {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hinj : InjOn quotientPoint ((fun z => (bandGeometry r charts n).center +
      (bandGeometry r charts n).basis z) '' Ω))
    (hsupp : Function.support r.cutoff ⊆ Ω)
    (hx : (bandGeometry r charts n).coordinates (copy n) x.2 ∈ Ω)
    (hψ : nativeCutoff r charts copy n =ᶠ[𝓝 x] ψ n) :
    (actualCommonCoefficients r charts c u b G A j base).amplitude n =ᶠ[𝓝 x]
      (((actualCopyCoefficients r charts c u b G A j base copy).withCutoff ψ).amplitude n) ∧
    (actualCommonCoefficients r charts c u b G A j base).pressure n =ᶠ[𝓝 x]
      (((actualCopyCoefficients r charts c u b G A j base copy).withCutoff ψ).pressure n) := by
  constructor
  · rw [actualCommon_amplitude_periodization]
    have he := periodizedCopies_germ (bandGeometry r charts n) r.cutoff
      (fun k => complexCopyVelocity (angleTangent (bandTangent r charts j n))
        (angleLift (residualSource c u b G A j n)) (bandGeometry r charts n) r.length_pos.le k)
      hΩ hinj hsupp (copy n) x hx
    filter_upwards [he, hψ] with y hy hψy
    change _ = ψ n y • _
    rw [hy, ← hψy]
    rfl
  · rw [actualCommon_pressure_periodization r charts c u b G A hj hfrequency]
    have he := periodizedCopies_germ (bandGeometry r charts n) r.cutoff
      (fun k => complexCopyPressure (angleTangent (bandTangent r charts j n))
        (angleLift (residualSource c u b G A j n)) (bandGeometry r charts n) r.length_pos.le k
        ((j : ℝ) * b.frequency n)) hΩ hinj hsupp (copy n) x hx
    filter_upwards [he, hψ] with y hy hψy
    change _ = (ψ n y : ℂ) * _
    rw [hy, ← hψy]
    rfl

theorem actualCommon_corrected_germ (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) {j : ℤ} (hj : j ≠ 0)
    (hfrequency : ∀ n, b.frequency n ≠ 0)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (copy : ℕ → Frequency)
    (s : StripData ((P × ℝ) × Plane)) (dirs : GraphDirections ((P × ℝ) × Plane))
    (ψ : ℕ → (P × ℝ) × Plane → ℝ) (n : ℕ) (x : (P × ℝ) × Plane)
    {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hinj : InjOn quotientPoint ((fun z => (bandGeometry r charts n).center +
      (bandGeometry r charts n).basis z) '' Ω))
    (hsupp : Function.support r.cutoff ⊆ Ω)
    (hx : (bandGeometry r charts n).coordinates (copy n) x.2 ∈ Ω)
    (hψ : nativeCutoff r charts copy n =ᶠ[𝓝 x] ψ n) :
    (actualCorrectedCommon r charts c u b G A j base s dirs).amplitude n =ᶠ[𝓝 x]
      (((actualCopyCoefficients r charts c u b G A j base copy).corrected s dirs ψ).amplitude n) ∧
    (actualCorrectedCommon r charts c u b G A j base s dirs).pressure n =ᶠ[𝓝 x]
      (((actualCopyCoefficients r charts c u b G A j base copy).corrected s dirs ψ).pressure n) :=
          by
  obtain ⟨ha,hp⟩ := actualCommon_raw_germ r charts c u b G A hj hfrequency base copy ψ n x
    hΩ hinj hsupp hx hψ
  refine ⟨?_, hp⟩
  exact realizedCoefficient_germ ha ((j : ℝ) * b.frequency n) (base.radius n)
    (dirs.radialField n) (fun _ => dirs.angular) (dirs.axialField s n) ((actualCarrier base b
        j).phase n)

theorem actualCommon_residual_germ (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) {j : ℤ} (hj : j ≠ 0)
    (hfrequency : ∀ n, b.frequency n ≠ 0)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (copy : ℕ → Frequency)
    (s : StripData ((P × ℝ) × Plane)) (dirs : GraphDirections ((P × ℝ) × Plane))
    (ψ : ℕ → (P × ℝ) × Plane → ℝ) (n : ℕ) (x : (P × ℝ) × Plane)
    {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hinj : InjOn quotientPoint ((fun z => (bandGeometry r charts n).center +
      (bandGeometry r charts n).basis z) '' Ω))
    (hsupp : Function.support r.cutoff ⊆ Ω)
    (hx : (bandGeometry r charts n).coordinates (copy n) x.2 ∈ Ω)
    (hψ : nativeCutoff r charts copy n =ᶠ[𝓝 x] ψ n) :
    (actualCorrectedCommon r charts c u b G A j base s dirs).harmonicResidual s dirs n =ᶠ[𝓝 x]
      (((actualCopyCoefficients r charts c u b G A j base copy).corrected s dirs
          ψ).harmonicResidual s dirs n) := by
  obtain ⟨ha,hp⟩ := actualCommon_corrected_germ r charts c u b G A hj hfrequency base copy s dirs ψ
      n x
    hΩ hinj hsupp hx hψ
  exact linearResidual_germ
    (vectorMode_germ ha ((j : ℝ) * b.frequency n) ((actualCarrier base b j).phase n))
    (mode_germ hp ((j : ℝ) * b.frequency n) ((actualCarrier base b j).phase n))
    (s.epsilon n) (base.radius n) (dirs.radialField n) (fun _ => dirs.angular) (dirs.axialField s n)
    (LinearWaveResidual.timeDirection (s.epsilon n) (dirs.fastField n) (fun _ => dirs.slow))
    (LinearWaveResidual.complexBase (base.radius n) (base.radialBase n)
      (base.frequencyBase n) (base.axialBase n))

end CommonLocalCurl

/-! ## Finite fields at the original residual carrier -/

theorem modeBlock_value {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ)
    (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (modeBlock j k Φ kp v p).oscillation n x i =
      (v n x.1 i * character j (k n * Φ n x.1 + (kp n : ℝ) * x.2)).re := by
  change (field (conjugatePair j (fun y => v n y i)) (k n) (Φ n) (kp n) x).re = _
  rw [field_conjugatePair, Complex.ofReal_re]

theorem modeBlock_pressure_value {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ)
    (n : ℕ) (x : D × ℝ) :
    (modeBlock j k Φ kp v p).oscillatoryPressure n x =
      (p n x.1 * character j (k n * Φ n x.1 + (kp n : ℝ) * x.2)).re := by
  change (field (conjugatePair j (p n)) (k n) (Φ n) (kp n) x).re = _
  rw [field_conjugatePair, Complex.ofReal_re]

theorem assembledBlock_value {D : Type} (N : ℕ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℤ → ℕ → D → ComplexVector) (p : ℤ → ℕ → D → ℂ)
    (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (assembledBlock N k Φ kp v p).oscillation n x i =
      ∑ j ∈ modes N, (v j n x.1 i * character j (k n * Φ n x.1 + (kp n : ℝ) * x.2)).re := by
  have he := sumBlock_represents (modes N) k Φ kp (fun j => modeBlock j k Φ kp (v j) (p j))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  change (sumBlock (modes N) k Φ kp (fun j => modeBlock j k Φ kp (v j) (p j))).oscillation n x i = _
  rw [he]
  simp only [Finset.sum_apply, modeBlock_value]

theorem assembledBlock_pressure_value {D : Type} (N : ℕ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (v : ℤ → ℕ → D → ComplexVector) (p : ℤ → ℕ → D → ℂ)
    (n : ℕ) (x : D × ℝ) :
    (assembledBlock N k Φ kp v p).oscillatoryPressure n x =
      ∑ j ∈ modes N, (p j n x.1 * character j (k n * Φ n x.1 + (kp n : ℝ) * x.2)).re := by
  classical
  change (field (∑ j ∈ modes N, (modeBlock j k Φ kp (v j) (p j)).pressure n)
    (k n) (Φ n) (kp n) x).re = _
  simp only [field, evaluate_eq_hom, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact modeBlock_pressure_value j k Φ kp (v j) (p j) n x

theorem residualSource_field {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (c : Context D) (u : State D) (b : HarmonicBlock D)
    (G A : HarmonicResidual.BlockCoefficients D) (N : ℕ)
    (hN : (HarmonicResidual.residualBlock c u b G A).BandLimited N)
    (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (HarmonicResidual.residualBlock c u b G A).oscillation n x i =
      ∑ j ∈ modes N, (residualSource c u b G A j n x.1 i *
        character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) * x.2)).re := by
  rw [← assembledBlock_value N b.frequency b.phase b.angularFrequency
    (residualSource c u b G A) (fun _ _ _ => 0)]
  change (field _ (b.frequency n) (b.phase n) (b.angularFrequency n) x).re =
    (field _ (b.frequency n) (b.phase n) (b.angularFrequency n) x).re
  rw [residualSource_reconstruct c u b G A N hN n i]

theorem finite_cancellation {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (c : Context D) (u : State D) (b : HarmonicBlock D)
    (G A : HarmonicResidual.BlockCoefficients D) (N : ℕ)
    (hN : (HarmonicResidual.residualBlock c u b G A).BandLimited N)
    (res : ℤ → ℕ → D × ℝ → ComplexVector)
    (good gaussian : ℤ → ℕ → D → ComplexVector)
    (n : ℕ) (x : D × ℝ)
    (hcancel : ∀ j ∈ modes N, ∀ i,
      res j n x i + residualSource c u b G A j n x.1 i *
        character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) * x.2) =
      (good j n x.1 i + gaussian j n x.1 i) *
        character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) * x.2)) :
    (fun i => ∑ j ∈ modes N, (res j n x i).re) +
        (HarmonicResidual.residualBlock c u b G A).oscillation n x =
      (assembledBlock N b.frequency b.phase b.angularFrequency good (fun _ _ _ => 0)).oscillation n
          x +
        (assembledBlock N b.frequency b.phase b.angularFrequency gaussian (fun _ _ _ =>
            0)).oscillation n x := by
  funext i
  simp only [Pi.add_apply, residualSource_field c u b G A N hN, assembledBlock_value]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hh := congrArg Complex.re (hcancel j hj i)
  simpa only [Complex.add_re, add_mul] using hh

/-- The real differential operator commutes with the actual finite sum
of real parts. This connects the coefficient cancellation to one field. -/
theorem real_linearResidual_sum {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Finset ι) {U : Set E} (hU : IsOpen U) (ε : ℝ) (R : E → ℝ)
    {Vr Vθ Vz : E → E} (Vt : E → E)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (B : E → Fin 3 → ℝ) (v : ι → E → ComplexVector) (p : ι → E → ℂ)
    (hv : ∀ l ∈ J, ∀ i, ContDiffOn ℝ ∞ (fun y => v l y i) U)
    (hp : ∀ l ∈ J, ContDiffOn ℝ ∞ (p l) U) {x : E}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x) (hx : x ∈ U) :
    LinearWaveResidual.realComponentLinearResidual ε R Vr Vθ Vz Vt B
      (fun y i => ∑ l ∈ J, (v l y i).re) (fun y => ∑ l ∈ J, (p l y).re) x =
        fun i => ∑ l ∈ J, (LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt
          (LinearWaveResidual.realLift B) (v l) (p l) x i).re := by
  have hs (i : Fin 3) : ContDiffOn ℝ ∞ (fun y => (∑ l ∈ J, v l) y i) U := by
    simpa only [Finset.sum_apply] using ContDiffOn.sum (fun l hl => hv l hl i)
  have hps : ContDiffOn ℝ ∞ (fun y => (∑ l ∈ J, p l) y) U := by
    simpa only [Finset.sum_apply] using ContDiffOn.sum hp
  have he := LinearWaveResidual.realMap_linearResidual Complex.reCLM ε R Vt hU hr hθ hz hs hB
    ((hps.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) hx
  rw [HarmonicResidual.Actual.linearResidual_sum J hU ε R Vt hr hθ hz
    (LinearWaveResidual.realLift B) v p hv hp hx] at he
  simpa only [Finset.sum_apply, Complex.reCLM_apply, Complex.re_sum] using he.symm

/-! ## Restriction of actual native coefficients to the angular section -/

section NativeBlocks

open CommonCoverSolve TorusInverse ParticularWaveBounds CopyAngularInvariance LinearWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Section strip, given by `SignedWaveUpdate.sectionStrip (reindexStrip (angleShuffle (P := P))
s)`. -/
noncomputable def sectionStrip (s : StripData ((P × ℝ) × Plane)) : StripData (P × Plane) :=
  SignedWaveUpdate.sectionStrip (reindexStrip (angleShuffle (P := P)) s)

/-- Native mode block, given by `fullModeBlock j b.frequency b.phase b.angularFrequency
(reindexCoefficients angleShuffle a)`. -/
noncomputable def nativeModeBlock (j : ℤ) (b : HarmonicBlock (P × Plane))
    (a : WaveCoefficients ((P × ℝ) × Plane)) : HarmonicBlock (P × Plane) :=
  fullModeBlock j b.frequency b.phase b.angularFrequency (reindexCoefficients angleShuffle a)

theorem nativeSlice_class {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : StripData ((P × ℝ) × Plane)} {w : ℕ → (P × ℝ) × Plane → ℝ} {α : ℝ}
    {f : ℕ → (P × ℝ) × Plane → F} (hf : MemClass s w α f) :
    MemClass (sectionStrip s) (fun n x => w n (angleShuffle (x,0))) α
      (fun n x => f n (angleShuffle (x,0))) := by
  have he : MemClass (reindexStrip (angleShuffle (P := P)) s)
      (fun n x => w n (angleShuffle x)) α (fun n x => f n (angleShuffle x)) :=
    memClass_reindex (angleShuffle (P := P)) hf
  exact SignedWaveUpdate.class_zeroSection (D := P × Plane) (E := F) he

theorem nativeSlice_waveClass {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : StripData ((P × ℝ) × Plane)} {W : ℕ → (P × ℝ) × Plane → ℝ} {α : ℝ}
    {f : ℕ → (P × ℝ) × Plane → F} (hf : WaveClass s W α f) :
    WaveClass (sectionStrip s) (fun n x => W n (angleShuffle (x,0))) α
      (fun n x => f n (angleShuffle (x,0))) := nativeSlice_class hf

theorem nativeModeBlock_classes {s : StripData ((P × ℝ) × Plane)}
    {W : ℕ → (P × ℝ) × Plane → ℝ} {α γ : ℝ}
    (j : ℤ) (b : HarmonicBlock (P × Plane)) (a : WaveCoefficients ((P × ℝ) × Plane))
    (ha : WaveClass s W α a.amplitude) (hp : WaveClass s W γ a.pressure) :
    (nativeModeBlock j b a).WaveBounds (sectionStrip s) (fun n x => W n (angleShuffle (x,0))) α ∧
    (nativeModeBlock j b a).PressureBounds (sectionStrip s) (fun n x => W n (angleShuffle (x,0))) γ
        :=
  modeBlock_classes j b.frequency b.phase b.angularFrequency (nativeSlice_waveClass ha)
      (nativeSlice_waveClass hp)

theorem nativeModeBlock_represents (j : ℤ) (b : HarmonicBlock (P × Plane))
    (a : WaveCoefficients ((P × ℝ) × Plane))
    (ha : ∀ n, Invariant (((0 : P), (1 : ℝ)), (0 : Plane)) (a.amplitude n))
    (hp : ∀ n, Invariant (((0 : P), (1 : ℝ)), (0 : Plane)) (a.pressure n))
    (hphase : ∀ n x θ, a.frequency n * a.phase n (angleShuffle (x, θ)) =
      (j : ℝ) * (b.frequency n * b.phase n x + (b.angularFrequency n : ℝ) * θ)) :
    (nativeModeBlock j b a).oscillation =
      (fun n x i => (vectorMode (a.frequency n) (a.phase n) (a.amplitude n) (angleShuffle x) i).re)
          ∧
    (nativeModeBlock j b a).oscillatoryPressure =
      (fun n x => (mode (a.frequency n) (a.phase n) (a.pressure n) (angleShuffle x)).re) := by
  exact fullModeBlock_represents j b.frequency b.phase b.angularFrequency (reindexCoefficients
      angleShuffle a)
    (fun n x θ => invariant_angleShuffle (ha n) x θ)
    (fun n x θ => invariant_angleShuffle (hp n) x θ) hphase

theorem actualCarrier_character (base : WaveCoefficients ((P × ℝ) × Plane))
    (b : HarmonicBlock (P × Plane)) (j : ℤ) (hfrequency : ∀ n, b.frequency n ≠ 0)
    (n : ℕ) (x : (P × Plane) × ℝ) :
    carrier ((actualCarrier base b j).frequency n) ((actualCarrier base b j).phase n) (angleShuffle
        x) =
      character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) * x.2) := by
  have he := congrArg Complex.ofReal (actualCarrier_phase base b j hfrequency n x.1 x.2)
  push_cast at he
  unfold character carrier phaseFactor
  congr 1
  push_cast
  rw [← he]
  ring

end NativeBlocks


/-! ## Primitive controls for the actual residual-source construction -/

section ConstructedControls

open Filter

open CommonCoverSolve TorusInverse HarmonicCalculus WeightedClasses LinearWaveBounds
open ParticularWaveBounds CopyAngularInvariance CorrectionState

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Source family, defined pointwise by `angleLift (residualSource c u b G A j n)`. -/
noncomputable def sourceFamily (c : Context (P × Plane)) (u : State (P × Plane))
    (b : HarmonicBlock (P × Plane)) (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) :
    ℕ → (P × ℝ) × Plane → ComplexVector :=
  fun n => angleLift (residualSource c u b G A j n)

/-- Tangent family, defined pointwise by `angleTangent (bandTangent r charts j n)`. -/
noncomputable def tangentFamily (r : Reference P) (charts : BandCharts P) (j : ℤ) :
    ℕ → TangentData (P × ℝ) ProblemStatement.Space :=
  fun n => angleTangent (bandTangent r charts j n)

/-- Envelope weight, defined pointwise by `W n ((bandGeometry r charts n).coordinates (copy n)
p.2).2`. -/
noncomputable def envelopeWeight (r : Reference P) (charts : BandCharts P)
    (copy : ℕ → Frequency) (W : ℕ → ℝ → ℝ) : ℕ → (P × ℝ) × Plane → ℝ :=
  fun n p => W n ((bandGeometry r charts n).coordinates (copy n) p.2).2

/-- Differential and angular facts about the primitive background fields.
No solved amplitude, pressure, or error estimate is stored here. -/
structure BackgroundControl (s : StripData ((P × ℝ) × Plane))
    (dirs : GraphDirections ((P × ℝ) × Plane)) (base : WaveCoefficients ((P × ℝ) × Plane))
    (b : HarmonicBlock (P × Plane)) (j : ℤ) : Prop where
  angular : dirs.angular = (((0 : P), (1 : ℝ)), (0 : Plane))
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ ((actualCarrier base b j).phase n) s.domain
  radius_ne : ∀ n x, x ∈ s.domain → base.radius n x ≠ 0
  radial_radius : ∀ n x, x ∈ s.domain → along (dirs.radialField n) (base.radius n) x = 1
  radius_invariant : ∀ n, Invariant dirs.angular (base.radius n)
  radial_base_invariant : ∀ n, Invariant dirs.angular (base.radialBase n)
  frequency_base_invariant : ∀ n, Invariant dirs.angular (base.frequencyBase n)
  axial_base_invariant : ∀ n, Invariant dirs.angular (base.axialBase n)
  radial_invariant : ∀ n, Invariant dirs.angular (dirs.radialField n)
  axial_invariant : ∀ n, Invariant dirs.angular (dirs.axialField s n)
  cylindrical : ∀ n, CurlClassBounds.CylindricalGeometry s.domain (base.radius n)
    (dirs.radialField n) (fun _ => dirs.angular) (dirs.axialField s n)

/-- Primitive modal, background, envelope, and native-chart input bounds
for the actual HR-source constructor. Every solution and residual below
is computed, rather than supplied as a record field. -/
structure LocalControl (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (copy : ℕ → Frequency)
    (s : StripData ((P × ℝ) × Plane)) (dirs : GraphDirections ((P × ℝ) × Plane)) (α κ : ℝ) where
  harmonic_ne : j ≠ 0
  frequency_ne : ∀ n, b.frequency n ≠ 0
  /-- Envelope of `LocalControl`, of type `ℕ → ℝ → ℝ`. -/
  envelope : ℕ → ℝ → ℝ
  /-- Frame of `LocalControl`, of type `ℕ → PrimaryODE.FrameData ((P × ℝ) × ℝ)`. -/
  frame : ℕ → PrimaryODE.FrameData ((P × ℝ) × ℝ)
  /-- Modal real supplied by `LocalControl`. -/
  modalReal : ModalCopyControl s α frame
    (fun n => realData (tangentFamily r charts j n) (sourceFamily c u b G A j n))
    j (bandGeometry r charts) copy (fun _ => r.length) envelope
  /-- Modal imag supplied by `LocalControl`. -/
  modalImag : ModalCopyControl s α frame
    (fun n => imagData (tangentFamily r charts j n) (sourceFamily c u b G A j n))
    j (bandGeometry r charts) copy (fun _ => r.length) envelope
  base_bounds : InputBounds s (envelopeWeight r charts copy envelope) α κ dirs
    (zeroAmplitudes (actualCarrier base b j))
  background : BackgroundControl s dirs base b j
  normal_jets : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
    (fun n x => (tangentFamily r charts j n).normal (nativePoint (bandGeometry r charts n) (copy n)
        x))
  normal_derivative : UnweightedClass s 0
    (fun n x => (tangentFamily r charts j n).normalDot (nativePoint (bandGeometry r charts n) (copy
        n) x))
  action_bounds : UnweightedClass s 0
    (fun n x => (tangentFamily r charts j n).action (nativePoint (bandGeometry r charts n) (copy n)
        x))
  source_bounds : WaveClass s (envelopeWeight r charts copy envelope) α (sourceFamily c u b G A j)
  /-- Normal min of `LocalControl`, of type `ℝ`. -/
  normalMin : ℝ
  /-- Normal max of `LocalControl`, of type `ℝ`. -/
  normalMax : ℝ
  normal_min_pos : 0 < normalMin
  normal_lower : ∀ n x, x ∈ s.domain → normalMin ≤
    ‖(tangentFamily r charts j n).normal (nativePoint (bandGeometry r charts n) (copy n) x)‖
  normal_upper : ∀ n x, x ∈ s.domain →
    ‖(tangentFamily r charts j n).normal (nativePoint (bandGeometry r charts n) (copy n) x)‖ ≤
        normalMax
  inverse_frequency : BandBound s (1 / 2) (fun n => 1 / ((j : ℝ) * b.frequency n))
  geometry : CopyGeometryMatch s dirs (actualCarrier base b j) (tangentFamily r charts j)
    (bandGeometry r charts) copy
  loss_le_half : κ ≤ 1 / 2
  /-- Radius of `LocalControl`, of type `(P × ℝ) × Plane → ℝ`. -/
  radius : (P × ℝ) × Plane → ℝ
  radius_eq : base.radius = fun _ => radius
  /-- Slot of `LocalControl`, of type `GaussianTailFlat.SlotFamily s`. -/
  slot : GaussianTailFlat.SlotFamily s
  slot_angular : ∀ n, slot.linear n dirs.angular = 0
  slot_fast : ∀ n, slot.linear n (dirs.fastScale n • dirs.fast) = (slot.length n)⁻¹
  /-- Flat edges of `LocalControl`, of type `GaussianTailFlat.FlatEdges s`. -/
  flatEdges : GaussianTailFlat.FlatEdges s
  /-- Band scales of `LocalControl`, of type `GaussianTailFlat.BandScaleControl s`. -/
  bandScales : GaussianTailFlat.BandScaleControl s
  /-- Gaussian rate of `LocalControl`, of type `ℝ`. -/
  gaussianRate : ℝ
  gaussian_rate_pos : 0 < gaussianRate
  gaussian_envelope : ∀ n x, x ∈ s.domain → envelopeWeight r charts copy envelope n x ≤
    Real.exp (-gaussianRate * (slot.coordinate n x - 1 / 2) ^ 2 * slot.length n)
  /-- Patch of `LocalControl`, of type `ℕ → Set Plane`. -/
  patch : ℕ → Set Plane
  patch_open : ∀ n, IsOpen (patch n)
  patch_injective : ∀ n, InjOn TorusAverages.quotientPoint
    ((fun z => (bandGeometry r charts n).center + (bandGeometry r charts n).basis z) '' patch n)
  cutoff_support : ∀ n, Function.support r.cutoff ⊆ patch n
  domain_patch : ∀ n x, x ∈ s.domain → (bandGeometry r charts n).coordinates (copy n) x.2 ∈ patch n
  cutoff_match : ∀ n, EqOn (nativeCutoff r charts copy n) (slot.cutoff n) s.domain

namespace LocalControl

variable {r : Reference P} {charts : BandCharts P}
  {c : Context (P × Plane)} {u : State (P × Plane)} {b : HarmonicBlock (P × Plane)}
  {G A : HarmonicResidual.BlockCoefficients (P × Plane)} {j : ℤ}
  {base : WaveCoefficients ((P × ℝ) × Plane)} {copy : ℕ → Frequency}
  {s : StripData ((P × ℝ) × Plane)} {dirs : GraphDirections ((P × ℝ) × Plane)} {α κ : ℝ}
  (C : LocalControl r charts c u b G A j base copy s dirs α κ)

include C

/-- Weight, given by `envelopeWeight r charts copy C.envelope`. -/
noncomputable def weight : ℕ → (P × ℝ) × Plane → ℝ := envelopeWeight r charts copy C.envelope

theorem frequency_nonzero (n : ℕ) : (j : ℝ) * b.frequency n ≠ 0 :=
  mul_ne_zero (by exact_mod_cast C.harmonic_ne) (C.frequency_ne n)

theorem slot_invariant (n : ℕ) : Invariant dirs.angular (C.slot.cutoff n) := by
  intro x t
  simp only [GaussianTailFlat.SlotFamily.cutoff, GaussianTailFlat.SlotFamily.coordinate,
    map_add, map_smul, C.slot_angular, smul_zero, add_zero]

theorem affine_phase (n : ℕ) : ∃ m, AffinePhase dirs.angular m ((actualCarrier base b j).phase n)
    := by
  rw [C.background.angular]
  exact ⟨_, actualCarrier_affine base b j n⟩

theorem amplitude_invariant (n : ℕ) : Invariant dirs.angular
    ((actualCopyCoefficients r charts c u b G A j base copy).amplitude n) := by
  rw [C.background.angular]
  exact actualCopy_amplitude_invariant r charts c u b G A j base copy n

theorem pressure_invariant (n : ℕ) : Invariant dirs.angular
    ((actualCopyCoefficients r charts c u b G A j base copy).pressure n) := by
  rw [C.background.angular]
  exact actualCopy_pressure_invariant r charts c u b G A j base copy n

theorem exact_conditions : ExactConditions s dirs
    ((actualCopyCoefficients r charts c u b G A j base copy).corrected s dirs C.slot.cutoff) :=
  exactConditions_corrected_of_invariants C.slot.cutoff C.background.phase_smooth
    C.background.radius_ne C.background.radial_radius C.background.radius_invariant
    C.background.radial_base_invariant C.background.frequency_base_invariant
        C.background.axial_base_invariant
    C.background.radial_invariant C.background.axial_invariant C.affine_phase
    C.amplitude_invariant C.pressure_invariant C.slot_invariant

theorem raw_bounds : InputBounds s C.weight α κ dirs
    (actualCopyCoefficients r charts c u b G A j base copy) :=
  complexCopy_inputBounds_of_modal (actualCarrier base b j) (tangentFamily r charts j)
    (sourceFamily c u b G A j) (bandGeometry r charts) copy (fun _ => r.length)
    (fun _ => r.length_pos) C.envelope C.frame j C.modalReal C.modalImag C.base_bounds
    C.normal_jets C.normal_derivative C.action_bounds C.source_bounds
    C.normal_min_pos C.normal_lower C.normal_upper C.inverse_frequency

theorem local_result :
    let a := actualCopyCoefficients r charts c u b G A j base copy
    WaveClass s C.weight α a.amplitude ∧
    WaveClass s C.weight α (a.corrected s dirs C.slot.cutoff).amplitude ∧
    WaveClass s C.weight (α + 1 / 2) (a.corrected s dirs C.slot.cutoff).pressure ∧
    WaveClass s C.weight (α + 1 / 2 - 3 * κ) (a.constructedGood s dirs C.slot.cutoff) ∧
    ∀ n x, x ∈ s.domain →
      (a.corrected s dirs C.slot.cutoff).harmonicResidual s dirs n x +
        (fun i => sourceFamily c u b G A j n x i * carrier (a.frequency n) (a.phase n) x) =
      (fun i => (a.constructedGood s dirs C.slot.cutoff n x i +
        excludedSlotError dirs C.slot.cutoff a.amplitude (sourceFamily c u b G A j) n x i) *
          carrier (a.frequency n) (a.phase n) x) :=
  constructed_modal_particular_wave (actualCarrier base b j) (tangentFamily r charts j)
    (sourceFamily c u b G A j) (bandGeometry r charts) copy (fun _ => r.length)
    (fun _ => r.length_pos) C.envelope C.frame j C.modalReal C.modalImag C.base_bounds
    C.normal_jets C.normal_derivative C.action_bounds C.source_bounds C.normal_min_pos
    C.normal_lower C.normal_upper C.inverse_frequency C.geometry C.frequency_nonzero
    C.loss_le_half C.slot.cutoff C.slot.cutoff_memClass C.radius_eq C.exact_conditions

theorem gaussian_flat (β : ℝ) : UnweightedClass s β
    (excludedSlotError dirs C.slot.cutoff
      (actualCopyCoefficients r charts c u b G A j base copy).amplitude (sourceFamily c u b G A j))
          :=
  LinearWaveBounds.excludedSlotError_all_gains C.slot dirs C.slot_fast C.flatEdges C.bandScales
    C.local_result.1 C.source_bounds C.gaussian_rate_pos C.gaussian_envelope β

theorem raw_tangent : ∀ n x, x ∈ s.domain →
    normalDot ((actualCarrier base b j).normal s dirs n x)
      ((actualCopyCoefficients r charts c u b G A j base copy).amplitude n x) = 0 :=
  complexCopyCoefficients_tangent_of_modal (actualCarrier base b j) (tangentFamily r charts j)
    (sourceFamily c u b G A j) (bandGeometry r charts) copy (fun _ => r.length)
    (fun _ => r.length_pos) C.envelope C.frame j C.modalReal C.modalImag C.geometry

theorem normal_nonzero (n : ℕ) (x : (P × ℝ) × Plane) (hx : x ∈ s.domain) :
    (actualCarrier base b j).normal s dirs n x ≠ 0 := by
  rw [C.geometry.normal n x hx]
  exact norm_pos_iff.mp (C.normal_min_pos.trans_le (C.normal_lower n x hx))

theorem exact_curl (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ s.domain) :
    let a := actualCopyCoefficients r charts c u b G A j base copy
    CurlClassBounds.cylindricalCurl (base.radius n) (dirs.radialField n) (fun _ => dirs.angular)
      (dirs.axialField s n) ((a.withCutoff C.slot.cutoff).curlPotential s dirs n) x =
        vectorMode (a.frequency n) (a.phase n) ((a.corrected s dirs C.slot.cutoff).amplitude n) x
            := by
  exact corrected_realizes_curl C.raw_bounds C.slot.cutoff_memClass n (C.background.cylindrical n)
    (C.frequency_nonzero n) (C.background.phase_smooth n) (C.normal_nonzero n) (C.raw_tangent n) hx

theorem divergence_zero (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ s.domain) :
    let a := actualCopyCoefficients r charts c u b G A j base copy
    cylindricalDivergence (base.radius n) (dirs.radialField n) (fun _ => dirs.angular)
      (dirs.axialField s n) (vectorMode (a.frequency n) (a.phase n)
        ((a.corrected s dirs C.slot.cutoff).amplitude n)) x = 0 :=
  corrected_divergence C.raw_bounds C.slot.cutoff_memClass n (C.background.cylindrical n)
    (C.frequency_nonzero n) (C.background.phase_smooth n) (C.normal_nonzero n) (C.raw_tangent n) hx

theorem cutoff_germ (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ s.domain) :
    nativeCutoff r charts copy n =ᶠ[𝓝 x] C.slot.cutoff n :=
  Filter.eventually_of_mem (s.isOpen_domain.mem_nhds hx) (C.cutoff_match n)

theorem common_germ (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ s.domain) :
    (actualCorrectedCommon r charts c u b G A j base s dirs).amplitude n =ᶠ[𝓝 x]
      (((actualCopyCoefficients r charts c u b G A j base copy).corrected s dirs
          C.slot.cutoff).amplitude n) ∧
    (actualCorrectedCommon r charts c u b G A j base s dirs).pressure n =ᶠ[𝓝 x]
      (((actualCopyCoefficients r charts c u b G A j base copy).corrected s dirs
          C.slot.cutoff).pressure n) :=
  actualCommon_corrected_germ r charts c u b G A C.harmonic_ne C.frequency_ne base copy s dirs
      C.slot.cutoff n x
    (C.patch_open n) (C.patch_injective n) (C.cutoff_support n) (C.domain_patch n x hx)
        (C.cutoff_germ n hx)

theorem common_residual_germ (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ s.domain) :
    (actualCorrectedCommon r charts c u b G A j base s dirs).harmonicResidual s dirs n =ᶠ[𝓝 x]
      (((actualCopyCoefficients r charts c u b G A j base copy).corrected s dirs
          C.slot.cutoff).harmonicResidual s dirs n) :=
  actualCommon_residual_germ r charts c u b G A C.harmonic_ne C.frequency_ne base copy s dirs
      C.slot.cutoff n x
    (C.patch_open n) (C.patch_injective n) (C.cutoff_support n) (C.domain_patch n x hx)
        (C.cutoff_germ n hx)

theorem common_classes :
    WaveClass s C.weight α (actualCorrectedCommon r charts c u b G A j base s dirs).amplitude ∧
    WaveClass s C.weight (α + 1 / 2) (actualCorrectedCommon r charts c u b G A j base s
        dirs).pressure := by
  refine ⟨LinearWaveBounds.class_congr C.local_result.2.1 ?_,
    LinearWaveBounds.class_congr C.local_result.2.2.1 ?_⟩
  · intro n x hx
    exact (C.common_germ n hx).1.self_of_nhds.symm
  · intro n x hx
    exact (C.common_germ n hx).2.self_of_nhds.symm

/-- Actual periodized, curl-corrected field cancellation. Both terms of
`excludedSlotError` remain in this exact identity. -/
theorem common_cancellation (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ s.domain) :
    let a := actualCopyCoefficients r charts c u b G A j base copy
    (actualCorrectedCommon r charts c u b G A j base s dirs).harmonicResidual s dirs n x +
      (fun i => sourceFamily c u b G A j n x i * carrier (a.frequency n) (a.phase n) x) =
    (fun i => (a.constructedGood s dirs C.slot.cutoff n x i +
      excludedSlotError dirs C.slot.cutoff a.amplitude (sourceFamily c u b G A j) n x i) *
        carrier (a.frequency n) (a.phase n) x) := by
  have hh := C.local_result.2.2.2.2 n x hx
  rw [← (C.common_residual_germ n hx).self_of_nhds] at hh
  exact hh

theorem good_invariant (n : ℕ) : Invariant dirs.angular
    ((actualCopyCoefficients r charts c u b G A j base copy).constructedGood s dirs C.slot.cutoff
        n) :=
  constructedGood_invariant (a := actualCopyCoefficients r charts c u b G A j base copy)
    C.slot.cutoff C.background.radius_invariant
    C.background.radial_base_invariant C.background.frequency_base_invariant
        C.background.axial_base_invariant
    C.background.radial_invariant C.background.axial_invariant C.affine_phase
    C.amplitude_invariant C.pressure_invariant C.slot_invariant n

theorem gaussian_invariant (n : ℕ) : Invariant dirs.angular
    (excludedSlotError dirs C.slot.cutoff (actualCopyCoefficients r charts c u b G A j base
        copy).amplitude
      (sourceFamily c u b G A j) n) := by
  have hs : Invariant dirs.angular (sourceFamily c u b G A j n) := by
    rw [C.background.angular]
    exact angleLift_invariant (residualSource c u b G A j n)
  have hd : Invariant dirs.angular (dirs.Dfast C.slot.cutoff n) :=
    (C.slot_invariant n).along (Invariant.const _)
  exact (hd.map₂ (C.amplitude_invariant n) (fun t v => t • v)).map₂
    ((C.slot_invariant n).map₂ hs (fun t v => (1 - t) • v)) (fun v w => v + w)

theorem common_amplitude_invariant (n : ℕ) : Invariant dirs.angular
    ((actualCorrectedCommon r charts c u b G A j base s dirs).amplitude n) := by
  have ha : Invariant dirs.angular
      ((actualCommonCoefficients r charts c u b G A j base).amplitude n) := by
    rw [C.background.angular]
    exact angleLift_invariant (actualBandVelocity r charts c u b G A j n)
  obtain ⟨m,hm⟩ := C.affine_phase n
  exact realizedCoefficient_invariant (C.background.radius_invariant n)
    (C.background.radial_invariant n) (Invariant.const _) (C.background.axial_invariant n)
    hm ha ((j : ℝ) * b.frequency n)

theorem common_pressure_invariant (n : ℕ) : Invariant dirs.angular
    ((actualCorrectedCommon r charts c u b G A j base s dirs).pressure n) := by
  rw [C.background.angular]
  exact angleLift_invariant (actualBandPressure r charts c u b G A j n)

theorem common_divergence_zero (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ s.domain) :
    let a := actualCorrectedCommon r charts c u b G A j base s dirs
    cylindricalDivergence (base.radius n) (dirs.radialField n) (fun _ => dirs.angular)
      (dirs.axialField s n) (vectorMode (a.frequency n) (a.phase n) (a.amplitude n)) x = 0 := by
  have he : EqOn
      (vectorMode ((j : ℝ) * b.frequency n) ((actualCarrier base b j).phase n)
        ((actualCorrectedCommon r charts c u b G A j base s dirs).amplitude n))
      (vectorMode ((j : ℝ) * b.frequency n) ((actualCarrier base b j).phase n)
        (((actualCopyCoefficients r charts c u b G A j base copy).corrected s dirs
            C.slot.cutoff).amplitude n))
      s.domain := by
    intro y hy
    exact (vectorMode_germ (C.common_germ n hy).1 _ _).self_of_nhds
  exact (CurlClassBounds.cylindricalDivergence_congr s.isOpen_domain (base.radius n)
    (dirs.radialField n) (fun _ => dirs.angular) (dirs.axialField s n) he hx).trans
        (C.divergence_zero n hx)

/-- Good, given by `(actualCopyCoefficients r charts c u b G A j base copy).constructedGood s
dirs C.slot.cutoff`. -/
noncomputable def good : ℕ → (P × ℝ) × Plane → ComplexVector :=
  (actualCopyCoefficients r charts c u b G A j base copy).constructedGood s dirs C.slot.cutoff

/-- Gaussian, given by `excludedSlotError dirs C.slot.cutoff (actualCopyCoefficients r charts c
u b G A j base copy).amplitude (sourceFamily c u b G A j)`. -/
noncomputable def gaussian : ℕ → (P × ℝ) × Plane → ComplexVector :=
  excludedSlotError dirs C.slot.cutoff
    (actualCopyCoefficients r charts c u b G A j base copy).amplitude (sourceFamily c u b G A j)

theorem section_cancellation (n : ℕ) (x : (P × Plane) × ℝ)
    (hx : angleShuffle x ∈ s.domain) (i : Fin 3) :
    (actualCorrectedCommon r charts c u b G A j base s dirs).harmonicResidual s dirs n
        (angleShuffle x) i +
      residualSource c u b G A j n x.1 i *
        HarmonicFields.character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) *
            x.2) =
      (C.good n (angleShuffle (x.1,0)) i + C.gaussian n (angleShuffle (x.1,0)) i) *
        HarmonicFields.character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) *
            x.2) := by
  have hg := C.good_invariant n
  have he := C.gaussian_invariant n
  rw [C.background.angular] at hg he
  have hgs : C.good n (angleShuffle x) = C.good n (angleShuffle (x.1,0)) :=
    invariant_angleShuffle hg x.1 x.2
  have hes : C.gaussian n (angleShuffle x) = C.gaussian n (angleShuffle (x.1,0)) :=
    invariant_angleShuffle he x.1 x.2
  have hh := congrFun (C.common_cancellation n hx) i
  change (actualCorrectedCommon r charts c u b G A j base s dirs).harmonicResidual s dirs n
      (angleShuffle x) i +
    residualSource c u b G A j n x.1 i * carrier ((actualCarrier base b j).frequency n)
      ((actualCarrier base b j).phase n) (angleShuffle x) =
    (C.good n (angleShuffle x) i + C.gaussian n (angleShuffle x) i) *
      carrier ((actualCarrier base b j).frequency n) ((actualCarrier base b j).phase n)
          (angleShuffle x) at hh
  rw [actualCarrier_character base b j C.frequency_ne n x, hgs, hes] at hh
  exact hh

theorem block_represents :
    (nativeModeBlock j b (actualCorrectedCommon r charts c u b G A j base s dirs)).oscillation =
      (fun n x i => (vectorMode ((j : ℝ) * b.frequency n) ((actualCarrier base b j).phase n)
        ((actualCorrectedCommon r charts c u b G A j base s dirs).amplitude n) (angleShuffle x)
            i).re) ∧
    (nativeModeBlock j b (actualCorrectedCommon r charts c u b G A j base s
        dirs)).oscillatoryPressure =
      (fun n x => (mode ((j : ℝ) * b.frequency n) ((actualCarrier base b j).phase n)
        ((actualCorrectedCommon r charts c u b G A j base s dirs).pressure n) (angleShuffle x)).re)
            := by
  apply nativeModeBlock_represents
  · intro n
    rw [← C.background.angular]
    exact C.common_amplitude_invariant n
  · intro n
    rw [← C.background.angular]
    exact C.common_pressure_invariant n
  · exact actualCarrier_phase base b j C.frequency_ne

end LocalControl

end ConstructedControls


/-! ## Finite actual fields and residual cancellation -/

section FiniteConstruction

open Filter

open CommonCoverSolve TorusInverse HarmonicCalculus HarmonicFields WeightedClasses LinearWaveBounds
open ParticularWaveBounds CopyAngularInvariance CorrectionState

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- All primitive choices for one original spatial label. There is only
one reference and one family of band charts for its entire harmonic sum. -/
structure AssemblyData (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] where
  /-- Reference of `AssemblyData`, of type `Reference P`. -/
  reference : Reference P
  /-- Charts of `AssemblyData`, of type `BandCharts P`. -/
  charts : BandCharts P
  /-- Context of `AssemblyData`, of type `Context (P × Plane)`. -/
  context : Context (P × Plane)
  /-- State of `AssemblyData`, of type `State (P × Plane)`. -/
  state : State (P × Plane)
  /-- Carrier block of `AssemblyData`, of type `HarmonicBlock (P × Plane)`. -/
  carrierBlock : HarmonicBlock (P × Plane)
  /-- Gaussian input of `AssemblyData`, of type `HarmonicResidual.BlockCoefficients (P ×
  Plane)`. -/
  gaussianInput : HarmonicResidual.BlockCoefficients (P × Plane)
  /-- Alias input of `AssemblyData`, of type `HarmonicResidual.BlockCoefficients (P × Plane)`. -/
  aliasInput : HarmonicResidual.BlockCoefficients (P × Plane)
  /-- Background of `AssemblyData`, of type `WaveCoefficients ((P × ℝ) × Plane)`. -/
  background : WaveCoefficients ((P × ℝ) × Plane)
  /-- Copy of `AssemblyData`, of type `ℕ → Frequency`. -/
  copy : ℕ → Frequency
  /-- Strip of `AssemblyData`, of type `StripData ((P × ℝ) × Plane)`. -/
  strip : StripData ((P × ℝ) × Plane)
  /-- Directions of `AssemblyData`, of type `GraphDirections ((P × ℝ) × Plane)`. -/
  directions : GraphDirections ((P × ℝ) × Plane)

namespace AssemblyData

variable (D : AssemblyData P)

/-- Wave, constructed using `actualCorrectedCommon`. -/
noncomputable def wave (j : ℤ) : WaveCoefficients ((P × ℝ) × Plane) :=
  actualCorrectedCommon D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.strip D.directions

/-- Controls as an element of `Type`. -/
noncomputable def controls (N : ℕ) (α κ : ℝ) : Type :=
  ∀ j ∈ modes N, LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ

/-- Velocity, defined pointwise by `∑ j ∈ modes N, (vectorMode ((D.wave j).frequency n) ((D.wave
j).phase n) ((D.wave j).amplitude n) x i).re`. -/
noncomputable def velocity (N : ℕ) : ℕ → (P × ℝ) × Plane → Fin 3 → ℝ :=
  fun n x i => ∑ j ∈ modes N, (vectorMode ((D.wave j).frequency n) ((D.wave j).phase n)
    ((D.wave j).amplitude n) x i).re

/-- Pressure, defined pointwise by `∑ j ∈ modes N, (mode ((D.wave j).frequency n) ((D.wave
j).phase n) ((D.wave j).pressure n) x).re`. -/
noncomputable def pressure (N : ℕ) : ℕ → (P × ℝ) × Plane → ℝ :=
  fun n x => ∑ j ∈ modes N, (mode ((D.wave j).frequency n) ((D.wave j).phase n)
    ((D.wave j).pressure n) x).re

/-- Update block, constructed using `assembledBlock`. -/
noncomputable def updateBlock (N : ℕ) : HarmonicBlock (P × Plane) :=
  assembledBlock N D.carrierBlock.frequency D.carrierBlock.phase D.carrierBlock.angularFrequency
    (fun j n x => (D.wave j).amplitude n (angleShuffle (x,0)))
    (fun j n x => (D.wave j).pressure n (angleShuffle (x,0)))

/-- Good family, with branches according to `hj : j ∈ modes N`. -/
noncomputable def goodFamily {N : ℕ} {α κ : ℝ} (C : D.controls N α κ) (j : ℤ) :
    ℕ → (P × ℝ) × Plane → ComplexVector :=
  if hj : j ∈ modes N then (C j hj).good else fun _ _ => 0

/-- Gaussian family, with branches according to `hj : j ∈ modes N`. -/
noncomputable def gaussianFamily {N : ℕ} {α κ : ℝ} (C : D.controls N α κ) (j : ℤ) :
    ℕ → (P × ℝ) × Plane → ComplexVector :=
  if hj : j ∈ modes N then (C j hj).gaussian else fun _ _ => 0

/-- Good block, constructed using `assembledBlock`. -/
noncomputable def goodBlock {N : ℕ} {α κ : ℝ} (C : D.controls N α κ) : HarmonicBlock (P × Plane) :=
  assembledBlock N D.carrierBlock.frequency D.carrierBlock.phase D.carrierBlock.angularFrequency
    (fun j n x => D.goodFamily C j n (angleShuffle (x,0))) (fun _ _ _ => 0)

/-- Gaussian block, constructed using `assembledBlock`. -/
noncomputable def gaussianBlock {N : ℕ} {α κ : ℝ} (C : D.controls N α κ) : HarmonicBlock (P ×
    Plane) :=
  assembledBlock N D.carrierBlock.frequency D.carrierBlock.phase D.carrierBlock.angularFrequency
    (fun j n x => D.gaussianFamily C j n (angleShuffle (x,0))) (fun _ _ _ => 0)

theorem update_band (N : ℕ) : (D.updateBlock N).BandLimited N := assembledBlock_band _ _ _ _ _ _
theorem update_real (N : ℕ) : ErrorHarmonics.RealBlock (D.updateBlock N) := assembledBlock_real _ _
    _ _ _ _

variable {D} {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)

theorem good_band : (D.goodBlock C).BandLimited N := assembledBlock_band _ _ _ _ _ _
theorem gaussian_band : (D.gaussianBlock C).BandLimited N := assembledBlock_band _ _ _ _ _ _
theorem good_real : ErrorHarmonics.RealBlock (D.goodBlock C) := assembledBlock_real _ _ _ _ _ _
theorem gaussian_real : ErrorHarmonics.RealBlock (D.gaussianBlock C) := assembledBlock_real _ _ _ _
    _ _

theorem error_mean_zero (hkp : ∀ n, D.carrierBlock.angularFrequency n ≠ 0) :
    ((∀ i, angularAverage (fun n x => (D.goodBlock C).oscillation n x i) = 0) ∧
      angularAverage (D.goodBlock C).oscillatoryPressure = 0) ∧
    ((∀ i, angularAverage (fun n x => (D.gaussianBlock C).oscillation n x i) = 0) ∧
      angularAverage (D.gaussianBlock C).oscillatoryPressure = 0) :=
  ⟨assembledBlock_mean_zero _ _ _ _ _ _ hkp, assembledBlock_mean_zero _ _ _ _ _ _ hkp⟩

theorem update_mean_zero (hkp : ∀ n, D.carrierBlock.angularFrequency n ≠ 0) :
    (∀ i, angularAverage (fun n x => (D.updateBlock N).oscillation n x i) = 0) ∧
    angularAverage (D.updateBlock N).oscillatoryPressure = 0 :=
  assembledBlock_mean_zero _ _ _ _ _ _ hkp

include C in
theorem update_represents :
    (D.updateBlock N).oscillation = (fun n x => D.velocity N n (angleShuffle x)) ∧
    (D.updateBlock N).oscillatoryPressure = (fun n x => D.pressure N n (angleShuffle x)) := by
  constructor
  · funext n x i
    rw [show (D.updateBlock N).oscillation n x i = _ from assembledBlock_value _ _ _ _ _ _ n x i]
    apply Finset.sum_congr rfl
    intro j hj
    have he := congrFun (congrFun (congrFun (C j hj).block_represents.1 n) x) i
    exact (modeBlock_value j D.carrierBlock.frequency D.carrierBlock.phase
        D.carrierBlock.angularFrequency
      (fun n x => (D.wave j).amplitude n (angleShuffle (x,0)))
      (fun n x => (D.wave j).pressure n (angleShuffle (x,0))) n x i).symm.trans he
  · funext n x
    rw [show (D.updateBlock N).oscillatoryPressure n x = _ from assembledBlock_pressure_value _ _ _
        _ _ _ n x]
    apply Finset.sum_congr rfl
    intro j hj
    have he := congrFun (congrFun (C j hj).block_represents.2 n) x
    exact (modeBlock_pressure_value j D.carrierBlock.frequency D.carrierBlock.phase
        D.carrierBlock.angularFrequency
      (fun n x => (D.wave j).amplitude n (angleShuffle (x,0)))
      (fun n x => (D.wave j).pressure n (angleShuffle (x,0))) n x).symm.trans he

theorem update_classes (W : ℕ → (P × ℝ) × Plane → ℝ)
    (hW : ∀ n x, x ∈ D.strip.domain → 0 ≤ W n x)
    (hCW : ∀ j hj n x, x ∈ D.strip.domain → (C j hj).weight n x ≤ W n x) :
    (D.updateBlock N).WaveBounds (sectionStrip D.strip) (fun n x => W n (angleShuffle (x,0))) α ∧
    (D.updateBlock N).PressureBounds (sectionStrip D.strip) (fun n x => W n (angleShuffle (x,0)))
        (α + 1 / 2) := by
  have hw : ∀ n x, x ∈ D.strip.domain → 0 ≤ Real.sqrt (D.strip.zeta x) * W n x :=
    fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n x hx)
  apply assembledBlock_classes
  · intro n x hx
    exact hW n _ hx
  · intro j hj
    apply nativeSlice_waveClass
    exact (C j hj).common_classes.1.mono_weight hw
      (fun n x hx => mul_le_mul_of_nonneg_left (hCW j hj n x hx) (Real.sqrt_nonneg _))
  · intro j hj
    apply nativeSlice_waveClass
    exact (C j hj).common_classes.2.mono_weight hw
      (fun n x hx => mul_le_mul_of_nonneg_left (hCW j hj n x hx) (Real.sqrt_nonneg _))

theorem good_classes (W : ℕ → (P × ℝ) × Plane → ℝ)
    (hW : ∀ n x, x ∈ D.strip.domain → 0 ≤ W n x)
    (hCW : ∀ j hj n x, x ∈ D.strip.domain → (C j hj).weight n x ≤ W n x) :
    (D.goodBlock C).WaveBounds (sectionStrip D.strip) (fun n x => W n (angleShuffle (x,0)))
      (α + 1 / 2 - 3 * κ) := by
  have hw : ∀ n x, x ∈ D.strip.domain → 0 ≤ Real.sqrt (D.strip.zeta x) * W n x :=
    fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n x hx)
  have hh := assembledBlock_classes (s := sectionStrip D.strip)
    (α := α + 1 / 2 - 3 * κ) (γ := (0 : ℝ))
    N D.carrierBlock.frequency D.carrierBlock.phase D.carrierBlock.angularFrequency
    (v := fun j n x => D.goodFamily C j n (angleShuffle (x,0))) (p := fun _ _ _ => 0)
    (fun n x hx => hW n _ hx) ?_ ?_
  · exact hh.1
  · intro j hj
    simp only [goodFamily, dite_eq_left hj]
    apply nativeSlice_waveClass
    exact (C j hj).local_result.2.2.2.1.mono_weight hw
      (fun n x hx => mul_le_mul_of_nonneg_left (hCW j hj n x hx) (Real.sqrt_nonneg _))
  · intro j hj
    exact MemClass.zero (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n _ hx))

theorem gaussian_classes (β : ℝ) (i : Fin 3) (m : ℤ) :
    UnweightedClass (sectionStrip D.strip) β (fun n x => (D.gaussianBlock C).velocity n i m x) := by
  have hj (j : ℤ) (h : j ∈ modes N) : UnweightedClass (sectionStrip D.strip) β
      (fun n x => ErrorHarmonics.conjugatePair j
        (fun x => D.gaussianFamily C j n (angleShuffle (x,0)) i) m x) := by
    simp only [gaussianFamily, dite_eq_left h]
    exact pair_class (CurlClassBounds.class_component (nativeSlice_class ((C j h).gaussian_flat β))
        i) j m
  have hh := MemClass.sum (modes N)
    (fun j n x => ErrorHarmonics.conjugatePair j
      (fun x => D.gaussianFamily C j n (angleShuffle (x,0)) i) m x)
    (fun _ _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) hj
  apply LinearWaveBounds.class_congr hh
  intro n x hx
  change _ = (∑ j ∈ modes N, ErrorHarmonics.conjugatePair j
    (fun x => D.gaussianFamily C j n (angleShuffle (x,0)) i)) m x
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]

theorem cancellation_sum
    (hN : (HarmonicResidual.residualBlock D.context D.state D.carrierBlock D.gaussianInput
        D.aliasInput).BandLimited N)
    (n : ℕ) (x : (P × Plane) × ℝ) (hx : angleShuffle x ∈ D.strip.domain) :
    (fun i => ∑ j ∈ modes N, ((D.wave j).harmonicResidual D.strip D.directions n (angleShuffle x)
        i).re) +
      (HarmonicResidual.residualBlock D.context D.state D.carrierBlock D.gaussianInput
          D.aliasInput).oscillation n x =
        (D.goodBlock C).oscillation n x + (D.gaussianBlock C).oscillation n x := by
  apply finite_cancellation D.context D.state D.carrierBlock D.gaussianInput D.aliasInput N hN
    (fun j n x => (D.wave j).harmonicResidual D.strip D.directions n (angleShuffle x))
    (fun j n x => D.goodFamily C j n (angleShuffle (x,0)))
    (fun j n x => D.gaussianFamily C j n (angleShuffle (x,0))) n x
  intro j hj i
  simp only [goodFamily, gaussianFamily, dite_eq_left hj]
  exact (C j hj).section_cancellation n x hx i

end AssemblyData

theorem along_finset_sum {E F ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (J : Finset ι) (V : E → E)
    (f : ι → E → F) {x : E} (hf : ∀ j ∈ J, DifferentiableAt ℝ (f j) x) :
    along V (fun y => ∑ j ∈ J, f j y) x = ∑ j ∈ J, along V (f j) x := by
  simp only [along, fderiv_fun_sum hf, _root_.sum_apply]

theorem divergence_finset_sum {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Finset ι) (R : E → ℝ) (Vr Vθ Vz : E → E) (v : ι → E → ComplexVector) {x : E}
    (hv : ∀ j ∈ J, ∀ i, DifferentiableAt ℝ (fun y => v j y i) x) :
    cylindricalDivergence R Vr Vθ Vz (fun y i => ∑ j ∈ J, v j y i) x =
      ∑ j ∈ J, cylindricalDivergence R Vr Vθ Vz (v j) x := by
  simp only [cylindricalDivergence, along_finset_sum J Vr _ (fun j hj => hv j hj 0),
    along_finset_sum J Vθ _ (fun j hj => hv j hj 1),
    along_finset_sum J Vz _ (fun j hj => hv j hj 2), Finset.smul_sum, Finset.sum_add_distrib]

theorem divergence_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] ℂ) (R : E → ℝ) (Vr Vθ Vz : E → E) {v : E → ComplexVector} {x : E}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    cylindricalDivergence R Vr Vθ Vz (fun y i => L (v y i)) x =
      L (cylindricalDivergence R Vr Vθ Vz v x) := by
  simp only [cylindricalDivergence, LinearWaveResidual.along_map L _ (hv _), map_add, map_smul]

theorem real_divergence_sum_zero {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Finset ι) (R : E → ℝ) (Vr Vθ Vz : E → E) (v : ι → E → ComplexVector) {x : E}
    (hv : ∀ j ∈ J, ∀ i, DifferentiableAt ℝ (fun y => v j y i) x)
    (hdiv : ∀ j ∈ J, cylindricalDivergence R Vr Vθ Vz (v j) x = 0) :
    cylindricalDivergence R Vr Vθ Vz (fun y i => ((∑ j ∈ J, (v j y i).re : ℝ) : ℂ)) x = 0 := by
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have hs (i : Fin 3) : DifferentiableAt ℝ (fun y => ∑ j ∈ J, v j y i) x :=
    DifferentiableAt.fun_sum (fun j hj => hv j hj i)
  have he := divergence_map L R Vr Vθ Vz hs
  rw [divergence_finset_sum J R Vr Vθ Vz v hv, Finset.sum_eq_zero hdiv, map_zero] at he
  simpa only [L, ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.ofRealCLM_apply,
    Complex.re_sum] using he

namespace AssemblyData

variable {D : AssemblyData P} {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)

include C

theorem wave_smooth (j : ℤ) (hj : j ∈ modes N) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => vectorMode ((D.wave j).frequency n) ((D.wave j).phase n)
      ((D.wave j).amplitude n) x i) D.strip.domain :=
  HarmonicCalculus.contDiffOn_mode _ ((C j hj).background.phase_smooth n)
    (contDiffOn_pi.mp ((C j hj).common_classes.1.smooth n) i)

theorem pressure_smooth (j : ℤ) (hj : j ∈ modes N) (n : ℕ) :
    ContDiffOn ℝ ∞ (mode ((D.wave j).frequency n) ((D.wave j).phase n)
      ((D.wave j).pressure n)) D.strip.domain :=
  HarmonicCalculus.contDiffOn_mode _ ((C j hj).background.phase_smooth n)
    ((C j hj).common_classes.2.smooth n)

theorem divergence_zero (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ D.strip.domain) :
    cylindricalDivergence (D.background.radius n) (D.directions.radialField n)
      (fun _ => D.directions.angular) (D.directions.axialField D.strip n)
      (fun y i => (D.velocity N n y i : ℂ)) x = 0 := by
  apply real_divergence_sum_zero (modes N)
  · intro j hj i
    exact ((D.wave_smooth C j hj n i).contDiffAt (D.strip.isOpen_domain.mem_nhds
        hx)).differentiableAt (by
        simp)
  · intro j hj
    exact (C j hj).common_divergence_zero n hx

/-- One actual real field cancels the current grouped residual, with the
computed good field and both Gaussian tails retained on the right. -/
theorem real_cancellation (hpos : 0 < N)
    (hN : (HarmonicResidual.residualBlock D.context D.state D.carrierBlock D.gaussianInput
        D.aliasInput).BandLimited N)
    (n : ℕ) (x : (P × Plane) × ℝ) (hx : angleShuffle x ∈ D.strip.domain) :
    LinearWaveResidual.realComponentLinearResidual (D.strip.epsilon n) (D.background.radius n)
      (D.directions.radialField n) (fun _ => D.directions.angular) (D.directions.axialField D.strip
          n)
      (LinearWaveResidual.timeDirection (D.strip.epsilon n) (D.directions.fastField n) (fun _ =>
          D.directions.slow))
      (LinearWaveResidual.base (D.background.radius n) (D.background.radialBase n)
        (D.background.frequencyBase n) (D.background.axialBase n))
      (D.velocity N n) (D.pressure N n) (angleShuffle x) +
      (HarmonicResidual.residualBlock D.context D.state D.carrierBlock D.gaussianInput
          D.aliasInput).oscillation n x =
        (D.goodBlock C).oscillation n x + (D.gaussianBlock C).oscillation n x := by
  have h1 : (1 : ℤ) ∈ modes N := by rw [mem_modes]; norm_num; omega
  let C0 := C 1 h1
  have hB (i : Fin 3) : DifferentiableAt ℝ (fun y => LinearWaveResidual.base
      (D.background.radius n) (D.background.radialBase n) (D.background.frequencyBase n)
      (D.background.axialBase n) y i) (angleShuffle x) :=
    LinearWaveResidual.differentiableAt_base
      (((C0.background.cylindrical n).radius_smooth.contDiffAt (D.strip.isOpen_domain.mem_nhds
          hx)).differentiableAt (by
          simp))
      (((C0.base_bounds.radial_base.smooth n).contDiffAt (D.strip.isOpen_domain.mem_nhds
          hx)).differentiableAt (by
          simp))
      (((C0.base_bounds.frequency_base.smooth n).contDiffAt (D.strip.isOpen_domain.mem_nhds
          hx)).differentiableAt (by
          simp))
      (((C0.base_bounds.axial_base.smooth n).contDiffAt (D.strip.isOpen_domain.mem_nhds
          hx)).differentiableAt (by
          simp)) i
  have he := real_linearResidual_sum (modes N) D.strip.isOpen_domain (D.strip.epsilon n)
    (D.background.radius n)
    (LinearWaveResidual.timeDirection (D.strip.epsilon n) (D.directions.fastField n) (fun _ =>
        D.directions.slow))
    (C0.background.cylindrical n).radial_smooth (C0.background.cylindrical n).angular_smooth
    (C0.background.cylindrical n).axial_smooth
    (LinearWaveResidual.base (D.background.radius n) (D.background.radialBase n)
      (D.background.frequencyBase n) (D.background.axialBase n))
    (fun j => vectorMode ((D.wave j).frequency n) ((D.wave j).phase n) ((D.wave j).amplitude n))
    (fun j => mode ((D.wave j).frequency n) ((D.wave j).phase n) ((D.wave j).pressure n))
    (fun j hj i => D.wave_smooth C j hj n i) (fun j hj => D.pressure_smooth C j hj n) hB hx
  calc
    _ = (fun i => ∑ j ∈ modes N,
        ((D.wave j).harmonicResidual D.strip D.directions n (angleShuffle x) i).re) +
          (HarmonicResidual.residualBlock D.context D.state D.carrierBlock D.gaussianInput
              D.aliasInput).oscillation n x :=
      congrArg (fun v => v + (HarmonicResidual.residualBlock D.context D.state D.carrierBlock
        D.gaussianInput D.aliasInput).oscillation n x) he
    _ = _ := D.cancellation_sum C hN n x hx

end AssemblyData

end FiniteConstruction

end NavierStokes.ParticularWaveAssembly
