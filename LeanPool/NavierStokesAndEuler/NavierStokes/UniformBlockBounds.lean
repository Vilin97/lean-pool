/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.StateReindex
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicWaveInteraction
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodizedWaveBounds

/-!
# Uniform coefficient bounds for the literal harmonic blocks

Restriction to angle zero, isometric coordinate changes, conjugate pairs,
and finite signed harmonic sums preserve constants chosen before labels.
The endpoints use the actual signed and particular block constructors.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.UniformBlockBounds

open Set Filter Function WeightedClasses LabelSumBounds HarmonicCalculus HarmonicFields
open scoped Topology ContDiff BigOperators

section Restriction

variable {D E : Type} {F ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An isometry preserves the constants and polynomial degrees of every
actual finite-jet bound, uniformly over the extra index. -/
theorem uniform_reindex (e : E ≃ₗᵢ[ℝ] D) {s : StripData D}
    {w : ι → ℕ → D → ℝ} {α : ℝ} {f : ι → ℕ → D → F}
    (hf : UniformClass s w α f) :
    UniformClass (ParticularWaveBounds.reindexStrip e s)
      (fun l n x => w l n (e x)) α (fun l n x => f l n (e x)) := by
  refine ⟨fun l n x hx => hf.weight_nonneg l n (e x) hx,
    fun l n => (hf.smooth l n).comp e.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun _ hx => hx), fun m => ?_⟩
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, fun l n x hx j hj => ?_⟩
  change ‖iteratedFDeriv ℝ j (f l n ∘ e) x‖ ≤ _
  rw [e.norm_iteratedFDeriv_comp_right]
  exact hb l n (e x) hx j hj

end Restriction

section ZeroSection

variable {D : Type} {F ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restriction to angle zero does not enlarge a single jet constant. -/
theorem uniform_zeroSection {s : StripData (D × ℝ)} {w : ι → ℕ → D × ℝ → ℝ}
    {α : ℝ} {f : ι → ℕ → D × ℝ → F} (hf : UniformClass s w α f) :
    UniformClass (SignedWaveUpdate.sectionStrip s) (fun l n x => w l n (x,0)) α
      (fun l n x => f l n (x,0)) := by
  refine ⟨fun l n x hx => hf.weight_nonneg l n _ hx,
    fun l n => (hf.smooth l n).comp (SignedWaveUpdate.zeroSection (D := D)).contDiff.contDiffOn
      (fun _ hx => hx), fun m => ?_⟩
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, fun l n x hx j hj => ?_⟩
  have hc := PhaseJetBounds.norm_jet_comp_linear s.isOpen_domain (hf.smooth l n)
    (SignedWaveUpdate.zeroSection (D := D)) hx j
  have hp : ‖SignedWaveUpdate.zeroSection (D := D)‖^j ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) SignedWaveUpdate.zeroSection_norm_le
  exact (hc.trans (mul_le_of_le_one_right (norm_nonneg _) hp)).trans (hb l n (x,0) hx j hj)

theorem sectionStrip_productStrip (s : StripData D) :
    SignedWaveUpdate.sectionStrip (HarmonicWaveInteraction.productStrip s) = s := by
  cases s
  rfl

theorem uniform_slice {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    {f : ι → ℕ → D × ℝ → F}
    (hf : UniformClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => w l n x.1) α f) :
    UniformClass s w α (fun l n x => f l n (x,0)) := by
  have hh := uniform_zeroSection hf
  rw [sectionStrip_productStrip] at hh
  exact hh

end ZeroSection

section Pairing

variable {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : ι → ℕ → D → ℝ} {α γ : ℝ}

/-- A conjugate pair retains uniformity, including both negative and
positive Fourier modes. -/
theorem pair_uniform {a : ι → ℕ → D → ℂ} (ha : UniformClass s w α a) (j m : ℤ) :
    UniformClass s w α (fun l n x => ErrorHarmonics.conjugatePair j (a l n) m x) := by
  have hp : UniformClass s w α (fun l n x => a l n x / 2) := by
    simpa only [ContinuousLinearMap.mul_apply', div_eq_mul_inv, mul_comm] using
      ha.map (ContinuousLinearMap.mul ℝ ℂ (2 : ℂ)⁻¹)
  have hn : UniformClass s w α (fun l n x => (starRingEnd ℂ) (a l n x / 2)) :=
    hp.map (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have hz := UniformClass.zero (s := s) (α := α) (E := ℂ) ha.weight_nonneg
  by_cases hm : m = j <;> by_cases hm' : -m = j
  · simpa only [ParticularWaveAssembly.pair_apply, ite_eq_left hm, ite_eq_left hm'] using hp.add hn
  · simpa only [ParticularWaveAssembly.pair_apply, ite_eq_left hm, ite_eq_right hm', map_zero,
      add_zero] using hp
  · simpa only [ParticularWaveAssembly.pair_apply, ite_eq_right hm, ite_eq_left hm', zero_add]
      using hn
  · simpa only [ParticularWaveAssembly.pair_apply, ite_eq_right hm, ite_eq_right hm', map_zero,
      add_zero] using hz

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem pair_sub_apply (j m : ℤ) (a b : D → ℂ) (x : D) :
    ErrorHarmonics.conjugatePair j (fun y => a y - b y) m x =
      ErrorHarmonics.conjugatePair j a m x - ErrorHarmonics.conjugatePair j b m x := by
  simp only [ParticularWaveAssembly.pair_apply]
  split_ifs <;> simp [sub_div, map_sub]
  all_goals ring

theorem coefficientBlock_uniform
    (k : ι → ℕ → ℝ) (Φ : ι → ℕ → D → ℝ) (kp : ι → ℕ → ℤ)
    {v : ι → ℕ → D → ComplexVector} {p : ι → ℕ → D → ℂ}
    (hv : UniformClass s w α v) (hp : UniformClass s w γ p) :
    (∀ i m, UniformClass s w α (fun l n x =>
      (SignedWaveUpdate.coefficientBlock (k l) (Φ l) (kp l) (v l) (p l)).velocity n i m x)) ∧
    (∀ m, UniformClass s w γ (fun l n x =>
      (SignedWaveUpdate.coefficientBlock (k l) (Φ l) (kp l) (v l) (p l)).pressure n m x)) :=
  ⟨fun i m => pair_uniform (hv.map (ContinuousLinearMap.proj i)) 1 m,
    fun m => pair_uniform hp 1 m⟩

end Pairing

section SignedBlocks

variable {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData (D × ℝ)} {w : ι → ℕ → D × ℝ → ℝ} {α γ : ℝ}

/-- Uniform full-angle amplitude and pressure bounds give the actual
stored coefficients of the angle-zero signed block. -/
theorem blockOfCoefficients_uniform
    (a : ι → LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ι → ℕ → ℤ)
    (ha : UniformClass s w α (fun l => (a l).amplitude))
    (hp : UniformClass s w γ (fun l => (a l).pressure)) :
    (∀ i m, UniformClass (SignedWaveUpdate.sectionStrip s) (fun l n x => w l n (x,0)) α
      (fun l n x => (SignedWaveUpdate.blockOfCoefficients (a l) (kp l)).velocity n i m x)) ∧
    (∀ m, UniformClass (SignedWaveUpdate.sectionStrip s) (fun l n x => w l n (x,0)) γ
      (fun l n x => (SignedWaveUpdate.blockOfCoefficients (a l) (kp l)).pressure n m x)) :=
  coefficientBlock_uniform (fun l => (a l).frequency) (fun l n x => (a l).phase n (x,0)) kp
    (uniform_zeroSection ha) (uniform_zeroSection hp)

/-- The smallness of a full-angle amplitude difference transfers to the
literal difference of the two stored velocity coefficients. -/
theorem blockOfCoefficients_difference_uniform
    (a b : ι → LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ι → ℕ → ℤ)
    (hab : UniformClass s w α (fun l n x => (a l).amplitude n x - (b l).amplitude n x))
    (i : Fin 3) (m : ℤ) :
    UniformClass (SignedWaveUpdate.sectionStrip s) (fun l n x => w l n (x,0)) α
      (fun l n x => (SignedWaveUpdate.blockOfCoefficients (a l) (kp l)).velocity n i m x -
        (SignedWaveUpdate.blockOfCoefficients (b l) (kp l)).velocity n i m x) := by
  have hh := pair_uniform ((uniform_zeroSection hab).map (ContinuousLinearMap.proj i)) 1 m
  apply hh.congr
  intro l n x hx
  exact pair_sub_apply 1 m (fun y => (a l).amplitude n (y,0) i)
    (fun y => (b l).amplitude n (y,0) i) x

/-- For the actual common corrected wave, the amplitude difference is
exactly the common curl correction. -/
theorem commonCorrected_difference_uniform {I : Type}
    (a : ι → PeriodizedWaveBounds.CopyData (D × ℝ) I)
    (d : ι → LinearWaveBounds.GraphDirections (D × ℝ)) (kp : ι → ℕ → ℤ)
    (hc : UniformClass s w α (fun l => (a l).common.curlCorrection s (d l)))
    (i : Fin 3) (m : ℤ) :
    UniformClass (SignedWaveUpdate.sectionStrip s) (fun l n x => w l n (x,0)) α
      (fun l n x => (SignedWaveUpdate.blockOfCoefficients ((a l).commonCorrected s (d l)) (kp
          l)).velocity n i m x -
        (SignedWaveUpdate.blockOfCoefficients (a l).common (kp l)).velocity n i m x) := by
  apply blockOfCoefficients_difference_uniform _ _ kp _ i m
  apply hc.congr
  intro l n x hx
  simp only [PeriodizedWaveBounds.CopyData.commonCorrected,
    LinearWaveBounds.WaveCoefficients.addAmplitude, add_sub_cancel_left]

end SignedBlocks

section ProductSignedBlocks

variable {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {P : ι → ℕ → D → ℝ} {α γ : ℝ}

theorem blockOfCoefficients_product_uniform
    (a : ι → LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ι → ℕ → ℤ)
    (ha : UniformWaveClass (HarmonicWaveInteraction.productStrip s) (fun l n x => P l n x.1)
      α (fun l => (a l).amplitude))
    (hp : UniformWaveClass (HarmonicWaveInteraction.productStrip s) (fun l n x => P l n x.1)
      γ (fun l => (a l).pressure)) :
    (∀ i m, UniformWaveClass s P α
      (fun l n x => (SignedWaveUpdate.blockOfCoefficients (a l) (kp l)).velocity n i m x)) ∧
    (∀ m, UniformWaveClass s P γ
      (fun l n x => (SignedWaveUpdate.blockOfCoefficients (a l) (kp l)).pressure n m x)) := by
  have h := blockOfCoefficients_uniform a kp ha hp
  rw [sectionStrip_productStrip] at h
  exact h

theorem commonCorrected_product_difference_uniform {I : Type}
    (a : ι → PeriodizedWaveBounds.CopyData (D × ℝ) I)
    (d : ι → LinearWaveBounds.GraphDirections (D × ℝ)) (kp : ι → ℕ → ℤ)
    (hc : UniformWaveClass (HarmonicWaveInteraction.productStrip s) (fun l n x => P l n x.1) α
      (fun l => (a l).common.curlCorrection (HarmonicWaveInteraction.productStrip s) (d l)))
    (i : Fin 3) (m : ℤ) :
    UniformWaveClass s P α
      (fun l n x => (SignedWaveUpdate.blockOfCoefficients
        ((a l).commonCorrected (HarmonicWaveInteraction.productStrip s) (d l)) (kp l)).velocity n i
            m x -
        (SignedWaveUpdate.blockOfCoefficients (a l).common (kp l)).velocity n i m x) := by
  have h := commonCorrected_difference_uniform a d kp hc i m
  rw [sectionStrip_productStrip] at h
  exact h

end ProductSignedBlocks

section FiniteAssembly

variable {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : ι → ℕ → D → ℝ} {α γ : ℝ}

/-- A fixed finite signed harmonic sum preserves uniformity in the
spatial label, independently of the total number of such labels. -/
theorem assembledBlock_uniform
    (N : ℕ) (k : ι → ℕ → ℝ) (Φ : ι → ℕ → D → ℝ) (kp : ι → ℕ → ℤ)
    {v : ι → ℤ → ℕ → D → ComplexVector} {p : ι → ℤ → ℕ → D → ℂ}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hv : ∀ j ∈ ParticularWaveAssembly.modes N, UniformClass s w α (fun l => v l j))
    (hp : ∀ j ∈ ParticularWaveAssembly.modes N, UniformClass s w γ (fun l => p l j)) :
    (∀ i m, UniformClass s w α (fun l n x =>
      (ParticularWaveAssembly.assembledBlock N (k l) (Φ l) (kp l) (v l) (p l)).velocity n i m x)) ∧
    (∀ m, UniformClass s w γ (fun l n x =>
      (ParticularWaveAssembly.assembledBlock N (k l) (Φ l) (kp l) (v l) (p l)).pressure n m x)) :=
          by
  constructor
  · intro i m
    have hs := UniformClass.sum (ParticularWaveAssembly.modes N)
      (fun j l n x => (ParticularWaveAssembly.modeBlock j (k l) (Φ l) (kp l) (v l j) (p l
          j)).velocity n i m x)
      hw (fun j hj => pair_uniform ((hv j hj).map (ContinuousLinearMap.proj i)) j m)
    apply hs.congr
    intro l n x hx
    change _ = (∑ j ∈ ParticularWaveAssembly.modes N,
      (ParticularWaveAssembly.modeBlock j (k l) (Φ l) (kp l) (v l j) (p l j)).velocity n i) m x
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
  · intro m
    have hs := UniformClass.sum (ParticularWaveAssembly.modes N)
      (fun j l n x => (ParticularWaveAssembly.modeBlock j (k l) (Φ l) (kp l) (v l j) (p l
          j)).pressure n m x)
      hw (fun j hj => pair_uniform (hp j hj) j m)
    apply hs.congr
    intro l n x hx
    change _ = (∑ j ∈ ParticularWaveAssembly.modes N,
      (ParticularWaveAssembly.modeBlock j (k l) (Φ l) (kp l) (v l j) (p l j)).pressure n) m x
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]

end FiniteAssembly

section NativeAssembly

variable {Q : Type} {ι F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual angle shuffle followed by the actual zero section. -/
theorem nativeSlice_uniform {s : StripData ((Q × ℝ) × TorusInverse.Plane)}
    {w : ι → ℕ → (Q × ℝ) × TorusInverse.Plane → ℝ} {α : ℝ}
    {f : ι → ℕ → (Q × ℝ) × TorusInverse.Plane → F} (hf : UniformClass s w α f) :
    UniformClass (ParticularWaveAssembly.sectionStrip s)
      (fun l n x => w l n (ParticularWaveAssembly.angleShuffle (x,0))) α
      (fun l n x => f l n (ParticularWaveAssembly.angleShuffle (x,0))) :=
  uniform_zeroSection (uniform_reindex (ParticularWaveAssembly.angleShuffle (P := Q)) hf)

/-- The native whole-angle strip used by the literal particular solver. -/
noncomputable def nativeStrip (s : StripData (Q × TorusInverse.Plane)) :
    StripData ((Q × ℝ) × TorusInverse.Plane) :=
  ParticularWaveBounds.reindexStrip (ParticularWaveAssembly.angleShuffle (P := Q)).symm
    (HarmonicWaveInteraction.productStrip s)

theorem sectionStrip_nativeStrip (s : StripData (Q × TorusInverse.Plane)) :
    ParticularWaveAssembly.sectionStrip (nativeStrip s) = s := by
  cases s
  rfl

theorem nativeSlice_original_uniform {s : StripData (Q × TorusInverse.Plane)}
    {w : ι → ℕ → (Q × ℝ) × TorusInverse.Plane → ℝ} {α : ℝ}
    {f : ι → ℕ → (Q × ℝ) × TorusInverse.Plane → F} (hf : UniformClass (nativeStrip s) w α f) :
    UniformClass s (fun l n x => w l n (ParticularWaveAssembly.angleShuffle (x,0))) α
      (fun l n x => f l n (ParticularWaveAssembly.angleShuffle (x,0))) := by
  have h := nativeSlice_uniform hf
  rw [sectionStrip_nativeStrip] at h
  exact h

/-- Full-angle, already periodized mode coefficients produce the actual
finite particular block. Every output mode has uniform label bounds. -/
theorem native_assembledBlock_uniform
    {s : StripData ((Q × ℝ) × TorusInverse.Plane)}
    {w : ι → ℕ → (Q × ℝ) × TorusInverse.Plane → ℝ} {α γ : ℝ}
    (N : ℕ) (k : ι → ℕ → ℝ) (Φ : ι → ℕ → Q × TorusInverse.Plane → ℝ) (kp : ι → ℕ → ℤ)
    {v : ι → ℤ → ℕ → (Q × ℝ) × TorusInverse.Plane → ComplexVector}
    {p : ι → ℤ → ℕ → (Q × ℝ) × TorusInverse.Plane → ℂ}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hv : ∀ j ∈ ParticularWaveAssembly.modes N, UniformClass s w α (fun l => v l j))
    (hp : ∀ j ∈ ParticularWaveAssembly.modes N, UniformClass s w γ (fun l => p l j)) :
    (∀ i m, UniformClass (ParticularWaveAssembly.sectionStrip s)
      (fun l n x => w l n (ParticularWaveAssembly.angleShuffle (x,0))) α
      (fun l n x => (ParticularWaveAssembly.assembledBlock N (k l) (Φ l) (kp l)
        (fun j n x => v l j n (ParticularWaveAssembly.angleShuffle (x,0)))
        (fun j n x => p l j n (ParticularWaveAssembly.angleShuffle (x,0)))).velocity n i m x)) ∧
    (∀ m, UniformClass (ParticularWaveAssembly.sectionStrip s)
      (fun l n x => w l n (ParticularWaveAssembly.angleShuffle (x,0))) γ
      (fun l n x => (ParticularWaveAssembly.assembledBlock N (k l) (Φ l) (kp l)
        (fun j n x => v l j n (ParticularWaveAssembly.angleShuffle (x,0)))
        (fun j n x => p l j n (ParticularWaveAssembly.angleShuffle (x,0)))).pressure n m x)) :=
  assembledBlock_uniform N k Φ kp (fun l n x hx => hw l n (ParticularWaveAssembly.angleShuffle
      (x,0)) hx)
    (fun j hj => nativeSlice_uniform (hv j hj)) (fun j hj => nativeSlice_uniform (hp j hj))

theorem native_assembledBlock_original_uniform
    {s : StripData (Q × TorusInverse.Plane)}
    {w : ι → ℕ → (Q × ℝ) × TorusInverse.Plane → ℝ} {α γ : ℝ}
    (N : ℕ) (k : ι → ℕ → ℝ) (Φ : ι → ℕ → Q × TorusInverse.Plane → ℝ) (kp : ι → ℕ → ℤ)
    {v : ι → ℤ → ℕ → (Q × ℝ) × TorusInverse.Plane → ComplexVector}
    {p : ι → ℤ → ℕ → (Q × ℝ) × TorusInverse.Plane → ℂ}
    (hw : ∀ l n x, x ∈ (nativeStrip s).domain → 0 ≤ w l n x)
    (hv : ∀ j ∈ ParticularWaveAssembly.modes N, UniformClass (nativeStrip s) w α (fun l => v l j))
    (hp : ∀ j ∈ ParticularWaveAssembly.modes N, UniformClass (nativeStrip s) w γ (fun l => p l j)) :
    (∀ i m, UniformClass s (fun l n x => w l n (ParticularWaveAssembly.angleShuffle (x,0))) α
      (fun l n x => (ParticularWaveAssembly.assembledBlock N (k l) (Φ l) (kp l)
        (fun j n x => v l j n (ParticularWaveAssembly.angleShuffle (x,0)))
        (fun j n x => p l j n (ParticularWaveAssembly.angleShuffle (x,0)))).velocity n i m x)) ∧
    (∀ m, UniformClass s (fun l n x => w l n (ParticularWaveAssembly.angleShuffle (x,0))) γ
      (fun l n x => (ParticularWaveAssembly.assembledBlock N (k l) (Φ l) (kp l)
        (fun j n x => v l j n (ParticularWaveAssembly.angleShuffle (x,0)))
        (fun j n x => p l j n (ParticularWaveAssembly.angleShuffle (x,0)))).pressure n m x)) := by
  have h := native_assembledBlock_uniform N k Φ kp hw hv hp
  rw [sectionStrip_nativeStrip] at h
  exact h

end NativeAssembly

section StateReindex

variable {D E : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The last coordinate reassociation acts on the actual stored velocity
coefficients and preserves the uniform class. -/
theorem block_velocity_reindex (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {w : ι → ℕ → E → ℝ} {α : ℝ} {a : ι → CorrectionState.HarmonicBlock E}
    (i : Fin 3) (j : ℤ) (ha : UniformClass s w α (fun l n x => (a l).velocity n i j x)) :
    UniformClass (StateReindex.strip e s) (fun l n x => w l n (e x)) α
      (fun l n x => (StateReindex.block e (a l)).velocity n i j x) :=
  uniform_reindex e ha

theorem block_pressure_reindex (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {w : ι → ℕ → E → ℝ} {α : ℝ} {a : ι → CorrectionState.HarmonicBlock E}
    (j : ℤ) (ha : UniformClass s w α (fun l n x => (a l).pressure n j x)) :
    UniformClass (StateReindex.strip e s) (fun l n x => w l n (e x)) α
      (fun l n x => (StateReindex.block e (a l)).pressure n j x) :=
  uniform_reindex e ha

end StateReindex

end NavierStokes.UniformBlockBounds
