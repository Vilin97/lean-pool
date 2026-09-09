/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformPrimaryWeights
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedMeanInteraction

@[expose] public section

/-!
# Uniform estimates for the actual harmonic interaction

The finite-jet constants are chosen before the spatial label and band.
The nonlinear estimate uses exact mode solenoidality to remove the phase
normal. Only the fixed signed harmonic ratio remains in that cancellation.
-/

noncomputable section

namespace NavierStokes.UniformHarmonicInteraction

open Set Filter Function WeightedClasses LabelSumBounds HarmonicCalculus HarmonicFields
open WaveInteractionBounds HarmonicMeanInteraction HarmonicWaveInteraction
open scoped Topology ContDiff BigOperators

variable {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Uniform input classes for each fixed signed Fourier mode and physical
component. The label and band are inside the uniform estimate. -/
noncomputable def UniformVelocity (s : StripData D) (P : ι → ℕ → D → ℝ) (α : ℝ)
    (a : ι → CorrectionState.HarmonicBlock D) : Prop :=
  ∀ i j, j ≠ 0 → UniformWaveClass s P α (fun l n x => (a l).velocity n i j x)

theorem waveBounds_each {s : StripData D} {P : ι → ℕ → D → ℝ} {α : ℝ}
    {a : ι → CorrectionState.HarmonicBlock D} (ha : UniformVelocity s P α a) (l : ι) :
    (a l).WaveBounds s (P l) α := fun i j hj => (ha i j hj).each l

section UniformAlgebra

variable {s : StripData D} {w v : ι → ℕ → D → ℝ} {α β κ : ℝ}

theorem cmul {f g : ι → ℕ → D → ℂ} (hf : UniformClass s w α f)
    (hg : UniformClass s v β g) :
    UniformClass s (fun l n x => w l n x * v l n x) (α+β)
      (fun l n x => f l n x * g l n x) :=
  hf.bilinear hg (ContinuousLinearMap.mul ℝ ℂ)

theorem div_radius (G : Geometry s κ) {f : ι → ℕ → D → ℂ} (hf : UniformClass s w α f) :
    UniformClass s w α (fun l n x => f l n x / (G.radius n x : ℂ)) := by
  simpa only [mul_one, add_zero, div_eq_mul_inv] using
    cmul hf (UniformPrimaryWeights.class_of_single (inverse_radius_complex G))

theorem generator {a : ι → Family D}
    (ha : ∀ i, UniformClass s w α (fun l n x => a l n x i)) (i : Fin 3) :
    UniformClass s w α (fun l n x => angularGenerator (a l n x) i) := by
  fin_cases i
  · exact (ha 1).neg
  · exact ha 0
  · exact UniformClass.zero (ha 0).weight_nonneg

theorem strippedTransport_uniform (G : Geometry s κ) (hκ : 0 ≤ κ)
    {a b : ι → Family D}
    (ha : ∀ i, UniformClass s w α (fun l n x => a l n x i))
    (hb : ∀ i, UniformClass s v β (fun l n x => b l n x i)) (i : Fin 3) :
    UniformClass s (fun l n x => w l n x * v l n x) (α+β-κ)
      (fun l n x => strippedTransport G (a l) (b l) n x i) := by
  have hr := cmul (ha 0) (UniformPrimaryWeights.along_class
    (UniformPrimaryWeights.class_of_single G.radial_class) (hb i))
  have hr' : UniformClass s (fun l n x => w l n x * v l n x) (α+β-κ)
      (fun l n x => a l n x 0 * along (G.radial n) (fun y => b l n y i) x) := by
    convert! hr using 1
    ring
  have hc := cmul (div_radius G (ha 1)) (generator hb i)
  have hc' := hc.mono_exponent (show α+β-κ ≤ α+β by linarith)
  have hz := cmul (ha 2) (UniformPrimaryWeights.along_class
    (UniformPrimaryWeights.class_of_single G.axial_class) (hb i))
  have hz' := hz.mono_exponent (show α+β-κ ≤ α+(β+1) by linarith)
  exact (hr'.add hc').add hz'

theorem strippedDivergence_uniform (G : Geometry s κ) (hκ : 0 ≤ κ)
    {a : ι → Family D} (ha : ∀ i, UniformClass s w α (fun l n x => a l n x i)) :
    UniformClass s w (α-κ)
      (fun l n => strippedDivergence (G.radius n) (G.radial n) (G.axial n) (a l n)) := by
  have hr : UniformClass s w (α-κ) (fun l n => along (G.radial n) (fun x => a l n x 0)) := by
    simpa only [sub_eq_add_neg] using UniformPrimaryWeights.along_class
      (UniformPrimaryWeights.class_of_single G.radial_class) (ha 0)
  have hc := (div_radius G (ha 0)).mono_exponent (show α-κ ≤ α by linarith)
  have hz := (UniformPrimaryWeights.along_class
    (UniformPrimaryWeights.class_of_single G.axial_class) (ha 2)).mono_exponent
      (show α-κ ≤ α+1 by linarith)
  apply ((hr.add hc).add hz).congr
  intro l n x hx
  simp only [strippedDivergence, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

end UniformAlgebra

section Cancellation

variable {s : StripData D} {κ α β : ℝ} {P : ℕ → D → ℝ}

/-- Exact cancellation for the literal ordered harmonic coefficient.
The output contains no phase normal and no carrier magnitude. -/
theorem orderedKernel_eq_cancelled
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : CorrectionState.HarmonicBlock D}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hdiv : ModeSolenoidal s c a)
    {j m : ℤ} (hj : j ≠ 0) (hm : m ≠ 0) (n : ℕ) {x : D} (hx : x ∈ s.domain) (i : Fin 3) :
    orderedKernel (HarmonicResidual.contextFrame c n) (a.frequency n)
      (a.phase n) (a.angularFrequency n) m (amplitude a j n) (amplitude b m n) x i =
      strippedTransport (slowGeometry c ho hR) (amplitude a j) (amplitude b m) n x i +
        (((m : ℝ)/(j : ℝ)) • (-strippedDivergence ((slowGeometry c ho hR).radius n)
          ((slowGeometry c ho hR).radial n) ((slowGeometry c ho hR).axial n)
          (amplitude a j n) x)) * amplitude b m n x i := by
  let G := slowGeometry c ho hR
  let G' := liftedGeometry G
  have hpa : DifferentiableAt ℝ (a.phase n) x :=
    ((hΦ n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have had (r : Fin 3) : DifferentiableAt ℝ (fun y => amplitude a j n y r) x :=
    (((blockAmplitude_class ha hj r).smooth n).contDiffAt
      (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hbd (r : Fin 3) : DifferentiableAt ℝ (fun y => amplitude b m n y r) x :=
    (((blockAmplitude_class hb hm r).smooth n).contDiffAt
      (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have had' (r : Fin 3) : DifferentiableAt ℝ
      (fun p : D × ℝ => amplitude a j n p.1 r) (x,0) :=
    (had r).comp (x,0) differentiableAt_fst
  have hphase : DifferentiableAt ℝ (fullPhase a n) (x,0) :=
    (fullPhase_hasFDerivAt a n hpa).differentiableAt
  have hnu : a.frequency n * (j : ℝ) ≠ 0 :=
    mul_ne_zero (hk n) (by exact_mod_cast hj)
  have hd := hdiv j hj n (x,0) hx
  rw [singleMode_eq a j n (hk n)] at hd
  have hang := lifted_amplitude_angularIndependent G ha hj n 1 (x,0) hx
  have hswitch := switched_longitudinal (G'.radius n) (G'.radial n) (G'.angular n) (G'.axial n)
    (a.frequency n*(j:ℝ)) (a.frequency n*(m:ℝ)) hnu hphase had' hang hd
  have hratio : (a.frequency n*(m:ℝ))/(a.frequency n*(j:ℝ)) = (m:ℝ)/(j:ℝ) := by
    field_simp [hk n]
  have ht : strippedTransport G'
      (fun n p => amplitude a j n p.1) (fun n p => amplitude b m n p.1) n (x,0) i =
      strippedTransport G (amplitude a j) (amplitude b m) n x i := by
    change amplitude a j n x 0 * along (HarmonicResidual.liftDirection (G.radial n))
      (fun p => amplitude b m n p.1 i) (x,0) +
      (amplitude a j n x 1 / (G.radius n x : ℂ)) * angularGenerator (amplitude b m n x) i +
      amplitude a j n x 2 * along (HarmonicResidual.liftDirection (G.axial n))
        (fun p => amplitude b m n p.1 i) (x,0) = _
    rw [along_fst (G.radial n) (p := (x,0)) (hbd i),
      along_fst (G.axial n) (p := (x,0)) (hbd i)]
    rfl
  have hd' : strippedDivergence (G'.radius n) (G'.radial n) (G'.axial n)
      (fun p => amplitude a j n p.1) (x,0) =
      strippedDivergence (G.radius n) (G.radial n) (G.axial n) (amplitude a j n) x := by
    change along (HarmonicResidual.liftDirection (G.radial n))
      (fun p => amplitude a j n p.1 0) (x,0) +
      (G.radius n x)⁻¹ • amplitude a j n x 0 +
      along (HarmonicResidual.liftDirection (G.axial n))
        (fun p => amplitude a j n p.1 2) (x,0) = _
    rw [along_fst (G.radial n) (p := (x,0)) (had 0),
      along_fst (G.axial n) (p := (x,0)) (had 2)]
    rfl
  rw [orderedKernel_eq_fullCoefficient c ho hR a (amplitude a j) (amplitude b m)
    m n hx (hk n) hpa hbd i]
  change strippedTransport G' _ _ n (x,0) i +
    (phaseFactor (a.frequency n*(m:ℝ)) *
      normalDot (phaseNormal (G'.radius n) (G'.radial n) (G'.angular n) (G'.axial n)
        (fullPhase a n) (x,0)) (amplitude a j n x)) * amplitude b m n x i = _
  rw [hswitch, hratio, hd', ht]

end Cancellation

section Nonlinear

variable {s : StripData D} {κ α β : ℝ} {P : ι → ℕ → D → ℝ}

theorem blockAmplitude_uniform {a : ι → CorrectionState.HarmonicBlock D}
    (ha : UniformVelocity s P α a) {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    UniformWaveClass s P α (fun l n x => amplitude (a l) j n x i) := by
  have h := ((ha i j hj).add ((ha i (-j) (neg_ne_zero.mpr hj)).map
    (Complex.conjCLE : ℂ →L[ℝ] ℂ))).map (ContinuousLinearMap.mul ℝ ℂ (2 : ℂ)⁻¹)
  simp only [amplitude, blockAmplitude, HarmonicResidual.realCoefficients_apply,
    ContinuousLinearMap.mul_apply'] at h ⊢
  exact h

/-- The genuine ordered coefficient has a uniform class before summing
harmonics. No quantitative assumption on the phase normal is used. -/
theorem orderedKernel_uniform
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : ι → CorrectionState.HarmonicBlock D}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0) (hdiv : ∀ l, ModeSolenoidal s c (a l))
    {j m : ℤ} (hj : j ≠ 0) (hm : m ≠ 0) (i : Fin 3) :
    UniformClass s (fun l n x => (Real.sqrt (s.zeta x) * P l n x) *
      (Real.sqrt (s.zeta x) * P l n x)) (α+β-κ)
      (fun l n x => orderedKernel (HarmonicResidual.contextFrame c n) ((a l).frequency n)
        ((a l).phase n) ((a l).angularFrequency n) m
        (amplitude (a l) j n) (amplitude (b l) m n) x i) := by
  let G := slowGeometry c ho hR
  have ha' := fun r => blockAmplitude_uniform ha hj r
  have hb' := fun r => blockAmplitude_uniform hb hm r
  have hd := (strippedDivergence_uniform G ho.kappa_nonneg ha').neg.map
    (((m:ℝ)/(j:ℝ)) • ContinuousLinearMap.id ℝ ℂ)
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply] at hd
  have hp : UniformClass s (fun l n x => (Real.sqrt (s.zeta x) * P l n x) *
      (Real.sqrt (s.zeta x) * P l n x)) (α+β-κ)
      (fun l n x => (((m:ℝ)/(j:ℝ)) • (-strippedDivergence (G.radius n)
        (G.radial n) (G.axial n) (amplitude (a l) j n) x)) * amplitude (b l) m n x i) := by
    convert! cmul hd (hb' i) using 1
    ring
  apply ((strippedTransport_uniform G ho.kappa_nonneg ha' hb' i).add hp).congr
  intro l n x hx
  exact (orderedKernel_eq_cancelled c ho hR (waveBounds_each ha l) (waveBounds_each hb l)
    (hΦ l) (hk l) (hdiv l) hj hm n hx i).symm

/-- Zero input modes contribute exactly zero, so the uniform ordered
estimate applies to every signed pair of Fourier indices. -/
theorem orderedKernel_uniform_all
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : ι → CorrectionState.HarmonicBlock D}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (ha0 : ∀ l, ZeroMode (a l)) (hb0 : ∀ l, ZeroMode (b l))
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0) (hdiv : ∀ l, ModeSolenoidal s c (a l))
    (j m : ℤ) (i : Fin 3) :
    UniformClass s (fun l n x => (Real.sqrt (s.zeta x) * P l n x) *
      (Real.sqrt (s.zeta x) * P l n x)) (α+β-κ)
      (fun l n x => orderedKernel (HarmonicResidual.contextFrame c n) ((a l).frequency n)
        ((a l).phase n) ((a l).angularFrequency n) m
        (amplitude (a l) j n) (amplitude (b l) m n) x i) := by
  have hw l n x (_ : x ∈ s.domain) :
      0 ≤ (Real.sqrt (s.zeta x)*P l n x) * (Real.sqrt (s.zeta x)*P l n x) :=
    mul_self_nonneg _
  by_cases hj : j = 0
  · subst j
    apply (UniformClass.zero (α := α+β-κ) (E := ℂ) hw).congr
    intro l n x hx
    simp only [amplitude_zero (ha0 l), orderedKernel_zero_left]
  by_cases hm : m = 0
  · subst m
    apply (UniformClass.zero (α := α+β-κ) (E := ℂ) hw).congr
    intro l n x hx
    simp only [amplitude_zero (hb0 l), orderedKernel_zero_right]
  exact orderedKernel_uniform c ho hR ha hb hΦ hk hdiv hj hm i

/-- Only the common harmonic band is summed. The number of spatial labels
does not enter the constants. -/
theorem transport_uniform_raw
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : ι → CorrectionState.HarmonicBlock D} {M : ℕ}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (ha0 : ∀ l, ZeroMode (a l)) (hb0 : ∀ l, ZeroMode (b l))
    (hM : ∀ l, (a l).BandLimited M)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0) (hdiv : ∀ l, ModeSolenoidal s c (a l))
    (m : ℤ) (i : Fin 3) :
    UniformClass s (fun l n x => (Real.sqrt (s.zeta x) * P l n x) *
      (Real.sqrt (s.zeta x) * P l n x)) (α+β-κ)
      (fun l n x => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
        ((a l).frequency n) ((a l).phase n) ((a l).angularFrequency n)
        (blockAmplitude (a l) n) (blockAmplitude (b l) n) i m x) := by
  have hsum := UniformClass.sum (harmonicRange M)
    (fun j l n x => orderedKernel (HarmonicResidual.contextFrame c n) ((a l).frequency n)
      ((a l).phase n) ((a l).angularFrequency n) (m-j)
      (amplitude (a l) j n) (amplitude (b l) (m-j) n) x i)
    (fun l n x _ => mul_self_nonneg (Real.sqrt (s.zeta x)*P l n x))
    (fun j _ => orderedKernel_uniform_all c ho hR ha hb ha0 hb0 hΦ hk hdiv j (m-j) i)
  apply hsum.congr
  intro l n x hx
  exact (transport_convolution _ _ _ _ _ _ (harmonicRange M)
    (fun r => band_support_range (HarmonicResidual.band_realCoefficients ((hM l).1 n r))) m x
      i).symm

theorem square_weight_wave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ} {f : ι → ℕ → D → E}
    (hf : UniformClass s (fun l n x => (Real.sqrt (s.zeta x)*P l n x) *
      (Real.sqrt (s.zeta x)*P l n x)) γ f)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1) : UniformWaveClass s P γ f := by
  apply hf.mono_weight (fun l n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP0 l n x hx))
  intro l n x hx
  have hs1 : Real.sqrt (s.zeta x) ≤ 1 := by
    nlinarith [Real.sq_sqrt (s.zeta_nonneg x hx), hζ x hx, Real.sqrt_nonneg (s.zeta x)]
  have hw1 : Real.sqrt (s.zeta x)*P l n x ≤ 1 :=
    (mul_le_mul hs1 (hP1 l n x hx) (hP0 l n x hx) zero_le_one).trans_eq (one_mul 1)
  exact mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) (hP0 l n x hx)) hw1

theorem transport_uniform
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : ι → CorrectionState.HarmonicBlock D} {M : ℕ}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (ha0 : ∀ l, ZeroMode (a l)) (hb0 : ∀ l, ZeroMode (b l))
    (hM : ∀ l, (a l).BandLimited M)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0) (hdiv : ∀ l, ModeSolenoidal s c (a l))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1) (m : ℤ) (i : Fin 3) :
    UniformWaveClass s P (α+β-κ)
      (fun l n x => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
        ((a l).frequency n) ((a l).phase n) ((a l).angularFrequency n)
        (blockAmplitude (a l) n) (blockAmplitude (b l) n) i m x) :=
  square_weight_wave (transport_uniform_raw c ho hR ha hb ha0 hb0 hM hΦ hk hdiv m i)
    ho.weight_le_one hP0 hP1

theorem mixed_uniform
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : ι → CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (ha0 : ∀ l, ZeroMode (a l)) (hb0 : ∀ l, ZeroMode (b l))
    (hM : ∀ l, (a l).BandLimited M) (hN : ∀ l, (b l).BandLimited N)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0)
    (hda : ∀ l, ModeSolenoidal s c (a l))
    (hdb : ∀ l, ModeSolenoidal s c (withCarrier (a l) (b l)))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1) (m : ℤ) (i : Fin 3) :
    UniformWaveClass s P (α+β-κ) (fun l n x =>
      blockTransport c (a l) (a l) (b l) n i m x +
        blockTransport c (a l) (b l) (a l) n i m x) := by
  have hab := transport_uniform c ho hR ha hb ha0 hb0 hM hΦ hk hda hP0 hP1 m i
  have hba := transport_uniform c ho hR (a := fun l => withCarrier (a l) (b l))
    hb ha hb0 ha0 hN hΦ hk hdb hP0 hP1 m i
  have hba' : UniformWaveClass s P (α+β-κ)
      (fun l n x => blockTransport c (a l) (b l) (a l) n i m x) := by
    simp only [blockTransport, withCarrier, add_comm β α] at hba ⊢
    exact hba
  exact hab.add hba'

theorem square_uniform
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (a : ι → CorrectionState.HarmonicBlock D) {b : ι → CorrectionState.HarmonicBlock D} {N : ℕ}
    (hb : UniformVelocity s P β b) (hb0 : ∀ l, ZeroMode (b l)) (hN : ∀ l, (b l).BandLimited N)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0)
    (hdb : ∀ l, ModeSolenoidal s c (withCarrier (a l) (b l)))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1) (m : ℤ) (i : Fin 3) :
    UniformWaveClass s P (2*β-κ)
      (fun l n x => blockTransport c (a l) (b l) (b l) n i m x) := by
  have he := transport_uniform c ho hR (a := fun l => withCarrier (a l) (b l))
    hb hb hb0 hb0 hN hΦ hk hdb hP0 hP1 m i
  simp only [two_mul] at he ⊢
  exact he

/-- The literal three-term nonlinear update has a uniform class over all
labels, with the mixed and self-interaction exponents both retained. -/
theorem nonlinearCoefficients_uniform
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {a b : ι → CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (ha0 : ∀ l, ZeroMode (a l)) (hb0 : ∀ l, ZeroMode (b l))
    (hM : ∀ l, (a l).BandLimited M) (hN : ∀ l, (b l).BandLimited N)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0)
    (hda : ∀ l, ModeSolenoidal s c (a l))
    (hdb : ∀ l, ModeSolenoidal s c (withCarrier (a l) (b l)))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1) (m : ℤ) (i : Fin 3) :
    UniformWaveClass s P (min (α+β-κ) (2*β-κ))
      (fun l n x => nonlinearCoefficients c (a l) (b l) n i m x) := by
  exact ((mixed_uniform c ho hR ha hb ha0 hb0 hM hN hΦ hk hda hdb hP0 hP1 m i).mono_exponent
    (min_le_left _ _)).add ((square_uniform c ho hR a hb hb0 hN hΦ hk hdb hP0 hP1 m i).mono_exponent
      (min_le_right _ _))

end Nonlinear

section ActualBlock

variable {s : StripData D} {κ α β μ : ℝ} {P : ι → ℕ → D → ℝ}

/-- The actual interaction block, including the unchanged state's mean,
has one finite-jet bound uniform over labels and bands. Phase normals and
frequencies are required only on the genuine support patch of each wave. -/
theorem interactionBlock_uniform
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1/2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {u : CorrectionState.State D} (hmean : MeanIncrementBounds.IncrementBounds s μ u.mean)
    {a b : ι → CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (ha0 : ∀ l, ZeroMode (a l)) (hb0 : ∀ l, ZeroMode (b l))
    (hM : ∀ l, (a l).BandLimited M) (hN : ∀ l, (b l).BandLimited N)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0)
    (hda : ∀ l, ModeSolenoidal s c (a l))
    (hdb : ∀ l, ModeSolenoidal s c (withCarrier (a l) (b l)))
    {C : ℕ → ι → Set D}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s C 0
      (fun n l x => slowNormal c ho hR (a l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s C (-(1/2))
      (fun n l _ => (a l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s C (-(1/2))
      (fun n l _ => ((a l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ C n l →
      ∀ i j, j ≠ 0 → (b l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    UniformClass s (fun l n x => Real.sqrt (s.zeta x) * P l n x)
      (min (β+μ-1/2) (min (α+β-κ) (2*β-κ)))
      (fun l n x => (interactionBlock c u (a l) (b l)).velocity n i j x) := by
  have hm := LocalizedMeanInteraction.uniform_realMeanCross_class c ho hκ hR hmean
    (b := fun l => withCarrier (a l) (b l)) (P := fun n l => P l n)
    hb hNormal hFreq hAng hz hj i
  have hn m := nonlinearCoefficients_uniform c ho hR ha hb ha0 hb0 hM hN hΦ hk hda hdb hP0 hP1 m i
  have hnr := LabelSumBounds.uniform_realCoefficients
    (fun l n => nonlinearCoefficients c (a l) (b l) n i) hn j
  apply ((hm.mono_exponent (min_le_left _ _)).add
    (hnr.mono_exponent (min_le_right _ _))).congr
  intro l n x hx
  change _ = HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients
    (meanCross c u.mean (withCarrier (a l) (b l)) n i + nonlinearCoefficients c (a l) (b l) n i)) j
      x
  rw [nonconstant_apply_of_ne _ hj, realCoefficients_add]
  rfl

/-- The same expression is still a genuine finite harmonic block, with
zero constant mode and the original carrier. This is independent of the
estimates and uses the exact coefficient constructors. -/
theorem interactionBlock_structure
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : ι → CorrectionState.HarmonicBlock D) {M N : ℕ}
    (hM : ∀ l, (a l).BandLimited M) (hN : ∀ l, (b l).BandLimited N) (l : ι) :
    (interactionBlock c u (a l) (b l)).BandLimited (max (M+N) (N+N)) ∧
    ZeroMode (interactionBlock c u (a l) (b l)) ∧
    (interactionBlock c u (a l) (b l)).frequency = (a l).frequency ∧
    (interactionBlock c u (a l) (b l)).phase = (a l).phase ∧
    (interactionBlock c u (a l) (b l)).angularFrequency = (a l).angularFrequency :=
  ⟨HarmonicWaveInteraction.interactionBlock_band c u (hM l) (hN l),
    HarmonicWaveInteraction.interactionBlock_zero c u (a l) (b l), rfl, rfl, rfl⟩

end ActualBlock

end NavierStokes.UniformHarmonicInteraction
