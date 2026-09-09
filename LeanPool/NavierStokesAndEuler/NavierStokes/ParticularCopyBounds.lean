/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveBounds

@[expose] public section

/-!
# Joint native-copy bounds for the actual particular inverse

The modal input bounds below quantify their constants before the lattice
copy.  The velocity is the actual finite-path Volterra solve and pressure
is its actual projected pressure coefficient.  No output jet estimate is
assumed, and no assertion that separate copy classes have uniform constants
is used.
-/

noncomputable section

namespace NavierStokes.ParticularCopyBounds

open Set Function Filter WeightedClasses PeriodizedWaveBounds
open CommonCoverSolve TorusInverse ParticularWaveBounds PrimaryODE
open PrimaryPulseBounds
open scoped Topology ContDiff InnerProductSpace


variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Primitive modal bounds on neighborhoods of the native support cells.
Every quantitative constant precedes the band and lattice copy. -/
structure ModalControl (s : StripData (P × Plane)) (α : ℝ)
    (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (t : ℕ → TangentData P ProblemStatement.Space)
    (harmonic : ℤ) (g : ℕ → Geometry) (L : ℕ → ℝ) (envelope : ℕ → ℝ → ℝ)
    (cells : ℕ → Frequency → Set (P × Plane)) where
  neighborhood : ℕ → Frequency → Set (P × Plane)
  open_neighborhood : ∀ n k, IsOpen (neighborhood n k)
  contains : ∀ n k x, x ∈ s.domain → x ∈ cells n k → x ∈ neighborhood n k
  interval : ℕ → Set ℝ
  open_interval : ∀ n, IsOpen (interval n)
  length_pos : ∀ n, 0 < L n
  contains_interval : ∀ n, Icc 0 (L n) ⊆ interval n
  bridge : ∀ n k, PrimaryCopyBridge.Inputs (d n) (t n) harmonic (g n) k (neighborhood n k) 0 (L n)
  coefficient_smooth : ∀ n k, ContDiffOn ℝ ∞
    ((PrimaryCopyBridge.copyFrame (d n) (g n) k).coefficient harmonic) (neighborhood n k ×ˢ
      interval n)
  forcing_smooth : ∀ n k, ContDiffOn ℝ ∞
    ((PrimaryCopyBridge.copyFrame (d n) (g n) k).forcing
      (PrimaryCopyBridge.copySource (t n).source (g n) k)) (neighborhood n k ×ˢ interval n)
  columns_smooth : ∀ n k (i : Fin 2), ContDiffOn ℝ ∞
    (synthesisColumn (PrimaryCopyBridge.copyFrame (d n) (g n) k) i) (neighborhood n k ×ˢ interval n)
  current_slot : ∀ n k x, x ∈ neighborhood n k → ((g n).coordinates k x.2).2 ∈ Ioo 0 (L n)
  rate : ℕ → ℝ → ℝ
  envelope_pos : ∀ n v, 0 < envelope n v
  envelope_deriv : ∀ n v, HasDerivAt (envelope n) (rate n v * envelope n v) v
  errorRate : ℕ → ℝ
  errorRate_nonneg : ∀ n, 0 ≤ errorRate n
  boundConstant : ℝ
  constant_ge_one : 1 ≤ boundConstant
  coordinate_power : ℕ
  length_bound : ∀ n, L n ≤ boundConstant * s.slow n
  exponential_bound : ∀ n, Real.exp (errorRate n * L n) ≤ boundConstant
  coordinate_bound : ∀ n, CommonCoverClass.argumentCost (g n) ≤ boundConstant * s.slow n ^
    coordinate_power
  energy : ∀ n k x, x ∈ s.domain → x ∈ cells n k → ∀ v ∈ Icc 0 (L n), ∀ z : PrimaryODE.State,
    ⟪z, (PrimaryCopyBridge.copyFrame (d n) (g n) k).coefficient harmonic (x,v) z⟫_ℝ ≤
      (rate n v + errorRate n) * ‖z‖^2
  input_jets : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ,
    ∀ n k x, x ∈ s.domain → x ∈ cells n k → ∀ j ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ j ((PrimaryCopyBridge.copyFrame (d n) (g n) k).coefficient harmonic) (x,v)‖
        ≤
        C * s.growth n x ^ m ∧
      ‖iteratedFDeriv ℝ j ((PrimaryCopyBridge.copyFrame (d n) (g n) k).forcing
        (PrimaryCopyBridge.copySource (t n).source (g n) k)) (x,v)‖ ≤
        (s.epsilon n ^ α * Real.sqrt (s.zeta x)) * C * s.growth n x ^ m * envelope n v ∧
      ∀ i : Fin 2, ‖iteratedFDeriv ℝ j
        (synthesisColumn (PrimaryCopyBridge.copyFrame (d n) (g n) k) i) (x,v)‖ ≤ C * s.growth n x ^
          m

namespace ModalControl

variable {s : StripData (P × Plane)} {α : ℝ}
  {d : ℕ → PrimaryODE.FrameData (P × ℝ)} {t : ℕ → TangentData P ProblemStatement.Space}
  {harmonic : ℤ} {g : ℕ → Geometry} {L : ℕ → ℝ} {envelope : ℕ → ℝ → ℝ}
  {cells : ℕ → Frequency → Set (P × Plane)}
  (h : ModalControl s α d t harmonic g L envelope cells)

include h

theorem smooth_at (hL : ∀ n, 0 < L n) {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ s.domain) (hk : x ∈ cells n k) :
    ContDiffAt ℝ ∞ ((t n).linearData.copySolve (g n) (hL n).le k) x :=
  (copySolve_contDiffOn_from_modal (d n) (t n) harmonic (g n) k (hL n)
    (h.open_neighborhood n k) (h.open_interval n) (h.contains_interval n) (h.bridge n k)
    (h.coefficient_smooth n k) (h.forcing_smooth n k) (h.columns_smooth n k)
    (h.current_slot n k)).contDiffAt ((h.open_neighborhood n k).mem_nhds (h.contains n k x hx hk))

/-- The actual finite-path solve has one bound for all lattice copies.
The comparison keeps the native Gaussian envelope in the output weight. -/
theorem localJets (hL : ∀ n, 0 < L n) (W : ℕ → P × Plane → ℝ)
    (hW : ∀ n k x, x ∈ s.domain → x ∈ cells n k → envelope n ((g n).coordinates k x.2).2 ≤ W n x) :
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α cells
      (fun n k => (t n).linearData.copySolve (g n) (hL n).le k) := by
  refine ⟨fun _ _ _ hx hk => h.smooth_at hL hx hk, ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := h.input_jets N
  let K := C + h.boundConstant + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith [h.constant_ge_one]
  have hCK : C ≤ K := by dsimp [K]; linarith [h.constant_ge_one]
  have hK₀K : h.boundConstant ≤ K := by dsimp [K]; linarith
  let B := (2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (hK.trans (le_rescaleConstant N K)))
  have hconst : 0 ≤ ambientJetConstant N := by unfold ambientJetConstant; positivity
  have hK₀ : 0 ≤ h.boundConstant := zero_le_one.trans h.constant_ge_one
  refine ⟨ambientJetConstant N * B ^ (N + 1) * K * h.boundConstant ^ N,
    by positivity, (m + 2) * (N + 1) + m + h.coordinate_power * N, ?_⟩
  intro n k p hp hcell j hj
  have hG := s.one_le_growth n p
  have hG0 := s.growth_nonneg n p
  have hw : 0 ≤ s.epsilon n ^ α * Real.sqrt (s.zeta p) :=
    mul_nonneg (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le (Real.sqrt_nonneg _)
  have hAj : ∀ i ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ i ((PrimaryCopyBridge.copyFrame (d n) (g n) k).coefficient harmonic)
        (p,v)‖ ≤ K * s.growth n p ^ m := by
    intro i hi v hv
    exact (hm n k p hp hcell i hi v hv).1.trans (mul_le_mul_of_nonneg_right hCK (pow_nonneg hG0 _))
  have hfj : ∀ i ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ i ((PrimaryCopyBridge.copyFrame (d n) (g n) k).forcing
        (PrimaryCopyBridge.copySource (t n).source (g n) k)) (p,v)‖ ≤
        (s.epsilon n ^ α * Real.sqrt (s.zeta p)) * K * s.growth n p ^ m * envelope n v := by
    intro i hi v hv
    exact (hm n k p hp hcell i hi v hv).2.1.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCK hw) (pow_nonneg hG0 _)) (h.envelope_pos n v).le)
  have hcj : ∀ i : Fin 2, ∀ q ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ q (synthesisColumn (PrimaryCopyBridge.copyFrame (d n) (g n) k) i)
        (p,v)‖ ≤ K * s.growth n p ^ m := by
    intro i q hq v hv
    exact (hm n k p hp hcell q hq v hv).2.2 i |>.trans
      (mul_le_mul_of_nonneg_right hCK (pow_nonneg hG0 _))
  have hh := copySolve_jet_bound_from_modal (d n) (t n) harmonic (g n) k (hL n) hG hK
    (h.errorRate_nonneg n) hw
    ((h.length_bound n).trans (mul_le_mul hK₀K (s.slow_le_growth n p)
      (zero_le_one.trans (s.one_le_slow n)) (zero_le_one.trans hK)))
    ((h.exponential_bound n).trans hK₀K) (h.neighborhood n k) (h.interval n)
    (h.open_neighborhood n k) (h.open_interval n) (h.contains_interval n) (h.bridge n k)
    (h.coefficient_smooth n k) (h.forcing_smooth n k) (h.columns_smooth n k)
    (envelope n) (h.rate n) (h.envelope_pos n) (h.envelope_deriv n) (h.contains n k p hp hcell)
    (h.current_slot n k p (h.contains n k p hp hcell)) (h.energy n k p hp hcell)
    m N hAj hfj hcj j hj
  have hcg : CommonCoverClass.argumentCost (g n) ≤ h.boundConstant * s.growth n p ^
    h.coordinate_power :=
    (h.coordinate_bound n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n p) _)
      (zero_le_one.trans h.constant_ge_one))
  have hcp : CommonCoverClass.argumentCost (g n) ^ j ≤
      h.boundConstant ^ N * s.growth n p ^ (h.coordinate_power * N) := by
    calc
      _ ≤ (h.boundConstant * s.growth n p ^ h.coordinate_power) ^ j := pow_le_pow_left₀
        (zero_le_one.trans (CommonCoverClass.one_le_argumentCost (g n))) hcg j
      _ ≤ (h.boundConstant * s.growth n p ^ h.coordinate_power) ^ N := pow_le_pow_right₀
        (one_le_mul_of_one_le_of_one_le h.constant_ge_one (one_le_pow₀ hG)) hj
      _ = _ := by rw [mul_pow, pow_mul]
  apply hh.trans
  have hen := (h.envelope_pos n ((g n).coordinates k p.2).2).le
  calc
    _ ≤ ambientJetConstant N *
        ((s.epsilon n ^ α * Real.sqrt (s.zeta p)) * B ^ (N + 1) *
          s.growth n p ^ ((m + 2) * (N + 1)) * envelope n ((g n).coordinates k p.2).2) *
        (K * s.growth n p ^ m) * (h.boundConstant ^ N * s.growth n p ^ (h.coordinate_power * N)) :=
          by
      apply mul_le_mul_of_nonneg_left hcp
      exact mul_nonneg (mul_nonneg hconst (by positivity)) (by positivity)
    _ ≤ ambientJetConstant N *
        ((s.epsilon n ^ α * Real.sqrt (s.zeta p)) * B ^ (N + 1) *
          s.growth n p ^ ((m + 2) * (N + 1)) * W n p) *
        (K * s.growth n p ^ m) * (h.boundConstant ^ N * s.growth n p ^ (h.coordinate_power * N)) :=
          by
      gcongr
      exact hW n k p hp hcell
    _ = _ := by unfold majorant; simp only [pow_add]; ring

end ModalControl

section Pressure

open SignedCopyBounds

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {cells : ℕ → I → Set D} {w : ℕ → D → ℝ} {α : ℝ}
  {normal normalDot velocity forcing : ℕ → I → D → ProblemStatement.Space}
  {action : ℕ → I → D → ProblemStatement.Space →L[ℝ] ProblemStatement.Space}

/-- The actual forcing contributes its normal projection to pressure. -/
theorem forced_pressureCoefficient
    (hN : LocalJets s (fun _ _ => 1) 0 cells normal)
    (hNd : LocalJets s (fun _ _ => 1) 0 cells normalDot)
    (hA : LocalJets s (fun _ _ => 1) 0 cells action)
    (hu : LocalJets s w α cells velocity) (hf : LocalJets s w α cells forcing)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n k x, x ∈ s.domain → x ∈ cells n k → b ≤ ‖normal n k x‖)
    (hh : ∀ n k x, x ∈ s.domain → x ∈ cells n k → ‖normal n k x‖ ≤ M) :
    LocalJets s w α cells (fun n k x => TangentProjection.pressureCoefficient
      (normal n k x) (normalDot n k x) (velocity n k x)
      (action n k x (velocity n k x)) (forcing n k x)) := by
  have hAu : LocalJets s w α cells (fun n k x => action n k x (velocity n k x)) := by
    have he := hA.bilinear hu (ContinuousLinearMap.apply ℝ ProblemStatement.Space).flip
        (fun _ _ _ => zero_le_one) hw
    simp only [one_mul, zero_add] at he
    exact he
  have hnum := (local_sub (local_inner hN hAu hw) (local_inner hNd hu hw) hw).add
    (local_inner hN hf hw) hw
  have hp := local_coeff_mul (local_normalInverse hN hb hl hh) hnum hw
  simpa only [TangentProjection.pressureCoefficient, real_inner_self_eq_norm_sq,
    div_eq_mul_inv, mul_comm] using hp

theorem forced_projectedPressure
    (hN : LocalJets s (fun _ _ => 1) 0 cells normal)
    (hNd : LocalJets s (fun _ _ => 1) 0 cells normalDot)
    (hA : LocalJets s (fun _ _ => 1) 0 cells action)
    (hu : LocalJets s w α cells velocity) (hf : LocalJets s w α cells forcing)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n k x, x ∈ s.domain → x ∈ cells n k → b ≤ ‖normal n k x‖)
    (hh : ∀ n k x, x ∈ s.domain → x ∈ cells n k → ‖normal n k x‖ ≤ M)
    {frequency : ℕ → ℝ} (hfrequency : BandBound s (1/2) (fun n => 1 / frequency n)) :
    LocalJets s w (α+1/2) cells (fun n k => projectedPressure (frequency n)
      (normal n k) (normalDot n k) (velocity n k) (fun x => action n k x (velocity n k x))
      (forcing n k)) := by
  have hp := (forced_pressureCoefficient hN hNd hA hu hf hw hb hl hh).map
    (Complex.I • Complex.ofRealCLM)
  have hp' := local_band_smul hp hfrequency hw
  apply local_of_eq hp'
  intro n k x
  simp only [projectedPressure, _root_.smul_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, Complex.real_smul,
    div_eq_mul_inv, mul_comm, mul_one, Complex.ofReal_inv]

end Pressure

section ActualComplex

open HarmonicCalculus LinearWaveBounds

variable {s : StripData (P × Plane)} {α : ℝ}
  (base : WaveCoefficients (P × Plane))
  (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
  (g : ℕ → Geometry) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
  (envelope : ℕ → ℝ → ℝ) (W : ℕ → P × Plane → ℝ)
  (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
  (cells : ℕ → Frequency → Set (P × Plane))

/-- Native bounds for the literal complex particular velocity and its
forced pressure, with constants preceding every copy selector. -/
theorem coefficients_jets
    (hr : ModalControl s α d (fun n => realData (t n) (source n)) harmonic g L envelope cells)
    (hi : ModalControl s α d (fun n => imagData (t n) (source n)) harmonic g L envelope cells)
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hcompare : ∀ n k x, x ∈ s.domain → x ∈ cells n k →
      envelope n ((g n).coordinates k x.2).2 ≤ W n x)
    (hN : LocalJets s (fun _ _ => 1) 0 cells
      (fun n k x => (t n).normal (nativePoint (g n) k x)))
    (hNd : LocalJets s (fun _ _ => 1) 0 cells
      (fun n k x => (t n).normalDot (nativePoint (g n) k x)))
    (hA : LocalJets s (fun _ _ => 1) 0 cells
      (fun n k x => (t n).action (nativePoint (g n) k x)))
    (hf : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α cells (fun n _ => source n))
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n k x, x ∈ s.domain → x ∈ cells n k → b ≤ ‖(t n).normal (nativePoint (g n) k x)‖)
    (hh : ∀ n k x, x ∈ s.domain → x ∈ cells n k → ‖(t n).normal (nativePoint (g n) k x)‖ ≤ M)
    (hfrequency : BandBound s (1/2) (fun n => 1 / base.frequency n)) :
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α cells
      (fun n k => (complexCopyCoefficients base t source g (fun _ => k) L hL).amplitude n) ∧
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (α+1/2) cells
      (fun n k => (complexCopyCoefficients base t source g (fun _ => k) L hL).pressure n) := by
  have hweight n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hW n x hx)
  have hur := hr.localJets hL W hcompare
  have hui := hi.localJets hL W hcompare
  have hva := (hur.map CurlClassBounds.complexify).add
    ((hui.map CurlClassBounds.complexify).map (complexScale Complex.I)) hweight
  refine ⟨hva, ?_⟩
  have hpr := forced_projectedPressure hN hNd hA hur (hf.map realPart) hweight hb hl hh hfrequency
  have hpi := forced_projectedPressure hN hNd hA hui (hf.map imagPart) hweight hb hl hh hfrequency
  exact hpr.add (hpi.map ((ContinuousLinearMap.mul ℝ ℂ) Complex.I)) hweight

/-- The common cutoff is applied once, before the periodized sum and the
exact curl. These are the native hypotheses of `common_bounds_from_native`. -/
theorem coefficients_localized_jets
    (hr : ModalControl s α d (fun n => realData (t n) (source n)) harmonic g L envelope cells)
    (hi : ModalControl s α d (fun n => imagData (t n) (source n)) harmonic g L envelope cells)
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hcompare : ∀ n k x, x ∈ s.domain → x ∈ cells n k →
      envelope n ((g n).coordinates k x.2).2 ≤ W n x)
    (hN : LocalJets s (fun _ _ => 1) 0 cells
      (fun n k x => (t n).normal (nativePoint (g n) k x)))
    (hNd : LocalJets s (fun _ _ => 1) 0 cells
      (fun n k x => (t n).normalDot (nativePoint (g n) k x)))
    (hA : LocalJets s (fun _ _ => 1) 0 cells
      (fun n k x => (t n).action (nativePoint (g n) k x)))
    (hf : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α cells (fun n _ => source n))
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n k x, x ∈ s.domain → x ∈ cells n k → b ≤ ‖(t n).normal (nativePoint (g n) k x)‖)
    (hh : ∀ n k x, x ∈ s.domain → x ∈ cells n k → ‖(t n).normal (nativePoint (g n) k x)‖ ≤ M)
    (hfrequency : BandBound s (1/2) (fun n => 1 / base.frequency n))
    (cutoff : Frequency → ℕ → P × Plane → ℝ)
    (hcutoff : LocalJets s (fun _ _ => 1) 0 cells (fun n k => cutoff k n)) :
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α cells
      (fun n k => ((complexCopyCoefficients base t source g (fun _ => k) L hL).withCutoff (cutoff
        k)).amplitude n) ∧
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (α+1/2) cells
      (fun n k => ((complexCopyCoefficients base t source g (fun _ => k) L hL).withCutoff (cutoff
        k)).pressure n) := by
  obtain ⟨ha, hp⟩ := coefficients_jets base t source g L hL envelope W d harmonic cells
    hr hi hW hcompare hN hNd hA hf hb hl hh hfrequency
  have hw n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hW n x hx)
  refine ⟨hcutoff.smul ha hw, ?_⟩
  simpa only [WaveCoefficients.withCutoff, Complex.real_smul] using hcutoff.smul hp hw

end ActualComplex

section NativeEnvelope

/-- The reference envelope of the unique active native copy.  This
majorant need not be smooth; the actual fields carry the smoothness. -/
noncomputable def nativeEnvelope (K : Cells (P × Plane) Frequency)
    (g : ℕ → Geometry) (envelope : ℕ → ℝ → ℝ) (n : ℕ) (x : P × Plane) : ℝ := by
  classical
  exact if h : ∃ k, x ∈ K.carrier n k then
    envelope n ((g n).coordinates (Classical.choose h) x.2).2 else 0

omit [NormedSpace ℝ P] in
theorem nativeEnvelope_eq (K : Cells (P × Plane) Frequency)
    (g : ℕ → Geometry) (envelope : ℕ → ℝ → ℝ) {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ K.carrier n k) :
    nativeEnvelope K g envelope n x = envelope n ((g n).coordinates k x.2).2 := by
  classical
  let hex : ∃ j : Frequency, x ∈ K.carrier n j := ⟨k,hx⟩
  unfold nativeEnvelope
  rw [dite_eq_left hex]
  have hchoose : Classical.choose hex = k :=
    K.unique n (Classical.choose hex) k x (Classical.choose_spec hex) hx
  rw [hchoose]

omit [NormedSpace ℝ P] in
theorem nativeEnvelope_nonneg (K : Cells (P × Plane) Frequency)
    (g : ℕ → Geometry) (envelope : ℕ → ℝ → ℝ)
    (he : ∀ n v, 0 ≤ envelope n v) (n : ℕ) (x : P × Plane) :
    0 ≤ nativeEnvelope K g envelope n x := by
  classical
  unfold nativeEnvelope
  split_ifs
  · exact he _ _
  · exact le_rfl

omit [NormedSpace ℝ P] in
theorem nativeEnvelope_le_one (K : Cells (P × Plane) Frequency)
    (g : ℕ → Geometry) (envelope : ℕ → ℝ → ℝ)
    (he : ∀ n k x, x ∈ K.carrier n k → envelope n ((g n).coordinates k x.2).2 ≤ 1)
    (n : ℕ) (x : P × Plane) : nativeEnvelope K g envelope n x ≤ 1 := by
  classical
  unfold nativeEnvelope
  split_ifs with h
  · exact he n _ x (Classical.choose_spec h)
  · norm_num

end NativeEnvelope

section UniformLabels

variable {Label : Type}

/-- All primitive constants are chosen before the external spatial label
as well as the band and native lattice copy. -/
structure UniformModalControl (s : StripData (P × Plane)) (α : ℝ)
    (d : Label → ℕ → PrimaryODE.FrameData (P × ℝ))
    (t : Label → ℕ → TangentData P ProblemStatement.Space)
    (harmonic : ℤ) (g : Label → ℕ → Geometry) (L : Label → ℕ → ℝ)
    (envelope : Label → ℕ → ℝ → ℝ) (cells : Label → ℕ → Frequency → Set (P × Plane)) where
  neighborhood : Label → ℕ → Frequency → Set (P × Plane)
  open_neighborhood : ∀ l n k, IsOpen (neighborhood l n k)
  contains : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k → x ∈ neighborhood l n k
  interval : Label → ℕ → Set ℝ
  open_interval : ∀ l n, IsOpen (interval l n)
  length_pos : ∀ l n, 0 < L l n
  contains_interval : ∀ l n, Icc 0 (L l n) ⊆ interval l n
  bridge : ∀ l n k, PrimaryCopyBridge.Inputs (d l n) (t l n) harmonic (g l n) k
    (neighborhood l n k) 0 (L l n)
  coefficient_smooth : ∀ l n k, ContDiffOn ℝ ∞
    ((PrimaryCopyBridge.copyFrame (d l n) (g l n) k).coefficient harmonic)
      (neighborhood l n k ×ˢ interval l n)
  forcing_smooth : ∀ l n k, ContDiffOn ℝ ∞
    ((PrimaryCopyBridge.copyFrame (d l n) (g l n) k).forcing
      (PrimaryCopyBridge.copySource (t l n).source (g l n) k)) (neighborhood l n k ×ˢ interval l n)
  columns_smooth : ∀ l n k (i : Fin 2), ContDiffOn ℝ ∞
    (synthesisColumn (PrimaryCopyBridge.copyFrame (d l n) (g l n) k) i)
      (neighborhood l n k ×ˢ interval l n)
  current_slot : ∀ l n k x, x ∈ neighborhood l n k → ((g l n).coordinates k x.2).2 ∈ Ioo 0 (L l n)
  rate : Label → ℕ → ℝ → ℝ
  envelope_pos : ∀ l n v, 0 < envelope l n v
  envelope_deriv : ∀ l n v, HasDerivAt (envelope l n) (rate l n v * envelope l n v) v
  errorRate : Label → ℕ → ℝ
  errorRate_nonneg : ∀ l n, 0 ≤ errorRate l n
  boundConstant : ℝ
  constant_ge_one : 1 ≤ boundConstant
  coordinate_power : ℕ
  length_bound : ∀ l n, L l n ≤ boundConstant * s.slow n
  exponential_bound : ∀ l n, Real.exp (errorRate l n * L l n) ≤ boundConstant
  coordinate_bound : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ boundConstant * s.slow n ^
    coordinate_power
  energy : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k → ∀ v ∈ Icc 0 (L l n), ∀ z : PrimaryODE.State,
    ⟪z, (PrimaryCopyBridge.copyFrame (d l n) (g l n) k).coefficient harmonic (x,v) z⟫_ℝ ≤
      (rate l n v + errorRate l n) * ‖z‖^2
  input_jets : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ,
    ∀ l n k x, x ∈ s.domain → x ∈ cells l n k → ∀ j ≤ N, ∀ v ∈ Icc 0 (L l n),
      ‖iteratedFDeriv ℝ j ((PrimaryCopyBridge.copyFrame (d l n) (g l n) k).coefficient harmonic)
        (x,v)‖ ≤
        C * s.growth n x ^ m ∧
      ‖iteratedFDeriv ℝ j ((PrimaryCopyBridge.copyFrame (d l n) (g l n) k).forcing
        (PrimaryCopyBridge.copySource (t l n).source (g l n) k)) (x,v)‖ ≤
        (s.epsilon n ^ α * Real.sqrt (s.zeta x)) * C * s.growth n x ^ m * envelope l n v ∧
      ∀ i : Fin 2, ‖iteratedFDeriv ℝ j
        (synthesisColumn (PrimaryCopyBridge.copyFrame (d l n) (g l n) k) i) (x,v)‖ ≤ C * s.growth n
          x ^ m

namespace UniformModalControl

variable {s : StripData (P × Plane)} {α : ℝ}
  {d : Label → ℕ → PrimaryODE.FrameData (P × ℝ)}
  {t : Label → ℕ → TangentData P ProblemStatement.Space}
  {harmonic : ℤ} {g : Label → ℕ → Geometry} {L : Label → ℕ → ℝ}
  {envelope : Label → ℕ → ℝ → ℝ} {cells : Label → ℕ → Frequency → Set (P × Plane)}

noncomputable def pull (h : UniformModalControl s α d t harmonic g L envelope cells)
    (e : ℕ → ℕ × Label) :
    ModalControl (UniformPrimaryWeights.reindexedStrip s e) α
      (fun n => d (e n).2 (e n).1) (fun n => t (e n).2 (e n).1) harmonic
      (fun n => g (e n).2 (e n).1) (fun n => L (e n).2 (e n).1)
      (fun n => envelope (e n).2 (e n).1) (fun n => cells (e n).2 (e n).1) where
  neighborhood n := h.neighborhood (e n).2 (e n).1
  open_neighborhood n := h.open_neighborhood (e n).2 (e n).1
  contains n := h.contains (e n).2 (e n).1
  interval n := h.interval (e n).2 (e n).1
  open_interval n := h.open_interval (e n).2 (e n).1
  length_pos n := h.length_pos (e n).2 (e n).1
  contains_interval n := h.contains_interval (e n).2 (e n).1
  bridge n := h.bridge (e n).2 (e n).1
  coefficient_smooth n := h.coefficient_smooth (e n).2 (e n).1
  forcing_smooth n := h.forcing_smooth (e n).2 (e n).1
  columns_smooth n := h.columns_smooth (e n).2 (e n).1
  current_slot n := h.current_slot (e n).2 (e n).1
  rate n := h.rate (e n).2 (e n).1
  envelope_pos n := h.envelope_pos (e n).2 (e n).1
  envelope_deriv n := h.envelope_deriv (e n).2 (e n).1
  errorRate n := h.errorRate (e n).2 (e n).1
  errorRate_nonneg n := h.errorRate_nonneg (e n).2 (e n).1
  boundConstant := h.boundConstant
  constant_ge_one := h.constant_ge_one
  coordinate_power := h.coordinate_power
  length_bound n := h.length_bound (e n).2 (e n).1
  exponential_bound n := h.exponential_bound (e n).2 (e n).1
  coordinate_bound n := h.coordinate_bound (e n).2 (e n).1
  energy n := h.energy (e n).2 (e n).1
  input_jets N := by
    obtain ⟨C, hC, m, hb⟩ := h.input_jets N
    exact ⟨C, hC, m, fun n => hb (e n).2 (e n).1⟩

theorem localJets [Countable Label] [Nonempty Label]
    (h : UniformModalControl s α d t harmonic g L envelope cells)
    (hL : ∀ l n, 0 < L l n) (W : Label → ℕ → P × Plane → ℝ)
    (hW : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k →
      envelope l n ((g l n).coordinates k x.2).2 ≤ W l n x) :
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α cells
      (fun l n k => (t l n).linearData.copySolve (g l n) (hL l n).le k) := by
  let e := UniformPrimaryWeights.enumeration Label
  apply SignedCopyBounds.uniform_local_of_pull (UniformPrimaryWeights.enumeration_surjective Label)
  exact (h.pull e).localJets (fun n => hL (e n).2 (e n).1)
    (fun n => W (e n).2 (e n).1) (fun n => hW (e n).2 (e n).1)

end UniformModalControl

noncomputable def reindexedBase {D : Type*} (base : Label → LinearWaveBounds.WaveCoefficients D)
    (e : ℕ → ℕ × Label) : LinearWaveBounds.WaveCoefficients D where
  radius n := (base (e n).2).radius (e n).1
  radialBase n := (base (e n).2).radialBase (e n).1
  frequencyBase n := (base (e n).2).frequencyBase (e n).1
  axialBase n := (base (e n).2).axialBase (e n).1
  phase n := (base (e n).2).phase (e n).1
  amplitude n := (base (e n).2).amplitude (e n).1
  pressure n := (base (e n).2).pressure (e n).1
  frequency n := (base (e n).2).frequency (e n).1

open HarmonicCalculus LinearWaveBounds SignedCopyBounds

variable [Countable Label] [Nonempty Label]
  {s : StripData (P × Plane)} {α : ℝ}
  (base : Label → WaveCoefficients (P × Plane))
  (t : Label → ℕ → TangentData P ProblemStatement.Space)
  (source : Label → ℕ → P × Plane → ComplexVector)
  (g : Label → ℕ → Geometry) (L : Label → ℕ → ℝ) (hL : ∀ l n, 0 < L l n)
  (envelope : Label → ℕ → ℝ → ℝ) (W : Label → ℕ → P × Plane → ℝ)
  (d : Label → ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
  (cells : Label → ℕ → Frequency → Set (P × Plane))

/-- Uniformity includes external countable spatial labels without
changing their envelopes or selecting separate output constants. -/
theorem uniform_coefficients_jets
    (hr : UniformModalControl s α d (fun l n => realData (t l n) (source l n)) harmonic g L
      envelope cells)
    (hi : UniformModalControl s α d (fun l n => imagData (t l n) (source l n)) harmonic g L
      envelope cells)
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hcompare : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k →
      envelope l n ((g l n).coordinates k x.2).2 ≤ W l n x)
    (hN : UniformLocalJets s (fun _ _ _ => 1) 0 cells
      (fun l n k x => (t l n).normal (nativePoint (g l n) k x)))
    (hNd : UniformLocalJets s (fun _ _ _ => 1) 0 cells
      (fun l n k x => (t l n).normalDot (nativePoint (g l n) k x)))
    (hA : UniformLocalJets s (fun _ _ _ => 1) 0 cells
      (fun l n k x => (t l n).action (nativePoint (g l n) k x)))
    (hf : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α cells (fun l n _ =>
      source l n))
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k → b ≤ ‖(t l n).normal (nativePoint (g l n) k
      x)‖)
    (hh : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k → ‖(t l n).normal (nativePoint (g l n) k x)‖ ≤
      M)
    (hfrequency : UniformPrimaryWeights.UniformBandBound s (1/2) (fun l n => 1 / (base l).frequency
      n)) :
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α cells
      (fun l n k => (complexCopyCoefficients (base l) (t l) (source l) (g l) (fun _ => k) (L l) (hL
        l)).amplitude n) ∧
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α+1/2) cells
      (fun l n k => (complexCopyCoefficients (base l) (t l) (source l) (g l) (fun _ => k) (L l) (hL
        l)).pressure n) := by
  let e := UniformPrimaryWeights.enumeration Label
  have he : Surjective e := UniformPrimaryWeights.enumeration_surjective Label
  have hboth := coefficients_jets (reindexedBase base e)
    (fun n => t (e n).2 (e n).1) (fun n => source (e n).2 (e n).1)
    (fun n => g (e n).2 (e n).1) (fun n => L (e n).2 (e n).1) (fun n => hL (e n).2 (e n).1)
    (fun n => envelope (e n).2 (e n).1) (fun n => W (e n).2 (e n).1)
    (fun n => d (e n).2 (e n).1) harmonic (fun n => cells (e n).2 (e n).1)
    (hr.pull e) (hi.pull e) (fun n => hW (e n).2 (e n).1)
    (fun n => hcompare (e n).2 (e n).1) (local_pull hN e) (local_pull hNd e) (local_pull hA e)
    (local_pull hf e) hb (fun n => hl (e n).2 (e n).1) (fun n => hh (e n).2 (e n).1)
    (UniformPrimaryWeights.pull_bandBound hfrequency e)
  exact ⟨uniform_local_of_pull he hboth.1, uniform_local_of_pull he hboth.2⟩

theorem uniform_coefficients_localized_jets
    (hr : UniformModalControl s α d (fun l n => realData (t l n) (source l n)) harmonic g L
      envelope cells)
    (hi : UniformModalControl s α d (fun l n => imagData (t l n) (source l n)) harmonic g L
      envelope cells)
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hcompare : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k →
      envelope l n ((g l n).coordinates k x.2).2 ≤ W l n x)
    (hN : UniformLocalJets s (fun _ _ _ => 1) 0 cells
      (fun l n k x => (t l n).normal (nativePoint (g l n) k x)))
    (hNd : UniformLocalJets s (fun _ _ _ => 1) 0 cells
      (fun l n k x => (t l n).normalDot (nativePoint (g l n) k x)))
    (hA : UniformLocalJets s (fun _ _ _ => 1) 0 cells
      (fun l n k x => (t l n).action (nativePoint (g l n) k x)))
    (hf : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α cells (fun l n _ =>
      source l n))
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k → b ≤ ‖(t l n).normal (nativePoint (g l n) k
      x)‖)
    (hh : ∀ l n k x, x ∈ s.domain → x ∈ cells l n k → ‖(t l n).normal (nativePoint (g l n) k x)‖ ≤
      M)
    (hfrequency : UniformPrimaryWeights.UniformBandBound s (1/2) (fun l n => 1 / (base l).frequency
      n))
    (cutoff : Label → Frequency → ℕ → P × Plane → ℝ)
    (hcutoff : UniformLocalJets s (fun _ _ _ => 1) 0 cells (fun l n k => cutoff l k n)) :
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α cells
      (fun l n k => ((complexCopyCoefficients (base l) (t l) (source l) (g l)
        (fun _ => k) (L l) (hL l)).withCutoff (cutoff l k)).amplitude n) ∧
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α+1/2) cells
      (fun l n k => ((complexCopyCoefficients (base l) (t l) (source l) (g l)
        (fun _ => k) (L l) (hL l)).withCutoff (cutoff l k)).pressure n) := by
  obtain ⟨ha, hp⟩ := uniform_coefficients_jets base t source g L hL envelope W d harmonic cells
    hr hi hW hcompare hN hNd hA hf hb hl hh hfrequency
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hW l n x hx)
  refine ⟨uniform_smul hcutoff ha hw, ?_⟩
  simpa only [WaveCoefficients.withCutoff, Complex.real_smul] using uniform_smul hcutoff hp hw

end UniformLabels

section PeriodicTranslation

open HarmonicCalculus

theorem jets_of_translate {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V} (a : E)
    (he : ∀ y, f (y+a) = g y) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m f (x+a) = iteratedFDeriv ℝ m g x := by
  rw [← iteratedFDeriv_comp_add_right]
  exact congrArg (fun f => iteratedFDeriv ℝ m f x) (funext he)

/-- Periodic translation preserves every full jet of the actual solution.
The copy index moves by the genuine common-cover index map. -/
theorem velocity_jets_deck (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (hperiodic : ∀ p, PeriodicAt source p) (k q : Frequency) (m : ℕ) (x : P × Plane) :
    iteratedFDeriv ℝ m (complexCopyVelocity t source g hab (k+coverIndex g.gap q))
      (x + (0,TorusAverages.latticePoint q)) =
      iteratedFDeriv ℝ m (complexCopyVelocity t source g hab k) x :=
  jets_of_translate (0,TorusAverages.latticePoint q)
    (fun y => by
      rcases y with ⟨p,Y⟩
      simpa only [Prod.mk_add_mk, add_zero] using
        complexCopyVelocity_deck t source g hab k q p (hperiodic p) Y) m x

theorem pressure_jets_deck (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (hperiodic : ∀ p, PeriodicAt source p) (frequency : ℝ) (k q : Frequency) (m : ℕ) (x : P ×
      Plane) :
    iteratedFDeriv ℝ m (complexCopyPressure t source g hab (k+coverIndex g.gap q) frequency)
      (x + (0,TorusAverages.latticePoint q)) =
      iteratedFDeriv ℝ m (complexCopyPressure t source g hab k frequency) x :=
  jets_of_translate (0,TorusAverages.latticePoint q)
    (fun y => by
      rcases y with ⟨p,Y⟩
      simpa only [Prod.mk_add_mk, add_zero] using
        complexCopyPressure_deck t source g hab k q frequency p (hperiodic p) Y) m x

/-- A zero-gap cover permits reduction to the zero copy. For a refined
cover the preceding deck theorem retains its actual index subgroup. -/
theorem velocity_jets_zero_copy (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) (hgap : g.gap = 0)
    {a b : ℝ} (hab : a ≤ b) (hperiodic : ∀ p, PeriodicAt source p)
    (q : Frequency) (m : ℕ) (x : P × Plane) :
    iteratedFDeriv ℝ m (complexCopyVelocity t source g hab q) (x + (0,TorusAverages.latticePoint
      q)) =
      iteratedFDeriv ℝ m (complexCopyVelocity t source g hab 0) x := by
  simpa only [coverIndex, hgap, Function.iterate_zero, id_eq, zero_add] using
    velocity_jets_deck t source g hab hperiodic 0 q m x

theorem coefficient_jets_deck (d : PrimaryODE.FrameData (P × ℝ)) (g : Geometry)
    (harmonic : ℤ) (k q : Frequency) (m : ℕ) (x : (P × Plane) × ℝ) :
    iteratedFDeriv ℝ m ((PrimaryCopyBridge.copyFrame d g (k+coverIndex g.gap q)).coefficient
      harmonic)
      (x + ((0,TorusAverages.latticePoint q),0)) =
      iteratedFDeriv ℝ m ((PrimaryCopyBridge.copyFrame d g k).coefficient harmonic) x := by
  apply jets_of_translate
  rintro ⟨⟨p,Y⟩,v⟩
  simp only [Prod.mk_add_mk, add_zero]
  change d.coefficient harmonic ((p, (g.coordinates (k+coverIndex g.gap q)
      (Y+TorusAverages.latticePoint q)).1), v) =
    d.coefficient harmonic ((p, (g.coordinates k Y).1), v)
  rw [g.coordinates_deck]

theorem source_jets_deck (source : P × Plane → ProblemStatement.Space) (g : Geometry)
    (hperiodic : ∀ p, PeriodicAt source p) (k q : Frequency) (m : ℕ) (x : (P × Plane) × ℝ) :
    iteratedFDeriv ℝ m (PrimaryCopyBridge.copySource source g (k+coverIndex g.gap q))
      (x + ((0,TorusAverages.latticePoint q),0)) =
      iteratedFDeriv ℝ m (PrimaryCopyBridge.copySource source g k) x := by
  apply jets_of_translate
  rintro ⟨⟨p,Y⟩,v⟩
  simp only [Prod.mk_add_mk, add_zero]
  change source (p, g.path (k+coverIndex g.gap q) (Y+TorusAverages.latticePoint q) v) =
    source (p, g.path k Y v)
  rw [g.path_deck, hperiodic]

theorem synthesis_jets_deck (d : PrimaryODE.FrameData (P × ℝ)) (g : Geometry)
    (i : Fin 2) (k q : Frequency) (m : ℕ) (x : (P × Plane) × ℝ) :
    iteratedFDeriv ℝ m (synthesisColumn (PrimaryCopyBridge.copyFrame d g (k+coverIndex g.gap q)) i)
      (x + ((0,TorusAverages.latticePoint q),0)) =
      iteratedFDeriv ℝ m (synthesisColumn (PrimaryCopyBridge.copyFrame d g k) i) x := by
  apply jets_of_translate
  rintro ⟨⟨p,Y⟩,v⟩
  simp only [Prod.mk_add_mk, add_zero]
  change synthesisColumn d i ((p, (g.coordinates (k+coverIndex g.gap q)
      (Y+TorusAverages.latticePoint q)).1), v) =
    synthesisColumn d i ((p, (g.coordinates k Y).1), v)
  rw [g.coordinates_deck]

theorem forcing_jets_deck (d : PrimaryODE.FrameData (P × ℝ))
    (source : P × Plane → ProblemStatement.Space) (g : Geometry)
    (hperiodic : ∀ p, PeriodicAt source p) (k q : Frequency) (m : ℕ) (x : (P × Plane) × ℝ) :
    iteratedFDeriv ℝ m ((PrimaryCopyBridge.copyFrame d g (k+coverIndex g.gap q)).forcing
      (PrimaryCopyBridge.copySource source g (k+coverIndex g.gap q)))
      (x + ((0,TorusAverages.latticePoint q),0)) =
      iteratedFDeriv ℝ m ((PrimaryCopyBridge.copyFrame d g k).forcing
        (PrimaryCopyBridge.copySource source g k)) x := by
  apply jets_of_translate
  rintro ⟨⟨p,Y⟩,v⟩
  simp only [Prod.mk_add_mk, add_zero]
  change frameForcingLinear d ((p, (g.coordinates (k+coverIndex g.gap q)
      (Y+TorusAverages.latticePoint q)).1), v)
      (source (p, g.path (k+coverIndex g.gap q) (Y+TorusAverages.latticePoint q) v)) =
    frameForcingLinear d ((p, (g.coordinates k Y).1), v) (source (p, g.path k Y v))
  rw [g.coordinates_deck, g.path_deck, hperiodic]

end PeriodicTranslation

end NavierStokes.ParticularCopyBounds

end
