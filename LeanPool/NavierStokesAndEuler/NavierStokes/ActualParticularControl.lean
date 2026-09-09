/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveEnvelopeTransport
public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledTangentTransport

@[expose] public section

/-!
# Modal inputs for the actual residual inverse

The frame is the selected `PhaseConstruction.frame`.  Its modal energy
estimate is derived from `FrameData.energy_bound`, including every nonzero
harmonic.  The source is differentiated along the genuine shifted copy path;
geometric separation identifies its grouped Gaussian at every integration
time.  All finite-jet constants precede the external label and lattice copy.
-/

noncomputable section

namespace NavierStokes.ActualParticularControl

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds
open CommonCoverSolve TorusInverse ParticularWaveBounds LabelSumBounds
open scoped Topology ContDiff InnerProductSpace BigOperators

abbrev Plane := TorusInverse.Plane


private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

section SelectedFrame

variable {ι : Type*} {D : PhaseJetBounds.Domain ι PhaseCalculus.Slow}

/-- Actual frame jets, directly from the base and phase data of the selected
construction.  No regularity of a solved amplitude is an input. -/
theorem selected_frame_jets (F : PhaseConstruction D) :
    FrameJets (D.slot F.V F.openV) F.frame :=
  F.phase.frameData_jets_of_phase_comparison D F.V F.openV
    F.lam F.c0 F.u F.L F.viscosity F.B F.K F.slope F.error
    F.baseF F.baseG F.r_pos F.b_pos F.one_le_M F.constants F.epsilon_ne
    F.radius F.slot F.lam_bound F.c0_bound F.u_bound F.rate_bound F.viscosity_bound
    F.B_bound F.K_unit F.slope_bound F.error_small F.normal_close

/-- The extra `j²` damping is dissipative.  The same Gaussian rate and
error constant work for all nonzero harmonics, without a bound on `j`. -/
theorem selected_energy (F : PhaseConstruction D) (i : ι)
    {p : PhaseCalculus.Slow} (hp : p ∈ D.carrier i) {v : ℝ}
    (hv : v ∈ Icc 0 (F.L i)) {j : ℤ} (hj : j ≠ 0) (z : PrimaryODE.State) :
    ⟪z, (F.frame i).coefficient j (p,v) z⟫_ℝ ≤
      (GaussianEnvelope.referenceRate (F.lam i) (F.u i) (F.L i) v +
        (F.E + 4 * F.C) / D.scale i) * ‖z‖^2 := by
  have hlam : 0 ≤ (F.frame i).eigenvalue (p,v) :=
    ViscousPropagator.referenceEigenvalue_nonneg (F.lam_pos i).le _ _ _
  have hvisc : 0 ≤ (F.frame i).viscosity (p,v) :=
    mul_nonneg (F.viscosity_nonneg i) (sq_nonneg _)
  exact (F.frame i).energy_bound (p,v) hj hlam hvisc
    (F.damping_error i p hp v hv) (F.modal_errors i p hp v hv) z

/-- The same selected frame satisfies its actual slot kinematics. -/
theorem selected_kinematics (F : PhaseConstruction D) (i : ι)
    {p : PhaseCalculus.Slow} (hp : p ∈ D.carrier i) :
    (F.frame i).Kinematics p (Icc 0 (F.L i)) := by
  have htail := (normal_range_of_reference_close F.B F.K F.slope F.error
    F.b_pos F.one_le_M F.B_bound F.K_unit F.slope_bound F.error_small F.normal_close).1
  apply PrimaryODE.FrameData.ofNormalLocal_kinematics
  · intro v _
    exact PhaseCalculus.hasDerivAt_phaseNormal_slot _ _ _ _ _ _ _ _ _ (F.epsilon_ne i)
      (((F.baseF.smooth i).contDiffAt ((D.isOpen i).mem_nhds hp)).differentiableAt (by simp))
      (((F.baseG.smooth i).contDiffAt ((D.isOpen i).mem_nhds hp)).differentiableAt (by simp))
  · intro v hv
    exact norm_pos_iff.mp (F.b_pos.trans_le (htail i (p,v) ⟨hp,F.interval i hv⟩))
  · intro v _
    exact mul_ne_zero (abs_pos.mp (F.b_pos.trans_le (F.c0_bound i).1))
      (by positivity : Real.sqrt (1 + PulseGrowth.slotMagnitude (F.u i) (F.L i) v^2) ≠ 0)
  · intro v _
    exact PrimaryODE.hasDerivAt_referenceProfile (F.c0 i) (F.u i) (F.L i) v

/-- A finite harmonic range introduces only a finite coefficient constant;
the index type may already include every spatial label and band. -/
theorem frame_coefficient_jets_bounded
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {U : PhaseJetBounds.Domain ι (Q × ℝ)} {d : ι → PrimaryODE.FrameData Q}
    (hd : FrameJets U d) (j : ι → ℤ) {J : ℝ} (hJ : 1 ≤ J)
    (hj : ∀ i, |(j i : ℝ)| ≤ J) :
    PolynomialJets U (fun i => (d i).coefficient (j i)) := by
  obtain ⟨h11, h12, h21, h22⟩ := hd.modal_errors
  have hjets : PolynomialJets U (fun i _ => (j i : ℝ)^2) :=
    PolynomialJets.const_uniform _ (one_le_pow₀ hJ) (fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hj i) 2)
  have hν := hjets.mul hd.viscosity
  have hh := (((((hd.eigenvalue.sub hν).add h11).smul
    (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 1 0 0 0))).add
      (h12.smul (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 1 0 0)))).add
        (h21.smul (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 0 1 0)))).add
          (((hd.eigenvalue.neg.sub hν).add h22).smul
            (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 0 0 1)))
  apply hh.congr
  intro i z _
  ext w k
  fin_cases k <;> simp [PrimaryODE.FrameData.coefficient, PrimaryODE.FrameData.damping,
    GrowingMode.modalOperator]

end SelectedFrame

section Projection

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {U : PhaseJetBounds.Domain ι (Q × ℝ)} {d : ι → PrimaryODE.FrameData Q}

/-- The source projection is built from its three actual frame columns. -/
theorem frame_forcingLinear_jets (hd : FrameJets U d) :
    PolynomialJets U (fun i => frameForcingLinear (d i)) := by
  have hc (k : Fin 3) :=
    (hd.forcing (PolynomialJets.const_fixed (ProblemStatement.coordinateVector k))).clm
      (ContinuousLinearMap.smulRightL ℝ ProblemStatement.Space PrimaryODE.State
        (EuclideanSpace.proj k))
  apply ((hc 0).add (hc 1) |>.add (hc 2)).congr
  intro i z hz
  apply ContinuousLinearMap.ext
  intro f
  change f 0 • (d i).forcing (fun _ => ProblemStatement.coordinateVector 0) z +
    f 1 • (d i).forcing (fun _ => ProblemStatement.coordinateVector 1) z +
    f 2 • (d i).forcing (fun _ => ProblemStatement.coordinateVector 2) z =
    (d i).forcing (fun _ => f) z
  symm
  simpa only [Fin.sum_univ_three] using
    ParticularWaveBounds.forcing_eq_columns (d i) (fun _ => f) z

end Projection

section FrameReindex

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The transverse copy coordinate is not a slow variable of the selected
frame.  The linear map also permits forgetting the auxiliary angle. -/
noncomputable def nativeFrame (d : PrimaryODE.FrameData PhaseCalculus.Slow)
    (χ : P →L[ℝ] PhaseCalculus.Slow) : PrimaryODE.FrameData (P × ℝ) :=
  PrimaryCopyBridge.reindex d (fun q => χ q.1)

noncomputable def frameArgument (χ : P →L[ℝ] PhaseCalculus.Slow) :
    ((P × Plane) × ℝ) →L[ℝ] (PhaseCalculus.Slow × ℝ) :=
  (χ.comp ((ContinuousLinearMap.fst ℝ P Plane).comp
    (ContinuousLinearMap.fst ℝ (P × Plane) ℝ))).prod
    (ContinuousLinearMap.snd ℝ (P × Plane) ℝ)

@[simp] theorem frameArgument_apply (χ : P →L[ℝ] PhaseCalculus.Slow)
    (z : (P × Plane) × ℝ) : frameArgument χ z = (χ z.1.1,z.2) := rfl

@[simp] theorem copyFrame_coefficient (d : PrimaryODE.FrameData PhaseCalculus.Slow)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Geometry) (k : Frequency) (j : ℤ)
    (z : (P × Plane) × ℝ) :
    (PrimaryCopyBridge.copyFrame (nativeFrame d χ) g k).coefficient j z =
      d.coefficient j (frameArgument χ z) := rfl

@[simp] theorem copyFrame_synthesis (d : PrimaryODE.FrameData PhaseCalculus.Slow)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Geometry) (k : Frequency) (i : Fin 2)
    (z : (P × Plane) × ℝ) :
    synthesisColumn (PrimaryCopyBridge.copyFrame (nativeFrame d χ) g k) i z =
      synthesisColumn d i (frameArgument χ z) := rfl

@[simp] theorem copyFrame_forcingLinear (d : PrimaryODE.FrameData PhaseCalculus.Slow)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Geometry) (k : Frequency)
    (z : (P × Plane) × ℝ) :
    frameForcingLinear (PrimaryCopyBridge.copyFrame (nativeFrame d χ) g k) z =
      frameForcingLinear d (frameArgument χ z) := rfl

noncomputable def frameDomain {ι : Type*}
    (U : PhaseJetBounds.Domain ι (PhaseCalculus.Slow × ℝ))
    (χ : P →L[ℝ] PhaseCalculus.Slow) : PhaseJetBounds.Domain ι ((P × Plane) × ℝ) where
  scale := U.scale
  carrier i := frameArgument χ ⁻¹' U.carrier i
  isOpen i := (U.isOpen i).preimage (frameArgument χ).continuous
  one_le_scale := U.one_le_scale

theorem pull_frame_jets {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : PhaseJetBounds.Domain ι (PhaseCalculus.Slow × ℝ)}
    {f : ι → PhaseCalculus.Slow × ℝ → V} (hf : PolynomialJets U f)
    (χ : P →L[ℝ] PhaseCalculus.Slow) :
    PolynomialJets (frameDomain U χ) (fun i z => f i (frameArgument χ z)) := by
  simpa only [add_zero] using hf.precomp_affine (D := frameDomain U χ)
    (frameArgument χ) (fun _ => 0) (fun _ => rfl) (fun _ _ hz => by simp only [add_zero]; exact hz)

end FrameReindex

section SourcePath

variable {Label : Type*} {P V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The grouped Gaussian of this label, built from its actual copy
geometry and its full padded integration rectangle. -/
noncomputable def groupedEnvelope (g : Label → ℕ → Geometry)
    (r L : Label → ℕ → ℝ) (W : Label → ℕ → ℝ → ℝ) :
    Label → ℕ → P × Plane → ℝ :=
  fun l n x => WaveEnvelopeTransport.copyEnvelope (g l n) (r l n) (L l n) (W l n) x.2

/-- Uniform full jets of the actual shifted source.  The source class is
an input on the current residual, not on the solution or projected forcing.
The Gaussian at an earlier integration time is derived by separation. -/
theorem source_path_bounds
    (s : StripData P) (g : Label → ℕ → Geometry) (r L : Label → ℕ → ℝ)
    (W : Label → ℕ → ℝ → ℝ) (hW : ∀ l n v, 0 ≤ W l n v)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (g l n) (r l n) (L l n))
    {A : ℝ} {a : ℕ} (hA : 1 ≤ A)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ A * s.slow n^a)
    {α : ℝ} {f : Label → ℕ → P × Plane → V}
    (hf : UniformWaveClass (CommonCoverClass.sourceStrip s) (groupedEnvelope g r L W) α f)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ l n k (x : P × Plane), x.1 ∈ s.domain →
      ((g l n).coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n) →
      ∀ v ∈ Icc 0 (L l n), ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (fun z : (P × Plane) × ℝ =>
        f l n (CommonCoverClass.sourceArgument (g l n) k z)) (x,v)‖ ≤
      C * s.growth n x.1^m * (s.epsilon n^α * Real.sqrt (s.zeta x.1)) * W l n v := by
  obtain ⟨B, hB, b, hb⟩ := hf.bounds N
  refine ⟨B * A^N, by positivity, b+a*N, ?_⟩
  intro l n k x hx hξ v hv j hj
  let G := g l n
  have hmap : CommonCoverClass.sourceArgument G k (x,v) ∈
      (CommonCoverClass.sourceStrip s).domain := hx
  have hlocal : CommonCoverClass.sourceArgument G k 0 +
      CommonCoverClass.sourceLinear P G (x,v) ∈ (CommonCoverClass.sourceStrip s).domain := by
    rw [← CommonCoverClass.sourceArgument_affine]
    exact hmap
  have hjet := CommonCoverClass.norm_affine_jet_le_on
    (CommonCoverClass.sourceStrip s).isOpen_domain (hf.smooth l n)
    (CommonCoverClass.sourceLinear P G) (CommonCoverClass.sourceArgument G k 0) hlocal j
  simp_rw [← CommonCoverClass.sourceArgument_affine] at hjet
  have hs := hb l n (CommonCoverClass.sourceArgument G k (x,v)) hmap j hj
  change ‖iteratedFDeriv ℝ j (f l n) (CommonCoverClass.sourceArgument G k (x,v))‖ ≤
    B * s.epsilon n^α * s.growth n x.1^b * (Real.sqrt (s.zeta x.1) *
      WaveEnvelopeTransport.copyEnvelope G (r l n) (L l n) (W l n) (G.path k x.2 v)) at hs
  rw [WaveEnvelopeTransport.copyEnvelope_path (hsep l n) (W l n) k x.2 hξ hv] at hs
  have hG := s.one_le_growth n x.1
  have hG0 := s.growth_nonneg n x.1
  have hlin : ‖CommonCoverClass.sourceLinear P G‖ ≤ A * s.growth n x.1^a :=
    (CommonCoverClass.norm_sourceLinear_le G).trans ((hgeometry l n).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x.1) a)
        (zero_le_one.trans hA)))
  have hpow : ‖CommonCoverClass.sourceLinear P G‖^j ≤ A^N * s.growth n x.1^(a*N) := by
    rw [pow_mul, ← mul_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hlin j).trans
      (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hG)) hj)
  have hw := hW l n v
  have he := s.epsilon_pos n
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f l n) (CommonCoverClass.sourceArgument G k (x,v))‖ *
        ‖CommonCoverClass.sourceLinear P G‖^j := hjet
    _ ≤ (B * s.epsilon n^α * s.growth n x.1^b * (Real.sqrt (s.zeta x.1) * W l n v)) *
        (A^N * s.growth n x.1^(a*N)) :=
      mul_le_mul hs hpow (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SourcePath

section NativeInputs

variable {Label : Type*} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}

private theorem raise_polynomial_bound {A B S G : ℝ} {p q : ℕ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hS : 0 ≤ S) (hSG : S ≤ G)
    (hG : 1 ≤ G) (hpq : p ≤ q) : A*S^p ≤ B*G^q := by
  exact mul_le_mul hAB ((pow_le_pow_left₀ hS hSG p).trans
    (pow_le_pow_right₀ hG hpq)) (pow_nonneg hS p) (hA.trans hAB)

/-- Joint coefficient, source-projection, and synthesis bounds of the
literal copy frame.  The full source path is used at every derivative order.
No modal energy or projected forcing bound is supplied. -/
theorem frame_input_jets
    (s : StripData P) (V : (Label × ℕ) → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (d : (Label × ℕ) → PrimaryODE.FrameData PhaseCalculus.Slow)
    (L : (Label × ℕ) → ℝ) (W : Label → ℕ → ℝ → ℝ)
    (hd : FrameJets (D.slot V hV) d) (hinterval : ∀ i, Icc 0 (L i) ⊆ V i)
    (hW : ∀ l n v, 0 ≤ W l n v) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)
    (hscale : ∀ l n, D.scale (l,n) = s.slow n)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (g l n) (r l n) (L (l,n)))
    {A : ℝ} {a : ℕ} (hA : 1 ≤ A)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ A*s.slow n^a)
    (harmonic : Label → ℤ) {J : ℝ} (hJ : 1 ≤ J) (hj : ∀ l, |(harmonic l : ℝ)| ≤ J)
    {α : ℝ} {f : Label → ℕ → P × Plane → ProblemStatement.Space}
    (hf : UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope g r (fun l n => L (l,n))
        (fun l n => W l n)) α f)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ l n k (x : P × Plane), x.1 ∈ s.domain →
      χ x.1 ∈ D.carrier (l,n) →
      ((g l n).coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n) →
      ∀ j ≤ N, ∀ v ∈ Icc 0 (L (l,n)),
      ‖iteratedFDeriv ℝ j
        ((PrimaryCopyBridge.copyFrame (nativeFrame (d (l,n)) χ) (g l n) k).coefficient
          (harmonic l)) (x,v)‖ ≤ C*s.growth n x.1^m ∧
      ‖iteratedFDeriv ℝ j
        ((PrimaryCopyBridge.copyFrame (nativeFrame (d (l,n)) χ) (g l n) k).forcing
          (PrimaryCopyBridge.copySource (f l n) (g l n) k)) (x,v)‖ ≤
        (s.epsilon n^α * Real.sqrt (s.zeta x.1))*C*s.growth n x.1^m *
          W l n v ∧
      ∀ i : Fin 2, ‖iteratedFDeriv ℝ j
        (synthesisColumn (PrimaryCopyBridge.copyFrame (nativeFrame (d (l,n)) χ) (g l n) k) i)
          (x,v)‖ ≤ C*s.growth n x.1^m := by
  have hc := pull_frame_jets (frame_coefficient_jets_bounded hd
    (fun i => harmonic i.1) hJ (fun i => hj i.1)) χ
  have hp := pull_frame_jets (frame_forcingLinear_jets hd) χ
  have h0 := pull_frame_jets (synthesisColumn_polynomial hd 0) χ
  have h1 := pull_frame_jets (synthesisColumn_polynomial hd 1) χ
  obtain ⟨Cc, hCc, mc, hCcj⟩ := hc.bound N
  obtain ⟨Cp, hCp, mp, hCpj⟩ := hp.bound N
  obtain ⟨C0, hC0, m0, hC0j⟩ := h0.bound N
  obtain ⟨C1, hC1, m1, hC1j⟩ := h1.bound N
  obtain ⟨Cs, hCs, ms, hCsj⟩ := source_path_bounds s g r (fun l n => L (l,n))
    (fun l n => W l n)
    hW hsep hA hgeometry hf N
  let B := Cc + Cp + C0 + C1
  let q := mc + mp + m0 + m1
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hbc : Cc ≤ B := by dsimp [B]; linarith
  have hbp : Cp ≤ B := by dsimp [B]; linarith
  have hb0 : C0 ≤ B := by dsimp [B]; linarith
  have hb1 : C1 ≤ B := by dsimp [B]; linarith
  let C := B + 2^N * B * Cs
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
  have hprodC : 2^N * B * Cs ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, q+ms, ?_⟩
  intro l n k x hx hχ hξ j hjN v hv
  have hz : (x,v) ∈ (frameDomain (D.slot V hV) χ).carrier (l,n) :=
    ⟨hχ, hinterval (l,n) hv⟩
  have hG := s.one_le_growth n x.1
  have hG0 := s.growth_nonneg n x.1
  have hS0 : 0 ≤ D.scale (l,n) := zero_le_one.trans (D.one_le_scale _)
  have hSG : D.scale (l,n) ≤ s.growth n x.1 := by
    rw [hscale]
    exact s.slow_le_growth n x.1
  have hcj (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun z => (d (l,n)).coefficient (harmonic l) (frameArgument χ z))
        (x,v)‖ ≤ B*s.growth n x.1^q :=
    (hCcj (l,n) i hi (x,v) hz).trans (raise_polynomial_bound
      (zero_le_one.trans hCc) hbc hS0 hSG hG (by dsimp [q]; omega))
  have hpj (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun z => frameForcingLinear (d (l,n)) (frameArgument χ z))
        (x,v)‖ ≤ B*s.growth n x.1^q :=
    (hCpj (l,n) i hi (x,v) hz).trans (raise_polynomial_bound
      (zero_le_one.trans hCp) hbp hS0 hSG hG (by dsimp [q]; omega))
  have hsynth (i : Fin 2) :
      ‖iteratedFDeriv ℝ j (fun z => synthesisColumn (d (l,n)) i (frameArgument χ z))
        (x,v)‖ ≤ B*s.growth n x.1^q := by
    fin_cases i
    · exact (hC0j (l,n) j hjN (x,v) hz).trans (raise_polynomial_bound
        (zero_le_one.trans hC0) hb0 hS0 hSG hG (by dsimp [q]; omega))
    · exact (hC1j (l,n) j hjN (x,v) hz).trans (raise_polynomial_bound
        (zero_le_one.trans hC1) hb1 hS0 hSG hG (by dsimp [q]; omega))
  have hra : B*s.growth n x.1^q ≤ C*s.growth n x.1^(q+ms) :=
    raise_polynomial_bound hB hBC hG0 le_rfl hG (Nat.le_add_right _ _)
  refine ⟨(hcj j hjN).trans hra, ?_, fun i => (hsynth i).trans hra⟩
  let U := (frameDomain (D.slot V hV) χ).carrier (l,n) ∩
    {z : (P × Plane) × ℝ | z.1.1 ∈ s.domain}
  have hU : IsOpen U := (frameDomain (D.slot V hV) χ).isOpen (l,n) |>.inter
    (s.isOpen_domain.preimage (continuous_fst.comp continuous_fst))
  have hxs : (x,v) ∈ U := ⟨hz,hx⟩
  have hpSmooth := (hp.smooth (l,n)).mono (inter_subset_left : U ⊆ _)
  have hsSmooth : ContDiffOn ℝ ∞
      (fun z : (P × Plane) × ℝ => f l n (CommonCoverClass.sourceArgument (g l n) k z)) U :=
    (hf.smooth l n).comp (CommonCoverClass.sourceArgument_smooth (g l n) k).contDiffOn
      (fun z hz => hz.2)
  have hweight : 0 ≤ s.epsilon n^α * Real.sqrt (s.zeta x.1) :=
    mul_nonneg (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le (Real.sqrt_nonneg _)
  have hen : 0 ≤ W l n v :=
    hW l n v
  have ht := WaveEnvelopeTransport.clm_apply_jet_bound_on hU hpSmooth hsSmooth hxs N
    (show 0 ≤ B*s.growth n x.1^q by positivity)
    (show 0 ≤ Cs*s.growth n x.1^ms*(s.epsilon n^α*Real.sqrt (s.zeta x.1))*
      W l n v by positivity)
    hpj (fun i hi => hCsj l n k x hx hξ v hv i hi) j hjN
  change ‖iteratedFDeriv ℝ j
    ((PrimaryCopyBridge.copyFrame (nativeFrame (d (l,n)) χ) (g l n) k).forcing
      (PrimaryCopyBridge.copySource (f l n) (g l n) k)) (x,v)‖ ≤ _ at ht
  calc
    _ ≤ 2^N*(B*s.growth n x.1^q)*(Cs*s.growth n x.1^ms*
        (s.epsilon n^α*Real.sqrt (s.zeta x.1))*
          W l n v) := ht
    _ = (s.epsilon n^α*Real.sqrt (s.zeta x.1))*(2^N*B*Cs)*s.growth n x.1^(q+ms)*
        W l n v := by rw [pow_add]; ring
    _ ≤ _ := by gcongr

/-- Instantiation of the input bound for the selected actual phase. -/
theorem selected_input_jets
    (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)
    (hscale : ∀ l n, D.scale (l,n) = s.slow n)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (g l n) (r l n) (F.L (l,n)))
    {A : ℝ} {a : ℕ} (hA : 1 ≤ A)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ A*s.slow n^a)
    (harmonic : Label → ℤ) {J : ℝ} (hJ : 1 ≤ J) (hj : ∀ l, |(harmonic l : ℝ)| ≤ J)
    {α : ℝ} {f : Label → ℕ → P × Plane → ProblemStatement.Space}
    (hf : UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope g r (fun l n => F.L (l,n))
        (fun l n => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)))) α f)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ l n k (x : P × Plane), x.1 ∈ s.domain →
      χ x.1 ∈ D.carrier (l,n) →
      ((g l n).coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n) →
      ∀ j ≤ N, ∀ v ∈ Icc 0 (F.L (l,n)),
      ‖iteratedFDeriv ℝ j
        ((PrimaryCopyBridge.copyFrame (nativeFrame (F.frame (l,n)) χ) (g l n) k).coefficient
          (harmonic l)) (x,v)‖ ≤ C*s.growth n x.1^m ∧
      ‖iteratedFDeriv ℝ j
        ((PrimaryCopyBridge.copyFrame (nativeFrame (F.frame (l,n)) χ) (g l n) k).forcing
          (PrimaryCopyBridge.copySource (f l n) (g l n) k)) (x,v)‖ ≤
        (s.epsilon n^α * Real.sqrt (s.zeta x.1))*C*s.growth n x.1^m *
          referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) v ∧
      ∀ i : Fin 2, ‖iteratedFDeriv ℝ j
        (synthesisColumn (PrimaryCopyBridge.copyFrame (nativeFrame (F.frame (l,n)) χ) (g l n) k) i)
          (x,v)‖ ≤ C*s.growth n x.1^m := by
  exact frame_input_jets s F.V F.openV F.frame F.L
    (fun l n => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)))
    (selected_frame_jets F) F.interval (fun _ _ _ => (referenceP_pos _ _ _ _).le)
    χ g r hscale hsep hA hgeometry harmonic hJ hj hf N

end NativeInputs

section CurrentResidual

variable {Label : Type*} {P E V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed linear pullback preserves the order of all uniform quantifiers. -/
theorem uniform_parameter_pull {s : StripData P} {w : Label → ℕ → P → ℝ}
    {α : ℝ} {f : Label → ℕ → P → V} (hf : UniformClass s w α f) (L : E →L[ℝ] P) :
    UniformClass (CommonCoverClass.parameterStrip s L)
      (fun l n x => w l n (L x)) α (fun l n x => f l n (L x)) := by
  refine ⟨fun l n x hx => hf.weight_nonneg l n (L x) hx,
    fun l n => (hf.smooth l n).comp_continuousLinearMap L, ?_⟩
  intro N
  obtain ⟨C,hC,m,hb⟩ := hf.bounds N
  refine ⟨C*(‖L‖+1)^N, by positivity, m, ?_⟩
  intro l n x hx j hj
  have ht := PhaseJetBounds.norm_jet_comp_linear s.isOpen_domain (hf.smooth l n) L hx j
  have hpow : ‖L‖^j ≤ (‖L‖+1)^N :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith) j).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg L]) hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f l n) (L x)‖*‖L‖^j := ht
    _ ≤ majorant s (w l) α C m n (L x)*(‖L‖+1)^N :=
      mul_le_mul (hb l n (L x) hx j hj) hpow (pow_nonneg (norm_nonneg _) _)
        (majorant_nonneg _ _ _ hC _ _ _ (hf.weight_nonneg l n (L x) hx))
    _ = _ := by dsimp [majorant, CommonCoverClass.parameterStrip, StripData.growth]; ring

/-- The actual three residual coefficients form one uniformly bounded
source vector.  No property of the inverse is assumed here. -/
theorem residualSource_uniform
    (s : StripData (P × Plane)) (W : Label → ℕ → P × Plane → ℝ) (α : ℝ)
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : Label → CorrectionState.HarmonicBlock (P × Plane))
    (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : Label → ℤ)
    (h : ∀ i : Fin 3, UniformWaveClass s W α (fun l n x =>
      (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).velocity n i (j l) x)) :
    UniformWaveClass s W α (fun l n =>
      ParticularWaveAssembly.residualSource c u (b l) (G l) (A l) (j l) n) := by
  have hc (i : Fin 3) := (h i).map (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i)
  apply ((hc 0).add (hc 1) |>.add (hc 2)).congr
  intro l n x hx
  funext i
  fin_cases i <;> simp [ParticularWaveAssembly.residualSource]

noncomputable def angleStrip (s : StripData P) : StripData (P × ℝ) :=
  CommonCoverClass.parameterStrip s (ContinuousLinearMap.fst ℝ P ℝ)

noncomputable def forgetAngle : ((P × ℝ) × Plane) →L[ℝ] (P × Plane) :=
  ((ContinuousLinearMap.fst ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ (P × ℝ) Plane)).prod
    (ContinuousLinearMap.snd ℝ (P × ℝ) Plane)

/-- The additional angular variable is genuinely absent from the current
source.  Its introduction preserves the same moving strip weight. -/
theorem sourceFamily_uniform
    (s : StripData P) (g : Label → ℕ → Geometry) (r L : Label → ℕ → ℝ)
    (W : Label → ℕ → ℝ → ℝ) (α : ℝ)
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : Label → CorrectionState.HarmonicBlock (P × Plane))
    (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : Label → ℤ)
    (h : ∀ i : Fin 3, UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope g r L W) α (fun l n x =>
        (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).velocity n i (j l) x)) :
    UniformWaveClass (CommonCoverClass.sourceStrip (angleStrip s))
      (groupedEnvelope g r L W) α (fun l =>
        ParticularWaveAssembly.sourceFamily c u (b l) (G l) (A l) (j l)) := by
  exact uniform_parameter_pull
    (residualSource_uniform (CommonCoverClass.sourceStrip s) (groupedEnvelope g r L W) α c u b G A
      j h)
    (forgetAngle (P := P))

end CurrentResidual

section FiniteHarmonics

variable {Label : Type*} {E V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem majorant_enlarge (s : StripData E) (w : ℕ → E → ℝ) (α : ℝ)
    {C B : ℝ} {p q : ℕ} (hC : 0 ≤ C) (hCB : C ≤ B) (hpq : p ≤ q)
    (n : ℕ) (x : E) (hw : 0 ≤ w n x) :
    majorant s w α C p n x ≤ majorant s w α B q n x := by
  have hp := raise_polynomial_bound hC hCB (s.growth_nonneg n x) le_rfl
    (s.one_le_growth n x) hpq
  have ht := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le hw)
  unfold majorant
  nlinarith only [ht]

/-- A stage's finite harmonic range can be folded into the external label
with one constant before both.  This never infers uniformity over an
unbounded harmonic family from separate class memberships. -/
theorem finite_harmonic_uniform
    (s : StripData E) (w : Label → ℕ → E → ℝ) (α : ℝ)
    (H : Finset ℤ) (f : ℤ → Label → ℕ → E → V)
    (hf : ∀ j ∈ H, UniformClass s w α (f j)) :
    UniformClass s (fun l : Label × {j : ℤ // j ∈ H} => w l.1) α
      (fun l => f l.2.1 l.1) := by
  have hbounds (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ,
      ∀ j ∈ H, ∀ l n x, x ∈ s.domain → ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (f j l n) x‖ ≤ majorant s (w l) α C m n x := by
    induction H using Finset.induction_on with
    | empty => exact ⟨0,le_rfl,0,by simp⟩
    | @insert j H hj ih =>
        obtain ⟨A,hA,a,ha⟩ := (hf j (Finset.mem_insert_self _ _)).bounds N
        obtain ⟨B,hB,b,hb⟩ := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
        refine ⟨A+B,add_nonneg hA hB,a+b,?_⟩
        intro k hk l n x hx i hi
        rcases Finset.mem_insert.mp hk with he | hk
        · subst k
          exact (ha l n x hx i hi).trans (majorant_enlarge s (w l) α hA
            (le_add_of_nonneg_right hB) (Nat.le_add_right _ _) n x
            ((hf j (Finset.mem_insert_self _ _)).weight_nonneg l n x hx))
        · exact (hb k hk l n x hx i hi).trans (majorant_enlarge s (w l) α hB
            (le_add_of_nonneg_left hA) (Nat.le_add_left _ _) n x
            ((hf k (Finset.mem_insert_of_mem hk)).weight_nonneg l n x hx))
  refine ⟨fun l => (hf l.2.1 l.2.2).weight_nonneg l.1,
    fun l => (hf l.2.1 l.2.2).smooth l.1, ?_⟩
  intro N
  obtain ⟨C,hC,m,hb⟩ := hbounds N
  exact ⟨C,hC,m,fun l => hb l.2.1 l.2.2 l.1⟩

end FiniteHarmonics

section ReferenceControl

variable {Label : Type} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}

private theorem frame_smooth_mono {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {d : PrimaryODE.FrameData Q} {U V : Set (Q × ℝ)} (h : d.SmoothOn U) (hVU : V ⊆ U) :
    d.SmoothOn V :=
  ⟨h.beta.mono hVU, h.betaDot.mono hVU, h.rho.mono hVU, h.rhoDot.mono hVU,
    h.rotation.mono hVU, h.F.mono hVU, h.shear.mono hVU, fun i => (h.frame i).mono hVU,
    h.eigenvalue.mono hVU, h.eigenvector.mono hVU, h.eigenRate.mono hVU,
    h.viscosity.mono hVU, fun x hx => h.eigenvector_ne_zero x (hVU hx)⟩

noncomputable def phaseNeighborhood (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Label → ℕ → Geometry)
    (l : Label) (n : ℕ) (k : Frequency) : Set (P × Plane) :=
  {x | x.1 ∈ s.domain ∧ χ x.1 ∈ D.carrier (l,n) ∧
    ((g l n).coordinates k x.2).2 ∈ Ioo 0 (F.L (l,n))}

noncomputable def phasePatch (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Label → ℕ → Geometry)
    (r : Label → ℕ → ℝ) (l : Label) (n : ℕ) (k : Frequency) : Set (P × Plane) :=
  phaseNeighborhood s F χ g l n k ∩
    {x | ((g l n).coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n)}

theorem phaseNeighborhood_open (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Label → ℕ → Geometry)
    (l : Label) (n : ℕ) (k : Frequency) :
    IsOpen (phaseNeighborhood s F χ g l n k) :=
  (s.isOpen_domain.preimage continuous_fst).inter
    (((D.isOpen (l,n)).preimage (χ.continuous.comp continuous_fst)).inter
      (isOpen_Ioo.preimage (((g l n).coordinates_contDiff k).continuous.comp continuous_snd
        |>.snd)))

/-- The output majorant is this same native Gaussian on the phase patch;
there is no replacement by an unweighted bound. -/
theorem phasePatch_envelope (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (g l n) (r l n) (F.L (l,n)))
    {l : Label} {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ phasePatch s F χ g r l n k) :
    groupedEnvelope g r (fun l n => F.L (l,n))
      (fun l n => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n))) l n x =
    referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) ((g l n).coordinates k x.2).2 :=
  WaveEnvelopeTransport.copyEnvelope_eq_copy (hsep l n) _
    ⟨hx.2,hx.1.2.2.1.le,hx.1.2.2.2.le⟩

theorem selected_copy_smooth (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Label → ℕ → Geometry)
    (l : Label) (n : ℕ) (k : Frequency) :
    (PrimaryCopyBridge.copyFrame (nativeFrame (F.frame (l,n)) χ) (g l n) k).SmoothOn
      (phaseNeighborhood s F χ g l n k ×ˢ F.V (l,n)) := by
  change (PrimaryCopyBridge.reindex (F.frame (l,n)) (fun x : P × Plane => χ x.1)).SmoothOn _
  exact PrimaryCopyBridge.reindex_smoothOn _ _ ((selected_frame_jets F).smoothOn (l,n))
    (frameArgument χ).contDiff.contDiffOn (fun z hz => ⟨hz.1.2.1,hz.2⟩)

/-- The reference/native control is assembled from the selected phase and
the current source class.  Its energy and all input jets are conclusions.
Only the geometric separation and scale comparison remain geometric inputs. -/
noncomputable def referenceControl
    (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)
    (hscale : ∀ l n, D.scale (l,n) = s.slow n)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (g l n) (r l n) (F.L (l,n)))
    {A : ℝ} {a : ℕ} (hA : 1 ≤ A)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ A*s.slow n^a)
    (j : ℤ) (hj : j ≠ 0) {α : ℝ} (f : Label → ℕ → P × Plane → ProblemStatement.Space)
    (hf : UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope g r (fun l n => F.L (l,n))
        (fun l n => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)))) α f) :
    ParticularCopyBounds.UniformModalControl (CommonCoverClass.sourceStrip s) α
      (fun l n => nativeFrame (F.frame (l,n)) χ)
      (fun l n => PrimaryCopyBridge.frameTangentData (nativeFrame (F.frame (l,n)) χ) j (f l n))
      j g (fun l n => F.L (l,n))
      (fun l n => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)))
      (phasePatch s F χ g r) := by
  let K := F.M + Real.exp ((F.E+4*F.C)*F.M) + A + 1
  have hKM : F.M ≤ K := by dsimp [K]; linarith [Real.exp_pos ((F.E+4*F.C)*F.M)]
  have hKA : A ≤ K := by dsimp [K]; linarith [F.one_le_M, Real.exp_pos ((F.E+4*F.C)*F.M)]
  have hK : 1 ≤ K := F.one_le_M.trans hKM
  have hnonneg : 0 ≤ F.E+4*F.C := by linarith [F.C_nonneg,F.E_nonneg]
  have hlength (l : Label) (n : ℕ) : F.L (l,n) ≤ F.M*D.scale (l,n) := by
    have hh := F.slot (l,n) (F.L (l,n)) (F.interval (l,n) ⟨(F.L_pos (l,n)).le,le_rfl⟩)
    simpa only [abs_of_pos (F.L_pos (l,n))] using hh
  have hsourceSmooth (l : Label) (n : ℕ) (k : Frequency) :
      ContDiffOn ℝ ∞ (PrimaryCopyBridge.copySource (f l n) (g l n) k)
        (phaseNeighborhood s F χ g l n k ×ˢ F.V (l,n)) :=
    PrimaryCopyBridge.copySource_contDiffOn (g l n) k (hf.smooth l n)
      (fun z hz => hz.1.1)
  refine {
    neighborhood := phaseNeighborhood s F χ g
    open_neighborhood := phaseNeighborhood_open s F χ g
    contains := fun _ _ _ _ _ hx => hx.1
    interval := fun l n => F.V (l,n)
    open_interval := fun l n => F.openV (l,n)
    length_pos := fun l n => F.L_pos (l,n)
    contains_interval := fun l n => F.interval (l,n)
    bridge := ?_
    coefficient_smooth := fun l n k => (selected_copy_smooth s F χ g l n k).coefficient j
    forcing_smooth := fun l n k => (selected_copy_smooth s F χ g l n k).forcing (hsourceSmooth l n
      k)
    columns_smooth := ?_
    current_slot := fun _ _ _ _ hx => hx.2.2
    rate := fun l n => GaussianEnvelope.referenceRate (F.lam (l,n)) (F.u (l,n)) (F.L (l,n))
    envelope_pos := fun _ _ _ => referenceP_pos _ _ _ _
    envelope_deriv := fun _ _ _ => referenceP_hasDerivAt _ _ _ _
    errorRate := fun l n => (F.E+4*F.C)/D.scale (l,n)
    errorRate_nonneg := fun l n => div_nonneg hnonneg (zero_le_one.trans (D.one_le_scale (l,n)))
    boundConstant := K
    constant_ge_one := hK
    coordinate_power := a
    length_bound := ?_
    exponential_bound := ?_
    coordinate_bound := fun l n => (hgeometry l n).trans
      (mul_le_mul_of_nonneg_right hKA (pow_nonneg (zero_le_one.trans (s.one_le_slow n)) _))
    energy := ?_
    input_jets := ?_ }
  · intro l n k
    apply PrimaryCopyBridge.inputs_of_smooth_frame
    · exact frame_smooth_mono (selected_copy_smooth s F χ g l n k)
        (prod_mono Subset.rfl (F.interval (l,n)))
    · exact (hsourceSmooth l n k).mono (prod_mono Subset.rfl (F.interval (l,n)))
    · intro x hx
      exact PrimaryCopyBridge.reindex_kinematics _ _ (selected_kinematics F (l,n) hx.2.1)
  · intro l n k i
    have hs := (synthesisColumn_polynomial (selected_frame_jets F) i).smooth (l,n)
    exact hs.comp (frameArgument χ).contDiff.contDiffOn (fun z hz => ⟨hz.1.2.1,hz.2⟩)
  · intro l n
    change F.L (l,n) ≤ K*s.slow n
    rw [← hscale l n]
    exact (hlength l n).trans (mul_le_mul_of_nonneg_right hKM (zero_le_one.trans (D.one_le_scale
      (l,n))))
  · intro l n
    have hS : 0 < D.scale (l,n) := zero_lt_one.trans_le (D.one_le_scale (l,n))
    have hμ : 0 ≤ (F.E+4*F.C)/D.scale (l,n) := div_nonneg hnonneg hS.le
    have he : ((F.E+4*F.C)/D.scale (l,n))*F.L (l,n) ≤ (F.E+4*F.C)*F.M := by
      calc
        _ ≤ ((F.E+4*F.C)/D.scale (l,n))*(F.M*D.scale (l,n)) :=
          mul_le_mul_of_nonneg_left (hlength l n) hμ
        _ = _ := by field_simp
    apply (Real.exp_le_exp.mpr he).trans
    dsimp [K]
    linarith [F.one_le_M]
  · intro l n k x hx hcell v hv z
    exact selected_energy F (l,n) hcell.1.2.1 hv hj z
  · intro N
    obtain ⟨C,hC,m,hb⟩ := selected_input_jets s F χ g r hscale hsep hA hgeometry
      (fun _ => j) (J := |(j : ℝ)|+1) (by linarith [abs_nonneg (j:ℝ)])
      (fun _ => by linarith) hf N
    exact ⟨C,hC,m,fun l n k x hx hcell i hi v hv =>
      hb l n k x hx hcell.1.2.1 hcell.2 i hi v hv⟩

end ReferenceControl

section ActualSourceControl

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}

/-- The actual HR-source control, with an arbitrary fixed real projection.
The two applications `part = realPart` and `part = imagPart` are the two
literal Volterra solves in `complexCopyCoefficients`. -/
noncomputable def actualSourceControl
    (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)
    (hscale : ∀ l n, D.scale (l,n) = s.slow n)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (g l n) (r l n) (F.L (l,n)))
    {K : ℝ} {a : ℕ} (hK : 1 ≤ K)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ K*s.slow n^a)
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : Label → CorrectionState.HarmonicBlock (P × Plane))
    (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (hj : j ≠ 0)
    {α : ℝ}
    (h : ∀ i : Fin 3, UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope g r (fun l n => F.L (l,n))
        (fun l n => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)))) α (fun l n x =>
        (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).velocity n i j x))
    (part : HarmonicCalculus.ComplexVector →L[ℝ] ProblemStatement.Space) :
    ParticularCopyBounds.UniformModalControl (CommonCoverClass.sourceStrip (angleStrip s)) α
      (fun l n => nativeFrame (F.frame (l,n)) (χ.comp (ContinuousLinearMap.fst ℝ P ℝ)))
      (fun l n => PrimaryCopyBridge.frameTangentData
        (nativeFrame (F.frame (l,n)) (χ.comp (ContinuousLinearMap.fst ℝ P ℝ))) j
        (fun x => part (ParticularWaveAssembly.sourceFamily c u (b l) (G l) (A l) j n x)))
      j g (fun l n => F.L (l,n))
      (fun l n => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)))
      (phasePatch (angleStrip s) F (χ.comp (ContinuousLinearMap.fst ℝ P ℝ)) g r) :=
  referenceControl (angleStrip s) F (χ.comp (ContinuousLinearMap.fst ℝ P ℝ)) g r
    hscale hsep hK hgeometry j hj _
    ((sourceFamily_uniform s g r (fun l n => F.L (l,n))
      (fun l n => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n))) α c u b G A
      (fun _ => j) h).map part)

end ActualSourceControl

section ClockTransport

variable {P Q : Type}

noncomputable def transportArgument [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] (φ : Q →L[ℝ] P) (rate : ℝ) :
    (Q × ℝ) →L[ℝ] (P × ℝ) :=
  (φ.comp (ContinuousLinearMap.fst ℝ Q ℝ)).prod (rate • ContinuousLinearMap.snd ℝ Q ℝ)

@[simp] theorem transportArgument_apply [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] (φ : Q →L[ℝ] P) (rate : ℝ) (z : Q × ℝ) :
    transportArgument φ rate z = (φ z.1,rate*z.2) := rfl

theorem norm_transportArgument_le [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] (φ : Q →L[ℝ] P) (rate : ℝ) :
    ‖transportArgument φ rate‖ ≤ ‖φ‖+|rate| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (abs_nonneg _))
  intro z
  rw [transportArgument_apply, Prod.norm_def, Real.norm_eq_abs, abs_mul]
  apply max_le
  · exact (φ.le_opNorm z.1).trans ((mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (norm_nonneg z)))
  · exact (mul_le_mul_of_nonneg_left (norm_snd_le z) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg z))

/-- Indexed affine parameter/clock changes, with a single polynomial cost
before every label.  Translation centers have no derivative cost. -/
theorem polynomial_affine_family {ι E V : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : PhaseJetBounds.Domain ι P} {T : PhaseJetBounds.Domain ι E}
    {f : ι → P → V} (hf : PolynomialJets U f)
    (L : ι → E →L[ℝ] P) (c : ι → P)
    {A B : ℝ} {a b : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hlin : ∀ i, ‖L i‖ ≤ A*T.scale i^a)
    (hscale : ∀ i, U.scale i ≤ B*T.scale i^b)
    (hmap : ∀ i, MapsTo (fun x => L i x+c i) (T.carrier i) (U.carrier i)) :
    PolynomialJets T (fun i x => f i (L i x+c i)) := by
  refine ⟨fun i => (hf.smooth i).comp ((L i).contDiff.contDiffOn.add contDiffOn_const) (hmap i), ?_⟩
  intro N
  obtain ⟨C,hC,m,hb⟩ := hf.bound N
  refine ⟨C*B^m*A^N, one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hB)) (one_le_pow₀ hA), b*m+a*N, ?_⟩
  intro i j hj x hx
  have hS := T.one_le_scale i
  have hS0 := zero_le_one.trans hS
  have hs : U.scale i^m ≤ B^m*T.scale i^(b*m) := by
    simpa only [mul_pow,pow_mul] using pow_le_pow_left₀
      (zero_le_one.trans (U.one_le_scale i)) (hscale i) m
  have hl : ‖L i‖^j ≤ A^N*T.scale i^(a*N) := by
    rw [pow_mul, ← mul_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hlin i) j).trans
      (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hS)) hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f i) (L i x+c i)‖*‖L i‖^j :=
      PhaseJetBounds.norm_jet_comp_affine (U.isOpen i) (hf.smooth i) (L i) (c i) (hmap i hx) j
    _ ≤ (C*U.scale i^m)*(A^N*T.scale i^(a*N)) := mul_le_mul
      (hb i j hj _ (hmap i hx)) hl (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans (U.one_le_scale i)) _))
    _ ≤ (C*(B^m*T.scale i^(b*m)))*(A^N*T.scale i^(a*N)) := by gcongr
    _ = _ := by rw [pow_add]; ring

/-- Transport all primitive frame fields with the same clock and normal
factors as `ScaledTangentTransport.transportTangent`. -/
noncomputable def transportedFrame (d : PrimaryODE.FrameData P) (φ : Q → P)
    (shift rate normalScale : ℝ) : PrimaryODE.FrameData Q where
  beta z := normalScale * d.beta (φ z.1,shift+rate*z.2)
  betaDot z := (normalScale*rate) * d.betaDot (φ z.1,shift+rate*z.2)
  rho z := d.rho (φ z.1,shift+rate*z.2)
  rhoDot z := rate * d.rhoDot (φ z.1,shift+rate*z.2)
  rotation z := rate * d.rotation (φ z.1,shift+rate*z.2)
  F z := rate * d.F (φ z.1,shift+rate*z.2)
  shear z := rate • d.shear (φ z.1,shift+rate*z.2)
  frame z := d.frame (φ z.1,shift+rate*z.2)
  eigenvalue z := rate * d.eigenvalue (φ z.1,shift+rate*z.2)
  eigenvector z := d.eigenvector (φ z.1,shift+rate*z.2)
  eigenRate z := rate * d.eigenRate (φ z.1,shift+rate*z.2)
  viscosity z := rate * d.viscosity (φ z.1,shift+rate*z.2)

/-- Actual primitive jets after the same affine parameter and clock
transport.  The scalar bounds precede every index; the normal multiplier
appears only in the two normal-scale fields. -/
theorem transported_frame_jets {ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {U : PhaseJetBounds.Domain ι (P × ℝ)} {T : PhaseJetBounds.Domain ι (Q × ℝ)}
    {d : ι → PrimaryODE.FrameData P} (hd : FrameJets U d)
    (φ : ι → Q →L[ℝ] P) (c : ι → P) (shift rate normalScale : ι → ℝ)
    {A B R : ℝ} {a b : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hrate : ∀ i, |rate i| ≤ R) (hnormal : ∀ i, |normalScale i| ≤ R)
    (hlin : ∀ i, ‖transportArgument (φ i) (rate i)‖ ≤ A*T.scale i^a)
    (hscale : ∀ i, U.scale i ≤ B*T.scale i^b)
    (hmap : ∀ i, MapsTo (fun z : Q × ℝ => (φ i z.1+c i,shift i+rate i*z.2))
      (T.carrier i) (U.carrier i)) :
    FrameJets T (fun i => transportedFrame (d i) (fun q => φ i q+c i)
      (shift i) (rate i) (normalScale i)) := by
  have pull {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ι → P × ℝ → E} (hf : PolynomialJets U f) :
      PolynomialJets T (fun i z => f i (φ i z.1+c i,shift i+rate i*z.2)) := by
    simpa only [transportArgument_apply, Prod.mk_add_mk, add_comm] using
      polynomial_affine_family hf (fun i => transportArgument (φ i) (rate i))
        (fun i => (c i,shift i)) hA hB hlin hscale
        (by simpa only [transportArgument_apply,Prod.mk_add_mk,add_comm] using hmap)
  have hr : PolynomialJets T (fun i _ => rate i) :=
    PolynomialJets.const_uniform rate hR (fun i => by simpa only [Real.norm_eq_abs] using hrate i)
  have hn : PolynomialJets T (fun i _ => normalScale i) :=
    PolynomialJets.const_uniform normalScale hR (fun i => by simpa only [Real.norm_eq_abs] using
      hnormal i)
  exact {
    beta := hn.mul (pull hd.beta)
    betaDot := (hn.mul hr).mul (pull hd.betaDot)
    rho := pull hd.rho
    rhoDot := hr.mul (pull hd.rhoDot)
    rotation := hr.mul (pull hd.rotation)
    F := hr.mul (pull hd.F)
    shear := hr.smul (pull hd.shear)
    K := pull hd.K
    N := pull hd.N
    invDenom := pull hd.invDenom
    eigenvalue := hr.mul (pull hd.eigenvalue)
    eigenvector := pull hd.eigenvector
    invEigenvector := pull hd.invEigenvector
    eigenRate := hr.mul (pull hd.eigenRate)
    viscosity := hr.mul (pull hd.viscosity)
    eigenvector_ne_zero := fun i z hz => hd.eigenvector_ne_zero i _ (hmap i hz) }

theorem transported_errors (d : PrimaryODE.FrameData P) (φ : Q → P)
    (shift rate normalScale : ℝ) (z : Q × ℝ) :
    (transportedFrame d φ shift rate normalScale).error11 z =
      rate*d.error11 (φ z.1,shift+rate*z.2) ∧
    (transportedFrame d φ shift rate normalScale).error12 z =
      rate*d.error12 (φ z.1,shift+rate*z.2) ∧
    (transportedFrame d φ shift rate normalScale).error21 z =
      rate*d.error21 (φ z.1,shift+rate*z.2) ∧
    (transportedFrame d φ shift rate normalScale).error22 z =
      rate*d.error22 (φ z.1,shift+rate*z.2) := by
  simp only [transportedFrame, PrimaryODE.FrameData.error11, PrimaryODE.FrameData.error12,
    PrimaryODE.FrameData.error21, PrimaryODE.FrameData.error22, PrimaryODE.FrameData.errorA,
    PrimaryODE.FrameData.errorB, PrimaryODE.FrameData.errorC,
    MovingFrameODE.modal11, MovingFrameODE.modal12, MovingFrameODE.modal21, MovingFrameODE.modal22,
    MovingFrameODE.coeff11, MovingFrameODE.coeff12, MovingFrameODE.coeff21, inner_smul_right]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem transported_coefficient (d : PrimaryODE.FrameData P) (φ : Q → P)
    (shift rate normalScale : ℝ) (j : ℤ) (z : Q × ℝ) :
    (transportedFrame d φ shift rate normalScale).coefficient j z =
      rate • d.coefficient j (φ z.1,shift+rate*z.2) := by
  obtain ⟨h11,h12,h21,h22⟩ := transported_errors d φ shift rate normalScale z
  simp only [PrimaryODE.FrameData.coefficient,h11,h12,h21,h22,PrimaryODE.FrameData.damping]
  ext x i
  fin_cases i <;>
    simp [transportedFrame, GrowingMode.modalOperator] <;> ring

theorem transported_energy {ι : Type*} {D : PhaseJetBounds.Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction D) (i : ι) (φ : Q → PhaseCalculus.Slow)
    (shift rate normalScale : ℝ) (hrate : 0 ≤ rate) {q : Q}
    (hq : φ q ∈ D.carrier i) {v : ℝ} (hv : shift+rate*v ∈ Icc 0 (F.L i))
    {j : ℤ} (hj : j ≠ 0) (z : PrimaryODE.State) :
    ⟪z, (transportedFrame (F.frame i) φ shift rate normalScale).coefficient j (q,v) z⟫_ℝ ≤
      (rate*GaussianEnvelope.referenceRate (F.lam i) (F.u i) (F.L i) (shift+rate*v) +
        rate*((F.E+4*F.C)/D.scale i))*‖z‖^2 := by
  rw [transported_coefficient, _root_.smul_apply, inner_smul_right]
  exact (mul_le_mul_of_nonneg_left (selected_energy F i hq hv hj z) hrate).trans_eq (by ring)

theorem transported_envelope_deriv (lam u L shift rate v : ℝ) :
    HasDerivAt (fun t => referenceP lam u L (shift+rate*t))
      ((rate*GaussianEnvelope.referenceRate lam u L (shift+rate*v))*
        referenceP lam u L (shift+rate*v)) v := by
  have ht : HasDerivAt (fun t : ℝ => shift+rate*t) rate v := by
    simpa using ((hasDerivAt_id v).const_mul rate).const_add shift
  simpa only [Function.comp_def, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (referenceP_hasDerivAt lam u L (shift+rate*v)).scomp v ht

/-- Clock shortening exactly compensates the rescaling of the modal error
rate.  No lower bound on the clock rate is lost inside the exponential. -/
theorem transported_exponential (rate mu L : ℝ) (hrate : rate ≠ 0) :
    Real.exp ((rate*mu)*(L/rate)) = Real.exp (mu*L) := by
  congr 1
  field_simp

@[simp] theorem transported_synthesis (d : PrimaryODE.FrameData P) (φ : Q → P)
    (shift rate normalScale : ℝ) (i : Fin 2) (z : Q × ℝ) :
    synthesisColumn (transportedFrame d φ shift rate normalScale) i z =
      synthesisColumn d i (φ z.1,shift+rate*z.2) := rfl

theorem transported_normal (d : PrimaryODE.FrameData P) (φ : Q → P)
    (shift rate normalScale : ℝ) (z : Q × ℝ) :
    (transportedFrame d φ shift rate normalScale).normal z =
      normalScale • d.normal (φ z.1,shift+rate*z.2) := by
  ext i
  fin_cases i <;>
    simp [transportedFrame, PrimaryODE.FrameData.normal, MovingFrameODE.normal,
      MovingFrameODE.pack] <;> ring

theorem transported_normalMotion (d : PrimaryODE.FrameData P) (φ : Q → P)
    (shift rate normalScale : ℝ) (z : Q × ℝ) :
    (transportedFrame d φ shift rate normalScale).normalMotion z =
      (normalScale*rate) • d.normalMotion (φ z.1,shift+rate*z.2) := by
  ext i
  fin_cases i <;>
    simp [transportedFrame, PrimaryODE.FrameData.normalMotion, MovingFrameODE.normalMotion,
      MovingFrameODE.pack] <;> ring

theorem transported_kinematics (d : PrimaryODE.FrameData P) (φ : Q → P)
    (shift rate normalScale : ℝ) (hnormal : normalScale ≠ 0)
    (q : Q) (I J : Set ℝ) (hmap : MapsTo (fun t => shift+rate*t) I J)
    (hd : d.Kinematics (φ q) J) :
    (transportedFrame d φ shift rate normalScale).Kinematics q I := by
  have ht (v : ℝ) : HasDerivAt (fun t : ℝ => shift+rate*t) rate v := by
    simpa using ((hasDerivAt_id v).const_mul rate).const_add shift
  refine ⟨fun v hv => mul_ne_zero hnormal (hd.beta_ne_zero _ (hmap hv)),
    fun v hv => hd.eigenvector_ne_zero _ (hmap hv), ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have he := ((hd.beta_deriv _ (hmap hv)).scomp v (ht v)).const_mul normalScale
    simpa only [transportedFrame,Function.comp_def,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm]
      using he
  · intro v hv
    have he := (hd.rho_deriv _ (hmap hv)).scomp v (ht v)
    simp only [transportedFrame, Function.comp_def, smul_eq_mul, mul_comm] at he ⊢
    exact he
  · intro v hv
    have he := (hd.eigenvector_deriv _ (hmap hv)).scomp v (ht v)
    simp only [transportedFrame, Function.comp_def, smul_eq_mul, mul_assoc,mul_left_comm,mul_comm]
      at he ⊢
    exact he
  · intro v hv
    have he := (hd.frameK_deriv _ (hmap hv)).scomp v (ht v)
    simp only [transportedFrame, Function.comp_def, smul_smul, mul_comm] at he ⊢
    exact he
  · intro v hv
    have he := (hd.frameN_deriv _ (hmap hv)).scomp v (ht v)
    simp only [transportedFrame, Function.comp_def, smul_smul, mul_neg, mul_comm] at he ⊢
    exact he

/-- The transformed frame is precisely the tangent transport already used
by the physical particular inverse, including its normal derivative. -/
theorem frameTangentData_transport
    (d : PrimaryODE.FrameData (P × ℝ)) (φ : Q → P)
    (f : P × Plane → ProblemStatement.Space) (j : ℤ) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) :
    PrimaryCopyBridge.frameTangentData
      (transportedFrame d (fun q : Q × ℝ => (φ q.1,q.2)) shift rate normalScale) j
      (fun z => (rate*amplitude) • f (φ z.1,coverPower gap z.2)) =
    ScaledTangentTransport.transportTangent (PrimaryCopyBridge.frameTangentData d j f)
      φ gap shift rate amplitude normalScale := by
  unfold PrimaryCopyBridge.frameTangentData ScaledTangentTransport.transportTangent
  congr 1
  · funext z
    exact transported_normal d _ shift rate normalScale (PrimaryCopyBridge.nativePoint z)
  · funext z
    exact transported_normalMotion d _ shift rate normalScale (PrimaryCopyBridge.nativePoint z)
  · funext z
    apply ContinuousLinearMap.ext
    intro x
    ext i
    fin_cases i <;>
      simp [ transportedFrame,
        PrimaryCopyBridge.baseOperator_apply, MovingFrameODE.baseAction, MovingFrameODE.pack,
        PrimaryCopyBridge.nativePoint, CopySolveCompatibility.nativeTimeMap] <;> ring
  · funext z
    simp [ transportedFrame,
      PrimaryODE.FrameData.damping, PrimaryCopyBridge.nativePoint,
        CopySolveCompatibility.nativeTimeMap]
    ring

end ClockTransport

/-- The complete integration rectangle remains separated after the actual
clock shortening and any covering refinement. -/
theorem separated_transport {g : Geometry} {r L rate : ℝ}
    (hsep : WaveEnvelopeTransport.Separated g r L) (hrate : 0 < rate) (gap : ℕ) :
    WaveEnvelopeTransport.Separated
      (CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne') r (L/rate) := by
  apply hsep.mono
  rintro Y ⟨z,hz,rfl⟩
  refine ⟨(z.1,rate*z.2), ⟨hz.1, mul_nonneg hrate.le hz.2.1, ?_⟩, ?_⟩
  · simpa only [mul_comm] using (le_div_iff₀ hrate).mp hz.2.2
  · simp [CopySolveCompatibility.transportGeometry, CopySolveCompatibility.refineGeometry,
      CopySolveCompatibility.timeGeometry, CommonCoverClass.scaledBasis_apply]

section TransportedSelectedInputs

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D T : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}

/-- The literal selected frame after the zero-entry physical clock change. -/
noncomputable def scaledSelectedFrame (F : PhaseConstruction D)
    (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)
    (rate normalScale : (Label × ℕ) → ℝ) (i : Label × ℕ) :
    PrimaryODE.FrameData PhaseCalculus.Slow :=
  transportedFrame (F.frame i) (φ i) 0 (rate i) (normalScale i)

theorem scaled_selected_copy_energy
    (F : PhaseConstruction D)
    (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)
    (rate normalScale : (Label × ℕ) → ℝ) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (g : Label → ℕ → Geometry) (l : Label) (n : ℕ) (k : Frequency)
    (hrate : 0 < rate (l,n)) (x : P × Plane)
    (hx : φ (l,n) (χ x.1) ∈ D.carrier (l,n))
    {v : ℝ} (hv : v ∈ Icc 0 (F.L (l,n)/rate (l,n))) {j : ℤ} (hj : j ≠ 0)
    (z : PrimaryODE.State) :
    ⟪z, (PrimaryCopyBridge.copyFrame (nativeFrame
        (scaledSelectedFrame F φ rate normalScale (l,n)) χ) (g l n) k).coefficient j (x,v) z⟫_ℝ ≤
      (rate (l,n)*GaussianEnvelope.referenceRate (F.lam (l,n)) (F.u (l,n))
          (F.L (l,n)) (rate (l,n)*v) +
        rate (l,n)*((F.E+4*F.C)/D.scale (l,n)))*‖z‖^2 := by
  have htime : 0+rate (l,n)*v ∈ Icc 0 (F.L (l,n)) := by
    constructor
    · simpa only [zero_add] using mul_nonneg hrate.le hv.1
    · simpa only [zero_add,mul_comm] using (le_div_iff₀ hrate).mp hv.2
  have he := transported_energy F (l,n) (φ (l,n)) 0
    (rate (l,n)) (normalScale (l,n)) hrate.le hx htime hj z
  simp only [zero_add] at he
  exact he

/-- All input jets at every target band are derived from the selected
reference phase, bounded affine clock data, and the *current* residual
source class on that target band.  Neither transported modal energies nor
transported output bounds are inputs. -/
theorem scaled_selected_input_jets
    (s : StripData P) (F : PhaseConstruction D)
    (V : (Label × ℕ) → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)
    (rate normalScale : (Label × ℕ) → ℝ)
    (χ : P →L[ℝ] PhaseCalculus.Slow)
    {A B R : ℝ} {a b : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hrateBound : ∀ i, |rate i| ≤ R) (hnormal : ∀ i, |normalScale i| ≤ R)
    (hlin : ∀ i, ‖transportArgument (φ i) (rate i)‖ ≤ A*T.scale i^a)
    (hscale : ∀ i, D.scale i ≤ B*T.scale i^b)
    (hmap : ∀ i, MapsTo (fun z : PhaseCalculus.Slow × ℝ => (φ i z.1,rate i*z.2))
      ((T.slot V hV).carrier i) ((D.slot F.V F.openV).carrier i))
    (hinterval : ∀ i, Icc 0 (F.L i/rate i) ⊆ V i)
    (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)
    (hscaleTarget : ∀ l n, T.scale (l,n) = s.slow n)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (g l n) (r l n) (F.L (l,n)/rate (l,n)))
    {C : ℝ} {c : ℕ} (hC : 1 ≤ C)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ C*s.slow n^c)
    (harmonic : Label → ℤ) {J : ℝ} (hJ : 1 ≤ J) (hj : ∀ l, |(harmonic l : ℝ)| ≤ J)
    {α : ℝ} {f : Label → ℕ → P × Plane → ProblemStatement.Space}
    (hf : UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope g r (fun l n => F.L (l,n)/rate (l,n))
        (fun l n v => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) (rate (l,n)*v))) α f)
    (N : ℕ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∃ m : ℕ, ∀ l n k (x : P × Plane), x.1 ∈ s.domain →
      χ x.1 ∈ T.carrier (l,n) →
      ((g l n).coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n) →
      ∀ j ≤ N, ∀ v ∈ Icc 0 (F.L (l,n)/rate (l,n)),
      ‖iteratedFDeriv ℝ j
        ((PrimaryCopyBridge.copyFrame (nativeFrame (scaledSelectedFrame F φ rate normalScale (l,n))
          χ)
          (g l n) k).coefficient (harmonic l)) (x,v)‖ ≤ C0*s.growth n x.1^m ∧
      ‖iteratedFDeriv ℝ j
        ((PrimaryCopyBridge.copyFrame (nativeFrame (scaledSelectedFrame F φ rate normalScale (l,n))
          χ)
          (g l n) k).forcing (PrimaryCopyBridge.copySource (f l n) (g l n) k)) (x,v)‖ ≤
        (s.epsilon n^α*Real.sqrt (s.zeta x.1))*C0*s.growth n x.1^m *
          referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) (rate (l,n)*v) ∧
      ∀ i : Fin 2, ‖iteratedFDeriv ℝ j
        (synthesisColumn (PrimaryCopyBridge.copyFrame
          (nativeFrame (scaledSelectedFrame F φ rate normalScale (l,n)) χ) (g l n) k) i)
          (x,v)‖ ≤ C0*s.growth n x.1^m := by
  have hd : FrameJets (T.slot V hV) (scaledSelectedFrame F φ rate normalScale) := by
    have he := transported_frame_jets (selected_frame_jets F) φ (fun _ => 0) (fun _ => 0)
        rate normalScale hA hB hR hrateBound hnormal hlin hscale
        (by simpa only [add_zero,zero_add] using hmap)
    simp only [add_zero] at he ⊢
    exact he
  exact frame_input_jets s V hV (scaledSelectedFrame F φ rate normalScale)
    (fun i => F.L i/rate i)
    (fun l n v => referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) (rate (l,n)*v))
    hd hinterval (fun _ _ _ => (referenceP_pos _ _ _ _).le) χ g r hscaleTarget hsep hC hgeometry
    harmonic hJ hj hf N

end TransportedSelectedInputs

end NavierStokes.ActualParticularControl
