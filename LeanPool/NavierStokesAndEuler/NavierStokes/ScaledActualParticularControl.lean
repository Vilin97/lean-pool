/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularControl
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedGeometry

/-!
# Complete controls for the scaled actual particular inverse

The clock, normal, integration interval and native geometry are transported
together.  The forcing is the current target residual, with no source
naturality assumption and no supplied modal-control record.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ScaledActualParticularControl

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds
open CommonCoverSolve TorusInverse ParticularWaveBounds LabelSumBounds
open ActualParticularControl
open scoped Topology ContDiff InnerProductSpace BigOperators

/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow


variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) Slow}

/-- Target domain, bundling `scale`, `carrier`, `isOpen`, `one_le_scale`. -/
noncomputable def targetDomain (s : StripData P)
    (φ : (Label × ℕ) → Slow →L[ℝ] Slow) : PhaseJetBounds.Domain (Label × ℕ) Slow where
  scale i := s.slow i.2
  carrier i := φ i ⁻¹' D.carrier i
  isOpen i := (D.isOpen i).preimage (φ i).continuous
  one_le_scale i := s.one_le_slow i.2

/-- Interval, given by `(fun v => clock.value i.1 i.2*v) ⁻¹' F.V i`. -/
noncomputable def interval (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale
    Label)
    (i : Label × ℕ) : Set ℝ := (fun v => clock.value i.1 i.2*v) ⁻¹' F.V i

theorem interval_open (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
    (i : Label × ℕ) : IsOpen (interval F clock i) :=
  (F.openV i).preimage (continuous_const.mul continuous_id)

/-- Length, given by `F.L (l,n)/clock.value l n`. -/
noncomputable def length (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
    (l : Label) (n : ℕ) : ℝ := F.L (l,n)/clock.value l n

theorem length_pos (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
    (l : Label) (n : ℕ) : 0 < length F clock l n :=
  div_pos (F.L_pos (l,n)) (clock.value_pos l n)

theorem clock_mem (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
    {l : Label} {n : ℕ} {v : ℝ} (hv : v ∈ Icc 0 (length F clock l n)) :
    clock.value l n*v ∈ Icc 0 (F.L (l,n)) := by
  refine ⟨mul_nonneg (clock.value_pos l n).le hv.1, ?_⟩
  simpa only [mul_comm] using (le_div_iff₀ (clock.value_pos l n)).mp hv.2

theorem interval_contains (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale
    Label)
    (i : Label × ℕ) : Icc 0 (length F clock i.1 i.2) ⊆ interval F clock i :=
  fun _ hv => F.interval i (clock_mem F clock hv)

/-- Geometry, given by `CopySolveCompatibility.transportGeometry (reference l n) (gap l n) 0
(clock.value l n) (clock.value_pos l n).ne'`. -/
noncomputable def geometry (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
    (clock : ActualSignedControl.PositiveScale Label) (l : Label) (n : ℕ) : Geometry :=
  CopySolveCompatibility.transportGeometry (reference l n) (gap l n) 0 (clock.value l n)
    (clock.value_pos l n).ne'

/-- Envelope, given by `referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) (clock.value l n*v)`. -/
noncomputable def envelope (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale
    Label)
    (l : Label) (n : ℕ) (v : ℝ) : ℝ :=
  referenceP (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) (clock.value l n*v)

/-- Frame, given by `scaledSelectedFrame F φ (fun i => clock.value i.1 i.2) (fun i =>
normal.value i.1 i.2) i`. -/
noncomputable def frame (F : PhaseConstruction D)
    (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
    (clock normal : ActualSignedControl.PositiveScale Label) (i : Label × ℕ) :
    PrimaryODE.FrameData Slow :=
  scaledSelectedFrame F φ (fun i => clock.value i.1 i.2) (fun i => normal.value i.1 i.2) i

/-- Neighborhood, given by `{x | x.1 ∈ s.domain ∧ φ (l,n) (χ x.1) ∈ D.carrier (l,n) ∧ ((g l
n).coordinates k x.2).2 ∈ Ioo 0 (length F clock l n)}`. -/
noncomputable def neighborhood (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] Slow) (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
    (clock : ActualSignedControl.PositiveScale Label) (g : Label → ℕ → Geometry)
    (l : Label) (n : ℕ) (k : Frequency) : Set (P × Plane) :=
  {x | x.1 ∈ s.domain ∧ φ (l,n) (χ x.1) ∈ D.carrier (l,n) ∧
    ((g l n).coordinates k x.2).2 ∈ Ioo 0 (length F clock l n)}

/-- Patch, given by `neighborhood s F χ φ clock g l n k ∩ {x | ((g l n).coordinates k x.2).1 ∈
Icc (-(r l n)) (r l n)}`. -/
noncomputable def patch (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] Slow) (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
    (clock : ActualSignedControl.PositiveScale Label) (g : Label → ℕ → Geometry)
    (r : Label → ℕ → ℝ) (l : Label) (n : ℕ) (k : Frequency) : Set (P × Plane) :=
  neighborhood s F χ φ clock g l n k ∩
    {x | ((g l n).coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n)}

theorem neighborhood_open (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] Slow) (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
    (clock : ActualSignedControl.PositiveScale Label) (g : Label → ℕ → Geometry)
    (l : Label) (n : ℕ) (k : Frequency) :
    IsOpen (neighborhood s F χ φ clock g l n k) :=
  (s.isOpen_domain.preimage continuous_fst).inter
    (((D.isOpen (l,n)).preimage (((φ (l,n)).comp χ).continuous.comp continuous_fst)).inter
      (isOpen_Ioo.preimage (((g l n).coordinates_contDiff k).continuous.comp continuous_snd
          |>.snd)))

private theorem frame_smooth_mono {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {d : PrimaryODE.FrameData Q} {U V : Set (Q × ℝ)} (h : d.SmoothOn U) (hVU : V ⊆ U) :
    d.SmoothOn V :=
  ⟨h.beta.mono hVU, h.betaDot.mono hVU, h.rho.mono hVU, h.rhoDot.mono hVU,
    h.rotation.mono hVU, h.F.mono hVU, h.shear.mono hVU, fun i => (h.frame i).mono hVU,
    h.eigenvalue.mono hVU, h.eigenvector.mono hVU, h.eigenRate.mono hVU,
    h.viscosity.mono hVU, fun x hx => h.eigenvector_ne_zero x (hVU hx)⟩

/-- Every frame jet follows from the selected reference phase and the
existing bounded affine/positive-scale data. -/
theorem frame_jets (s : StripData P) (F : PhaseConstruction D)
    (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
    (clock normal : ActualSignedControl.PositiveScale Label)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hφ : ∀ i, ‖φ i‖ ≤ A) (hscale : ∀ i, D.scale i ≤ B * s.slow i.2) :
    FrameJets ((targetDomain (D := D) s φ).slot (interval F clock) (interval_open F clock))
      (frame F φ clock normal) := by
  let R := max clock.upper normal.upper
  have hR : 1 ≤ R := clock.upper_one.trans (le_max_left _ _)
  have hclock (i : Label × ℕ) : |clock.value i.1 i.2| ≤ R := by
    rw [abs_of_pos (clock.value_pos i.1 i.2)]
    exact (clock.bounds i.1 i.2).2.trans (le_max_left _ _)
  have hnormal (i : Label × ℕ) : |normal.value i.1 i.2| ≤ R := by
    rw [abs_of_pos (normal.value_pos i.1 i.2)]
    exact (normal.bounds i.1 i.2).2.trans (le_max_right _ _)
  have hlin (i : Label × ℕ) :
      ‖transportArgument (φ i) (clock.value i.1 i.2)‖ ≤ (A+R)*s.slow i.2^0 := by
    simpa only [pow_zero,mul_one] using (norm_transportArgument_le _ _).trans
      (add_le_add (hφ i) (hclock i))
  have hj := transported_frame_jets (selected_frame_jets F) φ (fun _ => 0) (fun _ => 0)
      (fun i => clock.value i.1 i.2) (fun i => normal.value i.1 i.2)
      (a := 0) (b := 1)
      (T := (targetDomain (D := D) s φ).slot (interval F clock) (interval_open F clock))
      (show 1 ≤ A+R by linarith) hB hR hclock hnormal hlin
      (by simpa only [targetDomain,Domain.slot,pow_one] using hscale)
      (by intro i z hz; simp only [add_zero, zero_add]; exact ⟨hz.1, hz.2⟩)
  simp only [add_zero] at hj ⊢
  exact hj

/-- All fields of the scaled modal control are derived.  The remaining
quantitative inputs are affine/scale/rectangle facts about the chosen
geometry and the current source coefficient class. -/
noncomputable def scaledControl
    (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] Slow)
    (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
    (clock normal : ActualSignedControl.PositiveScale Label)
    (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ) (r : Label → ℕ → ℝ)
    {A B C : ℝ} {a : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hφ : ∀ i, ‖φ i‖ ≤ A) (hscale : ∀ i, D.scale i ≤ B * s.slow i.2)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (reference l n) (r l n) (F.L (l, n)))
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (geometry reference gap clock l n) ≤ C *
        s.slow
        n ^ a)
    (j : ℤ) (hj : j ≠ 0) {α : ℝ} (f : Label → ℕ → P × Plane → ProblemStatement.Space)
    (hf : UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope (geometry reference gap clock) r (length F clock) (envelope F clock)) α f) :
    ParticularCopyBounds.UniformModalControl (CommonCoverClass.sourceStrip s) α
      (fun l n => nativeFrame (frame F φ clock normal (l,n)) χ)
      (fun l n => PrimaryCopyBridge.frameTangentData (nativeFrame (frame F φ clock normal (l,n)) χ)
          j (f l n))
      j (geometry reference gap clock) (length F clock) (envelope F clock)
      (patch s F χ φ clock (geometry reference gap clock) r) := by
  let g := geometry reference gap clock
  let Lc := F.M*B/clock.lower
  let K := Lc + Real.exp ((F.E+4*F.C)*F.M) + C + 1
  have hLc : 0 ≤ Lc := div_nonneg (mul_nonneg (zero_le_one.trans F.one_le_M)
    (zero_le_one.trans hB)) clock.lower_pos.le
  have hK : 1 ≤ K := by dsimp [K]; linarith [Real.exp_pos ((F.E+4*F.C)*F.M)]
  have hCK : C ≤ K := by dsimp [K]; linarith [Real.exp_pos ((F.E+4*F.C)*F.M)]
  have hLK : Lc ≤ K := by dsimp [K]; linarith [Real.exp_pos ((F.E+4*F.C)*F.M)]
  have heK : Real.exp ((F.E+4*F.C)*F.M) ≤ K := by dsimp [K]; linarith
  have hd := frame_jets s F φ clock normal hA hB hφ hscale
  have hcopy (l : Label) (n : ℕ) (k : Frequency) :
      (PrimaryCopyBridge.copyFrame (nativeFrame (frame F φ clock normal (l,n)) χ) (g l n)
          k).SmoothOn
        (neighborhood s F χ φ clock g l n k ×ˢ interval F clock (l,n)) := by
    change (PrimaryCopyBridge.reindex (frame F φ clock normal (l,n))
      (fun x : P × Plane => χ x.1)).SmoothOn _
    exact PrimaryCopyBridge.reindex_smoothOn _ _ (hd.smoothOn (l,n))
      (frameArgument χ).contDiff.contDiffOn (fun z hz => ⟨hz.1.2.1,hz.2⟩)
  have hsource (l : Label) (n : ℕ) (k : Frequency) :
      ContDiffOn ℝ ∞ (PrimaryCopyBridge.copySource (f l n) (g l n) k)
        (neighborhood s F χ φ clock g l n k ×ˢ interval F clock (l,n)) :=
    PrimaryCopyBridge.copySource_contDiffOn (g l n) k (hf.smooth l n) (fun z hz => hz.1.1)
  have hlength (l : Label) (n : ℕ) : F.L (l,n) ≤ F.M*D.scale (l,n) := by
    simpa only [abs_of_pos (F.L_pos (l,n))] using F.slot (l,n) (F.L (l,n))
      (F.interval (l,n) ⟨(F.L_pos (l,n)).le,le_rfl⟩)
  have hsepTarget (l : Label) (n : ℕ) : WaveEnvelopeTransport.Separated (g l n) (r l n) (length F
      clock l n) :=
    separated_transport (hsep l n) (clock.value_pos l n) (gap l n)
  have herror : 0 ≤ F.E+4*F.C := by linarith [F.E_nonneg,F.C_nonneg]
  refine {
    neighborhood := neighborhood s F χ φ clock g
    open_neighborhood := neighborhood_open s F χ φ clock g
    contains := fun _ _ _ _ _ hx => hx.1
    interval := fun l n => interval F clock (l,n)
    open_interval := fun l n => interval_open F clock (l,n)
    length_pos := length_pos F clock
    contains_interval := fun l n => interval_contains F clock (l,n)
    bridge := ?_
    coefficient_smooth := fun l n k => (hcopy l n k).coefficient j
    forcing_smooth := fun l n k => (hcopy l n k).forcing (hsource l n k)
    columns_smooth := ?_
    current_slot := fun _ _ _ _ hx => hx.2.2
    rate := fun l n v => clock.value l n * GaussianEnvelope.referenceRate
      (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) (clock.value l n*v)
    envelope_pos := fun _ _ _ => referenceP_pos _ _ _ _
    envelope_deriv := ?_
    errorRate := fun l n => clock.value l n*((F.E+4*F.C)/D.scale (l,n))
    errorRate_nonneg := fun l n => mul_nonneg (clock.value_pos l n).le
      (div_nonneg herror (zero_le_one.trans (D.one_le_scale (l,n))))
    boundConstant := K
    constant_ge_one := hK
    coordinatePower := a
    length_bound := ?_
    exponential_bound := ?_
    coordinate_bound := fun l n => (hgeometry l n).trans
      (mul_le_mul_of_nonneg_right hCK (pow_nonneg (zero_le_one.trans (s.one_le_slow n)) _))
    energy := ?_
    input_jets := ?_ }
  · intro l n k
    apply PrimaryCopyBridge.inputs_of_smooth_frame
    · exact frame_smooth_mono (hcopy l n k) (prod_mono Subset.rfl (interval_contains F clock (l,n)))
    · exact (hsource l n k).mono (prod_mono Subset.rfl (interval_contains F clock (l,n)))
    · intro x hx
      apply PrimaryCopyBridge.reindex_kinematics
      apply transported_kinematics (F.frame (l,n)) (φ (l,n)) 0 (clock.value l n)
        (normal.value l n) (normal.value_pos l n).ne' (χ x.1) _ (Icc 0 (F.L (l,n)))
      · intro v hv
        simpa only [zero_add] using clock_mem F clock hv
      · exact selected_kinematics F (l,n) hx.2.1
  · intro l n k i
    exact ((synthesisColumn_polynomial hd i).smooth (l,n)).comp
      (frameArgument χ).contDiff.contDiffOn (fun z hz => ⟨hz.1.2.1,hz.2⟩)
  · intro l n v
    have he := transported_envelope_deriv
      (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) 0 (clock.value l n) v
    simp only [zero_add] at he
    exact he
  · intro l n
    change F.L (l,n)/clock.value l n ≤ K*s.slow n
    calc
      _ ≤ F.L (l,n)/clock.lower := div_le_div_of_nonneg_left (F.L_pos (l,n)).le
        clock.lower_pos (clock.bounds l n).1
      _ ≤ (F.M*(B*s.slow n))/clock.lower := div_le_div_of_nonneg_right
        ((hlength l n).trans (mul_le_mul_of_nonneg_left (hscale (l,n)) (zero_le_one.trans
            F.one_le_M)))
        clock.lower_pos.le
      _ = Lc*s.slow n := by dsimp [Lc]; ring
      _ ≤ K*s.slow n := mul_le_mul_of_nonneg_right hLK (zero_le_one.trans (s.one_le_slow n))
  · intro l n
    change Real.exp ((clock.value l n*((F.E+4*F.C)/D.scale (l,n)))*(F.L (l,n)/clock.value l n)) ≤ K
    rw [transported_exponential _ _ _ (clock.value_pos l n).ne']
    apply le_trans _ heK
    apply Real.exp_le_exp.mpr
    have hS : 0 < D.scale (l,n) := zero_lt_one.trans_le (D.one_le_scale (l,n))
    have hmu : 0 ≤ (F.E+4*F.C)/D.scale (l,n) := div_nonneg herror hS.le
    calc
      _ ≤ ((F.E+4*F.C)/D.scale (l,n))*(F.M*D.scale (l,n)) :=
        mul_le_mul_of_nonneg_left (hlength l n) hmu
      _ = _ := by field_simp
  · intro l n k x hx hcell v hv z
    exact scaled_selected_copy_energy F φ (fun i => clock.value i.1 i.2)
      (fun i => normal.value i.1 i.2) χ g l n k (clock.value_pos l n) x hcell.1.2.1 hv hj z
  · intro N
    obtain ⟨C0,hC0,m,hb⟩ := frame_input_jets s (interval F clock) (interval_open F clock)
      (frame F φ clock normal) (fun i => length F clock i.1 i.2) (envelope F clock)
      hd (interval_contains F clock) (fun _ _ _ => (referenceP_pos _ _ _ _).le)
      χ g r (fun _ _ => rfl) hsepTarget hC hgeometry (fun _ => j)
      (J := |(j : ℝ)|+1) (by linarith [abs_nonneg (j:ℝ)]) (fun _ => by linarith) hf N
    exact ⟨C0,hC0,m,fun l n k x hx hcell i hi v hv =>
      hb l n k x hx hcell.1.2.1 hcell.2 i hi v hv⟩

/-- Overwrite only the source, exactly as `realData` and `imagData` do. -/
noncomputable def withSource (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ProblemStatement.Space) : TangentData P ProblemStatement.Space :=
  { t with source := f }

/-- Normal and clock transport commute with the selected slow-coordinate
map.  The transverse coordinate remains an auxiliary parameter. -/
theorem nativeFrame_transport (d : PrimaryODE.FrameData Slow) (χ : P →L[ℝ] Slow)
    (φ : Slow →L[ℝ] Slow) (ψ : P → P) (hχ : ∀ p, χ (ψ p) = φ (χ p))
    (rate normal : ℝ) :
    transportedFrame (nativeFrame d χ) (fun q : P × ℝ => (ψ q.1,q.2)) 0 rate normal =
    nativeFrame (transportedFrame d φ 0 rate normal) χ := by
  simp only [transportedFrame,nativeFrame,PrimaryCopyBridge.reindex,hχ]

/-- The selected transported frame gives the exact angle-lifted STT
tangent after inserting the current target source.  No equality between
the current source and a transported old source is used. -/
theorem angle_transport_withSource (d : PrimaryODE.FrameData Slow) (χ : P →L[ℝ] Slow)
    (φ : Slow →L[ℝ] Slow) (ψ : P → P) (hχ : ∀ p, χ (ψ p) = φ (χ p))
    (referenceSource : P × Plane → ProblemStatement.Space)
    (targetSource : (P × ℝ) × Plane → ProblemStatement.Space)
    (j : ℤ) (gap : ℕ) (rate amplitude normal : ℝ) :
    withSource (ParticularWaveAssembly.angleTangent
      (ScaledTangentTransport.transportTangent
        (PrimaryCopyBridge.frameTangentData (nativeFrame d χ) j referenceSource)
        ψ gap 0 rate amplitude normal)) targetSource =
    PrimaryCopyBridge.frameTangentData
      (nativeFrame (transportedFrame d φ 0 rate normal) (χ.comp (ContinuousLinearMap.fst ℝ P ℝ)))
      j targetSource := by
  rw [← frameTangentData_transport (nativeFrame d χ) ψ referenceSource j gap 0 rate amplitude
      normal,
    nativeFrame_transport d χ φ ψ hχ rate normal]
  rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] theorem withSource_real (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) :
    withSource t (fun x => realPart (f x)) = realData t f := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] theorem withSource_imag (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) :
    withSource t (fun x => imagPart (f x)) = imagData t f := rfl

/-- Transported tangent, constructed using `ParticularWaveAssembly.angleTangent`. -/
noncomputable def transportedTangent
    (F : PhaseConstruction D) (χ : P →L[ℝ] Slow) (ψ : (Label × ℕ) → P → P)
    (clock normal : ActualSignedControl.PositiveScale Label)
    (referenceSource : Label → ℕ → P × Plane → ProblemStatement.Space)
    (gap : Label → ℕ → ℕ) (amplitude : Label → ℕ → ℝ) (j : ℤ)
    (l : Label) (n : ℕ) : TangentData (P × ℝ) ProblemStatement.Space :=
  ParticularWaveAssembly.angleTangent (ScaledTangentTransport.transportTangent
    (PrimaryCopyBridge.frameTangentData (nativeFrame (F.frame (l,n)) χ) j (referenceSource l n))
    (ψ (l,n)) (gap l n) 0 (clock.value l n) (amplitude l n) (normal.value l n))

/-- The full control for the literal target HR source and the exact
angle-lifted `ScaledTangentTransport` datum.  Inserting the current source
does not require it to equal a scaled old source. -/
noncomputable def actualControl
    (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] Slow)
    (φ : (Label × ℕ) → Slow →L[ℝ] Slow) (ψ : (Label × ℕ) → P → P)
    (hχ : ∀ i p, χ (ψ i p) = φ i (χ p))
    (clock normal : ActualSignedControl.PositiveScale Label)
    (reference : Label → ℕ → Geometry)
    (referenceSource : Label → ℕ → P × Plane → ProblemStatement.Space)
    (gap : Label → ℕ → ℕ) (amplitude r : Label → ℕ → ℝ)
    {A B C : ℝ} {a : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hφ : ∀ i, ‖φ i‖ ≤ A) (hscale : ∀ i, D.scale i ≤ B * s.slow i.2)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (reference l n) (r l n) (F.L (l, n)))
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (geometry reference gap clock l n) ≤ C *
        s.slow
        n ^ a)
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : Label → CorrectionState.HarmonicBlock (P × Plane))
    (G A0 : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (hj : j ≠ 0)
    {α : ℝ}
    (hsource : ∀ i : Fin 3, UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope (geometry reference gap clock) r (length F clock) (envelope F clock)) α
      (fun l n x => (HarmonicResidual.residualBlock c u (b l) (G l) (A0 l)).velocity n i j x))
    (part : HarmonicCalculus.ComplexVector →L[ℝ] ProblemStatement.Space) :
    ParticularCopyBounds.UniformModalControl (CommonCoverClass.sourceStrip (angleStrip s)) α
      (fun l n => nativeFrame (frame F φ clock normal (l,n)) (χ.comp (ContinuousLinearMap.fst ℝ P
          ℝ)))
      (fun l n => withSource (transportedTangent F χ ψ clock normal referenceSource gap amplitude j
          l n)
        (fun x => part (ParticularWaveAssembly.sourceFamily c u (b l) (G l) (A0 l) j n x)))
      j (geometry reference gap clock) (length F clock) (envelope F clock)
      (patch (angleStrip s) F (χ.comp (ContinuousLinearMap.fst ℝ P ℝ)) φ clock
        (geometry reference gap clock) r) := by
  have ht : (fun l n => withSource
      (transportedTangent F χ ψ clock normal referenceSource gap amplitude j l n)
      (fun x => part (ParticularWaveAssembly.sourceFamily c u (b l) (G l) (A0 l) j n x))) =
      (fun l n => PrimaryCopyBridge.frameTangentData
        (nativeFrame (frame F φ clock normal (l,n)) (χ.comp (ContinuousLinearMap.fst ℝ P ℝ))) j
        (fun x => part (ParticularWaveAssembly.sourceFamily c u (b l) (G l) (A0 l) j n x))) := by
    funext l n
    exact angle_transport_withSource (F.frame (l,n)) χ (φ (l,n)) (ψ (l,n)) (hχ (l,n))
      (referenceSource l n) _ j (gap l n) (clock.value l n) (amplitude l n) (normal.value l n)
  rw [ht]
  exact scaledControl (angleStrip s) F (χ.comp (ContinuousLinearMap.fst ℝ P ℝ)) φ clock normal
    reference gap r hA hB hC hφ hscale hsep hgeometry j hj _
    ((sourceFamily_uniform s (geometry reference gap clock) r (length F clock) (envelope F clock)
      α c u b G A0 (fun _ => j) hsource).map part)

/-! ## The clock change preserves the native Gaussian and polynomial geometry cost -/

theorem patch_envelope (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] Slow) (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
    (clock : ActualSignedControl.PositiveScale Label)
    (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ) (r : Label → ℕ → ℝ)
    (hsep : ∀ l n, WaveEnvelopeTransport.Separated (reference l n) (r l n) (F.L (l, n)))
    {l : Label} {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ patch s F χ φ clock (geometry reference gap clock) r l n k) :
    groupedEnvelope (geometry reference gap clock) r (length F clock) (envelope F clock) l n x =
      envelope F clock l n ((geometry reference gap clock l n).coordinates k x.2).2 :=
  WaveEnvelopeTransport.copyEnvelope_eq_copy
    (separated_transport (hsep l n) (clock.value_pos l n) (gap l n)) _
    ⟨hx.2,hx.1.2.2.1.le,hx.1.2.2.2.le⟩

theorem coordinateLinear_transport (g : Geometry) (gap : ℕ) (rate : ℝ) (hrate : rate ≠ 0) :
    (CopySolveCompatibility.transportGeometry g gap 0 rate hrate).coordinateLinear =
      ((TorusAverages.transverseChart rate hrate).symm : Plane →L[ℝ] Plane).comp
        (g.coordinateLinear.comp (coverPower gap : Plane →L[ℝ] Plane)) := by
  apply ContinuousLinearMap.ext
  intro Y
  change (TorusAverages.transverseChart rate hrate).symm
    (g.basis.symm (coverPower (g.gap+gap) Y)) =
    (TorusAverages.transverseChart rate hrate).symm
      (g.basis.symm (coverPower g.gap (coverPower gap Y)))
  rw [CopySolveCompatibility.coverPower_add]

theorem pointLinear_transport (g : Geometry) (gap : ℕ) (rate : ℝ) (hrate : rate ≠ 0) :
    (CopySolveCompatibility.transportGeometry g gap 0 rate hrate).pointLinear =
      ((coverPower gap).symm : Plane →L[ℝ] Plane).comp
        (g.pointLinear.comp (TorusAverages.transverseChart rate hrate : Plane →L[ℝ] Plane)) := by
  apply ContinuousLinearMap.ext
  intro Y
  apply (coverPower (g.gap+gap)).injective
  change coverPower (g.gap+gap) ((coverPower (g.gap+gap)).symm
      (g.basis (TorusAverages.transverseChart rate hrate Y))) =
    coverPower (g.gap+gap) ((coverPower gap).symm ((coverPower g.gap).symm
      (g.basis (TorusAverages.transverseChart rate hrate Y))))
  rw [ContinuousLinearEquiv.apply_symm_apply, CopySolveCompatibility.coverPower_add,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem norm_timeChart_le (rate : ℝ) (hrate : rate ≠ 0) :
    ‖(TorusAverages.transverseChart rate hrate : Plane →L[ℝ] Plane)‖ ≤ 1+|rate| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [ContinuousLinearEquiv.coe_coe, TorusAverages.transverseChart_apply, Prod.norm_def]
  refine max_le ((norm_fst_le z).trans ?_) ?_
  · exact le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg rate])
  · rw [norm_mul, Real.norm_eq_abs rate]
    exact mul_le_mul (by linarith [abs_nonneg rate] : |rate| ≤ 1+|rate|)
      (norm_snd_le z) (norm_nonneg _) (by positivity)

/-- Geometry factor, given by `1 + coveringBound budget * (2+clock.upper+clock.lower⁻¹)`. -/
noncomputable def geometryFactor (clock : ActualSignedControl.PositiveScale Label) (budget : ℕ) : ℝ
    :=
  1 + coveringBound budget * (2+clock.upper+clock.lower⁻¹)

theorem geometryFactor_one (clock : ActualSignedControl.PositiveScale Label) (budget : ℕ) :
    1 ≤ geometryFactor clock budget := by
  unfold geometryFactor
  have hi := inv_pos.mpr clock.lower_pos
  have hH := coveringBound_pos budget
  nlinarith [clock.upper_one]

/-- Refining the cover and scaling its time column has polynomial cost.
The constant uses only the already selected scale bounds and gap budget. -/
theorem geometry_cost (clock : ActualSignedControl.PositiveScale Label)
    (g : Geometry) {l : Label} {n gap budget : ℕ} (hgap : gap ≤ budget) :
    CommonCoverClass.argumentCost
      (CopySolveCompatibility.transportGeometry g gap 0 (clock.value l n) (clock.value_pos l
          n).ne') ≤
      4*(geometryFactor clock budget)^2*(CommonCoverClass.argumentCost g)^2 := by
  let H := coveringBound budget
  let U := geometryFactor clock budget
  let G := CopySolveCompatibility.transportGeometry g gap 0 (clock.value l n) (clock.value_pos l
      n).ne'
  have hH : 0 ≤ H := (coveringBound_pos budget).le
  have hU : 1 ≤ U := geometryFactor_one clock budget
  have hrate : |clock.value l n| ≤ clock.upper := by
    rw [abs_of_pos (clock.value_pos l n)]
    exact (clock.bounds l n).2
  have hinv : |(clock.value l n)⁻¹| ≤ clock.lower⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (clock.value_pos l n))]
    exact inv_anti₀ clock.lower_pos (clock.bounds l n).1
  have hU1 : (1+|(clock.value l n)⁻¹|)*H ≤ U := by
    dsimp [U,geometryFactor,H]
    nlinarith [clock.upper_one, coveringBound_pos budget,
      mul_nonneg (coveringBound_pos budget).le (sub_nonneg.mpr hinv)]
  have hU2 : H*(1+|clock.value l n|) ≤ U := by
    dsimp [U,geometryFactor,H]
    nlinarith [inv_pos.mpr clock.lower_pos, coveringBound_pos budget,
      mul_nonneg (coveringBound_pos budget).le (sub_nonneg.mpr hrate)]
  have hcoord : ‖G.coordinateLinear‖ ≤ U*‖g.coordinateLinear‖ := by
    dsimp [G]
    rw [coordinateLinear_transport]
    calc
      _ ≤ ‖((TorusAverages.transverseChart (clock.value l n) (clock.value_pos l n).ne').symm :
          Plane →L[ℝ] Plane)‖ * ‖g.coordinateLinear.comp (coverPower gap : Plane →L[ℝ] Plane)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1+|(clock.value l n)⁻¹|)*(‖g.coordinateLinear‖*H) :=
        mul_le_mul (CommonCoverClass.norm_inverse_transverseChart_le _ _)
          ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (coveringNorm_le_bound hgap) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
      _ = ((1+|(clock.value l n)⁻¹|)*H)*‖g.coordinateLinear‖ := by ring
      _ ≤ U*‖g.coordinateLinear‖ := mul_le_mul_of_nonneg_right hU1 (norm_nonneg _)
  have hpoint : ‖G.pointLinear‖ ≤ U*‖g.pointLinear‖ := by
    dsimp [G]
    rw [pointLinear_transport]
    calc
      _ ≤ ‖((coverPower gap).symm : Plane →L[ℝ] Plane)‖ *
          ‖g.pointLinear.comp (TorusAverages.transverseChart (clock.value l n) (clock.value_pos l
              n).ne' :
            Plane →L[ℝ] Plane)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ H*(‖g.pointLinear‖*(1+|clock.value l n|)) :=
        mul_le_mul (inverseCoveringNorm_le_bound hgap)
          ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (norm_timeChart_le _ _) (norm_nonneg _)))
          (norm_nonneg _) hH
      _ = (H*(1+|clock.value l n|))*‖g.pointLinear‖ := by ring
      _ ≤ U*‖g.pointLinear‖ := mul_le_mul_of_nonneg_right hU2 (norm_nonneg _)
  have hc0 := norm_nonneg g.coordinateLinear
  have hp0 := norm_nonneg g.pointLinear
  have hcost := CommonCoverClass.one_le_argumentCost g
  have hc : ‖g.coordinateLinear‖ ≤ CommonCoverClass.argumentCost g := by
    unfold CommonCoverClass.argumentCost
    nlinarith
  have hp : ‖g.pointLinear‖ ≤ CommonCoverClass.argumentCost g := by
    unfold CommonCoverClass.argumentCost
    nlinarith
  have hcx := hcoord.trans (mul_le_mul_of_nonneg_left hc (zero_le_one.trans hU))
  have hpx := hpoint.trans (mul_le_mul_of_nonneg_left hp (zero_le_one.trans hU))
  have hB : 1 ≤ U*CommonCoverClass.argumentCost g := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hU) (sub_nonneg.mpr hcost)]
  change 1+‖G.coordinateLinear‖+‖G.pointLinear‖*(1+‖G.coordinateLinear‖) ≤ _
  have hproduct := mul_le_mul hpx (add_le_add_right hcx 1)
    (by
        positivity : 0 ≤ 1+‖G.coordinateLinear‖) (by
            positivity : 0 ≤ U*CommonCoverClass.argumentCost g)
  nlinarith [sq_nonneg (U*CommonCoverClass.argumentCost g-1)]

theorem geometry_cost_uniform (s : StripData P) (clock : ActualSignedControl.PositiveScale Label)
    (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ) (budget : ℕ)
    {C : ℝ} {a : ℕ} (hgap : ∀ l n, gap l n ≤ budget)
    (href : ∀ l n, CommonCoverClass.argumentCost (reference l n) ≤ C * s.slow n ^ a) :
    ∀ l n, CommonCoverClass.argumentCost (geometry reference gap clock l n) ≤
      (4*(geometryFactor clock budget)^2*C^2)*s.slow n^(2*a) := by
  intro l n
  refine (geometry_cost clock (reference l n) (hgap l n)).trans ?_
  have hsq := pow_le_pow_left₀
    (zero_le_one.trans (CommonCoverClass.one_le_argumentCost (reference l n))) (href l n) 2
  have hm := mul_le_mul_of_nonneg_left hsq
    (by positivity : 0 ≤ 4*(geometryFactor clock budget)^2)
  convert! hm using 1
  ring

theorem geometry_cost_constant_one (clock : ActualSignedControl.PositiveScale Label)
    (budget : ℕ) {C : ℝ} (hC : 1 ≤ C) : 1 ≤ 4*(geometryFactor clock budget)^2*C^2 := by
  have hU := one_le_pow₀ (n := 2) (geometryFactor_one clock budget)
  have hC2 := one_le_pow₀ (n := 2) hC
  nlinarith [mul_nonneg (sub_nonneg.mpr hU) (sub_nonneg.mpr hC2)]

/-! ## The actual active-window parameter and frequency scales -/

/-- Physical phi, given by `ActualSignedGeometry.slowChange h (ChartScales.Q (chart i.2))
(ChartScales.Q (reference i.1 i.2))`. -/
noncomputable def physicalPhi (h : ℝ) (chart : ℕ → ℕ) (reference : Label → ℕ → ℕ)
    (i : Label × ℕ) : Slow →L[ℝ] Slow :=
  ActualSignedGeometry.slowChange h (ChartScales.Q (chart i.2)) (ChartScales.Q (reference i.1 i.2))

/-- Physical psi, given by `PhysicalParticularWave.parameterChange h (ChartScales.Q (chart i.2))
(ChartScales.Q (reference i.1 i.2))`. -/
noncomputable def physicalPsi (h : ℝ) (chart : ℕ → ℕ) (reference : Label → ℕ → ℕ)
    (i : Label × ℕ) : Slow → Slow :=
  PhysicalParticularWave.parameterChange h (ChartScales.Q (chart i.2))
    (ChartScales.Q (reference i.1 i.2))

theorem physical_commute (h : ℝ) (chart : ℕ → ℕ) (reference : Label → ℕ → ℕ)
    (i : Label × ℕ) (p : Slow) :
    ActualSignedGeometry.swapParameter (physicalPsi h chart reference i p) =
      physicalPhi h chart reference i (ActualSignedGeometry.swapParameter p) := rfl

theorem physicalPhi_bound (h : ℝ) (chart : ℕ → ℕ) (reference : Label → ℕ → ℕ)
    (hnear : ∀ l n, chart n ≤ reference l n + 4 ∧ reference l n ≤ chart n + 4) (i : Label × ℕ) :
    ‖physicalPhi h chart reference i‖ ≤ ActualSignedGeometry.slowChangeCost h :=
  ActualSignedGeometry.norm_slowChange_le h (hnear i.1 i.2).1 (hnear i.1 i.2).2

theorem active_scale_bound (s : StripData P) (chart : ℕ → ℕ) (reference : Label → ℕ → ℕ)
    (hchart : ∀ n, 1 ≤ chart n)
    (hnear : ∀ l n, chart n ≤ reference l n + 4 ∧ reference l n ≤ chart n + 4)
    (hs : ∀ n, ChartScales.S (chart n) ≤ s.slow n) (l : Label) (n : ℕ) :
    ChartScales.S (reference l n) ≤ 25*s.slow n :=
  (ActualSignedGeometry.S_window_le (hchart n) (hnear l n).2).trans
    (mul_le_mul_of_nonneg_left (hs n) (by norm_num))

/-- The same nonzero harmonic appears in both physical frequencies, so
normal scaling is independent of its sign and size. -/
theorem normalWeight_harmonic (Q Qr K Kr : ℝ) (j : ℤ) (hj : j ≠ 0) :
    PhysicalParticularWave.normalWeight Q Qr ((j:ℝ)*K) ((j:ℝ)*Kr) =
      PhysicalParticularWave.normalWeight Q Qr K Kr := by
  have hjR : (j:ℝ) ≠ 0 := by exact_mod_cast hj
  unfold PhysicalParticularWave.normalWeight
  rw [mul_div_mul_left _ _ hjR]

theorem normalScale_harmonic {h : ℝ} (hh : 0 ≤ h)
    (chart : ℕ → ℕ) (reference : Label → ℕ → ℕ)
    (hnear : ∀ l n, chart n ≤ reference l n + 4 ∧ reference l n ≤ chart n + 4)
    (j : ℤ) (hj : j ≠ 0) (l : Label) (n : ℕ) :
    (ActualSignedGeometry.normalScale chart reference hnear hh).value l n =
      PhysicalParticularWave.normalWeight (ChartScales.Q (chart n)) (ChartScales.Q (reference l n))
        ((j:ℝ)*(ChartScales.carrier h (chart n):ℝ))
        ((j:ℝ)*(ChartScales.carrier h (reference l n):ℝ)) := by
  rw [normalWeight_harmonic _ _ _ _ j hj]
  exact ActualSignedGeometry.normalScale_value chart reference hnear hh l n

section Slots

variable {h dimension : ℝ} {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem dimension h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
  (slot : Label → ℕ → SlotColoring.Label)

/-- Slot reference, given by `ActualSignedGeometry.slotGeometry sys hdet (slot l n) 0`. -/
noncomputable def slotReference (l : Label) (n : ℕ) : Geometry :=
  ActualSignedGeometry.slotGeometry sys hdet (slot l n) 0

/-- Slot cost, given by `4*(geometryFactor clock budget)^2 *
(25*CommonCoverClass.bandArgumentCost (TorusAverages.slotChart vr vt hdet) 0)^2`. -/
noncomputable def slotCost (clock : ActualSignedControl.PositiveScale Label) (budget : ℕ) : ℝ :=
  4*(geometryFactor clock budget)^2 *
    (25*CommonCoverClass.bandArgumentCost (TorusAverages.slotChart vr vt hdet) 0)^2

theorem slotCost_one (clock : ActualSignedControl.PositiveScale Label) (budget : ℕ) :
    1 ≤ slotCost hdet clock budget :=
  geometry_cost_constant_one clock budget (by
    have hc := CommonCoverClass.bandArgumentCost_one_le (TorusAverages.slotChart vr vt hdet) 0
    nlinarith)

theorem slot_geometry_cost (s : StripData P) (hh : 0 ≤ h)
    (clock : ActualSignedControl.PositiveScale Label) (gap : Label → ℕ → ℕ) (budget : ℕ)
    (hgap : ∀ l n, gap l n ≤ budget) (hslot : ∀ l n, 4 ≤ (slot l n).1)
    (hscale : ∀ l n, ChartScales.S (slot l n).1 ≤ 25 * s.slow n) :
    ∀ l n, CommonCoverClass.argumentCost
      (geometry (slotReference sys hdet slot) gap clock l n) ≤ slotCost hdet clock budget*s.slow
          n^2 := by
  have hr (l : Label) (n : ℕ) :
      CommonCoverClass.argumentCost (slotReference sys hdet slot l n) ≤
        (25*CommonCoverClass.bandArgumentCost (TorusAverages.slotChart vr vt hdet) 0)*s.slow n^1 :=
            by
    refine (ActualSignedGeometry.slotGeometry_argumentCost sys hdet hh (hslot l n) (le_refl
        0)).trans ?_
    have hm := mul_le_mul_of_nonneg_left (hscale l n)
      (zero_le_one.trans (CommonCoverClass.bandArgumentCost_one_le (TorusAverages.slotChart vr vt
          hdet) 0))
    convert! hm using 1
    ring
  simpa only [slotCost, Nat.mul_one] using geometry_cost_uniform s clock
    (slotReference sys hdet slot) gap budget hgap hr

/-- A full target control built from the original slot system, the selected
reference phase, active-band bounds, and current HR coefficient classes.
All clock, normal, affine and geometry bounds are supplied by the concrete
active-window constructions; no energy or output-control premise remains. -/
noncomputable def actualSlotControl
    (s : StripData Slow) (F : PhaseConstruction D) (hh : 0 ≤ h)
    (chart : ℕ → ℕ) (hchart : ∀ n, 1 ≤ chart n)
    (hnear : ∀ l n, chart n ≤ (slot l n).1 + 4 ∧ (slot l n).1 ≤ chart n + 4)
    (hslot : ∀ l n, 4 ≤ (slot l n).1)
    (hs : ∀ n, ChartScales.S (chart n) ≤ s.slow n)
    (hscale : ∀ i, D.scale i = ChartScales.S (slot i.1 i.2).1)
    (hL : ∀ i, F.L i = ChartScales.slotLength sys.radius h (slot i.1 i.2).1)
    (gap : Label → ℕ → ℕ) (budget : ℕ) (hgap : ∀ l n, gap l n ≤ budget)
    (referenceSource : Label → ℕ → Slow × Plane → ProblemStatement.Space)
    (c : CorrectionState.Context (Slow × Plane)) (u : CorrectionState.State (Slow × Plane))
    (b : Label → CorrectionState.HarmonicBlock (Slow × Plane))
    (G A0 : Label → HarmonicResidual.BlockCoefficients (Slow × Plane)) (j : ℤ) (hj : j ≠ 0)
    {α : ℝ}
    (hsource : ∀ i : Fin 3, UniformWaveClass (CommonCoverClass.sourceStrip s)
      (groupedEnvelope
        (geometry (slotReference sys hdet slot) gap
          (ActualSignedGeometry.clockScale chart (fun l n => (slot l n).1) hnear h))
        (fun _ _ => sys.radius)
        (length F (ActualSignedGeometry.clockScale chart (fun l n => (slot l n).1) hnear h))
        (envelope F (ActualSignedGeometry.clockScale chart (fun l n => (slot l n).1) hnear h))) α
      (fun l n x => (HarmonicResidual.residualBlock c u (b l) (G l) (A0 l)).velocity n i j x))
    (part : HarmonicCalculus.ComplexVector →L[ℝ] ProblemStatement.Space) :=
  actualControl s F ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap
    (physicalPhi h chart (fun l n => (slot l n).1))
    (physicalPsi h chart (fun l n => (slot l n).1))
    (physical_commute h chart (fun l n => (slot l n).1))
    (ActualSignedGeometry.clockScale chart (fun l n => (slot l n).1) hnear h)
    (ActualSignedGeometry.normalScale chart (fun l n => (slot l n).1) hnear hh)
    (slotReference sys hdet slot) referenceSource gap
    (fun l n => PhysicalParticularWave.velocityWeight h (ChartScales.Q (chart n)) (ChartScales.Q
        (slot l n).1))
    (fun _ _ => sys.radius)
    (ActualSignedGeometry.slowChangeCost_one h) (by norm_num : (1:ℝ) ≤ 25)
    (slotCost_one hdet _ budget)
    (physicalPhi_bound h chart (fun l n => (slot l n).1) hnear)
    (fun i => by rw [hscale i]; exact active_scale_bound s chart _ hchart hnear hs i.1 i.2)
    (fun l n => by
      rw [hL (l,n)]
      exact ActualSignedGeometry.slotGeometry_separated sys hdet hh (hslot l n) 0)
    (slot_geometry_cost sys hdet slot s hh _ gap budget hgap hslot
      (active_scale_bound s chart _ hchart hnear hs))
    c u b G A0 j hj hsource part

theorem actualSlot_tangent_eq
    (F : PhaseConstruction D) (hh : 0 ≤ h) (chart : ℕ → ℕ)
    (hnear : ∀ l n, chart n ≤ (slot l n).1 + 4 ∧ (slot l n).1 ≤ chart n + 4)
    (referenceSource : Label → ℕ → Slow × Plane → ProblemStatement.Space)
    (gap : Label → ℕ → ℕ) (j : ℤ) (hj : j ≠ 0) (l : Label) (n : ℕ) :
    transportedTangent F
        ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap
      (physicalPsi h chart (fun l n => (slot l n).1))
      (ActualSignedGeometry.clockScale chart (fun l n => (slot l n).1) hnear h)
      (ActualSignedGeometry.normalScale chart (fun l n => (slot l n).1) hnear hh)
      referenceSource gap
      (fun l n => PhysicalParticularWave.velocityWeight h (ChartScales.Q (chart n))
        (ChartScales.Q (slot l n).1)) j l n =
    ParticularWaveAssembly.angleTangent (ScaledTangentTransport.transportTangent
      (PrimaryCopyBridge.frameTangentData
        (nativeFrame (F.frame (l,n))
          ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap)
        j (referenceSource l n))
      (PhysicalParticularWave.parameterChange h (ChartScales.Q (chart n)) (ChartScales.Q (slot l
          n).1))
      (gap l n) 0
      (PhysicalParticularWave.clockWeight h (ChartScales.Q (chart n)) (ChartScales.Q (slot l n).1))
      (PhysicalParticularWave.velocityWeight h (ChartScales.Q (chart n)) (ChartScales.Q (slot l
          n).1))
      (PhysicalParticularWave.normalWeight (ChartScales.Q (chart n)) (ChartScales.Q (slot l n).1)
        ((j:ℝ)*(ChartScales.carrier h (chart n):ℝ))
        ((j:ℝ)*(ChartScales.carrier h (slot l n).1:ℝ)))) := by
  simp only [transportedTangent, physicalPsi, ActualSignedGeometry.clockScale_value,
    normalScale_harmonic hh chart (fun l n => (slot l n).1) hnear j hj l n]

end Slots

end NavierStokes.ScaledActualParticularControl
