/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalData

/-!
# Uniform jets of the actual current physical chart

Only the transverse normalized coordinates are restricted to a fixed annulus.
The slow, angular, and free auxiliary coordinates need no bound for the
positive jets of the chart map.  Native coefficients need smoothness only
on a neighborhood of the evaluation point.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CurrentPhysicalChartJets

open Set Function Filter
open scoped Topology ContDiff

/-- Lift point: an abbreviation for `PhysicalWaveSum.LiftPoint`. -/
abbrev LiftPoint := PhysicalWaveSum.LiftPoint
/-- Plane: an abbreviation for `PhysicalGraphBounds.Plane`. -/
abbrev Plane := PhysicalGraphBounds.Plane
/-- Native: an abbreviation for `PhysicalParticularWave.WaveSpace`. -/
abbrev Native := PhysicalParticularWave.WaveSpace
/-- Complex vector: an abbreviation for `HarmonicCalculus.ComplexVector`. -/
abbrev ComplexVector := HarmonicCalculus.ComplexVector

/-- The actual polar lift followed by the solver's fixed coordinate order. -/
noncomputable def chartMap (a : ℝ) (j : PolarCharts.Index) : LiftPoint → Native :=
  fun x => PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a j x)

/-- Only the radial and angular entries depend on the nonlinear polar map. -/
noncomputable def polarPart : Plane →L[ℝ] Native :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] Plane)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod (0 : Plane →L[ℝ] Plane)

/-- Reverse plane, given by `(ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ
ℝ)`. -/
noncomputable def reversePlane : Plane →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- The free coordinates are copied by a bounded linear map. -/
noncomputable def freePart : LiftPoint →L[ℝ] Native :=
  (((0 : LiftPoint →L[ℝ] ℝ).prod (reversePlane.comp PhysicalGraphBounds.liftZT)).prod
    (0 : LiftPoint →L[ℝ] ℝ)).prod
      (ContinuousLinearMap.snd ℝ PhysicalGraphBounds.ChartPoint Plane)

theorem norm_polarPart_le : ‖polarPart‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro y
  simp [polarPart, Prod.norm_def, Real.norm_eq_abs, abs_nonneg]

theorem norm_freePart_le : ‖freePart‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  have hzt : ‖PhysicalGraphBounds.liftZT x‖ ≤ ‖x‖ :=
    (PhysicalGraphBounds.liftZT.le_opNorm x).trans
      (mul_le_of_le_one_left (norm_nonneg x) PhysicalGraphBounds.norm_liftZT_le)
  have hs : ‖reversePlane (PhysicalGraphBounds.liftZT x)‖ =
      ‖PhysicalGraphBounds.liftZT x‖ := by
    simp only [reversePlane, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', Prod.norm_def]
    exact max_comm _ _
  change max (max (max ‖(0 : ℝ)‖ ‖reversePlane (PhysicalGraphBounds.liftZT x)‖)
    ‖(0 : ℝ)‖) ‖x.2‖ ≤ 1 * ‖x‖
  rw [norm_zero, hs, max_eq_right (norm_nonneg _), max_eq_left (norm_nonneg _), one_mul]
  exact max_le hzt (le_max_right _ _)

theorem chartMap_decomposition (a : ℝ) (j : PolarCharts.Index) :
    chartMap a j = fun x => polarPart (PolarCharts.chart a j (PhysicalGraphBounds.liftXY x)) +
      freePart x := by
  funext x
  ext <;> simp [chartMap, PhysicalParticularWave.waveEquiv_apply,
    ActualSignedPhysicalData.cylinderAt, polarPart, freePart, reversePlane]

theorem chartMap_smooth {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) :
    ContDiff ℝ ∞ (chartMap a j) := by
  rw [chartMap_decomposition]
  exact (polarPart.contDiff.comp ((PolarCharts.chart_contDiff ha j).comp
    PhysicalGraphBounds.liftXY.contDiff)).add freePart.contDiff

/-- One constant bounds all positive map jets on the transverse ball,
uniformly in all four charts and every unbounded free coordinate. -/
theorem chartMap_positive_jets_ball {a : ℝ} (ha : 0 < a) (b : ℝ) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : PolarCharts.Index, ∀ x : LiftPoint,
      PhysicalGraphBounds.liftXY x ∈ Metric.closedBall (0 : Plane) b →
      ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k (chartMap a j) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  refine ⟨B + 1, by linarith, fun j x hx k hk hkm => ?_⟩
  have hc := (PolarCharts.chart_contDiff ha j).comp PhysicalGraphBounds.liftXY.contDiff
  have hcb := PhysicalGraphBounds.jet_comp_linear_bound (PolarCharts.chart_contDiff ha j)
    PhysicalGraphBounds.liftXY PhysicalGraphBounds.norm_liftXY_le x (zero_le_one.trans hB) m
    (fun i hi => hb j i hi _ hx)
  have hp := PhysicalGraphBounds.norm_jet_linear_comp hc polarPart x k
  have hpb : ‖iteratedFDeriv ℝ k
      (fun y => polarPart (PolarCharts.chart a j (PhysicalGraphBounds.liftXY y))) x‖ ≤ B :=
    hp.trans ((mul_le_mul norm_polarPart_le (hcb k hkm) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul B))
  rw [chartMap_decomposition]
  have ha := ResidualStability.norm_jet_add_le isOpen_univ
    (f := fun y => polarPart (PolarCharts.chart a j (PhysicalGraphBounds.liftXY y)))
    (g := fun y => freePart y)
    (polarPart.contDiff.comp hc).contDiffOn freePart.contDiff.contDiffOn (mem_univ x) k
  exact ha.trans (add_le_add hpb
    ((PhysicalGraphBounds.norm_positive_jet_linear_le freePart x hk).trans norm_freePart_le))

theorem chartMap_positive_jets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : PolarCharts.Index, ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b,
      ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k (chartMap a j) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := chartMap_positive_jets_ball ha (b + 1) m
  refine ⟨B, hB, fun j x hx => hb j x ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.le

section Composition

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a : ℝ} (ha : 0 < a) {j : PolarCharts.Index} {x : LiftPoint} {f : Native → E}

include ha

/-- One native open neighborhood suffices for the pulled-back coefficient. -/
theorem composition_smoothNear
    (hf : LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x)) :
    LocalPhysicalCopyBounds.SmoothNear (f ∘ chartMap a j) x := by
  obtain ⟨V, hV, hx, hf⟩ := hf
  exact ⟨chartMap a j ⁻¹' V, hV.preimage (chartMap_smooth ha j).continuous, hx,
    hf.comp (chartMap_smooth ha j).contDiffOn (fun _ hy => hy)⟩

/-- Pointwise finite-jet composition using only the native germ. -/
theorem composition_jet_bound (m : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hf : LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x))
    (hfj : ∀ k ≤ m, ‖iteratedFDeriv ℝ k f (chartMap a j x)‖ ≤ A)
    (hmap : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k (chartMap a j) x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ chartMap a j) x‖ ≤
      (m.factorial : ℝ) * A * B ^ m := by
  obtain ⟨V, hV, hx, hf⟩ := hf
  exact LocalPhysicalCopyBounds.composition_jet_bound_on
    (g := f) (φ := chartMap a j) (U := chartMap a j ⁻¹' V) (V := V)
    (hV.preimage (chartMap_smooth ha j).continuous) hV hf
    (chartMap_smooth ha j).contDiffOn (fun _ hy => hy) hx m hA hB hfj hmap

/-- The multiplicative constant is chosen before the chart, point, native
coefficient, band, or value of its frozen finite-jet bound. -/
theorem composition_jets {b : ℝ} (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : PolarCharts.Index, ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b,
      ∀ (f : Native → E), LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x) →
      ∀ A : ℝ, 0 ≤ A → (∀ k ≤ m, ‖iteratedFDeriv ℝ k f (chartMap a j x)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ chartMap a j) x‖ ≤ C * A := by
  obtain ⟨B, hB, hb⟩ := chartMap_positive_jets (b := b) ha m
  refine ⟨max 1 ((m.factorial : ℝ) * B ^ m), le_max_left _ _, ?_⟩
  intro j x hx f hf A hA hfj k hk
  have he := composition_jet_bound ha m hA hB hf hfj (hb j x hx) k hk
  calc
    _ ≤ (m.factorial : ℝ) * A * B ^ m := he
    _ = ((m.factorial : ℝ) * B ^ m) * A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hA

end Composition

/-! ## Compatibility with positive physical radial scaling -/

theorem chartDomain_smul {a c : ℝ} (hc : 0 < c) (j : PolarCharts.Index) {p : Plane}
    (hp : p ∈ PolarCharts.chartDomain a j) :
    c • p ∈ PolarCharts.chartDomain (c * a) j := by
  change c * a / 4 < (PolarCharts.rotate j (c • p)).1
  rw [PolarCharts.rotate_smul]
  change c * a / 4 < c * (PolarCharts.rotate j p).1
  have he := mul_lt_mul_of_pos_left (show a / 4 < (PolarCharts.rotate j p).1 from hp) hc
  linarith

/-- On the genuine inverse-chart region, simultaneous scaling of the
physical radius and chart padding preserves the exact angular branch. -/
theorem chart_smul {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (j : PolarCharts.Index) {p : Plane}
    (hp : p ∈ PolarCharts.chartDomain a j) :
    PolarCharts.chart (c * a) j (c • p) =
      (c * (PolarCharts.chart a j p).1, (PolarCharts.chart a j p).2) := by
  rw [PolarCharts.chart_eq_localChart (mul_pos hc ha) j (chartDomain_smul hc j hp),
    PolarCharts.chart_eq_localChart ha j hp, PolarCharts.localChart_smul j hc]

/-- The scaling identity holds on an open neighborhood, so it can be used
for physical germ and jet comparisons without an angle-branch inference. -/
theorem chart_smul_germ {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (j : PolarCharts.Index) {p : Plane}
    (hp : p ∈ PolarCharts.chartDomain a j) :
    (fun y : Plane => PolarCharts.chart (c * a) j (c • y)) =ᶠ[𝓝 p]
      (fun y => (c * (PolarCharts.chart a j y).1, (PolarCharts.chart a j y).2)) := by
  filter_upwards [(PolarCharts.chartDomain_open a j).mem_nhds hp] with y hy
  exact chart_smul ha hc j hy

/-! ## The actual Cartesian rotation -/

/-- Rotation, given by `CartesianCopySource.rotationMap (PhysicalGraphBounds.liftXY x)`. -/
noncomputable def rotation (x : LiftPoint) : ComplexVector →L[ℝ] ComplexVector :=
  CartesianCopySource.rotationMap (PhysicalGraphBounds.liftXY x)

theorem rotation_smooth {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ rotation (PhysicalClassBounds.cylindricalDomain a b) :=
  CartesianCopySource.rotationMap_smooth.comp PhysicalGraphBounds.liftXY.contDiff.contDiffOn
    (fun _ hx => PhysicalClassBounds.cylindricalDomain_axisFree ha hx)

theorem rotation_smoothNear {a b : ℝ} (ha : 0 < a) {x : LiftPoint}
    (hx : x ∈ PhysicalClassBounds.cylindricalDomain a b) :
    LocalPhysicalCopyBounds.SmoothNear rotation x :=
  ⟨_, PhysicalClassBounds.cylindricalDomain_open a b, hx, rotation_smooth ha⟩

/-- These are full jets, including order zero, of the literal rotation
operator.  The same constant works for every chart and free coordinate. -/
theorem rotation_jets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k rotation x‖ ≤ C :=
  CartesianCopySource.rotationMap_jets ha m

/-- Positive radial rescaling leaves the actual Cartesian rotation fixed,
including at its totalized zero input. -/
theorem rotationMap_smul {c : ℝ} (hc : 0 < c) (p : Plane) :
    CartesianCopySource.rotationMap (c • p) = CartesianCopySource.rotationMap p := by
  have hr : PhysicalClassBounds.cartesianRadius (c • p) =
      c * PhysicalClassBounds.cartesianRadius p := PolarCharts.radius_smul hc p
  simp only [CartesianCopySource.rotationMap, hr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc.ne', mul_div_mul_left _ _ hc.ne']

/-- Rotate a native vector coefficient after pulling it into the actual
normalized Cartesian lift. -/
noncomputable def rotated (a : ℝ) (j : PolarCharts.Index) (f : Native → ComplexVector)
    (x : LiftPoint) : ComplexVector := rotation x (f (chartMap a j x))

theorem rotated_smoothNear {a b : ℝ} (ha : 0 < a) {j : PolarCharts.Index}
    {x : LiftPoint} (hx : x ∈ PhysicalClassBounds.cylindricalDomain a b)
    {f : Native → ComplexVector}
    (hf : LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x)) :
    LocalPhysicalCopyBounds.SmoothNear (rotated a j f) x := by
  obtain ⟨U, hU, hxU, hs⟩ := composition_smoothNear ha hf
  exact ⟨PhysicalClassBounds.cylindricalDomain a b ∩ U,
    (PhysicalClassBounds.cylindricalDomain_open a b).inter hU, ⟨hx, hxU⟩,
    ((rotation_smooth ha).mono inter_subset_left).clm_apply (hs.mono inter_subset_right)⟩

/-- Local composition and the full Leibniz estimate give a uniform bound
for the actual rotated coefficient, including order zero.  The constant is
independent of every band or label entering the native finite-jet bound. -/
theorem rotated_composition_jets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : PolarCharts.Index, ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b,
      ∀ (f : Native → ComplexVector), LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x) →
      ∀ A : ℝ, 0 ≤ A → (∀ k ≤ m, ‖iteratedFDeriv ℝ k f (chartMap a j x)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (rotated a j f) x‖ ≤ C * A := by
  obtain ⟨B, hB, hcomp⟩ := composition_jets (E := ComplexVector) (b := b) ha m
  obtain ⟨R, hR, hrot⟩ := rotation_jets (b := b) ha m
  refine ⟨max 1 ((2 : ℝ) ^ m * R * B), le_max_left _ _, ?_⟩
  intro j x hx f hf A hA hfj k hk
  obtain ⟨U, hU, hxU, hs⟩ := composition_smoothNear ha hf
  have he := WaveEnvelopeTransport.clm_apply_jet_bound_on
    ((PhysicalClassBounds.cylindricalDomain_open a b).inter hU)
    ((rotation_smooth ha).mono inter_subset_left) (hs.mono inter_subset_right)
    (show x ∈ PhysicalClassBounds.cylindricalDomain a b ∩ U from ⟨hx, hxU⟩)
    m (zero_le_one.trans hR) (mul_nonneg (zero_le_one.trans hB) hA)
    (hrot x hx) (hcomp j x hx f hf A hA hfj) k hk
  calc
    _ ≤ (2 : ℝ) ^ m * R * (B * A) := he
    _ = ((2 : ℝ) ^ m * R * B) * A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hA

/-! ## The fixed Cartesian realification -/

theorem realVector_norm_le (z : ComplexVector) :
    ‖PhysicalCurlCovariance.realVector z‖ ≤ 3 * ‖z‖ := by
  have hi (i : Fin 3) : ‖PhysicalCurlCovariance.realVector z i‖ ≤ ‖z‖ := by
    rw [PhysicalCurlCovariance.realVector_apply, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i)
  have hs : ‖PhysicalCurlCovariance.realVector z‖ ^ 2 ≤ 3 * ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _i : Fin 3, ‖z‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hi i) 2)
      _ = 3 * ‖z‖ ^ 2 := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * ‖z‖)).mp
  nlinarith [sq_nonneg ‖z‖]

/-- The literal real-vector constructor is a fixed bounded linear map.
This provides the final codomain conversion for physical vector modes. -/
noncomputable def realVectorCLM : ComplexVector →L[ℝ] ProblemStatement.Space :=
  ({ toFun := PhysicalCurlCovariance.realVector
     map_add' := by
       intro z w
       ext i
       simp [PhysicalCurlCovariance.realVector_apply]
     map_smul' := by
       intro c z
       ext i
       simp [PhysicalCurlCovariance.realVector_apply, Complex.real_smul] } :
    ComplexVector →ₗ[ℝ] ProblemStatement.Space).mkContinuous 3 realVector_norm_le

@[simp] theorem realVectorCLM_apply (z : ComplexVector) :
    realVectorCLM z = PhysicalCurlCovariance.realVector z := rfl

theorem norm_realVectorCLM_le : ‖realVectorCLM‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) realVector_norm_le

end NavierStokes.CurrentPhysicalChartJets
