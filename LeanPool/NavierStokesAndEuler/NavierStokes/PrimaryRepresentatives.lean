/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PartitionedCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.CoordinateAlgebra
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityCoordinates
import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityHomogeneity
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone

/-!
# Actual grid representatives and uniform primary reference parameters

Representatives are selected in the intersection of the actual closed mask
support and the fixed closed active set. The enlarged-box distance is then a
consequence of the mesh, rather than a hypothesis on the selected point.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PrimaryRepresentatives

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Plane: an abbreviation for `MovingFrameODE.Plane`. -/
abbrev Plane := MovingFrameODE.Plane
/-- Grid: an abbreviation for `SlotColoring.Grid`. -/
abbrev Grid := SlotColoring.Grid
/-- Label: an abbreviation for `PartitionedCovariance.UnsignedLabel`. -/
abbrev Label := PartitionedCovariance.UnsignedLabel
/-- Position: an abbreviation for `SlotColoring.Position`. -/
abbrev Position := SlotColoring.Position

/-- Position, given by `![q.1, q.2.1, q.2.2]`. -/
noncomputable def position (q : Slow) : Position := ![q.1, q.2.1, q.2.2]
/-- Slow, given by `(x 0, (x 1, x 2))`. -/
noncomputable def slow (x : Position) : Slow := (x 0, (x 1, x 2))

@[simp] theorem position_slow (x : Position) : position (slow x) = x := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem slow_position (q : Slow) : slow (position q) = q := rfl

theorem position_smooth : ContDiff ℝ ∞ position := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_fst
  · exact contDiff_snd.fst
  · exact contDiff_snd.snd

theorem slow_smooth : ContDiff ℝ ∞ slow :=
  (contDiff_apply ℝ ℝ 0).prodMk
    ((contDiff_apply ℝ ℝ 1).prodMk (contDiff_apply ℝ ℝ 2))

theorem norm_slow_sub_le {x y : Position} {c : ℝ}
    (h : ∀ j, |x j - y j| ≤ c) : ‖slow x - slow y‖ ≤ c := by
  change max |x 0 - y 0| (max |x 1 - y 1| |x 2 - y 2|) ≤ c
  exact max_le (h 0) (max_le (h 1) (h 2))

/-- Native mask, given by `SquaredPartition.slowMask n k (position q)`. -/
noncomputable def nativeMask (n : ℕ) (k : Grid) (q : Slow) : ℝ :=
  SquaredPartition.slowMask n k (position q)

/-- Grid box, given by `{q | ∀ j, |position q j - SquaredPartition.nativeSpacing n * (k j : ℝ)|
≤ a * SquaredPartition.nativeSpacing n}`. -/
noncomputable def gridBox (n : ℕ) (k : Grid) (a : ℝ) : Set Slow :=
  {q | ∀ j, |position q j - SquaredPartition.nativeSpacing n * (k j : ℝ)| ≤
    a * SquaredPartition.nativeSpacing n}

theorem gridBox_closed (n : ℕ) (k : Grid) (a : ℝ) : IsClosed (gridBox n k a) := by
  simp only [gridBox, Set.ofPred_forall]
  exact isClosed_iInter fun j => isClosed_le
    (((continuous_apply j).comp position_smooth.continuous).sub continuous_const).abs
        continuous_const

theorem nativeMask_smooth (n : ℕ) (k : Grid) : ContDiff ℝ ∞ (nativeMask n k) :=
  (SquaredPartition.slowMask_smooth n k).comp position_smooth

theorem nativeMask_tsupport_subset {n : ℕ} (hn : 1 ≤ n) (k : Grid) :
    tsupport (nativeMask n k) ⊆ gridBox n k 1 := by
  apply closure_minimal _ (gridBox_closed n k 1)
  intro q hq j
  have hx : position q ∈ tsupport (SquaredPartition.slowMask n k) := subset_closure hq
  have hj := SquaredPartition.slowMask_tsupport_subset hn k hx j (mem_univ _)
  change |position q j - SquaredPartition.nativeSpacing n * (k j : ℝ)| ≤
    1 * SquaredPartition.nativeSpacing n
  rw [one_mul, abs_le]
  constructor <;> linarith [hj.1, hj.2]

theorem gridBox_distance {n : ℕ} {k : Grid} {a b : ℝ} {q q₀ : Slow}
    (hq : q ∈ gridBox n k a) (h₀ : q₀ ∈ gridBox n k b) :
    ‖q - q₀‖ ≤ (a + b) * SquaredPartition.nativeSpacing n := by
  rw [← slow_position q, ← slow_position q₀]
  apply norm_slow_sub_le
  intro j
  have ht := abs_sub_le (position q j)
    (SquaredPartition.nativeSpacing n * (k j : ℝ)) (position q₀ j)
  rw [abs_sub_comm (SquaredPartition.nativeSpacing n * (k j : ℝ))] at ht
  linarith [hq j, h₀ j]

/-- Exactly the labels whose closed mask support meets the closed active set. -/
noncomputable def ActiveLabel (K : Set Slow) :=
  {L : Label // 1 ≤ L.1 ∧ (K ∩ tsupport (nativeMask L.1 L.2)).Nonempty}

/-- Representative, given by `Classical.choose L.property.2`. -/
noncomputable def representative (K : Set Slow) (L : ActiveLabel K) : Slow :=
  Classical.choose L.property.2

theorem representative_mem (K : Set Slow) (L : ActiveLabel K) : representative K L ∈ K :=
  (Classical.choose_spec L.property.2).1

theorem representative_mem_tsupport (K : Set Slow) (L : ActiveLabel K) :
    representative K L ∈ tsupport (nativeMask L.val.1 L.val.2) :=
  (Classical.choose_spec L.property.2).2

/-- The sharp bound furnished by a one-mesh support and a two-mesh pad. -/
theorem representative_enlarged_distance (K : Set Slow) (L : ActiveLabel K)
    {q : Slow} (hq : q ∈ gridBox L.val.1 L.val.2 2) :
    ‖q - representative K L‖ ≤ 3 / ChartScales.S L.val.1 ^ 3 := by
  have h₀ := nativeMask_tsupport_subset L.property.1 L.val.2 (representative_mem_tsupport K L)
  simpa only [show (2 : ℝ) + 1 = 3 by norm_num, SquaredPartition.nativeSpacing,
    div_eq_mul_inv] using gridBox_distance hq h₀

theorem representative_support_distance (K : Set Slow) (L : ActiveLabel K)
    {q : Slow} (hq : q ∈ tsupport (nativeMask L.val.1 L.val.2)) :
    ‖q - representative K L‖ ≤ 2 / ChartScales.S L.val.1 ^ 3 := by
  have h₀ := nativeMask_tsupport_subset L.property.1 L.val.2 (representative_mem_tsupport K L)
  have hq' := nativeMask_tsupport_subset L.property.1 L.val.2 hq
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num, SquaredPartition.nativeSpacing,
    div_eq_mul_inv] using gridBox_distance hq' h₀

/-- Normalized slow, given by `slow (SquaredPartition.slowCoordinates D n x)`. -/
noncomputable def normalizedSlow (D : ℝ) (n : ℕ) (x : Position) : Slow :=
  slow (SquaredPartition.slowCoordinates D n x)

theorem width_eq_scaled_spacing (D : ℝ) (n : ℕ) (j : Fin 3) :
    SlotColoring.width D j n = ChartScales.Q n ^ SlotColoring.axisExponent D j *
      SquaredPartition.nativeSpacing n := by
  unfold SlotColoring.width
  rw [SlotColoring.spacing_eq_scaled_mesh]
  simp only [ChartScales.Q, SquaredPartition.nativeSpacing, ChartScales.S, one_div]

theorem physicalBox_normalizes (D : ℝ) (L : SlotColoring.Label) {x : Position}
    (hx : x ∈ SlotColoring.physicalBox D L) :
    normalizedSlow D L.1 x ∈ gridBox L.1 L.2.1 2 := by
  intro j
  have hp : 0 < ChartScales.Q L.1 ^ SlotColoring.axisExponent D j :=
    Real.rpow_pos_of_pos (ChartScales.Q_pos _) _
  have he : position (normalizedSlow D L.1 x) j -
      SquaredPartition.nativeSpacing L.1 * (L.2.1 j : ℝ) =
      (x j - SlotColoring.width D j L.1 * (L.2.1 j : ℝ)) /
        (ChartScales.Q L.1 ^ SlotColoring.axisExponent D j) := by
    simp only [normalizedSlow, position_slow, SquaredPartition.slowCoordinates,
      width_eq_scaled_spacing]
    field_simp
  rw [he, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hj := hx j
  rw [width_eq_scaled_spacing] at hj
  rw [width_eq_scaled_spacing]
  nlinarith

theorem physicalMask_nativeMask (D : ℝ) (L : Label) (q : ℝ) (x : Position) :
    PartitionedCovariance.mask D L q x = SquaredPartition.dyadicMask (L.1 : ℤ) q *
      nativeMask L.1 L.2 (normalizedSlow D L.1 x) := by
  simp only [PartitionedCovariance.mask, PartitionedCovariance.physicalMask,
    PartitionedCovariance.signedLabel, nativeMask, normalizedSlow, position_slow,
    SquaredPartition.physicalSlowMask]

/-- Every nonzero actual physical mask on the active set produces one of
the labels for which the representative was constructed. -/
theorem physicalMask_active (K : Set Slow) (D : ℝ) (L : Label)
    (hL : 1 ≤ L.1) {q : ℝ} {x : Position}
    (hx : normalizedSlow D L.1 x ∈ K) (hm : PartitionedCovariance.mask D L q x ≠ 0) :
    ∃ A : ActiveLabel K, A.val = L := by
  refine ⟨⟨L, hL, normalizedSlow D L.1 x, hx, ?_⟩, rfl⟩
  apply subset_closure
  rw [physicalMask_nativeMask] at hm
  exact (mul_ne_zero_iff.mp hm).2

theorem grid_mesh_tendsto_zero :
    Tendsto (fun n : ℕ => 3 / ChartScales.S n ^ 3) atTop (𝓝 0) := by
  have hS : Tendsto (fun n : ℕ => ChartScales.S n ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp PhaseEstimates.chart_S_tendsto_atTop
  have hi : Tendsto (fun n : ℕ => (ChartScales.S n ^ 3)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    hS.inv_tendsto_atTop
  simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul (3 : ℝ)

/-- All enlarged boxes of active sufficiently fine labels lie in a single
prescribed open base-control chart. -/
theorem enlarged_eventually_in_chart {K U : Set Slow} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : ℕ, ∀ L : ActiveLabel K, N ≤ L.val.1 → gridBox L.val.1 L.val.2 2 ⊆ U := by
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 grid_mesh_tendsto_zero).2 r hr)
  refine ⟨N, fun L hL q hq => hsub ?_⟩
  apply Metric.mem_cthickening_of_dist_le q (representative K L) r K (representative_mem K L)
  simpa only [dist_eq_norm] using
    (representative_enlarged_distance K L hq).trans (hN _ hL).le

/-! ## Reference frame and exact unstable-mode parameters -/

/-- Normal direction, given by `‖g‖⁻¹ • g`. -/
noncomputable def normalDirection (g : Plane) : Plane := ‖g‖⁻¹ • g
/-- Transverse direction, given by `-MovingFrameODE.quarterTurn (normalDirection g)`. -/
noncomputable def transverseDirection (g : Plane) : Plane :=
  -MovingFrameODE.quarterTurn (normalDirection g)
/-- Coupling, given by `2 * F * normalDirection g 0`. -/
noncomputable def coupling (F : ℝ) (g : Plane) : ℝ := 2 * F * normalDirection g 0
/-- Lambda0, given by `Real.sqrt (-(coupling F g) * (coupling F g + ‖g‖))`. -/
noncomputable def lambda0 (F : ℝ) (g : Plane) : ℝ :=
  Real.sqrt (-(coupling F g) * (coupling F g + ‖g‖))
/-- C0, given by `lambda0 F g / coupling F g`. -/
noncomputable def c0 (F : ℝ) (g : Plane) : ℝ := lambda0 F g / coupling F g

/-- Primitive strict shear conditions. The last inequality is the positive
opening of the unstable two-dimensional reference system. -/
structure ReferenceCone (F : ℝ) (g : Plane) : Prop where
  frequency_pos : 0 < F
  theta_neg : g 0 < 0
  opening_pos : 0 < 2 * F * g 0 + ‖g‖ ^ 2

theorem ReferenceCone.shear_ne_zero {F : ℝ} {g : Plane} (h : ReferenceCone F g) : g ≠ 0 := by
  intro hg
  simpa [hg] using h.theta_neg

/-- The manuscript's shear coordinates give the primitive reference cone
from `a > 0` and `a²+b² > 2a`. -/
theorem referenceCone_of_shear_coordinates {F a b : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 * a < a ^ 2 + b ^ 2) : ReferenceCone F (F • !₂[-a, b]) := by
  refine ⟨hF, ?_, ?_⟩
  · change F * -a < 0
    exact mul_neg_of_pos_of_neg hF (neg_neg_of_pos ha)
  · have hn := ViscousPropagator.plane_norm_sq (F • !₂[-a, b])
    change ‖F • !₂[-a, b]‖ ^ 2 = (F * -a) ^ 2 + (F * b) ^ 2 at hn
    change 0 < 2 * F * (F * -a) + ‖F • !₂[-a, b]‖ ^ 2
    rw [hn]
    nlinarith [mul_pos (sq_pos_of_pos hF) (sub_pos.mpr hv)]

theorem normalDirection_unit {g : Plane} (hg : g ≠ 0) : ‖normalDirection g‖ = 1 := by
  simp only [normalDirection, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)

theorem transverseDirection_unit {g : Plane} (hg : g ≠ 0) : ‖transverseDirection g‖ = 1 := by
  rw [transverseDirection, norm_neg, PhaseEstimates.quarterTurn_norm, normalDirection_unit hg]

theorem quarterTurn_transverseDirection (g : Plane) :
    MovingFrameODE.quarterTurn (transverseDirection g) = normalDirection g := by
  rw [transverseDirection, map_neg, MovingFrameODE.quarterTurn_square, neg_neg]

theorem norm_smul_normalDirection {g : Plane} (hg : g ≠ 0) :
    ‖g‖ • normalDirection g = g := by
  rw [normalDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_smul]

theorem transverseDirection_inner_shear (g : Plane) :
    ⟪transverseDirection g, g⟫_ℝ = 0 := by
  rw [transverseDirection, normalDirection, map_smul, inner_neg_left, real_inner_smul_left,
    real_inner_comm, MovingFrameODE.inner_quarterTurn_self]
  ring

theorem normalDirection_theta (g : Plane) : normalDirection g 0 = g 0 / ‖g‖ := by
  simp [normalDirection, div_eq_mul_inv, mul_comm]

theorem coupling_eq (F : ℝ) (g : Plane) : coupling F g = (2 * F * g 0) / ‖g‖ := by
  rw [coupling, normalDirection_theta]
  ring

theorem ReferenceCone.coupling_neg {F : ℝ} {g : Plane} (h : ReferenceCone F g) :
    coupling F g < 0 := by
  rw [coupling_eq]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith [h.frequency_pos]) h.theta_neg)
    (norm_pos_iff.mpr h.shear_ne_zero)

theorem ReferenceCone.normalDirection_theta_neg {F : ℝ} {g : Plane} (h : ReferenceCone F g) :
    normalDirection g 0 < 0 := by
  rw [normalDirection_theta]
  exact div_neg_of_neg_of_pos h.theta_neg (norm_pos_iff.mpr h.shear_ne_zero)

theorem ReferenceCone.coupling_add_norm_pos {F : ℝ} {g : Plane} (h : ReferenceCone F g) :
    0 < coupling F g + ‖g‖ := by
  have hg := norm_pos_iff.mpr h.shear_ne_zero
  have he : coupling F g + ‖g‖ = (2 * F * g 0 + ‖g‖ ^ 2) / ‖g‖ := by
    rw [coupling_eq]
    field_simp
  rw [he]
  exact div_pos h.opening_pos hg

theorem ReferenceCone.lambda0_pos {F : ℝ} {g : Plane} (h : ReferenceCone F g) :
    0 < lambda0 F g :=
  Real.sqrt_pos.mpr (mul_pos (neg_pos.mpr h.coupling_neg) h.coupling_add_norm_pos)

theorem ReferenceCone.lambda0_sq {F : ℝ} {g : Plane} (h : ReferenceCone F g) :
    lambda0 F g ^ 2 = -(coupling F g) * (coupling F g + ‖g‖) :=
  Real.sq_sqrt (mul_pos (neg_pos.mpr h.coupling_neg) h.coupling_add_norm_pos).le

theorem ReferenceCone.c0_neg {F : ℝ} {g : Plane} (h : ReferenceCone F g) : c0 F g < 0 :=
  div_neg_of_pos_of_neg h.lambda0_pos h.coupling_neg

theorem ReferenceCone.lambda0_div_c0 {F : ℝ} {g : Plane} (h : ReferenceCone F g) :
    lambda0 F g / c0 F g = 2 * F * normalDirection g 0 := by
  rw [c0, div_div_eq_mul_div, mul_div_cancel_left₀ _ h.lambda0_pos.ne']
  rfl

theorem ReferenceCone.lambda0_mul_c0 {F : ℝ} {g : Plane} (h : ReferenceCone F g) :
    lambda0 F g * c0 F g = -(2 * F * normalDirection g 0 + ‖g‖) := by
  change lambda0 F g * (lambda0 F g / coupling F g) = -(coupling F g + ‖g‖)
  rw [← mul_div_assoc, ← pow_two, h.lambda0_sq]
  field_simp [h.coupling_neg.ne]

section Continuity

variable {X : Type*} [TopologicalSpace X] {K : Set X} {F : X → ℝ} {g : X → Plane}

theorem normalDirection_continuousOn (hg : ContinuousOn g K)
    (hne : ∀ q ∈ K, g q ≠ 0) : ContinuousOn (fun q => normalDirection (g q)) K :=
  (hg.norm.inv₀ (fun q hq => norm_ne_zero_iff.mpr (hne q hq))).smul hg

theorem transverseDirection_continuousOn (hg : ContinuousOn g K)
    (hne : ∀ q ∈ K, g q ≠ 0) : ContinuousOn (fun q => transverseDirection (g q)) K :=
  (MovingFrameODE.quarterTurn.continuous.comp_continuousOn
    (normalDirection_continuousOn hg hne)).neg

theorem coupling_continuousOn (hF : ContinuousOn F K) (hg : ContinuousOn g K)
    (hne : ∀ q ∈ K, g q ≠ 0) : ContinuousOn (fun q => coupling (F q) (g q)) K := by
  exact (continuousOn_const.mul hF).mul
    ((PiLp.continuous_apply 2 _ 0).comp_continuousOn (normalDirection_continuousOn hg hne))

theorem lambda0_continuousOn (hF : ContinuousOn F K) (hg : ContinuousOn g K)
    (hne : ∀ q ∈ K, g q ≠ 0) : ContinuousOn (fun q => lambda0 (F q) (g q)) K := by
  have hc := coupling_continuousOn hF hg hne
  exact (hc.neg.mul (hc.add hg.norm)).sqrt

theorem c0_continuousOn (hF : ContinuousOn F K) (hg : ContinuousOn g K)
    (hc : ∀ q ∈ K, ReferenceCone (F q) (g q)) : ContinuousOn (fun q => c0 (F q) (g q)) K :=
  (lambda0_continuousOn hF hg (fun q hq => (hc q hq).shear_ne_zero)).div
    (coupling_continuousOn hF hg (fun q hq => (hc q hq).shear_ne_zero))
    (fun q hq => (hc q hq).coupling_neg.ne)

end Continuity

/-- Parameter scalars, given by `![q.1, F q, ‖g q‖, lambda0 (F q) (g q), c0 (F q) (g q), q.1⁻¹,
‖g q‖⁻¹, (lambda0 (F q) (g q))⁻¹, (c0 (F q) (g q))⁻¹]`. -/
noncomputable def parameterScalars (F : Slow → ℝ) (g : Slow → Plane) (q : Slow) : Fin 9 → ℝ :=
  ![q.1, F q, ‖g q‖, lambda0 (F q) (g q), c0 (F q) (g q),
    q.1⁻¹, ‖g q‖⁻¹, (lambda0 (F q) (g q))⁻¹, (c0 (F q) (g q))⁻¹]

theorem parameterScalars_continuousOn {K : Set Slow} {F : Slow → ℝ} {g : Slow → Plane}
    (hF : ContinuousOn F K) (hg : ContinuousOn g K) (hR : ∀ q ∈ K, 0 < q.1)
    (hc : ∀ q ∈ K, ReferenceCone (F q) (g q)) : ContinuousOn (parameterScalars F g) K := by
  have hn : ∀ q ∈ K, g q ≠ 0 := fun q hq => (hc q hq).shear_ne_zero
  have hlam := lambda0_continuousOn hF hg hn
  have hc0 := c0_continuousOn hF hg hc
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact continuous_fst.continuousOn
  · exact hF
  · exact hg.norm
  · exact hlam
  · exact hc0
  · exact continuous_fst.continuousOn.inv₀ (fun q hq => (hR q hq).ne')
  · exact hg.norm.inv₀ (fun q hq => norm_ne_zero_iff.mpr (hn q hq))
  · exact hlam.inv₀ (fun q hq => (hc q hq).lambda0_pos.ne')
  · exact hc0.inv₀ (fun q hq => (hc q hq).c0_neg.ne)

/-- The same constant controls every representative parameter and reciprocal. -/
structure ParameterBounds (M R F : ℝ) (g : Plane) : Prop where
  radius : R ≤ M
  frequency : |F| ≤ M
  shear : ‖g‖ ≤ M
  lambda : lambda0 F g ≤ M
  ratio : |c0 F g| ≤ M
  radius_inv : R⁻¹ ≤ M
  shear_inv : ‖g‖⁻¹ ≤ M
  lambda_inv : (lambda0 F g)⁻¹ ≤ M
  ratio_inv : |c0 F g|⁻¹ ≤ M

theorem compact_parameter_bounds {K : Set Slow} (hK : IsCompact K)
    {F : Slow → ℝ} {g : Slow → Plane} (hF : ContinuousOn F K) (hg : ContinuousOn g K)
    (hR : ∀ q ∈ K, 0 < q.1) (hc : ∀ q ∈ K, ReferenceCone (F q) (g q)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ K, ParameterBounds M q.1 (F q) (g q) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (parameterScalars_continuousOn hF hg hR hc)
  refine ⟨max 1 B, le_max_left _ _, fun q hq => ?_⟩
  have hb (i : Fin 9) : |parameterScalars F g q i| ≤ max 1 B := by
    exact (norm_le_pi_norm (parameterScalars F g q) i).trans
      ((hB q hq).trans (le_max_right _ _))
  have hgq : 0 < ‖g q‖ := norm_pos_iff.mpr (hc q hq).shear_ne_zero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [parameterScalars, abs_of_pos (hR q hq)] using hb 0
  · simpa [parameterScalars] using hb 1
  · simpa [parameterScalars] using hb 2
  · simpa [parameterScalars, abs_of_pos (hc q hq).lambda0_pos] using hb 3
  · simpa [parameterScalars] using hb 4
  · simpa [parameterScalars, abs_of_pos (inv_pos.mpr (hR q hq))] using hb 5
  · simpa [parameterScalars, abs_of_pos (inv_pos.mpr hgq)] using hb 6
  · simpa [parameterScalars, abs_of_pos (inv_pos.mpr (hc q hq).lambda0_pos)] using hb 7
  · simpa [parameterScalars, abs_inv] using hb 8

private theorem reciprocal_lower {M x : ℝ} (hM : 0 < M) (hx : 0 < x) (h : x⁻¹ ≤ M) :
    M⁻¹ ≤ x := by
  have hb := mul_le_mul_of_nonneg_right h hx.le
  rw [inv_mul_cancel₀ hx.ne'] at hb
  have he : M * M⁻¹ = 1 := mul_inv_cancel₀ hM.ne'
  nlinarith

theorem ParameterBounds.mono {M M' R F : ℝ} {g : Plane}
    (h : ParameterBounds M R F g) (hMM' : M ≤ M') : ParameterBounds M' R F g :=
  ⟨h.radius.trans hMM', h.frequency.trans hMM', h.shear.trans hMM', h.lambda.trans hMM',
    h.ratio.trans hMM', h.radius_inv.trans hMM', h.shear_inv.trans hMM',
    h.lambda_inv.trans hMM', h.ratio_inv.trans hMM'⟩

theorem ParameterBounds.positive_lower {M R F : ℝ} {g : Plane}
    (h : ParameterBounds M R F g) (hM : 1 ≤ M) (hR : 0 < R) (hc : ReferenceCone F g) :
    M⁻¹ ≤ R ∧ M⁻¹ ≤ ‖g‖ ∧ M⁻¹ ≤ lambda0 F g ∧ M⁻¹ ≤ |c0 F g| := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  exact ⟨reciprocal_lower hM0 hR h.radius_inv,
    reciprocal_lower hM0 (norm_pos_iff.mpr hc.shear_ne_zero) h.shear_inv,
    reciprocal_lower hM0 hc.lambda0_pos h.lambda_inv,
    reciprocal_lower hM0 (abs_pos.mpr hc.c0_neg.ne) h.ratio_inv⟩

theorem representative_parameter_bounds {K : Set Slow} (hK : IsCompact K)
    {F : Slow → ℝ} {g : Slow → Plane} (hF : ContinuousOn F K) (hg : ContinuousOn g K)
    (hR : ∀ q ∈ K, 0 < q.1) (hc : ∀ q ∈ K, ReferenceCone (F q) (g q)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ L : ActiveLabel K,
      ParameterBounds M (representative K L).1 (F (representative K L)) (g (representative K L)) :=
          by
  obtain ⟨M, hM, hb⟩ := compact_parameter_bounds hK hF hg hR hc
  exact ⟨M, hM, fun L => hb _ (representative_mem K L)⟩

/-! ## A fixed compact set from the actual normalized similarity range -/

/-- Normalized active points, including the limiting time face `T = 0`. -/
noncomputable def activeReference (h a b : ℝ) : Set Slow :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ ∃ q ∈ Icc (1 / 2 : ℝ) 2,
    SimilarityCoordinates.forwardScalar (2 * h) p.2.1 q = p.2.2 ∧
      p.1 ^ 2 / (2 * q) ∈ Icc a b}

/-- Reference box, given by `Icc (Real.sqrt a) (2 * Real.sqrt b) ×ˢ (Icc (-2 : ℝ) 2 ×ˢ Icc (0 :
ℝ) 2)`. -/
noncomputable def referenceBox (a b : ℝ) : Set Slow :=
  Icc (Real.sqrt a) (2 * Real.sqrt b) ×ˢ (Icc (-2 : ℝ) 2 ×ˢ Icc (0 : ℝ) 2)

/-- Reference compact, given by `closure (activeReference h a b)`. -/
noncomputable def referenceCompact (h a b : ℝ) : Set Slow := closure (activeReference h a b)

theorem activeReference_subset_box {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) : activeReference h a b ⊆ referenceBox a b := by
  rintro p ⟨hR, hT, q, hq, he, hX⟩
  have hq0 : 0 < q := by linarith [hq.1]
  have hb : 0 < b := ha.trans_le hab
  have hp : 0 < q ^ (2 * h) := Real.rpow_pos_of_pos hq0 _
  have hfactor : q ^ (2 * h) * (q ^ (1 - 2 * h) - p.2.1 ^ 2) = p.2.2 := by
    rw [← SimilarityCoordinates.forwardScalar_factor hq0]
    exact he
  have hZ : p.2.1 ^ 2 ≤ q ^ (1 - 2 * h) := by nlinarith
  have hqpow : q ^ (1 - 2 * h) ≤ 2 := by
    calc
      q ^ (1 - 2 * h) ≤ (2 : ℝ) ^ (1 - 2 * h) :=
        Real.rpow_le_rpow hq0.le hq.2 (by linarith)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  have hRlo := (le_div_iff₀ (show 0 < 2 * q by positivity)).mp hX.1
  have hRhi := (div_le_iff₀ (show 0 < 2 * q by positivity)).mp hX.2
  have hRlower : a ≤ p.1 ^ 2 := by nlinarith [hq.1]
  have hRupper : p.1 ^ 2 ≤ 4 * b := by nlinarith [hq.2]
  have hsa := Real.sq_sqrt ha.le
  have hsb := Real.sq_sqrt hb.le
  have hTq : p.2.2 ≤ q := by
    dsimp [SimilarityCoordinates.forwardScalar] at he
    nlinarith [sq_nonneg p.2.1]
  refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨hT, hTq.trans hq.2⟩⟩⟩
  · nlinarith [Real.sqrt_nonneg a]
  · nlinarith [Real.sqrt_nonneg b]
  · nlinarith
  · nlinarith

theorem referenceCompact_subset_box {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) : referenceCompact h a b ⊆ referenceBox a b :=
  closure_minimal (activeReference_subset_box hh hh1 ha hab)
    (isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc))

theorem referenceCompact_isCompact {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) : IsCompact (referenceCompact h a b) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
    isClosed_closure (referenceCompact_subset_box hh hh1 ha hab)

theorem referenceCompact_radius_pos {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) {q : Slow} (hq : q ∈ referenceCompact h a b) : 0 < q.1 :=
  (Real.sqrt_pos.mpr ha).trans_le (referenceCompact_subset_box hh hh1 ha hab hq).1.1

/-- One explicit convex chart containing the whole normalized compact set. -/
noncomputable def baseChart (a b : ℝ) : Set Slow :=
  Ioo (Real.sqrt a / 2) (2 * Real.sqrt b + 1) ×ˢ
    (Ioo (-3 : ℝ) 3 ×ˢ Ioo (-1 : ℝ) 3)

theorem baseChart_open (a b : ℝ) : IsOpen (baseChart a b) :=
  isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)

theorem baseChart_convex (a b : ℝ) : Convex ℝ (baseChart a b) :=
  (convex_Ioo _ _).prod ((convex_Ioo _ _).prod (convex_Ioo _ _))

theorem referenceCompact_subset_baseChart {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) : referenceCompact h a b ⊆ baseChart a b := by
  intro q hq
  obtain ⟨hR, hZ, hT⟩ := referenceCompact_subset_box hh hh1 ha hab hq
  have hsa := Real.sqrt_pos.mpr ha
  exact ⟨⟨by linarith [hR.1], by linarith [hR.2]⟩,
    ⟨⟨by linarith [hZ.1], by linarith [hZ.2]⟩,
      ⟨by linarith [hT.1], by linarith [hT.2]⟩⟩⟩

theorem reference_enlarged_eventually_in_chart {h a b : ℝ} (hh : 0 ≤ h)
    (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a ≤ b) :
    ∃ N : ℕ, ∀ L : ActiveLabel (referenceCompact h a b), N ≤ L.val.1 →
      gridBox L.val.1 L.val.2 2 ⊆ baseChart a b :=
  enlarged_eventually_in_chart (referenceCompact_isCompact hh hh1 ha hab)
    (baseChart_open a b) (referenceCompact_subset_baseChart hh hh1 ha hab)

theorem normalizedSlow_coordinates (D : ℝ) (n : ℕ) (x : Position) :
    normalizedSlow D n x =
      (x 0 / ChartScales.Q n ^ (1 / 2 : ℝ), (x 1 / ChartScales.Q n ^ D, x 2 / ChartScales.Q n)) :=
          by
  simp [normalizedSlow, slow, SquaredPartition.slowCoordinates, SlotColoring.axisExponent]

/-- The physical similarity equation and the actual dyadic mask put every
active point into the same compact reference set, independent of its label. -/
theorem physicalMask_normalized_mem {h a b : ℝ} (L : Label) {q : ℝ} {x : Position}
    (hq : 0 < q) (hR : 0 ≤ x 0) (hT : 0 ≤ x 2)
    (he : SimilarityCoordinates.forwardScalar (2 * h) (x 1) q = x 2)
    (hX : x 0 ^ 2 / (2 * q) ∈ Icc a b)
    (hm : PartitionedCovariance.mask (CoordinateAlgebra.D h) L q x ≠ 0) :
    normalizedSlow (CoordinateAlgebra.D h) L.1 x ∈ referenceCompact h a b := by
  apply subset_closure
  have hQ := ChartScales.Q_pos L.1
  have hQp : 0 < ChartScales.Q L.1 ^ CoordinateAlgebra.D h := Real.rpow_pos_of_pos hQ _
  rw [physicalMask_nativeMask] at hm
  have hd : q ∈ support (SquaredPartition.dyadicMask (L.1 : ℤ)) := (mul_ne_zero_iff.mp hm).1
  rw [SquaredPartition.dyadicMask_support, SquaredPartition.integerQ_nat] at hd
  have hqn : q / ChartScales.Q L.1 ∈ Icc (1 / 2 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hQ).mpr
      linarith [hd.1]
    · exact (div_le_iff₀ hQ).mpr hd.2.le
  have hs := SimilarityHomogeneity.forwardScalar_scale hQ (div_pos hq hQ) (2 * h)
    (x 1 / ChartScales.Q L.1 ^ CoordinateAlgebra.D h)
  have hD : (1 - 2 * h) / 2 = CoordinateAlgebra.D h := by
    unfold CoordinateAlgebra.D
    ring
  rw [hD, mul_div_cancel₀ _ hQp.ne', mul_div_cancel₀ _ hQ.ne', he] at hs
  have hnormeq : SimilarityCoordinates.forwardScalar (2 * h)
      (x 1 / ChartScales.Q L.1 ^ CoordinateAlgebra.D h) (q / ChartScales.Q L.1) =
      x 2 / ChartScales.Q L.1 := by
    apply (eq_div_iff hQ.ne').mpr
    nlinarith [hs]
  have hroot : (ChartScales.Q L.1 ^ (1 / 2 : ℝ)) ^ 2 = ChartScales.Q L.1 := by
    rw [← Real.rpow_mul_natCast hQ.le]
    norm_num
  have hratio : (x 0 / ChartScales.Q L.1 ^ (1 / 2 : ℝ)) ^ 2 /
      (2 * (q / ChartScales.Q L.1)) = x 0 ^ 2 / (2 * q) := by
    rw [div_pow, hroot]
    field_simp
  rw [normalizedSlow_coordinates]
  refine ⟨div_nonneg hR (Real.rpow_pos_of_pos hQ _).le, div_nonneg hT hQ.le,
    q / ChartScales.Q L.1, hqn, hnormeq, ?_⟩
  simpa only [hratio] using hX

theorem physicalMask_has_representative {h a b : ℝ} (L : Label) (hL : 1 ≤ L.1)
    {q : ℝ} {x : Position} (hq : 0 < q) (hR : 0 ≤ x 0) (hT : 0 ≤ x 2)
    (he : SimilarityCoordinates.forwardScalar (2 * h) (x 1) q = x 2)
    (hX : x 0 ^ 2 / (2 * q) ∈ Icc a b)
    (hm : PartitionedCovariance.mask (CoordinateAlgebra.D h) L q x ≠ 0) :
    ∃ A : ActiveLabel (referenceCompact h a b), A.val = L :=
  physicalMask_active (referenceCompact h a b) (CoordinateAlgebra.D h) L hL
    (physicalMask_normalized_mem L hq hR hT he hX hm) hm

/-! ## One target-direction parameter, with uniform mixed-point slack -/

/-- Target ratio, given by `|c0 F g * ⟪T, transverseDirection g⟫_ℝ / ⟪T, normalDirection g⟫_ℝ|`. -/
noncomputable def targetRatio (F : ℝ) (g T : Plane) : ℝ :=
  |c0 F g * ⟪T, transverseDirection g⟫_ℝ / ⟪T, normalDirection g⟫_ℝ|

/-- `T` is a continuous target direction, including at zero-amplitude edges. -/
structure TargetCone (F : ℝ) (g T : Plane) : Prop where
  inward : ⟪T, normalDirection g⟫_ℝ < 0
  ratio_lt_one : targetRatio F g T < 1

/-- Slope ratio, given by `u / Real.sqrt (1 + u ^ 2)`. -/
noncomputable def slopeRatio (u : ℝ) : ℝ := u / Real.sqrt (1 + u ^ 2)

theorem exists_slopeRatio_gt {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ u : ℝ, 0 < u ∧ r < slopeRatio u := by
  have hsq : 0 < 1 - r ^ 2 := by nlinarith
  let u := (Real.sqrt (1 - r ^ 2))⁻¹
  have hu : 0 < u := inv_pos.mpr (Real.sqrt_pos.mpr hsq)
  have hp : u ^ 2 * (1 - r ^ 2) = 1 := by
    dsimp [u]
    rw [inv_pow, Real.sq_sqrt hsq.le, inv_mul_cancel₀ hsq.ne']
  have hroot : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsquare : (r * Real.sqrt (1 + u ^ 2)) ^ 2 < u ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ 1 + u ^ 2 by positivity)]
    nlinarith
  refine ⟨u, hu, (lt_div_iff₀ hroot).mpr ?_⟩
  by_contra! hn
  have hbad := pow_le_pow_left₀ hu.le hn 2
  linarith

theorem slopeRatio_lt_one (u : ℝ) : slopeRatio u < 1 := by
  have hp : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  apply (div_lt_one hp).mpr
  have hs := Real.sq_sqrt (show 0 ≤ 1 + u ^ 2 by positivity)
  nlinarith [Real.sqrt_nonneg (1 + u ^ 2)]

theorem targetRatio_continuousOn {K : Set Slow} {F : Slow → ℝ} {g T : Slow → Plane}
    (hF : ContinuousOn F K) (hg : ContinuousOn g K) (hT : ContinuousOn T K)
    (hc : ∀ q ∈ K, ReferenceCone (F q) (g q))
    (ht : ∀ q ∈ K, TargetCone (F q) (g q) (T q)) :
    ContinuousOn (fun q => targetRatio (F q) (g q) (T q)) K := by
  have hn := normalDirection_continuousOn hg (fun q hq => (hc q hq).shear_ne_zero)
  have hk := transverseDirection_continuousOn hg (fun q hq => (hc q hq).shear_ne_zero)
  exact (((c0_continuousOn hF hg hc).mul (hT.inner hk)).div (hT.inner hn)
    (fun q hq => (ht q hq).inward.ne)).abs

theorem compact_target_choice {K : Set Slow} (hK : IsCompact K)
    {F : Slow → ℝ} {g T : Slow → Plane}
    (hF : ContinuousOn F K) (hg : ContinuousOn g K) (hT : ContinuousOn T K)
    (hc : ∀ q ∈ K, ReferenceCone (F q) (g q))
    (ht : ∀ q ∈ K, TargetCone (F q) (g q) (T q)) :
    ∃ u η : ℝ, 0 < u ∧ 0 < η ∧ ∀ q ∈ K,
      ⟪T q, normalDirection (g q)⟫_ℝ ≤ -η ∧
      targetRatio (F q) (g q) (T q) + η ≤ slopeRatio u := by
  have hn := normalDirection_continuousOn hg (fun q hq => (hc q hq).shear_ne_zero)
  obtain ⟨d, hd, hdb⟩ := UniformCone.positive_uniform_margin hK (hT.inner hn).fun_neg
    (fun q hq => neg_pos.mpr (ht q hq).inward)
  obtain ⟨e, he, heb⟩ := UniformCone.positive_uniform_margin hK
    (continuousOn_const.fun_sub (targetRatio_continuousOn hF hg hT hc ht))
    (fun q hq => sub_pos.mpr (ht q hq).ratio_lt_one)
  let r := 1 - min e (1 / 2)
  have hr : 0 ≤ r := by dsimp [r]; linarith [min_le_right e (1 / 2 : ℝ)]
  have hr1 : r < 1 := by dsimp [r]; linarith [lt_min he (by norm_num : (0 : ℝ) < 1 / 2)]
  obtain ⟨u, hu, hur⟩ := exists_slopeRatio_gt hr hr1
  let η := min d ((slopeRatio u - r) / 2)
  have hη : 0 < η := lt_min hd (half_pos (sub_pos.mpr hur))
  refine ⟨u, η, hu, hη, fun q hq => ?_⟩
  have hηd : η ≤ d := min_le_left _ _
  have hηr : η ≤ (slopeRatio u - r) / 2 := min_le_right _ _
  have hratio : targetRatio (F q) (g q) (T q) ≤ r := by
    dsimp [r]
    linarith [heb q hq, min_le_left e (1 / 2 : ℝ)]
  refine ⟨by linarith [hdb q hq], ?_⟩
  calc
    targetRatio (F q) (g q) (T q) + η ≤ r + (slopeRatio u - r) / 2 :=
      add_le_add hratio hηr
    _ ≤ r + (slopeRatio u - r) :=
      add_le_add_right (half_le_self (sub_pos.mpr hur).le) r
    _ = slopeRatio u := by ring

/-- A continuous positive diagonal on a compact set stays positive at
nearby pairs, with one distance independent of the base point. -/
theorem compact_diagonal_positive {K : Set Slow} (hK : IsCompact K)
    {f : Slow × Slow → ℝ} (hf : ContinuousOn f (K ×ˢ K))
    (hpos : ∀ q ∈ K, 0 < f (q, q)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q₀ ∈ K, ∀ q ∈ K, dist q q₀ < δ → 0 < f (q₀, q) := by
  have hd : ContinuousOn (fun q => f (q, q)) K :=
    hf.comp (continuous_id.prodMk continuous_id).continuousOn (fun _ hq => ⟨hq, hq⟩)
  obtain ⟨m, hm, hmb⟩ := UniformCone.positive_uniform_margin hK hd hpos
  obtain ⟨δ, hδ, hb⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod hK).uniformContinuousOn_of_continuous hf)
    (m / 2) (half_pos hm)
  refine ⟨δ, hδ, fun q₀ h₀ q hq hdist => ?_⟩
  have hp : dist (q₀, q) (q₀, q₀) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hdist
  have hh := hb (q₀, q) ⟨h₀, hq⟩ (q₀, q₀) ⟨h₀, h₀⟩ hp
  rw [Real.dist_eq] at hh
  have hlo := (abs_lt.mp hh).1
  linarith [hmb q₀ h₀]

theorem compact_mixed_target {K : Set Slow} (hK : IsCompact K)
    {F : Slow → ℝ} {g T : Slow → Plane}
    (hF : ContinuousOn F K) (hg : ContinuousOn g K) (hT : ContinuousOn T K)
    (hc : ∀ q ∈ K, ReferenceCone (F q) (g q))
    (ht : ∀ q ∈ K, TargetCone (F q) (g q) (T q)) :
    ∃ u δ : ℝ, 0 < u ∧ 0 < δ ∧ ∀ q₀ ∈ K, ∀ q ∈ K, dist q q₀ < δ →
      ⟪T q, normalDirection (g q₀)⟫_ℝ < 0 ∧
      |c0 (F q₀) (g q₀) * ⟪T q, transverseDirection (g q₀)⟫_ℝ /
        ⟪T q, normalDirection (g q₀)⟫_ℝ| < slopeRatio u := by
  obtain ⟨u, η, hu, hη, hb⟩ := compact_target_choice hK hF hg hT hc ht
  have hn : ContinuousOn (fun z : Slow × Slow => normalDirection (g z.1)) (K ×ˢ K) :=
    (normalDirection_continuousOn hg (fun q hq => (hc q hq).shear_ne_zero)).comp
    continuous_fst.continuousOn (fun _ hq => hq.1)
  have hk : ContinuousOn (fun z : Slow × Slow => transverseDirection (g z.1)) (K ×ˢ K) :=
    (transverseDirection_continuousOn hg (fun q hq => (hc q hq).shear_ne_zero)).comp
    continuous_fst.continuousOn (fun _ hq => hq.1)
  have hc0 : ContinuousOn (fun z : Slow × Slow => c0 (F z.1) (g z.1)) (K ×ˢ K) :=
    (c0_continuousOn hF hg hc).comp continuous_fst.continuousOn (fun _ hq => hq.1)
  have ht' : ContinuousOn (fun z : Slow × Slow => T z.2) (K ×ˢ K) :=
    hT.comp continuous_snd.continuousOn (fun _ hq => hq.2)
  let a : Slow × Slow → ℝ := fun z => -⟪T z.2, normalDirection (g z.1)⟫_ℝ
  let b : Slow × Slow → ℝ := fun z => slopeRatio u * a z -
    |c0 (F z.1) (g z.1) * ⟪T z.2, transverseDirection (g z.1)⟫_ℝ|
  have ha : ContinuousOn a (K ×ˢ K) := (ht'.inner hn).neg
  have hb' : ContinuousOn b (K ×ˢ K) :=
    (continuousOn_const.mul ha).sub (hc0.mul (ht'.inner hk)).abs
  obtain ⟨δa, hδa, hpa⟩ := compact_diagonal_positive hK ha
    (fun q hq => neg_pos.mpr (ht q hq).inward)
  have hbp : ∀ q ∈ K, 0 < b (q, q) := by
    intro q hq
    have hratio : targetRatio (F q) (g q) (T q) < slopeRatio u := by linarith [(hb q hq).2]
    rw [targetRatio, abs_div, abs_of_neg (ht q hq).inward] at hratio
    exact sub_pos.mpr ((div_lt_iff₀ (neg_pos.mpr (ht q hq).inward)).mp hratio)
  obtain ⟨δb, hδb, hpb⟩ := compact_diagonal_positive hK hb' hbp
  refine ⟨u, min δa δb, hu, lt_min hδa hδb, fun q₀ h₀ q hq hdist => ?_⟩
  have hneg : ⟪T q, normalDirection (g q₀)⟫_ℝ < 0 :=
    neg_pos.mp (hpa q₀ h₀ q hq (hdist.trans_le (min_le_left _ _)))
  refine ⟨hneg, ?_⟩
  rw [abs_div, abs_of_neg hneg]
  apply (div_lt_iff₀ (neg_pos.mpr hneg)).mpr
  exact sub_pos.mp (hpb q₀ h₀ q hq (hdist.trans_le (min_le_right _ _)))

/-- A single `u` works for the actual selected representatives and every
active target point in the enlarged boxes of all sufficiently fine labels. -/
theorem representative_target_choice {K : Set Slow} (hK : IsCompact K)
    {F : Slow → ℝ} {g T : Slow → Plane}
    (hF : ContinuousOn F K) (hg : ContinuousOn g K) (hT : ContinuousOn T K)
    (hc : ∀ q ∈ K, ReferenceCone (F q) (g q))
    (ht : ∀ q ∈ K, TargetCone (F q) (g q) (T q)) :
    ∃ u : ℝ, 0 < u ∧ ∃ N : ℕ, ∀ L : ActiveLabel K, N ≤ L.val.1 →
      ∀ q ∈ K, q ∈ gridBox L.val.1 L.val.2 2 →
      ⟪T q, normalDirection (g (representative K L))⟫_ℝ < 0 ∧
      |c0 (F (representative K L)) (g (representative K L)) *
        ⟪T q, transverseDirection (g (representative K L))⟫_ℝ /
        ⟪T q, normalDirection (g (representative K L))⟫_ℝ| < slopeRatio u := by
  obtain ⟨u, δ, hu, hδ, hb⟩ := compact_mixed_target hK hF hg hT hc ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 grid_mesh_tendsto_zero).2 δ hδ)
  refine ⟨u, hu, N, fun L hL q hq hbox => hb _ (representative_mem K L) q hq ?_⟩
  simpa only [dist_eq_norm] using
    (representative_enlarged_distance K L hbox).trans_lt (hN _ hL)

/-- The mixed-point cone has a positive numerical margin independent of
both points. The single selected `u` is strictly above the supremum. -/
theorem compact_mixed_target_margin {K : Set Slow} (hK : IsCompact K)
    {F : Slow → ℝ} {g T : Slow → Plane}
    (hF : ContinuousOn F K) (hg : ContinuousOn g K) (hT : ContinuousOn T K)
    (hc : ∀ q ∈ K, ReferenceCone (F q) (g q))
    (ht : ∀ q ∈ K, TargetCone (F q) (g q) (T q)) :
    ∃ u η δ : ℝ, 0 < u ∧ 0 < η ∧ 0 < δ ∧ ∀ q₀ ∈ K, ∀ q ∈ K, dist q q₀ < δ →
      ⟪T q, normalDirection (g q₀)⟫_ℝ ≤ -η ∧
      |c0 (F q₀) (g q₀) * ⟪T q, transverseDirection (g q₀)⟫_ℝ /
        ⟪T q, normalDirection (g q₀)⟫_ℝ| + η ≤ slopeRatio u := by
  obtain ⟨u₀, δ₀, hu₀, hδ₀, hbase⟩ := compact_mixed_target hK hF hg hT hc ht
  have hr₀ : 0 ≤ slopeRatio u₀ := div_nonneg hu₀.le (Real.sqrt_nonneg _)
  obtain ⟨u, hu, hgap⟩ := exists_slopeRatio_gt hr₀ (slopeRatio_lt_one u₀)
  have hn₀ := normalDirection_continuousOn hg (fun q hq => (hc q hq).shear_ne_zero)
  obtain ⟨m, hm, hmb⟩ := UniformCone.positive_uniform_margin hK (hT.inner hn₀).fun_neg
    (fun q hq => neg_pos.mpr (ht q hq).inward)
  have hn : ContinuousOn (fun z : Slow × Slow => normalDirection (g z.1)) (K ×ˢ K) :=
    hn₀.comp continuous_fst.continuousOn (fun _ hq => hq.1)
  have hT' : ContinuousOn (fun z : Slow × Slow => T z.2) (K ×ˢ K) :=
    hT.comp continuous_snd.continuousOn (fun _ hq => hq.2)
  have hcont : ContinuousOn (fun z : Slow × Slow =>
      -⟪T z.2, normalDirection (g z.1)⟫_ℝ - m / 2) (K ×ˢ K) :=
    (hT'.inner hn).neg.sub continuousOn_const
  obtain ⟨δ₁, hδ₁, hden⟩ := compact_diagonal_positive hK hcont
    (fun q hq => by dsimp only; linarith [hmb q hq])
  let η := min (m / 2) ((slopeRatio u - slopeRatio u₀) / 2)
  have hη : 0 < η := lt_min (half_pos hm) (half_pos (sub_pos.mpr hgap))
  refine ⟨u, η, min δ₀ δ₁, hu, hη, lt_min hδ₀ hδ₁, fun q₀ h₀ q hq hd => ?_⟩
  have hinner := hden q₀ h₀ q hq (hd.trans_le (min_le_right _ _))
  have hratio := (hbase q₀ h₀ q hq (hd.trans_le (min_le_left _ _))).2
  have hηm : η ≤ m / 2 := min_le_left _ _
  have hηgap : η ≤ (slopeRatio u - slopeRatio u₀) / 2 := min_le_right _ _
  refine ⟨by dsimp only at hinner; linarith, ?_⟩
  calc
    _ ≤ slopeRatio u₀ + (slopeRatio u - slopeRatio u₀) / 2 := add_le_add hratio.le hηgap
    _ ≤ slopeRatio u₀ + (slopeRatio u - slopeRatio u₀) :=
      add_le_add_right (half_le_self (sub_pos.mpr hgap).le) _
    _ = slopeRatio u := by ring

theorem representative_target_margin {K : Set Slow} (hK : IsCompact K)
    {F : Slow → ℝ} {g T : Slow → Plane}
    (hF : ContinuousOn F K) (hg : ContinuousOn g K) (hT : ContinuousOn T K)
    (hc : ∀ q ∈ K, ReferenceCone (F q) (g q))
    (ht : ∀ q ∈ K, TargetCone (F q) (g q) (T q)) :
    ∃ u η : ℝ, 0 < u ∧ 0 < η ∧ ∃ N : ℕ, ∀ L : ActiveLabel K, N ≤ L.val.1 →
      ∀ q ∈ K, q ∈ gridBox L.val.1 L.val.2 2 →
      ⟪T q, normalDirection (g (representative K L))⟫_ℝ ≤ -η ∧
      |c0 (F (representative K L)) (g (representative K L)) *
        ⟪T q, transverseDirection (g (representative K L))⟫_ℝ /
        ⟪T q, normalDirection (g (representative K L))⟫_ℝ| + η ≤ slopeRatio u := by
  obtain ⟨u, η, δ, hu, hη, hδ, hb⟩ := compact_mixed_target_margin hK hF hg hT hc ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 grid_mesh_tendsto_zero).2 δ hδ)
  refine ⟨u, η, hu, hη, N, fun L hL q hq hbox => hb _ (representative_mem K L) q hq ?_⟩
  simpa only [dist_eq_norm] using
    (representative_enlarged_distance K L hbox).trans_lt (hN _ hL)

theorem targetRatio_smul (F : ℝ) (g T : Plane) {a : ℝ} (ha : a ≠ 0) :
    targetRatio F g (a • T) = targetRatio F g T := by
  unfold targetRatio
  rw [real_inner_smul_left, real_inner_smul_left]
  congr 1
  rw [show c0 F g * (a * ⟪T, transverseDirection g⟫_ℝ) =
    a * (c0 F g * ⟪T, transverseDirection g⟫_ℝ) by ring]
  exact mul_div_mul_left _ _ ha

theorem TargetCone.pos_smul {F : ℝ} {g T : Plane} (h : TargetCone F g T)
    {a : ℝ} (ha : 0 < a) : TargetCone F g (a • T) := by
  refine ⟨?_, ?_⟩
  · rw [real_inner_smul_left]
    exact mul_neg_of_pos_of_neg ha h.inward
  · rw [targetRatio_smul F g T ha.ne']
    exact h.ratio_lt_one

end NavierStokes.PrimaryRepresentatives
