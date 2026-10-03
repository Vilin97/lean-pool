/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.CutoffSizes
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Basic
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Basic -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- The vector cutoff field used in coarse Caccioppoli, obtained by applying
the scalar cutoff gradient to the coordinate basis vectors. -/
def scalarCutoffGradientField {d : ℕ} (η : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => (fderiv ℝ η x) (basisVec i)

@[simp] theorem scalarCutoffGradientField_apply {d : ℕ} (η : Vec d → ℝ)
    (x : Vec d) (i : Fin d) :
    scalarCutoffGradientField η x i = (fderiv ℝ η x) (basisVec i) :=
  rfl

theorem support_scalarCutoffGradientField_subset_tsupport {d : ℕ}
    (η : Vec d → ℝ) :
    Function.support (scalarCutoffGradientField η) ⊆ tsupport η := by
  intro x hx
  exact (support_fderiv_subset (𝕜 := ℝ) (f := η)) <| by
    change fderiv ℝ η x ≠ 0
    intro hzero
    apply hx
    ext i
    simp [scalarCutoffGradientField, hzero]

theorem scalarCutoffGradientField_eq_zero_of_notMem_tsupport {d : ℕ}
    {η : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport η) :
    scalarCutoffGradientField η x = 0 := by
  by_contra hnonzero
  exact hx (support_scalarCutoffGradientField_subset_tsupport η hnonzero)

@[simp] theorem norm_basisVec {d : ℕ} (i : Fin d) :
    ‖basisVec i‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases h : j = i
    · subst h
      simp [basisVec]
    · simp [basisVec, h]
  · have hi : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

theorem norm_scalarCutoffGradientField_le_fderiv {d : ℕ} (η : Vec d → ℝ)
    (x : Vec d) :
    ‖scalarCutoffGradientField η x‖ ≤ ‖fderiv ℝ η x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro i
  calc
    ‖scalarCutoffGradientField η x i‖ = ‖(fderiv ℝ η x) (basisVec i)‖ := by
      rfl
    _ ≤ ‖fderiv ℝ η x‖ * ‖basisVec i‖ := by
      simpa using (fderiv ℝ η x).le_opNorm (basisVec i)
    _ = ‖fderiv ℝ η x‖ := by simp [norm_basisVec]

theorem continuous_scalarCutoffGradientField {d : ℕ} {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    Continuous (scalarCutoffGradientField η) := by
  refine continuous_pi ?_
  intro i
  simpa [scalarCutoffGradientField] using
    ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem contDiff_scalarCutoffGradientField_component {d : ℕ} {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => scalarCutoffGradientField η x i) := by
  simpa [scalarCutoffGradientField] using
    ((hη.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => basisVec i)))

theorem memLp_top_scalarCutoffGradientField_of_bound_on_cubeSet {d : ℕ}
    (Q : TriadicCube d) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) {Xi : ℝ}
    (hgrad : ∀ z ∈ cubeSet Q, ‖fderiv ℝ η z‖ ≤ Xi) :
    MeasureTheory.MemLp (scalarCutoffGradientField η) ∞ (normalizedCubeMeasure Q) := by
  have hcont : Continuous (scalarCutoffGradientField η) :=
    continuous_scalarCutoffGradientField hη
  have hbound_ae_cube :
      ∀ᵐ x ∂ cubeMeasure Q, ‖scalarCutoffGradientField η x‖ ≤ Xi := by
    exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
      Filter.Eventually.of_forall fun x hx =>
        le_trans (norm_scalarCutoffGradientField_le_fderiv η x) (hgrad x hx)
  have hbound_ae :
      ∀ᵐ x ∂ normalizedCubeMeasure Q, ‖scalarCutoffGradientField η x‖ ≤ Xi := by
    rw [MeasureTheory.ae_iff]
    rw [normalizedCubeMeasure, MeasureTheory.Measure.smul_apply]
    rw [(MeasureTheory.ae_iff).1 hbound_ae_cube]
    simp
  exact MeasureTheory.memLp_top_of_bound hcont.aestronglyMeasurable Xi hbound_ae

theorem cubeLpNorm_infty_scalarCutoffGradientField_le_of_bound_on_cubeSet {d : ℕ}
    (Q : TriadicCube d) {η : Vec d → ℝ} {Xi : ℝ} (hXi : 0 ≤ Xi)
    (hgrad : ∀ z ∈ cubeSet Q, ‖fderiv ℝ η z‖ ≤ Xi) :
    cubeLpNorm Q ∞ (scalarCutoffGradientField η) ≤ Xi := by
  apply cubeLpNorm_infty_le_of_bound_on_cubeSet Q (hC := hXi)
  intro x hx
  exact le_trans (norm_scalarCutoffGradientField_le_fderiv η x) (hgrad x hx)

theorem scaledClosedCubeSet_subset_openCubeSet_of_lt_one {d : ℕ}
    (Q : TriadicCube d) {ρ : ℝ} (hρ_nonneg : 0 ≤ ρ) (hρ_lt_one : ρ < 1) :
    scaledClosedCubeSet Q ρ ⊆ openCubeSet Q := by
  intro x hx
  rw [← ball_cubeCenter_eq_openCubeSet]
  have hxball :
      x ∈ Metric.closedBall (cubeCenter Q) (ρ * cubeRadius Q) :=
    scaledClosedCubeSet_subset_metricClosedBall Q hρ_nonneg hx
  have hr_lt : ρ * cubeRadius Q < cubeRadius Q := by
    have hrad : 0 < cubeRadius Q := cubeRadius_pos Q
    nlinarith
  exact Metric.closedBall_subset_ball hr_lt hxball

theorem scaledOpenCubeSet_subset_scaledClosedCubeSet_of_coord_lt {d : ℕ}
    (Q : TriadicCube d) (ρ : ℝ) :
    scaledOpenCubeSet Q ρ ⊆ scaledClosedCubeSet Q ρ := by
  intro x hx i
  exact le_of_lt (hx i)

private theorem quantitativeCutoff_isOpen_scaledOpenCubeSet {d : ℕ}
    (Q : TriadicCube d) (ρ : ℝ) :
    IsOpen (scaledOpenCubeSet Q ρ) := by
  rw [show scaledOpenCubeSet Q ρ =
      ⋂ i : Fin d, {x : Vec d | |x i - cubeCenter Q i| < ρ * cubeRadius Q} by
    ext x
    simp [scaledOpenCubeSet]]
  refine isOpen_iInter_of_finite ?_
  intro i
  exact isOpen_lt
    (continuous_abs.comp ((continuous_apply i).sub continuous_const))
    continuous_const

private theorem volume_scaledOpenCubeSet_toReal_of_nonneg {d : ℕ}
    (Q : TriadicCube d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (MeasureTheory.volume (scaledOpenCubeSet Q ρ)).toReal =
      (ρ * cubeScaleFactor Q) ^ d := by
  let a : Fin d → ℝ := fun i => cubeCenter Q i - ρ * cubeRadius Q
  let b : Fin d → ℝ := fun i => cubeCenter Q i + ρ * cubeRadius Q
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    nlinarith [hρ, cubeRadius_nonneg Q]
  rw [show scaledOpenCubeSet Q ρ =
      Set.pi Set.univ (fun i : Fin d => Set.Ioo (a i) (b i)) by
    ext x
    constructor
    · intro hx i _hi
      have hi := hx i
      rw [abs_lt] at hi
      constructor <;> dsimp [a, b] <;> linarith
    · intro hx i
      have hi := hx i (by simp)
      rw [abs_lt]
      constructor
      · dsimp [a, b] at hi
        linarith [hi.1]
      · dsimp [a, b] at hi
        linarith [hi.2]]
  have hside : ∀ i : Fin d, b i - a i = ρ * cubeScaleFactor Q := by
    intro i
    dsimp [a, b]
    rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
    ring
  calc
    (MeasureTheory.volume
        (Set.pi Set.univ (fun i : Fin d => Set.Ioo (a i) (b i)))).toReal =
        ∏ i : Fin d, (b i - a i) := by
          simpa [a, b] using Real.volume_pi_Ioo_toReal (ι := Fin d) hab
    _ = (ρ * cubeScaleFactor Q) ^ d := by
      calc
        ∏ i : Fin d, (b i - a i) =
            ∏ _i : Fin d, ρ * cubeScaleFactor Q := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          exact hside i
        _ = (ρ * cubeScaleFactor Q) ^ d := by
          simp

theorem QuantitativeCubeCutoff.tsupport_subset_scaledClosedCubeSet {d : ℕ}
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    tsupport η ⊆ scaledClosedCubeSet Q ρ₂ := by
  have hsupp :
      Function.support η ⊆ scaledClosedCubeSet Q ρ₂ :=
    η.support_subset.trans (scaledOpenCubeSet_subset_scaledClosedCubeSet_of_coord_lt Q ρ₂)
  simpa [tsupport] using
    closure_minimal hsupp (isClosed_scaledClosedCubeSet Q ρ₂)

theorem QuantitativeCubeCutoff.support_scalarCutoffGradientField_subset_scaledClosedCubeSet {d : ℕ}
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    Function.support (scalarCutoffGradientField (η : Vec d → ℝ)) ⊆ scaledClosedCubeSet Q ρ₂ :=
  (support_scalarCutoffGradientField_subset_tsupport (η : Vec d → ℝ)).trans
    η.tsupport_subset_scaledClosedCubeSet

theorem QuantitativeCubeCutoff.scalarCutoffGradientField_eq_zero_of_notMem_scaledClosedCubeSet
    {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {x : Vec d} (hx : x ∉ scaledClosedCubeSet Q ρ₂) :
    scalarCutoffGradientField (η : Vec d → ℝ) x = 0 := by
  exact scalarCutoffGradientField_eq_zero_of_notMem_tsupport
    (fun hx_support => hx (η.tsupport_subset_scaledClosedCubeSet hx_support))

/-- A descendant cube that touches a smaller scaled cube is contained in a
larger scaled cube, provided its side length fits in the radial buffer. -/
theorem cubeSet_subset_scaledClosedCubeSet_of_intersects_scaledClosedCubeSet_of_scaleFactor_le_gap
    {d : ℕ} {Q R : TriadicCube d} {ρinner ρouter : ℝ}
    (hgap : cubeScaleFactor R ≤ (ρouter - ρinner) * cubeRadius Q)
    (hinter : ∃ y ∈ cubeSet R, y ∈ scaledClosedCubeSet Q ρinner) :
    cubeSet R ⊆ scaledClosedCubeSet Q ρouter := by
  rcases hinter with ⟨y, hyR, hyinner⟩
  intro x hxR i
  have hxy_norm : ‖x - y‖ ≤ cubeScaleFactor R :=
    norm_sub_le_cubeScaleFactor_of_mem_cubeSet R hxR hyR
  have hxy_coord : |x i - y i| ≤ cubeScaleFactor R := by
    calc
      |x i - y i| = ‖(x - y) i‖ := by
        simp [Pi.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
      _ ≤ cubeScaleFactor R := hxy_norm
  have htri :
      |x i - cubeCenter Q i| ≤ |x i - y i| + |y i - cubeCenter Q i| := by
    have hdecomp :
        x i - cubeCenter Q i = (x i - y i) + (y i - cubeCenter Q i) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  calc
    |x i - cubeCenter Q i|
        ≤ |x i - y i| + |y i - cubeCenter Q i| := htri
    _ ≤ ρinner * cubeRadius Q + cubeScaleFactor R := by
          linarith [hxy_coord, hyinner i]
    _ ≤ ρinner * cubeRadius Q + (ρouter - ρinner) * cubeRadius Q := by
          linarith [hgap]
    _ = ρouter * cubeRadius Q := by ring

/-- The note's triadic gap scale makes depth-`j` descendants fit inside the
radial buffer, as soon as `j` dominates the chosen scale. -/
theorem cubeScaleFactor_le_gap_mul_cubeRadius_of_mem_descendantsAtDepth_of_triadicGapScaleChoice
    {d : ℕ} {Q R : TriadicCube d} {j k : ℕ} {ρinner ρouter : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρinner ρouter)
    (hkj : k ≤ j) :
    cubeScaleFactor R ≤ (ρouter - ρinner) * cubeRadius Q := by
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ j :=
    cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR
  have hQscale : cubeScaleFactor Q = 2 * cubeRadius Q := by
    unfold cubeRadius
    ring
  have hpow_le : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ j := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkj
  have hinv_le : ((3 : ℝ) ^ j)⁻¹ ≤ ((3 : ℝ) ^ k)⁻¹ := by
    have hpow_pos : 0 < (3 : ℝ) ^ k := by positivity
    simpa [one_div] using
      (one_div_le_one_div_of_le hpow_pos hpow_le)
  have hgap_nonneg : 0 ≤ ρouter - ρinner := by
    have hinv_pos : 0 < ((3 : ℝ) ^ k)⁻¹ := by positivity
    nlinarith [hchoice.2]
  have hsmall :
      2 * ((3 : ℝ) ^ j)⁻¹ ≤ ρouter - ρinner := by
    calc
      2 * ((3 : ℝ) ^ j)⁻¹
          ≤ 2 * ((3 : ℝ) ^ k)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv_le (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ 2 * ((1 / 27 : ℝ) * (ρouter - ρinner)) := by
            exact mul_le_mul_of_nonneg_left hchoice.2 (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ ρouter - ρinner := by
            nlinarith [hgap_nonneg]
  calc
    cubeScaleFactor R
        = cubeScaleFactor Q / (3 : ℝ) ^ j := hscale
    _ = (2 * ((3 : ℝ) ^ j)⁻¹) * cubeRadius Q := by
          rw [hQscale]
          ring
    _ ≤ (ρouter - ρinner) * cubeRadius Q := by
          exact mul_le_mul_of_nonneg_right hsmall (cubeRadius_nonneg Q)

/-- The midpoint cutoff leaves a half-gap buffer, and the note's triadic scale
still makes depth-`j` descendants fit inside that buffer. -/
theorem cubeScaleFactor_le_buffer_of_mem_descendantsAtDepth_of_triadicGapScaleChoice
    {d : ℕ} {Q R : TriadicCube d} {j k : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hkj : k ≤ j) :
    cubeScaleFactor R ≤
      (ρ₂ - coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) * cubeRadius Q := by
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ j :=
    cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR
  have hQscale : cubeScaleFactor Q = 2 * cubeRadius Q := by
    unfold cubeRadius
    ring
  have hpow_le : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ j := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkj
  have hinv_le : ((3 : ℝ) ^ j)⁻¹ ≤ ((3 : ℝ) ^ k)⁻¹ := by
    have hpow_pos : 0 < (3 : ℝ) ^ k := by positivity
    simpa [one_div] using
      (one_div_le_one_div_of_le hpow_pos hpow_le)
  have hgap_nonneg : 0 ≤ ρ₂ - ρ₁ := by
    have hinv_pos : 0 < ((3 : ℝ) ^ k)⁻¹ := by positivity
    nlinarith [hchoice.2]
  have hsmall :
      2 * ((3 : ℝ) ^ j)⁻¹ ≤ (ρ₂ - ρ₁) / 2 := by
    calc
      2 * ((3 : ℝ) ^ j)⁻¹
          ≤ 2 * ((3 : ℝ) ^ k)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv_le (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ 2 * ((1 / 27 : ℝ) * (ρ₂ - ρ₁)) := by
            exact mul_le_mul_of_nonneg_left hchoice.2 (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ (ρ₂ - ρ₁) / 2 := by
            nlinarith [hgap_nonneg]
  calc
    cubeScaleFactor R
        = cubeScaleFactor Q / (3 : ℝ) ^ j := hscale
    _ = (2 * ((3 : ℝ) ^ j)⁻¹) * cubeRadius Q := by
          rw [hQscale]
          ring
    _ ≤ ((ρ₂ - ρ₁) / 2) * cubeRadius Q := by
          exact mul_le_mul_of_nonneg_right hsmall (cubeRadius_nonneg Q)
    _ = (ρ₂ - coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) * cubeRadius Q := by
          rw [coarseCaccioppoliBufferedCutoffRadius_outer_gap]

/-- One extra descendant generation fits the midpoint buffer at the
`Q.scale - 1` local-patch scale. -/
theorem cubeScaleFactor_le_local_buffer_of_mem_descendantsAtDepth_succ_of_triadicGapScaleChoice
    {d : ℕ} {Q R : TriadicCube d} {j k : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q (j + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hkj : k ≤ j) :
    cubeScaleFactor R ≤
      (ρ₂ - coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) * (cubeRadius Q / 3) := by
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ (j + 1) :=
    cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR
  have hQscale : cubeScaleFactor Q = 2 * cubeRadius Q := by
    unfold cubeRadius
    ring
  have hpow_le : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ j := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkj
  have hinv_le : ((3 : ℝ) ^ j)⁻¹ ≤ ((3 : ℝ) ^ k)⁻¹ := by
    have hpow_pos : 0 < (3 : ℝ) ^ k := by positivity
    simpa [one_div] using
      (one_div_le_one_div_of_le hpow_pos hpow_le)
  have hgap_nonneg : 0 ≤ ρ₂ - ρ₁ := by
    have hinv_pos : 0 < ((3 : ℝ) ^ k)⁻¹ := by positivity
    nlinarith [hchoice.2]
  have hsmall :
      2 * ((3 : ℝ) ^ (j + 1))⁻¹ ≤ (ρ₂ - ρ₁) / 6 := by
    have hpow_succ :
        ((3 : ℝ) ^ (j + 1))⁻¹ = (3 : ℝ)⁻¹ * ((3 : ℝ) ^ j)⁻¹ := by
      rw [pow_succ']
      field_simp
    rw [hpow_succ]
    calc
      2 * ((3 : ℝ)⁻¹ * ((3 : ℝ) ^ j)⁻¹)
          = (2 * ((3 : ℝ) ^ j)⁻¹) / 3 := by ring
      _ ≤ (2 * ((3 : ℝ) ^ k)⁻¹) / 3 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hinv_le (by norm_num : (0 : ℝ) ≤ 2))
              (by norm_num : (0 : ℝ) ≤ 3)
      _ ≤ (2 * ((1 / 27 : ℝ) * (ρ₂ - ρ₁))) / 3 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hchoice.2 (by norm_num : (0 : ℝ) ≤ 2))
              (by norm_num : (0 : ℝ) ≤ 3)
      _ ≤ (ρ₂ - ρ₁) / 6 := by
            nlinarith [hgap_nonneg]
  calc
    cubeScaleFactor R
        = cubeScaleFactor Q / (3 : ℝ) ^ (j + 1) := hscale
    _ = (2 * ((3 : ℝ) ^ (j + 1))⁻¹) * cubeRadius Q := by
          rw [hQscale]
          ring
    _ ≤ ((ρ₂ - ρ₁) / 6) * cubeRadius Q := by
          exact mul_le_mul_of_nonneg_right hsmall (cubeRadius_nonneg Q)
    _ = (ρ₂ - coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) *
          (cubeRadius Q / 3) := by
          rw [coarseCaccioppoliBufferedCutoffRadius_outer_gap]
          ring

theorem QuantitativeCubeCutoff.tsupport_subset_openCubeSet_of_lt_one {d : ℕ}
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hρ₂_nonneg : 0 ≤ ρ₂) (hρ₂_lt_one : ρ₂ < 1) :
    tsupport η ⊆ openCubeSet Q := by
  exact (η.tsupport_subset_scaledClosedCubeSet).trans <|
    scaledClosedCubeSet_subset_openCubeSet_of_lt_one Q hρ₂_nonneg hρ₂_lt_one

theorem QuantitativeCubeCutoff.support_scalarCutoffGradientField_subset_openCubeSet_of_lt_one
    {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hρ₂_nonneg : 0 ≤ ρ₂) (hρ₂_lt_one : ρ₂ < 1) :
    Function.support (scalarCutoffGradientField (η : Vec d → ℝ)) ⊆ openCubeSet Q :=
  (support_scalarCutoffGradientField_subset_tsupport (η : Vec d → ℝ)).trans
    (η.tsupport_subset_openCubeSet_of_lt_one hρ₂_nonneg hρ₂_lt_one)

theorem QuantitativeCubeCutoff.scalarCutoffGradientField_eq_zero_of_notMem_openCubeSet_of_lt_one
    {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hρ₂_nonneg : 0 ≤ ρ₂) (hρ₂_lt_one : ρ₂ < 1) {x : Vec d}
    (hx : x ∉ openCubeSet Q) :
    scalarCutoffGradientField (η : Vec d → ℝ) x = 0 := by
  exact scalarCutoffGradientField_eq_zero_of_notMem_tsupport
    (fun hx_support => hx (η.tsupport_subset_openCubeSet_of_lt_one
      hρ₂_nonneg hρ₂_lt_one hx_support))

theorem quantitativeCubeCutoff_canonicalFun_tsupport_subset_openCubeSet {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₂_lt_one : ρ₂ < 1) :
    tsupport (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) ⊆ openCubeSet Q := by
  have htsupport :
      tsupport (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) ⊆ scaledClosedCubeSet Q ρ₂ := by
    simpa [QuantitativeCubeCutoff.canonicalFun] using
      (QuantitativeTransitionProfile.cubeCutoff_tsupport_subset_scaledClosedCubeSet
        smoothTransitionProfile.quantitativeProfile (Q := Q) hρ₁ hρ₁₂)
  exact htsupport.trans <|
    scaledClosedCubeSet_subset_openCubeSet_of_lt_one Q
      (le_of_lt (lt_trans hρ₁ hρ₁₂)) hρ₂_lt_one

/-- Canonical cube cutoff packaged as an `H10` test function on `openCubeSet Q`
whenever the outer cutoff radius stays strictly inside the cube. -/
noncomputable def quantitativeCubeCutoffCanonicalH10 {d : ℕ}
    (Q : TriadicCube d) (ρ₁ ρ₂ : ℝ)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₂_lt_one : ρ₂ < 1) :
    H10Function (openCubeSet Q) :=
  H10Function.ofContDiff (isOpen_openCubeSet Q)
    (QuantitativeCubeCutoff.canonicalFun_smooth Q hρ₁ hρ₁₂)
    (QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q hρ₁ hρ₁₂)
    (quantitativeCubeCutoff_canonicalFun_tsupport_subset_openCubeSet Q hρ₁ hρ₁₂ hρ₂_lt_one)

theorem cubeAverage_quantitativeCubeCutoff_canonicalFun_pos
    {d : ℕ} (Q : TriadicCube d) :
    0 < cubeAverage Q
      (QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_smooth Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hη_compact : HasCompactSupport η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hη_int : MeasureTheory.IntegrableOn η (cubeSet Q) MeasureTheory.volume :=
    (hη_smooth.continuous.integrable_of_hasCompactSupport hη_compact).integrableOn
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] η := by
    exact Filter.Eventually.of_forall fun x => by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_nonneg Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
  have hscaled_subset :
      scaledOpenCubeSet Q (1 / 2 : ℝ) ⊆ Function.support η ∩ cubeSet Q := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have hxclosed : x ∈ scaledClosedCubeSet Q (1 / 2 : ℝ) :=
        scaledOpenCubeSet_subset_scaledClosedCubeSet_of_coord_lt Q (1 / 2 : ℝ) hx
      have hone : η x = 1 := by
        simpa [η] using
          QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner
            (Q := Q) (ρ₁ := (1 / 2 : ℝ)) (ρ₂ := (3 / 4 : ℝ))
            (by norm_num : (0 : ℝ) < 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 3 / 4) hxclosed
      simp [Function.support, hone]
    · have hxclosed : x ∈ scaledClosedCubeSet Q (1 / 2 : ℝ) :=
        scaledOpenCubeSet_subset_scaledClosedCubeSet_of_coord_lt Q (1 / 2 : ℝ) hx
      have hxopen : x ∈ openCubeSet Q :=
        scaledClosedCubeSet_subset_openCubeSet_of_lt_one Q
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hxclosed
      exact openCubeSet_subset_cubeSet Q hxopen
  have hscaled_nonempty : (scaledOpenCubeSet Q (1 / 2 : ℝ)).Nonempty := by
    refine ⟨cubeCenter Q, ?_⟩
    intro i
    have hpos : 0 < (1 / 2 : ℝ) * cubeRadius Q := by
      nlinarith [cubeRadius_pos Q]
    simpa using hpos
  have hscaled_pos : 0 < MeasureTheory.volume (scaledOpenCubeSet Q (1 / 2 : ℝ)) :=
    (quantitativeCutoff_isOpen_scaledOpenCubeSet Q (1 / 2 : ℝ)).measure_pos
      MeasureTheory.volume hscaled_nonempty
  have hsupport_pos : 0 < MeasureTheory.volume (Function.support η ∩ cubeSet Q) :=
    lt_of_lt_of_le hscaled_pos (MeasureTheory.measure_mono hscaled_subset)
  have hint_pos : 0 < ∫ x in cubeSet Q, η x ∂MeasureTheory.volume :=
    (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonneg hη_int).2 hsupport_pos
  unfold cubeAverage
  exact mul_pos (inv_pos.mpr (cubeVolume_pos Q)) hint_pos

/-- The canonical cutoff has a dimension-only lower average: it is identically
one on the concentric half cube. -/
theorem half_pow_card_le_cubeAverage_quantitativeCubeCutoff_canonicalFun
    {d : ℕ} (Q : TriadicCube d) :
    (1 / 2 : ℝ) ^ d ≤
      cubeAverage Q
        (QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  let S : Set (Vec d) := scaledOpenCubeSet Q (1 / 2 : ℝ)
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_smooth Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hη_compact : HasCompactSupport η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hη_int : MeasureTheory.IntegrableOn η (cubeSet Q) MeasureTheory.volume :=
    (hη_smooth.continuous.integrable_of_hasCompactSupport hη_compact).integrableOn
  have hS_meas : MeasurableSet S :=
    (quantitativeCutoff_isOpen_scaledOpenCubeSet Q (1 / 2 : ℝ)).measurableSet
  have hS_sub : S ⊆ cubeSet Q := by
    intro x hx
    have hxclosed : x ∈ scaledClosedCubeSet Q (1 / 2 : ℝ) :=
      scaledOpenCubeSet_subset_scaledClosedCubeSet_of_coord_lt Q (1 / 2 : ℝ) hx
    have hxopen : x ∈ openCubeSet Q :=
      scaledClosedCubeSet_subset_openCubeSet_of_lt_one Q
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hxclosed
    exact openCubeSet_subset_cubeSet Q hxopen
  have hS_int :
      MeasureTheory.IntegrableOn (S.indicator (fun _ : Vec d => (1 : ℝ)))
        (cubeSet Q) MeasureTheory.volume := by
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : Vec d => (1 : ℝ))
          (cubeSet Q) MeasureTheory.volume :=
      MeasureTheory.integrableOn_const
        (μ := MeasureTheory.volume) (s := cubeSet Q) (C := (1 : ℝ))
        (volume_cubeSet_lt_top Q).ne
    exact hconst.indicator hS_meas
  have hpoint :
      ∀ x ∈ cubeSet Q,
        S.indicator (fun _ : Vec d => (1 : ℝ)) x ≤ η x := by
    intro x _hxQ
    by_cases hxS : x ∈ S
    · have hxclosed : x ∈ scaledClosedCubeSet Q (1 / 2 : ℝ) :=
        scaledOpenCubeSet_subset_scaledClosedCubeSet_of_coord_lt Q (1 / 2 : ℝ) hxS
      have hone : η x = 1 := by
        simpa [η] using
          QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner
            (Q := Q) (ρ₁ := (1 / 2 : ℝ)) (ρ₂ := (3 / 4 : ℝ))
            (by norm_num : (0 : ℝ) < 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 3 / 4) hxclosed
      simp [Set.indicator_of_mem hxS, hone]
    · have hnonneg : 0 ≤ η x := by
        simpa [η] using
          QuantitativeCubeCutoff.canonicalFun_nonneg Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
      simpa [Set.indicator_of_notMem hxS] using hnonneg
  have hmono :
      ∫ x in cubeSet Q, S.indicator (fun _ : Vec d => (1 : ℝ)) x ∂MeasureTheory.volume
        ≤ ∫ x in cubeSet Q, η x ∂MeasureTheory.volume :=
    MeasureTheory.setIntegral_mono_on hS_int hη_int (measurableSet_cubeSet Q) hpoint
  have hleft_eq :
      ∫ x in cubeSet Q, S.indicator (fun _ : Vec d => (1 : ℝ)) x ∂MeasureTheory.volume =
        (MeasureTheory.volume S).toReal := by
    rw [MeasureTheory.setIntegral_indicator hS_meas]
    have hinter : cubeSet Q ∩ S = S := Set.inter_eq_right.mpr hS_sub
    rw [hinter]
    simp [MeasureTheory.measureReal_def]
  have hS_vol :
      (MeasureTheory.volume S).toReal =
        ((1 / 2 : ℝ) * cubeScaleFactor Q) ^ d := by
    simpa [S] using
      volume_scaledOpenCubeSet_toReal_of_nonneg Q
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hratio :
      (cubeVolume Q)⁻¹ * ((1 / 2 : ℝ) * cubeScaleFactor Q) ^ d =
        (1 / 2 : ℝ) ^ d := by
    have hpow_ne : cubeScaleFactor Q ^ d ≠ 0 :=
      pow_ne_zero d hscale_pos.ne'
    simp [cubeVolume, mul_pow]
    field_simp [hpow_ne]
  unfold cubeAverage
  calc
    (1 / 2 : ℝ) ^ d =
        (cubeVolume Q)⁻¹ *
          ((1 / 2 : ℝ) * cubeScaleFactor Q) ^ d := hratio.symm
    _ =
        (cubeVolume Q)⁻¹ * (MeasureTheory.volume S).toReal := by
          rw [hS_vol]
    _ =
        (cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q,
            S.indicator (fun _ : Vec d => (1 : ℝ)) x ∂MeasureTheory.volume := by
          rw [hleft_eq]
    _ ≤
        (cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, η x ∂MeasureTheory.volume := by
          exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (cubeVolume_pos Q).le)

/-- The inverse average of the canonical cutoff is bounded by a
dimension-only constant. -/
theorem inv_cubeAverage_quantitativeCubeCutoff_canonicalFun_le_two_pow_card
    {d : ℕ} (Q : TriadicCube d) :
    (cubeAverage Q
      (QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)))⁻¹ ≤
      (2 : ℝ) ^ d := by
  let A : ℝ :=
    cubeAverage Q
      (QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ))
  have hApos : 0 < A := by
    simpa [A] using cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q
  have hhalf_pos : 0 < (1 / 2 : ℝ) ^ d := by positivity
  have hle : (1 / 2 : ℝ) ^ d ≤ A := by
    simpa [A] using half_pow_card_le_cubeAverage_quantitativeCubeCutoff_canonicalFun Q
  have hinv :
      A⁻¹ ≤ ((1 / 2 : ℝ) ^ d)⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le hhalf_pos hle
  have hpow :
      ((1 / 2 : ℝ) ^ d)⁻¹ = (2 : ℝ) ^ d := by
    calc
      ((1 / 2 : ℝ) ^ d)⁻¹ = ((1 / 2 : ℝ)⁻¹) ^ d := by
        rw [inv_pow]
      _ = (2 : ℝ) ^ d := by norm_num
  simpa [A, hpow] using hinv

theorem cubeAverage_normalized_quantitativeCubeCutoff_canonicalFun_eq_one
    {d : ℕ} (Q : TriadicCube d) :
    cubeAverage Q (fun x =>
      (cubeAverage Q (QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)))⁻¹ *
        QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ) x) = 1 := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  let A : ℝ := cubeAverage Q η
  have hpos : 0 < A := by
    simpa [A, η] using cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q
  change cubeAverage Q (fun x => A⁻¹ * η x) = 1
  unfold cubeAverage
  rw [MeasureTheory.integral_const_mul]
  calc
    (cubeVolume Q)⁻¹ * (A⁻¹ * ∫ (x : Vec d) in cubeSet Q, η x ∂MeasureTheory.volume)
        = A⁻¹ *
            ((cubeVolume Q)⁻¹ * ∫ (x : Vec d) in cubeSet Q, η x ∂MeasureTheory.volume) := by
              ring
    _ = A⁻¹ * A := by rfl
    _ = 1 := inv_mul_cancel₀ hpos.ne.symm

theorem normalized_quantitativeCubeCutoff_canonicalFun_basic_controls
    {d : ℕ} (Q : TriadicCube d) :
    let η : Vec d → ℝ :=
      QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
    let φ : Vec d → ℝ := fun x => (cubeAverage Q η)⁻¹ * η x
    cubeAverage Q φ = 1 ∧
    MeasureTheory.AEStronglyMeasurable φ (volumeMeasureOn (cubeSet Q)) ∧
    (∀ᵐ x ∂ volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ (cubeAverage Q η)⁻¹) ∧
    ContDiff ℝ (⊤ : ℕ∞) φ ∧
    HasCompactSupport φ ∧
    tsupport φ ⊆ openCubeSet Q := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  let A : ℝ := cubeAverage Q η
  let φ : Vec d → ℝ := fun x => A⁻¹ * η x
  have hpos : 0 < A := by
    simpa [A, η] using cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_smooth Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hη_compact : HasCompactSupport η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    simpa [φ, smul_eq_mul] using hη_smooth.const_smul A⁻¹
  have hφ_compact : HasCompactSupport φ := by
    have hmul : HasCompactSupport ((fun _ : Vec d => A⁻¹) * η) := hη_compact.mul_left
    simpa [φ, Pi.mul_apply] using! hmul
  have hφ_tsupport_subset : tsupport φ ⊆ tsupport η := by
    have hsupp : Function.support φ ⊆ tsupport η := by
      intro x hx
      have hηx : η x ≠ 0 := by
        intro hzero
        apply hx
        simp [φ, hzero]
      exact subset_closure hηx
    simpa [tsupport] using closure_minimal hsupp (isClosed_tsupport η)
  have hη_tsupport_subset : tsupport η ⊆ openCubeSet Q := by
    simpa [η] using
      quantitativeCubeCutoff_canonicalFun_tsupport_subset_openCubeSet Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
        (by norm_num : (3 / 4 : ℝ) < 1)
  have hbound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ A⁻¹ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hA_nonneg : 0 ≤ A⁻¹ := inv_nonneg.mpr (le_of_lt hpos)
    have hη_nonneg : 0 ≤ η x := by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_nonneg Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
    have hη_le : η x ≤ 1 := by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_le_one Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
    calc
      ‖φ x‖ = ‖A⁻¹‖ * ‖η x‖ := by simp [φ, norm_mul]
      _ = A⁻¹ * η x := by
            rw [Real.norm_eq_abs, abs_of_nonneg hA_nonneg,
              Real.norm_eq_abs, abs_of_nonneg hη_nonneg]
      _ ≤ A⁻¹ * 1 := mul_le_mul_of_nonneg_left hη_le hA_nonneg
      _ = A⁻¹ := by ring
  have hmean : cubeAverage Q φ = 1 := by
    simpa [φ, A, η] using cubeAverage_normalized_quantitativeCubeCutoff_canonicalFun_eq_one Q
  refine ⟨hmean, ?_, hbound, hφ_smooth, hφ_compact, ?_⟩
  · exact hφ_smooth.continuous.aestronglyMeasurable
  · exact hφ_tsupport_subset.trans hη_tsupport_subset

end

end Homogenization
