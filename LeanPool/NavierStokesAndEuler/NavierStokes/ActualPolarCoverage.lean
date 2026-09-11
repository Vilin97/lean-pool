/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformHarmonicInteraction
public import LeanPool.NavierStokesAndEuler.NavierStokes.DiagonalResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualPolarGraph
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpacetimeEndpoint
import LeanPool.NavierStokesAndEuler.NavierStokes.AnnularEndpoint
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual polar graph coverage of the nominal active annulus

The geometric hypotheses are the nominal closed active annulus and the strict
dyadic choice q ≤ Q n < 2 * q. Chart coverage is a conclusion. The native
open domain allows every positive radius and retains the actual slow region;
the smaller weighted strip is reached through its closure at radial endpoints.
-/

section

/-!
# Physical jets of the actual finite-state residual

The estimates are on genuine Fréchet derivatives.  Harmonic coefficients,
mean residuals and excluded errors are combined before the physical graph
restriction.  Phase regularity is needed only on coefficient support.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PhysicalResidualJetBounds

open Set Function Filter ProblemStatement WeightedClasses LabelSumBounds
open LocalPhysicalCopyBounds PhysicalWaveSum
open scoped Topology ContDiff BigOperators

/-- Point: an abbreviation for `PhysicalMeanJetBounds.Point`. -/
abbrev Point := PhysicalMeanJetBounds.Point
/-- Cylinder: an abbreviation for `Point × ℝ`. -/
abbrev Cylinder := Point × ℝ
/-- Components: an abbreviation for `Fin 3 → ℝ`. -/
abbrev Components := Fin 3 → ℝ

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

/-! ## Local harmonic calculus -/

/-- A constant shift of the phase costs nothing: only positive phase jets
are needed, even when the phase value itself is unbounded. -/
theorem character_positive_jet_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Φ : E → ℝ} {x : E} (hΦ : SmoothNear Φ x) (m : ℕ) {c B M : ℝ}
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (PhysicalGraphBounds.character c ∘ Φ) x‖ ≤
      (m.factorial : ℝ) * M ^ m * B ^ m := by
  obtain ⟨G, hG, he⟩ := hΦ.exists_global_germ
  have hec : PhysicalGraphBounds.character c ∘ Φ =ᶠ[𝓝 x]
      PhysicalGraphBounds.character c ∘ G := by
    filter_upwards [he] with y hy
    exact congrArg (PhysicalGraphBounds.character c) hy
  intro k hk
  rw [iteratedFDeriv_eq_of_eventuallyEq hec k]
  have hb := norm_iteratedFDeriv_comp_le (PhysicalGraphBounds.character_smooth c) hG
    (nat_le_infty k) x (C := M ^ m) (D := B)
    (fun i hi => by
      rw [PhysicalGraphBounds.norm_character_jet]
      exact (pow_le_pow_left₀ (abs_nonneg _) hc i).trans
        (pow_le_pow_right₀ hM (hi.trans hk)))
    (fun i hi hik => by
      rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
      exact (hΦb i hi (hik.trans hk)).trans (by
        simpa only [pow_one] using pow_le_pow_right₀ hB hi))
  apply hb.trans
  have hfac : (k.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hk
  exact mul_le_mul (mul_le_mul_of_nonneg_right hfac (by positivity))
    (pow_le_pow_right₀ hB hk) (by positivity) (by positivity)

theorem product_jet_bound_local {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {a b : E → ℂ} {x : E} (ha : SmoothNear a x) (hb : SmoothNear b x)
    {m k : ℕ} (hk : k ≤ m) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haB : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a x‖ ≤ A)
    (hbB : ∀ i ≤ m, ‖iteratedFDeriv ℝ i b x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => a y * b y) x‖ ≤ (2 : ℝ) ^ m * A * B := by
  obtain ⟨a', ha', hea⟩ := ha.exists_global_germ
  obtain ⟨b', hb', heb⟩ := hb.exists_global_germ
  have he : (fun y => a y * b y) =ᶠ[𝓝 x] (fun y => a' y * b' y) := hea.mul heb
  rw [iteratedFDeriv_eq_of_eventuallyEq he k]
  apply PhysicalGraphBounds.pointwise_product_jet_bound ha' hb' x hk hA hB
  · intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq hea i]
    exact haB i hi
  · intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq heb i]
    exact hbB i hi

theorem mode_jet_bound_local {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {a : E → ℂ} {Φ : E → ℝ} {x : E} (ha : SmoothNear a x) (hΦ : SmoothNear Φ x)
    (m : ℕ) {c A B M : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hM : 1 ≤ M) (hc : |c| ≤ M)
    (haB : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a x‖ ≤ A)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k
      (fun y => a y * PhysicalGraphBounds.character c (Φ y)) x‖ ≤
      (2 : ℝ) ^ m * A * ((m.factorial : ℝ) * M ^ m * B ^ m) := by
  have hchar : SmoothNear (PhysicalGraphBounds.character c ∘ Φ) x := by
    obtain ⟨U, hU, hx, hΦU⟩ := hΦ
    exact SmoothNear.of_open hU ((PhysicalGraphBounds.character_smooth c).comp_contDiffOn hΦU) hx
  intro k hk
  exact product_jet_bound_local ha hchar hk hA (by positivity) haB
    (character_positive_jet_bound hΦ m hB hM hc hΦb)

/-! ## Actual residual reconstruction and Cartesian scaling -/

/-- Vector map as an element of `Components →L[ℝ] Space`. -/
noncomputable def vectorMap : Components →L[ℝ] Space :=
  (ContinuousLinearMap.proj (0 : Fin 3)).smulRight (coordinateVector 0) +
    (ContinuousLinearMap.proj (1 : Fin 3)).smulRight (coordinateVector 1) +
    (ContinuousLinearMap.proj (2 : Fin 3)).smulRight (coordinateVector 2)

@[simp] theorem vectorMap_apply (v : Components) (i : Fin 3) : vectorMap v i = v i := by
  fin_cases i <;> simp [vectorMap, coordinateVector]

/-- Residual degree, given by `2 * CoordinateAlgebra.A h + 1 / 2`. -/
noncomputable def residualDegree (h : ℝ) : ℝ := 2 * CoordinateAlgebra.A h + 1 / 2

/-- Invert the actual residual scaling and cylindrical frame. -/
theorem physical_vector_of_components {Q : ℝ} (hQ : 0 < Q) (h θ : ℝ)
    (a : Components) (R : Space)
    (ha : ∀ i, a i = Q ^ residualDegree h * CylindricalResidual.frame (-θ) R i) :
    R = Q ^ (-residualDegree h) • CylindricalResidual.frame θ (vectorMap a) := by
  have he : vectorMap a = Q ^ residualDegree h • CylindricalResidual.frame (-θ) R := by
    ext i
    simpa only [vectorMap_apply, PiLp.smul_apply, smul_eq_mul] using ha i
  rw [he, map_smul, CylindricalResidual.frame_inverse', smul_smul,
    ← Real.rpow_add hQ]
  simp

theorem state_fullResidual_reconstructed {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : CorrectionState.Context D} {s : CorrectionState.State D} {labels : ℕ → Finset ι}
    {b : ι → CorrectionState.HarmonicBlock D} {G A : ι → HarmonicResidual.BlockCoefficients D}
    (hrep : HarmonicResidual.BlockRepresentation labels b G A s)
    (hmean : LiftedMeanResidual.MeanHypotheses U c s) {n : ℕ}
    (hreg : HarmonicResidual.ExtractionRegular U c s labels b G A n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    LiftedMeanResidual.fullResidual c s n x i =
      (∑ l ∈ labels n, (HarmonicResidual.residualBlock c s (b l) (G l) (A l)).oscillation n x i) +
      s.meanGoodResidual c n x.1 i + s.errors.total n x i := by
  change HarmonicResidual.stateFullResidual c s n x i = _
  rw [HarmonicResidual.stateFullResidual_reconstructed hU hrep hreg hx i,
    HarmonicResidual.stateMeanCoefficientValue_eq_average hU hrep hreg hx.1 i]
  congr 1
  congr 1
  exact LiftedMeanResidual.angularMean_fullGoodResidual hmean n hx.1 i

/-! ## The actual polar common graph and rotating Cartesian basis -/

/-- Polar assoc, bundling `toFun`, `invFun`, `left_inv`, `right_inv` and the required
compatibility proofs. -/
noncomputable def polarAssoc :
    (PhysicalGraphBounds.Plane × ((ℝ × ℝ) × PhysicalGraphBounds.Plane)) ≃ₗᵢ[ℝ] Cylinder where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change max (max ‖x.1.1‖ ‖x.2‖) ‖x.1.2‖ = max (max ‖x.1.1‖ ‖x.1.2‖) ‖x.2‖
    simp only [Prod.norm_def]
    ac_rfl

/-- Polar lift, given by `polarAssoc (PolarCharts.chart a j (PhysicalGraphBounds.liftXY x),
PhysicalClassBounds.slowFast x)`. -/
noncomputable def polarLift (a : ℝ) (j : PolarCharts.Index) (x : LiftPoint) : Cylinder :=
  polarAssoc (PolarCharts.chart a j (PhysicalGraphBounds.liftXY x), PhysicalClassBounds.slowFast x)

/-- Polar graph, given by `polarLift a j ∘ commonLift h n d`. -/
noncomputable def polarGraph (a h : ℝ) (j : PolarCharts.Index) (n d : ℕ) : SpaceTime → Cylinder :=
  polarLift a j ∘ commonLift h n d

theorem polarLift_smooth {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) :
    ContDiff ℝ ∞ (polarLift a j) :=
  polarAssoc.toContinuousLinearEquiv.contDiff.comp
    (((PolarCharts.chart_contDiff ha j).comp PhysicalGraphBounds.liftXY.contDiff).prodMk
      PhysicalClassBounds.slowFast.contDiff)

theorem polarLift_positiveJets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : PolarCharts.Index, ∀ x : LiftPoint,
      PhysicalGraphBounds.liftXY x ∈ Metric.closedBall 0 b → ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (polarLift a j) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  refine ⟨B, hB, ?_⟩
  intro j x hx k hk hkm
  have hc := PhysicalGraphBounds.jet_comp_linear_bound (PolarCharts.chart_contDiff ha j)
    PhysicalGraphBounds.liftXY PhysicalGraphBounds.norm_liftXY_le x (zero_le_one.trans hB) m
    (fun i hi => hb j i hi _ hx) k hkm
  have hpair : ‖iteratedFDeriv ℝ k
      (fun y : LiftPoint => (PolarCharts.chart a j (PhysicalGraphBounds.liftXY y),
        PhysicalClassBounds.slowFast y)) x‖ ≤ B := by
    change ‖iteratedFDeriv ℝ k (fun y =>
      ((PolarCharts.chart a j ∘ PhysicalGraphBounds.liftXY) y, PhysicalClassBounds.slowFast y)) x‖
          ≤ B
    rw [PhysicalGraphBounds.iteratedFDeriv_pair
      (((PolarCharts.chart_contDiff ha j).comp PhysicalGraphBounds.liftXY.contDiff).contDiffAt.of_le
        (nat_le_infty k)) (PhysicalClassBounds.slowFast.contDiff.contDiffAt.of_le (nat_le_infty k)),
      ContinuousMultilinearMap.opNorm_prod]
    exact max_le hc ((PhysicalGraphBounds.norm_positive_jet_linear_le
      PhysicalClassBounds.slowFast x hk).trans (PhysicalClassBounds.norm_slowFast_le.trans hB))
  have hnorm : ‖polarAssoc.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖polarAssoc y‖ ≤ 1 * ‖y‖
    rw [polarAssoc.norm_map, one_mul]
  have he := norm_jet_linear_comp_at (w := x)
    ((((PolarCharts.chart_contDiff ha j).comp PhysicalGraphBounds.liftXY.contDiff).prodMk
      PhysicalClassBounds.slowFast.contDiff).contDiffAt.of_le (nat_le_infty k))
    polarAssoc.toContinuousLinearEquiv.toContinuousLinearMap
  change ‖iteratedFDeriv ℝ k
    (polarAssoc.toContinuousLinearEquiv.toContinuousLinearMap ∘
      (fun y : LiftPoint => (PolarCharts.chart a j (PhysicalGraphBounds.liftXY y),
        PhysicalClassBounds.slowFast y))) x‖ ≤ B
  exact he.trans ((mul_le_mul hnorm hpair (norm_nonneg _) zero_le_one).trans_eq (one_mul B))

/-- Rotation base, given by `(CylindricalResidual.frame (PolarCharts.chart a j x).2).comp
vectorMap`. -/
noncomputable def rotationBase (a : ℝ) (j : PolarCharts.Index) (x : PhysicalGraphBounds.Plane) :
    Components →L[ℝ] Space :=
  (CylindricalResidual.frame (PolarCharts.chart a j x).2).comp vectorMap

theorem rotationBase_smooth {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) :
    ContDiff ℝ ∞ (rotationBase a j) :=
  (CylindricalResidual.contDiff_frame.comp (PolarCharts.chart_contDiff ha j).snd).clm_comp
      contDiff_const

theorem finite_compact_jet_bound {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ι → E → F} {U K : Set E} (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i k, k ≤ m → ∀ x ∈ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C := by
  classical
  let := Fintype.ofFinite ι
  choose C hC hb using fun i => PhysicalGraphBounds.compact_jet_bound hU (hf i) hK hKU m
  refine ⟨1 + ∑ i, |C i|, ?_, ?_⟩
  · have hsum : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg (C i))
    linarith
  · intro i k hk x hx
    have hi : |C i| ≤ ∑ j, |C j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)
    exact (hb i k hk x hx).trans ((le_abs_self (C i)).trans (by linarith))

theorem rotationLift_jet_bound {a : ℝ} (ha : 0 < a) (b : ℝ) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : PolarCharts.Index, ∀ x : LiftPoint,
      PhysicalGraphBounds.liftXY x ∈ Metric.closedBall 0 b → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (rotationBase a j ∘ PhysicalGraphBounds.liftXY) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := finite_compact_jet_bound isOpen_univ
    (fun j => (rotationBase_smooth ha j).contDiffOn) (isCompact_closedBall 0 b)
    (subset_univ _) m
  refine ⟨B, hB, ?_⟩
  intro j x hx k hk
  exact PhysicalGraphBounds.jet_comp_linear_bound (rotationBase_smooth ha j)
    PhysicalGraphBounds.liftXY PhysicalGraphBounds.norm_liftXY_le x (zero_le_one.trans hB) m
    (fun i hi => hb j i hi _ hx) k hk

theorem clm_apply_jet_bound {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : D → E →L[ℝ] F} {g : D → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : D) {m k : ℕ} (hk : k ≤ m) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => f y (g y)) x‖ ≤ (2 : ℝ) ^ m * A * B := by
  apply (norm_iteratedFDeriv_clm_apply hf hg x (nat_le_infty k)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfa i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk))
          (Nat.cast_nonneg _))
        (hgb (k - i) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ k * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ (2 : ℝ) ^ m * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hA) hB

/-- The Cartesian reconstruction keeps the exact residual degree and
the actual rotating basis, before any derivative estimate is applied. -/
noncomputable def cartesianPull (a h : ℝ) (j : PolarCharts.Index) (n d : ℕ)
    (degree : ℝ) (F : Cylinder → Components) : SpaceTime → Space := fun w =>
  ChartScales.Q n ^ (-degree) •
    rotationBase a j (PhysicalGraphBounds.scaledRadial n w) (F (polarGraph a h j n d w))

/-- The actual angular graph and Cartesian basis add only an order-dependent
constant. The displayed loss retains the exact physical scaling degree. -/
theorem cartesianPull_jet_bound {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ j : PolarCharts.Index, ∀ F : Cylinder → Components, SmoothNear F (polarGraph a h j n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F (polarGraph a h j n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (cartesianPull a h j n d degree F) w‖ ≤
        C * q ^ (gain - PhysicalMeanJetBounds.loss degree m) := by
  obtain ⟨B, hB, hBj⟩ := polarLift_positiveJets (b := b) ha m
  obtain ⟨V, hV, hVj⟩ := rotationLift_jet_bound ha b m
  let A' : ℝ := (2 : ℝ) ^ m * V * ((m.factorial : ℝ) * A * B ^ m)
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  obtain ⟨C, hC, hb⟩ := PhysicalMeanJetBounds.common_stripped_physical_bound_local
    (E := Space) (b := b) hh hh1 ha Δ m (gain - degree) e A' hA'
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi j F hF hjet
  obtain ⟨F', hF', he⟩ := hF.exists_global_germ
  have hx : PhysicalGraphBounds.liftXY (commonLift h n d w) ∈ Metric.closedBall 0 b := by
    rw [PhysicalClassBounds.liftXY_commonLift]
    exact hann.1
  let r := rotationBase a j ∘ PhysicalGraphBounds.liftXY
  let f := F' ∘ polarLift a j
  have hr : ContDiff ℝ ∞ r := (rotationBase_smooth ha j).comp PhysicalGraphBounds.liftXY.contDiff
  have hf : ContDiff ℝ ∞ f := hF'.comp (polarLift_smooth ha j)
  let u : LiftPoint → Space := fun y => ChartScales.Q n ^ (-degree) • r y (f y)
  have hu : ContDiff ℝ ∞ u := (hr.clm_apply hf).const_smul _
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha
      hann)
  have hgraph : ContinuousAt (polarGraph a h j n d) w :=
    (polarLift_smooth ha j).continuous.continuousAt.comp (commonLift_smoothAt h n d
        haxis).continuousAt
  have he' : cartesianPull a h j n d degree F =ᶠ[𝓝 w] u ∘ commonLift h n d := by
    filter_upwards [he.comp_tendsto hgraph] with z hz
    change ChartScales.Q n ^ (-degree) •
        rotationBase a j (PhysicalGraphBounds.scaledRadial n z) (F (polarGraph a h j n d z)) =
      ChartScales.Q n ^ (-degree) •
        rotationBase a j (PhysicalGraphBounds.liftXY (commonLift h n d z))
          (F' (polarGraph a h j n d z))
    rw [PhysicalClassBounds.liftXY_commonLift]
    exact congrArg (fun v => ChartScales.Q n ^ (-degree) •
      rotationBase a j (PhysicalGraphBounds.scaledRadial n z) v) hz
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  have hab : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by positivity
  have hFjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F' (polarGraph a h j n d w)‖ ≤
      A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by
    intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hjet i hi
  have hcomp := PhysicalClassBounds.composition_jet_bound hF' isOpen_univ
    (polarLift_smooth ha j).contDiffOn (mem_univ (commonLift h n d w)) m hab hB hFjet
    (hBj j _ hx)
  have huc : ∀ i ≤ m, ‖iteratedFDeriv ℝ i u (commonLift h n d w)‖ ≤
      A' * ChartScales.Q n ^ (gain - degree) * ChartScales.S n ^ e := by
    intro i hi
    change ‖iteratedFDeriv ℝ i (fun y => ChartScales.Q n ^ (-degree) • r y (f y))
      (commonLift h n d w)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hr.clm_apply hf).contDiffAt.of_le (nat_le_infty i)),
      norm_smul (ChartScales.Q n ^ (-degree))
        (iteratedFDeriv ℝ i (fun x => r x (f x)) (commonLift h n d w)),
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hQ _).le]
    have hp := clm_apply_jet_bound hr hf (commonLift h n d w) hi (zero_le_one.trans hV)
      (by positivity : 0 ≤ (m.factorial : ℝ) *
        (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m)
      (hVj j _ hx) hcomp
    calc
      _ ≤ ChartScales.Q n ^ (-degree) * ((2 : ℝ) ^ m * V * ((m.factorial : ℝ) *
          (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m)) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hQ _).le
      _ = _ := by dsimp [A']; rw [Real.rpow_sub hQ, Real.rpow_neg hQ.le]; ring
  have hout := hb n hn d hd w hann ht q hq hlo hhi u (SmoothNear.of_open isOpen_univ hu.contDiffOn
    (mem_univ _)) huc
  convert! hout using 1
  congr 2
  unfold PhysicalMeanJetBounds.loss
  ring

/-! ## Uniform native jets and support-local harmonic synthesis -/

theorem finite_pi_iteratedFDeriv_norm_le
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {f : E → ι → ℝ} {x : E} {m : ℕ} {C : ℝ}
    (hf : ContDiffAt ℝ m f x) (hC : 0 ≤ C)
    (hb : ∀ i, ‖iteratedFDeriv ℝ m (fun y => f y i) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg hC (Finset.prod_nonneg (fun i _ => norm_nonneg (v i))))).2
  intro i
  have he := (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left hf le_rfl
  have hev := congrArg (fun T => T v) he
  change (iteratedFDeriv ℝ m (fun y => f y i) x) v =
    (iteratedFDeriv ℝ m f x v) i at hev
  rw [← hev]
  exact ContinuousMultilinearMap.le_of_opNorm_le (hb i) v

/-- Constants are chosen before the label and band. `loss` is allowed to
depend on the derivative order; it never depends on the correction stage. -/
structure NativeBounds {D E ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (U : Set D) (gain : ℝ) (loss : ℕ → ℝ) (f : ι → ℕ → D → E) : Prop where
  smooth : ∀ l n, N ≤ n → ContDiffOn ℝ ∞ (f l n) U
  bounds : ∀ m, ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n, N ≤ n → ∀ x ∈ U, ∀ j ≤ m,
    ‖iteratedFDeriv ℝ j (f l n) x‖ ≤ A * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ p

namespace NativeBounds

variable {D : Type} {E F ι κ : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : ℕ} {U : Set D} {gain : ℝ} {loss : ℕ → ℝ} {f g : ι → ℕ → D → E}

theorem zero : NativeBounds N U gain loss (fun (_ : ι) _ _ => (0 : E)) := by
  refine ⟨fun _ _ _ => contDiffOn_const, fun m => ⟨0, le_rfl, 0, ?_⟩⟩
  intros
  simp [iteratedFDeriv_fun_zero]

theorem reindex (hf : NativeBounds N U gain loss f) (a : κ → ι) :
    NativeBounds N U gain loss (fun l => f (a l)) := by
  refine ⟨fun l => hf.smooth (a l), ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  exact ⟨A, hA, p, fun l => hb (a l)⟩

theorem map (hf : NativeBounds N U gain loss f) (hU : IsOpen U) (L : E →L[ℝ] F) :
    NativeBounds N U gain loss (fun l n x => L (f l n x)) := by
  refine ⟨fun l n hn => (hf.smooth l n hn).continuousLinearMap_comp L, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  refine ⟨‖L‖ * A, mul_nonneg (norm_nonneg _) hA, p, ?_⟩
  intro l n hn x hx j hj
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f l n) x‖ :=
      norm_jet_linear_comp_at (((hf.smooth l n hn).contDiffAt (hU.mem_nhds hx)).of_le
        (nat_le_infty j)) L
    _ ≤ ‖L‖ * (A * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ p) :=
      mul_le_mul_of_nonneg_left (hb l n hn x hx j hj) (norm_nonneg _)
    _ = _ := by ring

theorem add (hN : 1 ≤ N) (hU : IsOpen U) (hf : NativeBounds N U gain loss f)
    (hg : NativeBounds N U gain loss g) :
    NativeBounds N U gain loss (fun l n x => f l n x + g l n x) := by
  refine ⟨fun l n hn => (hf.smooth l n hn).add (hg.smooth l n hn), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hg.bounds m
  refine ⟨A + B, add_nonneg hA hB, p + q, ?_⟩
  intro l n hn x hx j hj
  have hS := PhysicalGraphBounds.S_ge_one (hN.trans hn)
  have hQ : 0 ≤ ChartScales.Q n ^ (gain - loss m) := Real.rpow_pos_of_pos (ChartScales.Q_pos n) _
      |>.le
  rw [fun_iteratedFDeriv_add_apply
    (((hf.smooth l n hn).contDiffAt (hU.mem_nhds hx)).of_le (nat_le_infty j))
    (((hg.smooth l n hn).contDiffAt (hU.mem_nhds hx)).of_le (nat_le_infty j))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f l n) x‖ + ‖iteratedFDeriv ℝ j (g l n) x‖ := norm_add_le _ _
    _ ≤ A * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ p +
        B * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ q :=
      add_le_add (ha l n hn x hx j hj) (hb l n hn x hx j hj)
    _ ≤ A * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ (p + q) +
        B * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ (p + q) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS (Nat.le_add_right p q)) (mul_nonneg hA hQ))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS (Nat.le_add_left q p)) (mul_nonneg hB hQ))
    _ = _ := by ring

theorem sum (hN : 1 ≤ N) (hU : IsOpen U) (K : Finset κ) (a : κ → ι → ℕ → D → E)
    (ha : ∀ k ∈ K, NativeBounds N U gain loss (a k)) :
    NativeBounds N U gain loss (fun l n x => ∑ k ∈ K, a k l n x) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using (zero : NativeBounds N U gain loss (fun (_ : ι) _ _ => (0
          : E)))
  | @insert k K hk ih =>
    simpa only [Finset.sum_insert hk] using
      (ha k (Finset.mem_insert_self _ _)).add hN hU
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem congr (hU : IsOpen U) (hf : NativeBounds N U gain loss f)
    (hfg : ∀ l n, N ≤ n → EqOn (f l n) (g l n) U) : NativeBounds N U gain loss g := by
  refine ⟨fun l n hn => (hf.smooth l n hn).congr (fun x hx => (hfg l n hn hx).symm), ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  refine ⟨A, hA, p, ?_⟩
  intro l n hn x hx j hj
  rw [← iteratedFDeriv_eq_of_eventuallyEq
    (eventually_of_mem (hU.mem_nhds hx) (hfg l n hn)) j]
  exact hb l n hn x hx j hj

theorem weaken (hN : 1 ≤ N) (hf : NativeBounds N U gain loss f)
    {gain' : ℝ} {loss' : ℕ → ℝ} (he : ∀ m, gain' - loss' m ≤ gain - loss m) :
    NativeBounds N U gain' loss' f := by
  refine ⟨hf.smooth, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  refine ⟨A, hA, p, ?_⟩
  intro l n hn x hx j hj
  exact (hb l n hn x hx j hj).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n)
        (ChartScales.Q_le_one n) (he m)) hA)
    (pow_nonneg (le_trans zero_le_one (PhysicalGraphBounds.S_ge_one (hN.trans hn))) p))

/-- Genuine edge extensions retain the interior weighted estimate on the
closure; outside that closure the actual zero germ is used. -/
theorem of_localSource {D' E' : Type} [NormedAddCommGroup D'] [NormedSpace ℝ D']
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {s : StripData D'} {h α : ℝ} {w : ι → ℕ → D' → ℝ} {a : ι → ℕ → D' → E'}
    {V : Set D'} (hN : 4 ≤ N) (hV : IsOpen V)
    (ha : LocalSourceBounds (E := E') s h α w a)
    (hsm : ∀ l n, N ≤ n → ContDiffOn ℝ ∞ (a l n) V)
    (hcover : ∀ l n, N ≤ n → ∀ x ∈ V, x ∈ closure s.domain ∨ x ∉ tsupport (a l n)) :
    NativeBounds N V (h * α) (fun _ => 0) a := by
  refine ⟨hsm, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := ha.chart_bound m
  refine ⟨A, hA, p, ?_⟩
  intro l n hn x hx j hj
  simp only [sub_zero]
  rcases hcover l n hn x hx with hc | hz
  · exact jet_bound_at_closure ((hsm l n hn).contDiffAt (hV.mem_nhds hx)) hc j
      (fun y hy => hb l n (hN.trans hn) y hy j hj)
  · rw [jet_zero_off_tsupport _ _ hz, norm_zero]
    have hQ := ChartScales.Q_pos n
    have hS := ChartScales.S_pos (show 1 ≤ n by omega)
    positivity

/-- Closed label windows, not the size of the active finite set, control
the spatial sum. The constant multiplier is the proved overlap `2250`. -/
theorem window_sum (hU : IsOpen U) (hf : NativeBounds N U gain loss f)
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, N ≤ n → Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n, N ≤ n → ∀ l ∈ labels n, 1 ≤ (label n l).1)
    (d : ℝ) (χ : ℕ → D → WindowPoint) (hχ : ∀ n, N ≤ n → ContinuousOn (χ n) U)
    (hs : ∀ n, N ≤ n → ∀ l ∈ labels n, ∀ x ∈ U,
      f l n x ≠ 0 → χ n x ∈ closedWindow d (label n l)) :
    NativeBounds N U gain loss (fun (_ : Unit) n x => ∑ l ∈ labels n, f l n x) := by
  refine ⟨fun _ n hn => ContDiffOn.sum (fun l _ => hf.smooth l n hn), ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  refine ⟨2250 * A, by positivity, p, ?_⟩
  intro _ n hn x hx j hj
  have hQ := ChartScales.Q_pos n
  have hS : 0 ≤ ChartScales.S n := by unfold ChartScales.S; positivity
  have h := LabelSumBounds.finite_sum_jet_bound hU hx (labels n) (label n) (hinj n hn)
    (hlevel n hn) d (χ n) ((hχ n hn).continuousAt (hU.mem_nhds hx)) (fun l => f l n) j
    (fun l _ => ((hf.smooth l n hn).contDiffAt (hU.mem_nhds hx)).of_le (nat_le_infty j))
    (hs n hn) (by positivity : 0 ≤ A * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ p)
    (fun l _ _ => hb l n hn x hx j hj)
  exact h.trans_eq (by ring)

end NativeBounds

/-- Only positive derivatives of the literal phase are bounded, only on
the actual coefficient support. Copy-dependent phase germs fit this interface. -/
structure SupportedPhaseBounds {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (N : ℕ) (U : Set D) (β : ℝ) (a : ι → ℕ → D → ℂ) (Φ : ι → ℕ → D → ℝ) : Prop where
  smooth : ∀ l n, N ≤ n → ∀ x ∈ U, x ∈ tsupport (a l n) → SmoothNear (Φ l n) x
  bounds : ∀ m, ∃ B : ℝ, 1 ≤ B ∧ ∃ p : ℕ, ∀ l n, N ≤ n → ∀ x ∈ U,
    x ∈ tsupport (a l n) → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (Φ l n) x‖ ≤ B * ChartScales.S n ^ p * ChartScales.Q n ^ (-β)

theorem mode_zero_germ {D : Type*} [NormedAddCommGroup D]
    {a : D → ℂ} (Φ : D → ℝ) (c : ℝ) {x : D} (hx : x ∉ tsupport a) :
    (fun y => a y * PhysicalGraphBounds.character c (Φ y)) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  change a y = 0 at hy
  simp only [hy, zero_mul]

theorem mode_contDiffOn {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} (hU : IsOpen U) {a : D → ℂ} {Φ : D → ℝ} (c : ℝ)
    (ha : ContDiffOn ℝ ∞ a U)
    (hΦ : ∀ x ∈ U, x ∈ tsupport a → SmoothNear Φ x) :
    ContDiffOn ℝ ∞ (fun y => a y * PhysicalGraphBounds.character c (Φ y)) U := by
  intro x hx
  by_cases hs : x ∈ tsupport a
  · exact ((ha.contDiffAt (hU.mem_nhds hx)).mul
      ((PhysicalGraphBounds.character_smooth c).contDiffAt.comp x
        (hΦ x hx hs).contDiffAt)).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq (mode_zero_germ Φ c hs)).contDiffWithinAt

theorem NativeBounds.mode {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] {N : ℕ} {U : Set D} {gain β : ℝ} {loss : ℕ → ℝ}
    {a : ι → ℕ → D → ℂ} {Φ : ι → ℕ → D → ℝ}
    (hN : 1 ≤ N) (hU : IsOpen U) (hβ : 0 ≤ β)
    (ha : NativeBounds N U gain loss a) (hΦ : SupportedPhaseBounds N U β a Φ) :
    NativeBounds N U gain (fun m => loss m + β * m)
      (fun l n x => a l n x * PhysicalGraphBounds.character 1 (Φ l n x)) := by
  refine ⟨fun l n hn => mode_contDiffOn hU 1 (ha.smooth l n hn) (hΦ.smooth l n hn), ?_⟩
  intro m
  obtain ⟨A, hA, p, haB⟩ := ha.bounds m
  obtain ⟨B, hB, q, hΦB⟩ := hΦ.bounds m
  refine ⟨(2 : ℝ) ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, p + q * m, ?_⟩
  intro l n hn x hx j hj
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (hN.trans hn)
  have hphase : 1 ≤ B * ChartScales.S n ^ q * ChartScales.Q n ^ (-β) := by
    have hQb : 1 ≤ ChartScales.Q n ^ (-β) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hQ
        (ChartScales.Q_le_one n) (neg_nonpos.mpr hβ)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hS)) hQb
  by_cases hs : x ∈ tsupport (a l n)
  · have hb := mode_jet_bound_local (a := a l n) (Φ := Φ l n) (x := x)
      (SmoothNear.of_open hU (ha.smooth l n hn) hx)
      (hΦ.smooth l n hn x hx hs) m
      (by positivity : 0 ≤ A * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ p)
      hphase (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : |(1 : ℝ)| ≤ 1)
      (haB l n hn x hx) (hΦB l n hn x hx hs) j hj
    apply hb.trans_eq
    simp only [one_pow, mul_one, mul_pow, ← pow_mul]
    rw [← Real.rpow_mul_natCast hQ.le (-β) m]
    have he : gain - (loss m + β * m) = (gain - loss m) + (-β) * m := by ring
    rw [he, Real.rpow_add hQ, pow_add]
    ring
  · rw [iteratedFDeriv_eq_of_eventuallyEq (mode_zero_germ (Φ l n) 1 hs) j,
      iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity

theorem NativeBounds.pi {D ι κ : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [Fintype κ] {N : ℕ} {U : Set D} {gain : ℝ} {loss : ℕ → ℝ}
    {f : ι → ℕ → D → κ → ℝ} (hN : 1 ≤ N) (hU : IsOpen U)
    (hf : ∀ i, NativeBounds N U gain loss (fun l n x => f l n x i)) :
    NativeBounds N U gain loss f := by
  classical
  refine ⟨fun l n hn => contDiffOn_pi.mpr (fun i => (hf i).smooth l n hn), ?_⟩
  intro m
  choose A hA p hb using fun i => (hf i).bounds m
  refine ⟨∑ i, A i, Finset.sum_nonneg (fun i _ => hA i), ∑ i, p i, ?_⟩
  intro l n hn x hx j hj
  have hS := PhysicalGraphBounds.S_ge_one (hN.trans hn)
  have hQ : 0 ≤ ChartScales.Q n ^ (gain - loss m) := (Real.rpow_pos_of_pos (ChartScales.Q_pos n)
      _).le
  have hSA : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => hA i)
  have hSp : 0 ≤ ChartScales.S n ^ (∑ i, p i) := pow_nonneg (zero_le_one.trans hS) _
  apply finite_pi_iteratedFDeriv_norm_le
    ((contDiffOn_pi.mpr (fun i => (hf i).smooth l n hn)).contDiffAt
      (hU.mem_nhds hx) |>.of_le (nat_le_infty j)) (by positivity)
  intro i
  exact (hb i l n hn x hx j hj).trans (mul_le_mul
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ i)) hQ)
    (pow_le_pow_right₀ hS (Finset.single_le_sum (fun k _ => Nat.zero_le (p k)) (Finset.mem_univ i)))
    (pow_nonneg (zero_le_one.trans hS) _) (by positivity))

/-- Pull a genuine local bound through a fixed contraction, including the
angular projection. No global extension estimate is needed. -/
theorem NativeBounds.pull_linear {D E F ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] {N : ℕ} {U : Set E} {gain : ℝ} {loss : ℕ → ℝ}
    {f : ι → ℕ → E → F} (hU : IsOpen U) (hf : NativeBounds N U gain loss f)
    (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1) :
    NativeBounds N (L ⁻¹' U) gain loss (fun l n => f l n ∘ L) := by
  refine ⟨fun l n hn => (hf.smooth l n hn).comp L.contDiff.contDiffOn (fun _ hx => hx), ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  refine ⟨A, hA, p, ?_⟩
  intro l n hn x hx j hj
  have hQ := ChartScales.Q_pos n
  have hS : 0 ≤ ChartScales.S n := by unfold ChartScales.S; positivity
  obtain ⟨g, hg, he⟩ := (SmoothNear.of_open hU (hf.smooth l n hn) hx).exists_global_germ
  rw [iteratedFDeriv_eq_of_eventuallyEq (he.comp_tendsto L.continuous.continuousAt) j]
  apply PhysicalGraphBounds.jet_comp_linear_bound hg L hL x (by positivity) m _ j hj
  intro i hi
  rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
  exact hb l n hn (L x) hx i hi

/-- Full phase, given by `(j : ℝ) * (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ)
* x.2)`. -/
noncomputable def fullPhase (b : CorrectionState.HarmonicBlock Point) (j : ℤ)
    (n : ℕ) (x : Cylinder) : ℝ :=
  (j : ℝ) * (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) * x.2)

theorem character_fullPhase (j : ℤ) (t : ℝ) :
    PhysicalGraphBounds.character 1 ((j : ℝ) * t) = HarmonicFields.character j t := by
  unfold PhysicalGraphBounds.character PhysicalGraphBounds.phaseFactor HarmonicFields.character
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_one, one_mul, Complex.ofReal_intCast]
  ring

theorem block_expansion (b : CorrectionState.HarmonicBlock Point) (J : Finset ℤ)
    (n : ℕ) (i : Fin 3) (hs : (b.velocity n i).support ⊆ J) (x : Cylinder) :
    b.oscillation n x i = ∑ j ∈ J,
      ((b.velocity n i j x.1) * PhysicalGraphBounds.character 1 (fullPhase b j n x)).re := by
  unfold CorrectionState.HarmonicBlock.oscillation HarmonicFields.field
  rw [HarmonicFields.evaluate_over _ J hs, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [fullPhase, character_fullPhase]

/-- The actual finite group-algebra block, not a separate modeled wave,
inherits the coefficient bounds. The fixed harmonic set affects constants. -/
theorem block_nativeBounds {ι : Type} {N : ℕ} {U : Set Cylinder} {gain β : ℝ}
    (hN : 1 ≤ N) (hU : IsOpen U) (hβ : 0 ≤ β)
    (b : ι → CorrectionState.HarmonicBlock Point) (J : Finset ℤ)
    (hs : ∀ l n, N ≤ n → ∀ i, ((b l).velocity n i).support ⊆ J)
    (ha : ∀ i j, j ∈ J → NativeBounds N U gain (fun _ => 0)
      (fun l n (x : Cylinder) => (b l).velocity n i j x.1))
    (hΦ : ∀ i j, j ∈ J → SupportedPhaseBounds N U β
      (fun l n (x : Cylinder) => (b l).velocity n i j x.1) (fun l => fullPhase (b l) j)) :
    NativeBounds N U gain (fun m => β * m) (fun l => (b l).oscillation) := by
  apply NativeBounds.pi hN hU
  intro i
  have hj : ∀ j ∈ J, NativeBounds N U gain (fun m => β * m)
      (fun l n (x : Cylinder) =>
        ((b l).velocity n i j x.1 * PhysicalGraphBounds.character 1 (fullPhase (b l) j n x)).re) :=
            by
    intro j hj
    simpa only [zero_add, Complex.reCLM_apply] using
      ((ha i j hj).mode hN hU hβ (hΦ i j hj)).map hU Complex.reCLM
  apply (NativeBounds.sum hN hU J _ hj).congr hU
  intro l n hn x _
  exact (block_expansion (b l) J n i (hs l n hn i) x).symm

/-- The exact reconstructed state residual is controlled by the true label
overlap, the mean-good residual and the three excluded errors. -/
theorem state_nativeBounds {ι : Type} {N : ℕ} {V : Set Point}
    (hN : 1 ≤ N) (hV : IsOpen V) {gain β : ℝ}
    {c : CorrectionState.Context Point} {s : CorrectionState.State Point}
    (labels : ℕ → Finset ι) (b : ι → CorrectionState.HarmonicBlock Point)
    (G A : ι → HarmonicResidual.BlockCoefficients Point)
    (hrep : HarmonicResidual.BlockRepresentation labels b G A s)
    (hmean : LiftedMeanResidual.MeanHypotheses V c s)
    (hreg : ∀ n, N ≤ n → HarmonicResidual.ExtractionRegular V c s labels b G A n)
    (hb : NativeBounds N (HarmonicResidual.liftDomain V) gain (fun m => β * m)
      (fun l => (HarmonicResidual.residualBlock c s (b l) (G l) (A l)).oscillation))
    (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, N ≤ n → Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n, N ≤ n → ∀ l ∈ labels n, 1 ≤ (label n l).1)
    (d : ℝ) (χ : ℕ → Cylinder → WindowPoint)
    (hχ : ∀ n, N ≤ n → ContinuousOn (χ n) (HarmonicResidual.liftDomain V))
    (hs : ∀ n, N ≤ n → ∀ l ∈ labels n, ∀ x ∈ HarmonicResidual.liftDomain V,
      (HarmonicResidual.residualBlock c s (b l) (G l) (A l)).oscillation n x ≠ 0 →
        χ n x ∈ closedWindow d (label n l))
    (hm : NativeBounds N (HarmonicResidual.liftDomain V) gain (fun m => β * m)
      (fun (_ : Unit) n (x : Cylinder) => s.meanGoodResidual c n x.1))
    (he : NativeBounds N (HarmonicResidual.liftDomain V) gain (fun m => β * m)
      (fun (_ : Unit) => s.errors.total)) :
    NativeBounds N (HarmonicResidual.liftDomain V) gain (fun m => β * m)
      (fun (_ : Unit) => LiftedMeanResidual.fullResidual c s) := by
  have hU : IsOpen (HarmonicResidual.liftDomain V) := HarmonicResidual.liftDomain_open hV
  have hsum := hb.window_sum hU labels label hinj hlevel d χ hχ hs
  apply ((hsum.add hN hU hm).add hN hU he).congr hU
  intro _ n hn x hx
  ext i
  simpa only [Pi.add_apply, Finset.sum_apply] using
    (state_fullResidual_reconstructed hV hrep hmean (hreg n hn) hx i).symm

/-! ## One physical residual, selected comparable bands, and the base patch -/

/-- Residual, defined pointwise by `navierStokesResidual u p w.1 w.2`. -/
noncomputable def residual (u : VelocityField) (p : PressureField) : SpaceTime → Space :=
  fun w => navierStokesResidual u p w.1 w.2

/-- Changed support, given by `tsupport (fun w => u w - u₀ w) ∪ tsupport (fun w => p w - p₀ w)`. -/
noncomputable def changedSupport (u u₀ : VelocityField) (p p₀ : PressureField) : Set SpaceTime :=
  tsupport (fun w => u w - u₀ w) ∪ tsupport (fun w => p w - p₀ w)

theorem residual_germ_off_changedSupport {u u₀ : VelocityField} {p p₀ : PressureField}
    {w : SpaceTime} (hw : w ∉ changedSupport u u₀ p p₀) :
    residual u p =ᶠ[𝓝 w] residual u₀ p₀ := by
  have hu : u =ᶠ[𝓝 w] u₀ := by
    have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hw (Or.inl h))
    filter_upwards [hz] with y hy
    exact sub_eq_zero.mp hy
  have hp : p =ᶠ[𝓝 w] p₀ := by
    have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hw (Or.inr h))
    filter_upwards [hz] with y hy
    exact sub_eq_zero.mp hy
  exact ResidualRegularity.residual_eventuallyEq hu hp

/-- The loss contains the actual physical residual degree, graph derivative
loss, one polynomial-in-band absorption, and the fixed phase loss. -/
noncomputable def physicalLoss (h β : ℝ) (m : ℕ) : ℝ :=
  PhysicalMeanJetBounds.loss (residualDegree h) m + β * m

/-- Exact realization on the true polar charts. This is a value identity,
not a derivative or size estimate; a primitive-state constructor is below. -/
def ChartIdentity (a h : ℝ) (N : ℕ) (gap : ℕ → ℕ) (U : Set Cylinder)
    (F : ℕ → Cylinder → Components) (R : SpaceTime → Space) : Prop :=
  ∀ n, N ≤ n → ∀ j w, w ∈ preterminal →
    PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j →
    polarGraph a h j n (gap n) w ∈ U →
    R w = cartesianPull a h j n (gap n) (residualDegree h) (F n) w

theorem ChartIdentity.germ {a b h : ℝ} {N : ℕ} {gap : ℕ → ℕ} {U : Set Cylinder}
    {F : ℕ → Cylinder → Components} {R : SpaceTime → Space}
    (ha : 0 < a) (hU : IsOpen U) (hreal : ChartIdentity a h N gap U F R)
    {n : ℕ} (hn : N ≤ n) (j : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ preterminal)
    (hann : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b)
    (hj : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j)
    (hx : polarGraph a h j n (gap n) w ∈ U) :
    R =ᶠ[𝓝 w] cartesianPull a h j n (gap n) (residualDegree h) (F n) := by
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha
      hann)
  have hg : ContinuousAt (polarGraph a h j n (gap n)) w :=
    (polarLift_smooth ha j).continuous.continuousAt.comp
      (commonLift_smoothAt h n (gap n) haxis).continuousAt
  filter_upwards [preterminal_open.mem_nhds hw,
    (PhysicalGraphBounds.scaledRadial n).continuous.continuousAt
      ((PolarCharts.chartDomain_open a j).mem_nhds hj), hg (hU.mem_nhds hx)] with y hy hyj hyU
  exact hreal n hn j y hy hyj hyU

/-- Geometric support and exact coherent realization of the same physical
fields. No physical residual bound or global raw smoothness is a field. -/
structure ResidualChartData (a b h : ℝ) (N Δ : ℕ) (U : Set Cylinder)
    (F : ℕ → Cylinder → Components) (u u₀ : VelocityField) (p p₀ : PressureField) where
  /-- Active of `ResidualChartData`, of type `Set SpaceTime`. -/
  active : Set SpaceTime
  changed_subset : changedSupport u u₀ p p₀ ⊆ active
  /-- Gap of `ResidualChartData`, of type `ℕ → ℕ`. -/
  gap : ℕ → ℕ
  gap_le : ∀ n, N ≤ n → gap n ≤ Δ
  realization : ChartIdentity a h N gap U F (residual u p)
  annulus : ∀ n, N ≤ n → ∀ w, w ∈ preterminal →
    physicalQ h w / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * physicalQ h w →
    w ∈ active →
    PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b
  in_domain : ∀ n, N ≤ n → ∀ w, w ∈ preterminal →
    physicalQ h w / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * physicalQ h w →
    w ∈ active → ∀ j,
    PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j →
    polarGraph a h j n (gap n) w ∈ U

/-- A comparable band is proved to exist at each supported point. Outside
the correction support the actual finite residual has the base residual germ. -/
theorem ResidualChartData.residual_jet_bound {a b h gain β : ℝ} {N Δ : ℕ} {U : Set Cylinder}
    {F : ℕ → Cylinder → Components} {u u₀ : VelocityField} {p p₀ : PressureField}
    (d : ResidualChartData a b h N Δ U F u u₀ p p₀)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hN : 4 ≤ N) (hU : IsOpen U)
    (hF : NativeBounds N U gain (fun m => β * m) (fun (_ : Unit) => F)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, w ∈ preterminal → |w.1| ≤ 1 → physicalQ h w ≤ ChartScales.Q N →
      w ∈ d.active → ‖iteratedFDeriv ℝ m (residual u p) w‖ ≤
        C * physicalQ h w ^ (gain - physicalLoss h β m) := by
  obtain ⟨A, hA, e, hjet⟩ := hF.bounds m
  obtain ⟨C, hC, hb⟩ := cartesianPull_jet_bound (b := b) hh.le hh1.le ha Δ m
    (gain - β * m) (residualDegree h) e A hA
  refine ⟨C, hC, ?_⟩
  intro w hw ht hsmall hs
  have hq := physicalQ_pos hh hh1 hw
  obtain ⟨n, hn, hlo, hhi⟩ := PhysicalMeanJetBounds.exists_comparable_band N hq hsmall
  have hlo' : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
  have hann := d.annulus n hn w hw hlo' hhi.le hs
  obtain ⟨j, hj⟩ := PolarCharts.annulus_covered ha hann
  have hc := PolarCharts.sector_subset_chartDomain ha j hj
  have hdom := d.in_domain n hn w hw hlo' hhi.le hs j hc
  rw [iteratedFDeriv_eq_of_eventuallyEq (d.realization.germ ha hU hn j hw hann hc hdom) m]
  have he := hb n (hN.trans hn) (d.gap n) (d.gap_le n hn) w hann ht (physicalQ h w) hq
    hlo' hhi.le j (F n) (SmoothNear.of_open hU (hF.smooth () n hn) hdom)
    (by simpa only [Real.rpow_natCast] using hjet () n hn _ hdom)
  have hexp : gain - β * m - PhysicalMeanJetBounds.loss (residualDegree h) m =
      gain - physicalLoss h β m := by unfold physicalLoss; ring
  simpa only [hexp] using he

theorem eventually_time_small (x : Space) :
    ∀ᶠ w : SpaceTime in 𝓝[SpacetimeEndpoint.openPast 1] (1, x), |w.1| ≤ 1 := by
  have ht₀ : ∀ᶠ w : SpaceTime in 𝓝 (1, x), 0 < w.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (by norm_num)
  have ht : ∀ᶠ w : SpaceTime in 𝓝[SpacetimeEndpoint.openPast 1] (1, x), 0 < w.1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds ht₀
  filter_upwards [ht, self_mem_nhdsWithin] with w hpos hpast
  rw [abs_of_pos hpos]
  exact hpast.1.le

/-- The finite-residual rate consumed by the diagonal assembly. The same
`physicalLoss h β m` works for every stage and every native exponent `gain`. -/
theorem ResidualChartData.residual_jetRate {a b h gain β : ℝ} {N Δ : ℕ} {U : Set Cylinder}
    {F : ℕ → Cylinder → Components} {u u₀ : VelocityField} {p p₀ : PressureField}
    (d : ResidualChartData a b h N Δ U F u u₀ p p₀)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hN : 4 ≤ N) (hU : IsOpen U)
    (hF : NativeBounds N U gain (fun m => β * m) (fun (_ : Unit) => F)) (m : ℕ)
    (hbase : DiagonalResidual.JetRate
      ((𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) ⊓ 𝓟 d.activeᶜ)
      (physicalQ h) (residual u₀ p₀) m (gain - physicalLoss h β m)) :
    DiagonalResidual.JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
      (physicalQ h) (residual u p) m (gain - physicalLoss h β m) := by
  obtain ⟨C, hC, hb⟩ := d.residual_jet_bound hh hh1 ha hN hU hF m
  obtain ⟨B, hB, hbase⟩ := hbase
  rw [Filter.eventually_inf_principal] at hbase
  have hsmall : ∀ᶠ w : SpaceTime in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      physicalQ h w ≤ ChartScales.Q N :=
    (AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (by simp)).eventually
      (eventually_le_nhds (ChartScales.Q_pos N))
  refine ⟨B + C, add_nonneg hB hC, ?_⟩
  filter_upwards [hbase, hsmall, eventually_time_small (0 : Space), self_mem_nhdsWithin]
    with w hbw hsw ht hw
  have hp : w ∈ preterminal := hw.1
  have hq := physicalQ_pos hh hh1 hp
  by_cases hs : w ∈ d.active
  · exact (hb w hp ht hsw hs).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hB) (Real.rpow_pos_of_pos hq _).le)
  · rw [iteratedFDeriv_eq_of_eventuallyEq
      (residual_germ_off_changedSupport (fun hc => hs (d.changed_subset hc))) m]
    exact (hbw hs).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hC) (Real.rpow_pos_of_pos hq _).le)

/-! ## Primitive physical-state realization -/

/-- Band graph, given by `PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
(ChartScales.nativeIndex h n - d)`. -/
noncomputable def bandGraph (h : ℝ) (n d : ℕ) : PhysicalResidualBridge.ScaledGraph :=
  PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - d)

theorem polarGraph_eq_meanGraph {a : ℝ} (ha : 0 < a) (h : ℝ) (j : PolarCharts.Index)
    (n d : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    polarGraph a h j n d w =
      (PhysicalMeanJetBounds.graph h n d w, ResidualPolarGraph.angle a j n w) := by
  apply Prod.ext
  · apply Prod.ext
    · change (PolarCharts.chart a j (PhysicalGraphBounds.liftXY (commonLift h n d w))).1 = _
      rw [PhysicalClassBounds.liftXY_commonLift]
      exact ResidualPolarGraph.chart_radius_eq_graph ha h j n d hw
    · rfl
  · change (PolarCharts.chart a j (PhysicalGraphBounds.liftXY (commonLift h n d w))).2 = _
    rw [PhysicalClassBounds.liftXY_commonLift]
    rfl

/-- All assumptions refer to the primitive physical fields or the already
fixed base-pressure equation. No residual equality or estimate is assumed. -/
structure StateRealization (h : ℝ) (N : ℕ) (gap : ℕ → ℕ) (U : Set Cylinder)
    (c : CorrectionState.Context Point) (s : CorrectionState.State Point)
    (p₀ : ℕ → Cylinder → ℝ) (u : VelocityField) (P : PressureField) : Prop where
  domain_open : IsOpen U
  radius_ne : ∀ x ∈ U, x.1.1 ≠ 0
  gap_native : ∀ n, N ≤ n → gap n ≤ ChartScales.nativeIndex h n
  matching : ∀ n, N ≤ n → PhysicalResidualTZ.MatchesAtTZ c.operators (bandGraph h n (gap n)) n
  base_smooth : ∀ n, N ≤ n → ∀ i,
    ContDiffOn ℝ ∞ (fun x => PhysicalResidualBridge.baseComponents c n x i) U
  increment_smooth : ∀ n, N ≤ n → ∀ i,
    ContDiffOn ℝ ∞ (fun x => PhysicalResidualBridge.incrementComponents s n x i) U
  base_pressure_smooth : ∀ n, N ≤ n → ContDiffOn ℝ ∞ (p₀ n) U
  pressure_smooth : ∀ n, N ≤ n → ContDiffOn ℝ ∞ (s.totalPressureIncrement n) U
  base_equation : ∀ n, N ≤ n → ∀ x ∈ U, ∀ i,
    PhysicalResidualBridge.graphResidual (ChartScales.Q n ^ h)
      PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualTZ.graphRadialTZ (bandGraph h n (gap n))) PhysicalResidualTZ.graphAngularTZ
      (PhysicalResidualTZ.graphAxialTZ (bandGraph h n (gap n)))
      (PhysicalResidualTZ.graphTemporalTZ (bandGraph h n (gap n)))
      (PhysicalResidualBridge.baseComponents c n) (p₀ n) x i =
        LiftedMeanResidual.virtualDivergence c n x i + s.errors.base n x i
  physical_velocity_smooth : ∀ n, N ≤ n → ∀ z ∈ preterminal,
    z ∈ PhysicalResidualTZ.graphSourceTZ (bandGraph h n (gap n)) U →
    ContDiffAt ℝ 2 u (z.1, CylindricalResidual.chart z.2)
  physical_pressure_differentiable : ∀ n, N ≤ n → ∀ z ∈ preterminal,
    z ∈ PhysicalResidualTZ.graphSourceTZ (bandGraph h n (gap n)) U →
    DifferentiableAt ℝ P (z.1, CylindricalResidual.chart z.2)
  velocity_germ : ∀ n, N ≤ n → ∀ z ∈ preterminal,
    z ∈ PhysicalResidualTZ.graphSourceTZ (bandGraph h n (gap n)) U →
    (fun y : SpaceTime => u (y.1, CylindricalResidual.chart y.2)) =ᶠ[𝓝 z]
      (fun y => CylindricalResidual.frame (y.2 1)
        (PhysicalResidualTZ.velocityTZ (bandGraph h n (gap n))
          (fun x i => PhysicalResidualBridge.baseComponents c n x i +
            PhysicalResidualBridge.incrementComponents s n x i) y))
  pressure_germ : ∀ n, N ≤ n → ∀ z ∈ preterminal,
    z ∈ PhysicalResidualTZ.graphSourceTZ (bandGraph h n (gap n)) U →
    CylindricalResidual.pressurePullback P =ᶠ[𝓝 z]
      PhysicalResidualTZ.pressureTZ (bandGraph h n (gap n))
        (fun x => p₀ n x + s.totalPressureIncrement n x)

/-- The exact Cartesian reconstruction follows from the concrete
Navier--Stokes operator identity, after the genuine polar inverse. -/
theorem StateRealization.chartIdentity {a h : ℝ} {N : ℕ} {gap : ℕ → ℕ} {U : Set Cylinder}
    {c : CorrectionState.Context Point} {s : CorrectionState.State Point}
    {p₀ : ℕ → Cylinder → ℝ} {u : VelocityField} {P : PressureField}
    (ha : 0 < a) (r : StateRealization h N gap U c s p₀ u P) :
    ChartIdentity a h N gap U (LiftedMeanResidual.fullResidual c s) (residual u P) := by
  intro n hn j w hw hj hU
  let z := ResidualPolarGraph.cylindricalPoint a j n w
  have hztime : z ∈ preterminal := hw
  have hzcart : (z.1, CylindricalResidual.chart z.2) = w :=
    ResidualPolarGraph.spacetimeChart_cylindricalPoint ha j n hj
  have hzangle : z.2 1 = ResidualPolarGraph.angle a j n w :=
    ResidualPolarGraph.cylindricalPoint_angle a j n w
  have hzgraph : PhysicalResidualTZ.graphMapTZ (bandGraph h n (gap n)) z =
      polarGraph a h j n (gap n) w := by
    rw [polarGraph_eq_meanGraph ha h j n (gap n) hj]
    exact ResidualPolarGraph.graphMapTZ_cylindricalPoint ha h j n (gap n) (r.gap_native n hn) hj
  have hzU : z ∈ PhysicalResidualTZ.graphSourceTZ (bandGraph h n (gap n)) U :=
    ⟨ResidualPolarGraph.cylindricalPoint_radius_pos ha j n hj, hzgraph.symm ▸ hU⟩
  have hu : ContDiffAt ℝ 2 u (z.1, CylindricalResidual.chart z.2) :=
    r.physical_velocity_smooth n hn z hztime hzU
  have hP : DifferentiableAt ℝ P (z.1, CylindricalResidual.chart z.2) :=
    r.physical_pressure_differentiable n hn z hztime hzU
  have he : ∀ i, LiftedMeanResidual.fullResidual c s n (polarGraph a h j n (gap n) w) i =
      ChartScales.Q n ^ residualDegree h *
        CylindricalResidual.frame (-ResidualPolarGraph.angle a j n w) (residual u P w) i := by
    intro i
    have hi := PhysicalResidualTZ.context_fullResidual_physicalTZ (ChartScales.Q_pos n) h
      (ChartScales.nativeIndex h n - gap n) n c s (r.matching n hn) r.domain_open r.radius_ne
      (r.base_smooth n hn) (r.increment_smooth n hn) (r.base_pressure_smooth n hn)
      (r.pressure_smooth n hn) hzU (r.base_equation n hn _ hzU.2) hu hP
      (r.velocity_germ n hn z hztime hzU) (r.pressure_germ n hn z hztime hzU) i
    change LiftedMeanResidual.fullResidual c s n (PhysicalResidualTZ.graphMapTZ (bandGraph h n (gap
        n)) z) i =
      ChartScales.Q n ^ residualDegree h *
        CylindricalResidual.frame (-(z.2 1)) (residual u P (z.1, CylindricalResidual.chart z.2)) i
            at hi
    rw [hzgraph, hzangle, hzcart] at hi
    exact hi
  have hout := physical_vector_of_components (ChartScales.Q_pos n) h
    (ResidualPolarGraph.angle a j n w)
    (LiftedMeanResidual.fullResidual c s n (polarGraph a h j n (gap n) w)) (residual u P w) he
  exact hout

/-! ## Weighted invariant and finite-stage consumers -/

/-- The concrete uniform harmonic invariant supplies the uniform part of
each weighted coefficient input; all remaining hypotheses are geometry. -/
theorem coefficient_source_of_uniformVelocity {ι : Type} {s : StripData Point}
    {h α : ℝ} {P : ι → ℕ → Point → ℝ}
    {b : ι → CorrectionState.HarmonicBlock Point}
    (hb : UniformHarmonicInteraction.UniformVelocity s P α b)
    (hflat : ∃ cL cR L : ℝ, ∃ ρ : Point → ℝ, PhysicalClassBounds.FlatGeometry s cL cR L ρ)
    (hw : ∃ c : ℝ, 0 < c ∧ ∀ l n x, x ∈ s.domain → Real.sqrt (s.zeta x) * P l n x ≤ s.zeta x ^ c)
    (he : ∀ n, s.epsilon n = ChartScales.epsilon h n)
    (hslow : ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n, 4 ≤ n → s.slow n ≤ C * ChartScales.S n ^ p)
    (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    LocalSourceBounds s h α (fun l n x => Real.sqrt (s.zeta x) * P l n x)
      (fun l n x => (b l).velocity n i j x) :=
  ⟨hb i j hj, hflat, hw, he, hslow⟩

/-- This adapter uses the actual smooth edge extension of each coefficient,
then lifts it to the angular product. The raw totalization need not be smooth. -/
theorem block_nativeBounds_of_weighted {ι : Type} {N : ℕ} {V : Set Point}
    {h α β : ℝ} {s : StripData Point} {w : ι → ℕ → Point → ℝ}
    (hN : 4 ≤ N) (hV : IsOpen V) (hβ : 0 ≤ β)
    (b : ι → CorrectionState.HarmonicBlock Point) (J : Finset ℤ)
    (hs : ∀ l n, N ≤ n → ∀ i, ((b l).velocity n i).support ⊆ J)
    (ha : ∀ i j, j ∈ J → LocalSourceBounds s h α w (fun l n x => (b l).velocity n i j x))
    (hsm : ∀ i j, j ∈ J → ∀ l n, N ≤ n → ContDiffOn ℝ ∞ ((b l).velocity n i j) V)
    (hcover : ∀ i j, j ∈ J → ∀ l n, N ≤ n → ∀ x ∈ V,
      x ∈ closure s.domain ∨ x ∉ tsupport ((b l).velocity n i j))
    (hΦ : ∀ i j, j ∈ J → SupportedPhaseBounds N (HarmonicResidual.liftDomain V) β
      (fun l n (x : Cylinder) => (b l).velocity n i j x.1) (fun l => fullPhase (b l) j)) :
    NativeBounds N (HarmonicResidual.liftDomain V) (h * α) (fun m => β * m)
      (fun l => (b l).oscillation) := by
  apply block_nativeBounds (by omega) (HarmonicResidual.liftDomain_open hV) hβ b J hs _ hΦ
  intro i j hj
  have hc := NativeBounds.of_localSource hN hV (ha i j hj) (hsm i j hj) (hcover i j hj)
  let π : Cylinder →L[ℝ] Point := ContinuousLinearMap.fst ℝ Point ℝ
  have hπ : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [one_mul]
    exact norm_fst_le x
  have hp := hc.pull_linear hV π hπ
  have hdom : π ⁻¹' V = HarmonicResidual.liftDomain V := by
    ext x
    simp [π, HarmonicResidual.liftDomain]
  rw [hdom] at hp
  exact hp

/-- Raising the fixed derivative loss never changes a coefficient field. -/
theorem NativeBounds.to_phaseLoss {D E ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ} {U : Set D} {gain gain' β : ℝ}
    {f : ι → ℕ → D → E} (hf : NativeBounds N U gain (fun _ => 0) f)
    (hN : 1 ≤ N) (hβ : 0 ≤ β) (hg : gain' ≤ gain) :
    NativeBounds N U gain' (fun m => β * m) f := by
  apply hf.weaken hN
  intro m
  have hm := mul_nonneg hβ (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  linarith

theorem excluded_nativeBounds {N : ℕ} {U : Set Cylinder} {gain : ℝ} {loss : ℕ → ℝ}
    (hN : 1 ≤ N) (hU : IsOpen U) (e : CorrectionState.ExcludedErrors Point)
    (hb : NativeBounds N U gain loss (fun (_ : Unit) => e.base))
    (hg : NativeBounds N U gain loss (fun (_ : Unit) => e.gaussian))
    (ha : NativeBounds N U gain loss (fun (_ : Unit) => e.aliasError)) :
    NativeBounds N U gain loss (fun (_ : Unit) => e.total) := by
  have he := (hb.add hN hU hg).add hN hU ha
  simp only [CorrectionState.ExcludedErrors.total] at he ⊢
  exact he

/-- An actual exterior zero germ proves every exterior residual rate. -/
theorem jetRate_of_zero_germs {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {R : SpaceTime → Space} (hz : ∀ᶠ w in l, R =ᶠ[𝓝 w] fun _ => 0) (m : ℕ) (r : ℝ) :
    DiagonalResidual.JetRate l q R m r := by
  refine ⟨0, le_rfl, ?_⟩
  filter_upwards [hz] with w hw
  rw [iteratedFDeriv_eq_of_eventuallyEq hw m, iteratedFDeriv_fun_zero]
  simp

/-- One fixed loss function applies to the actual residual after every
finite correction stage. Constants and the finite harmonic cutoff may vary
with the stage; the band floor, cover gap and phase loss stay fixed. -/
theorem finite_residual_rates {a b h β : ℝ} {N Δ : ℕ} {gain : ℕ → ℝ}
    {U : ℕ → Set Cylinder} {F : ℕ → ℕ → Cylinder → Components}
    {u : ℕ → VelocityField} {p : ℕ → PressureField} {u₀ : VelocityField} {p₀ : PressureField}
    (d : ∀ J, ResidualChartData a b h N Δ (U J) (F J) (u J) u₀ (p J) p₀)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hN : 4 ≤ N) (hU : ∀ J, IsOpen (U J))
    (hF : ∀ J, NativeBounds N (U J) (gain J) (fun m => β * m) (fun (_ : Unit) => F J))
    (hbase : ∀ J m, DiagonalResidual.JetRate
      ((𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) ⊓ 𝓟 (d J).activeᶜ)
      (physicalQ h) (residual u₀ p₀) m (gain J - physicalLoss h β m)) :
    ∀ J m, DiagonalResidual.JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
      (physicalQ h) (fun z => navierStokesResidual (u J) (p J) z.1 z.2)
      m (gain J - physicalLoss h β m) :=
  fun J m => (d J).residual_jetRate hh hh1 ha hN (hU J) (hF J) m (hbase J m)

end NavierStokes.PhysicalResidualJetBounds

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualPolarCoverage

open Set Function Filter ProblemStatement CorrectionInitialization
open PhysicalWaveSum PhysicalGraphBounds PhysicalMeanJetBounds
open scoped Topology

/-- Point: an abbreviation for `PhysicalMeanJetBounds.Point`. -/
abbrev Point := PhysicalMeanJetBounds.Point
/-- Cylinder: an abbreviation for `PhysicalResidualJetBounds.Cylinder`. -/
abbrev Cylinder := PhysicalResidualJetBounds.Cylinder

/-- Active as an element of `Set SpaceTime`. -/
noncomputable def active : Set SpaceTime :=
  {w | (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 ∈
    Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal)}

/-- Inner, given by `PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4`. -/
noncomputable def inner : ℝ :=
  PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4

/-- Outer, given by `2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal`. -/
noncomputable def outer : ℝ :=
  2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal

/-- Native domain, given by `HarmonicResidual.liftDomain (ActualInitialization.geometry.domain ∩
{x : Point | 0 < x.1})`. -/
noncomputable def nativeDomain : Set Cylinder :=
  HarmonicResidual.liftDomain
    (ActualInitialization.geometry.domain ∩ {x : Point | 0 < x.1})

theorem inner_pos : 0 < inner :=
  div_pos (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) (by norm_num)

theorem outer_pos : 0 < outer :=
  mul_pos (by norm_num) (PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal)

theorem inner_lt_outer : inner < outer := by
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hab := PrimaryTargetBounds.radii_ordered ActualPrimary.nominal
  change PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4 <
    2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal
  linarith

theorem nativeDomain_open : IsOpen nativeDomain :=
  HarmonicResidual.liftDomain_open
    (ActualInitialization.geometry.domain_open.inter
      (isOpen_lt continuous_const continuous_fst))

theorem nativeDomain_radius_pos {x : Cylinder} (hx : x ∈ nativeDomain) :
    0 < x.1.1 := hx.1.2

theorem nativeDomain_radius_ne {x : Cylinder} (hx : x ∈ nativeDomain) :
    x.1.1 ≠ 0 := (nativeDomain_radius_pos hx).ne'

/-! ## Scale identities independent of the particular actual profile -/

theorem graph_radius_nonneg (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    0 ≤ (graph h n d w).1 := by
  rw [graph_radius]
  exact PolarCharts.radius_nonneg _

theorem graph_radius_sq (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    (graph h n d w).1 ^ 2 =
      (w.2 0 ^ 2 + w.2 1 ^ 2) / ChartScales.Q n := by
  rw [graph_radius, PolarCharts.radius_sq]
  have hs : (ChartScales.Q n ^ (-(1 / 2 : ℝ))) ^ 2 =
      (ChartScales.Q n)⁻¹ := by
    rw [← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
    norm_num [Real.rpow_neg_one]
  change (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * w.2 0) ^ 2 +
    (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * w.2 1) ^ 2 = _
  calc
    _ = (ChartScales.Q n ^ (-(1 / 2 : ℝ))) ^ 2 *
        (w.2 0 ^ 2 + w.2 1 ^ 2) := by ring
    _ = _ := by rw [hs]; ring

theorem graph_profileRadius_sq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    ((graph h n d w).1 /
      VariableGaugeMean.qLength (2 * h) (graph h n d w).2.1) ^ 2 / 2 =
        (SlowBorelBase.cartesianChart h w).2.1 := by
  have hq := physicalQ_pos hh hh1 hw
  have hQ := ChartScales.Q_pos n
  have hqc : 0 < SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1 := by
    rw [graph_q_eq hh hh1 n d hw]
    exact div_pos hq hQ
  change ((graph h n d w).1 /
    Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1)) ^ 2 / 2 = _
  rw [div_pow, Real.sq_sqrt hqc.le, graph_radius_sq, graph_q_eq hh hh1 n d hw]
  change ((w.2 0 ^ 2 + w.2 1 ^ 2) / ChartScales.Q n /
    (physicalQ h w / ChartScales.Q n)) / 2 =
      ((w.2 0 ^ 2 + w.2 1 ^ 2) / 2) / physicalQ h w
  rw [div_div_div_cancel_right₀ hQ.ne']
  ring

theorem graph_profileRadius_mem {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (n d : ℕ) {w : SpaceTime}
    (hw : w ∈ preterminal)
    (hactive : (SlowBorelBase.cartesianChart F.data.h w).2.1 ∈
      Icc (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    (graph F.data.h n d w).1 /
      VariableGaugeMean.qLength (2 * F.data.h) (graph F.data.h n d w).2.1 ∈
        Icc (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) := by
  have hsq := graph_profileRadius_sq F.data.h_pos F.data.h_lt_half n d hw
  have hr := div_nonneg (graph_radius_nonneg F.data.h n d w)
    (graph_length_pos F.data.h_pos F.data.h_lt_half n d hw).le
  have ha := PrimaryTargetBounds.leftRadius_pos W
  have hb := PrimaryTargetBounds.rightRadius_pos W
  have hasq : PrimaryTargetBounds.leftRadius W ^ 2 =
      2 * NominalConeAssembly.activeLeft W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)
  have hbsq : PrimaryTargetBounds.rightRadius W ^ 2 =
      2 * NominalConeAssembly.activeRight W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)
  constructor
  · apply (sq_le_sq₀ ha.le hr).mp
    nlinarith [hactive.1]
  · apply (sq_le_sq₀ hr hb.le).mp
    nlinarith [hactive.2]

/-! ## Closure of a moving strip, including both radial endpoints -/

theorem mem_closure_strip (G : SignedMeanGain.Geometry) {x : Point}
    (hx : x ∈ G.domain)
    (hr : (LocalSignedRequest.profileMap G.coord x).1 ∈ Icc G.patch.a G.patch.b) :
    x ∈ closure G.strip.domain := by
  let ell := Real.sqrt (MeanRankUpdate.chartQ G.coord x)
  have hell : 0 < ell := Real.sqrt_pos.mpr (G.region.chartQ_pos hx)
  let f : ℝ → Point := fun r => (r * ell, x.2)
  have hf : Continuous f := (continuous_id.mul continuous_const).prodMk continuous_const
  have hmaps : MapsTo f (Ioo G.patch.a G.patch.b) G.strip.domain := by
    intro r hr
    apply (LocalSignedRequest.movingStrip_domain G.region G.patch.a G.patch.b
      G.leftWeight G.rightWeight G.patch.a_pos G.left_pos G.right_pos G.epsilon G.slow
      G.epsilon_pos G.epsilon_le_one G.slow_ge_one (f r)).mpr
    refine ⟨hx, ?_⟩
    change r * ell / ell ∈ Ioo G.patch.a G.patch.b
    simpa only [mul_div_cancel_right₀ _ hell.ne'] using hr
  have hrcl : x.1 / ell ∈ closure (Ioo G.patch.a G.patch.b) := by
    rw [closure_Ioo G.patch.a_lt_b.ne]
    exact hr
  have hfcl := hf.continuousAt.continuousWithinAt.mem_closure hrcl hmaps
  have hfx : f (x.1 / ell) = x := by
    dsimp only [f]
    rw [div_mul_cancel₀ _ hell.ne']
  rwa [hfx] at hfcl

theorem mem_closure_liftStrip (G : SignedMeanGain.Geometry) {x : Point}
    (hx : x ∈ G.domain)
    (hr : (LocalSignedRequest.profileMap G.coord x).1 ∈ Icc G.patch.a G.patch.b)
    (theta : ℝ) :
    (x, theta) ∈ closure (HarmonicResidual.liftDomain G.strip.domain) := by
  have hc := mem_closure_strip G hx hr
  have hf : Continuous (fun y : Point => (y, theta)) :=
    continuous_id.prodMk continuous_const
  exact hf.continuousAt.continuousWithinAt.mem_closure hc
    (fun y hy => ⟨hy, Set.mem_univ theta⟩)

/-! ## The actual selected band belongs to the native slow window -/

theorem graph_slow_mem_standard {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hqQ : physicalQ h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ h w) :
    (graph h n d w).2.1 ∈ (ActualSignedGeometry.standardSlowRegion hh hh1).carrier := by
  change 0 < (graph h n d w).2.1.1 ∧
    SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1 ∈ Ioo (1 / 2 : ℝ) 2
  refine ⟨graph_time_pos h n d hw, ?_⟩
  rw [graph_q_eq hh hh1 n d hw]
  have hQ := ChartScales.Q_pos n
  constructor
  · apply (lt_div_iff₀ hQ).mpr
    linarith
  · apply (div_lt_iff₀ hQ).mpr
    linarith

theorem selected_mean_domain (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w) :
    graph ActualPrimary.h n d w ∈ ActualInitialization.geometry.domain :=
  graph_slow_mem_standard ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n d hw hqQ hQq

theorem selected_mean_radius_pos (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ active) : 0 < (graph ActualPrimary.h n d w).1 := by
  have hr := graph_profileRadius_mem ActualPrimary.nominal n d hw hactive
  have hell := graph_length_pos ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n d hw
  exact (mul_pos (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) hell).trans_le
    ((le_div_iff₀ hell).mp hr.1)

theorem selected_annulus (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ active)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w) :
    scaledRadial n w ∈ annulus inner outer := by
  have hq := physicalQ_pos ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half hw
  have hlo : physicalQ ActualPrimary.h w / 2 ≤ ChartScales.Q n := by linarith
  have hell := graph_length_pos ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 hw
  have hlen := graph_length_bounds ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 hw hlo hQq.le
  have hr := graph_profileRadius_mem ActualPrimary.nominal n 0 hw hactive
  have hloR := (le_div_iff₀ hell).mp hr.1
  have hhiR := (div_le_iff₀ hell).mp hr.2
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have hRlo : PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 2 ≤
      (graph ActualPrimary.h n 0 w).1 := by nlinarith [hlen.1]
  have hRhi : (graph ActualPrimary.h n 0 w).1 ≤
      2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal := by nlinarith [hlen.2]
  rw [graph_radius] at hRlo hRhi
  refine ⟨?_, ?_⟩
  · simpa only [outer, Metric.mem_closedBall, dist_zero_right] using
      (PolarCharts.norm_le_radius (scaledRadial n w)).trans hRhi
  · change PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4 ≤ ‖scaledRadial n w‖
    linarith only [hRlo, PolarCharts.radius_le_two_norm (scaledRadial n w)]

theorem selected_chart_exists (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ active)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w) :
    ∃ j : PolarCharts.Index, scaledRadial n w ∈ PolarCharts.chartDomain inner j := by
  obtain ⟨j, hj⟩ := PolarCharts.annulus_covered inner_pos
    (selected_annulus n hw hactive hqQ hQq)
  exact ⟨j, PolarCharts.sector_subset_chartDomain inner_pos j hj⟩

theorem selected_polar_nativeDomain (j : PolarCharts.Index) (n d : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal) (hactive : w ∈ active)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w)
    (hj : scaledRadial n w ∈ PolarCharts.chartDomain inner j) :
    PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈ nativeDomain := by
  rw [PhysicalResidualJetBounds.polarGraph_eq_meanGraph inner_pos ActualPrimary.h j n d hj]
  exact ⟨⟨selected_mean_domain n d hw hqQ hQq, selected_mean_radius_pos n d hw hactive⟩,
    Set.mem_univ _⟩

theorem selected_polar_closure (j : PolarCharts.Index) (n d : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal) (hactive : w ∈ active)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w)
    (hj : scaledRadial n w ∈ PolarCharts.chartDomain inner j) :
    PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈
      closure (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain) := by
  rw [PhysicalResidualJetBounds.polarGraph_eq_meanGraph inner_pos ActualPrimary.h j n d hj]
  apply mem_closure_liftStrip ActualInitialization.geometry
    (selected_mean_domain n d hw hqQ hQq)
  change (graph ActualPrimary.h n d w).1 /
    VariableGaugeMean.qLength (2 * ActualPrimary.h) (graph ActualPrimary.h n d w).2.1 ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
  exact graph_profileRadius_mem ActualPrimary.nominal n d hw hactive

/-! ## Selection above an arbitrary certified floor -/

theorem exists_selected_band (N : ℕ) {w : SpaceTime}
    (hw : w ∈ preterminal) (hactive : w ∈ active)
    (hsmall : physicalQ ActualPrimary.h w ≤ ChartScales.Q N) :
    ∃ n : ℕ, N ≤ n ∧ physicalQ ActualPrimary.h w ≤ ChartScales.Q n ∧
      ChartScales.Q n < 2 * physicalQ ActualPrimary.h w ∧
      scaledRadial n w ∈ annulus inner outer ∧
      ∀ (j : PolarCharts.Index) (d : ℕ),
        scaledRadial n w ∈ PolarCharts.chartDomain inner j →
          PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈ nativeDomain ∧
          PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈
            closure (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain) := by
  obtain ⟨n, hn, hqQ, hQq⟩ := exists_comparable_band N
    (physicalQ_pos ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hw)
    hsmall
  refine ⟨n, hn, hqQ, hQq, selected_annulus n hw hactive hqQ hQq, ?_⟩
  intro j d hj
  exact ⟨selected_polar_nativeDomain j n d hw hactive hqQ hQq hj,
    selected_polar_closure j n d hw hactive hqQ hQq hj⟩

theorem exists_selected_band_of_qbig (firstBand : ℕ) {qbig : ℝ} {w : SpaceTime}
    (hw : w ∈ preterminal) (hactive : w ∈ active)
    (hsmall : physicalQ ActualPrimary.h w ≤ qbig)
    (hfloor : qbig ≤ ChartScales.Q firstBand) :
    ∃ n : ℕ, firstBand ≤ n ∧ physicalQ ActualPrimary.h w ≤ ChartScales.Q n ∧
      ChartScales.Q n < 2 * physicalQ ActualPrimary.h w ∧
      scaledRadial n w ∈ annulus inner outer ∧
      ∀ (j : PolarCharts.Index) (d : ℕ),
        scaledRadial n w ∈ PolarCharts.chartDomain inner j →
          PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈ nativeDomain ∧
          PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈
            closure (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain) :=
  exists_selected_band firstBand hw hactive (hsmall.trans hfloor)

end NavierStokes.ActualPolarCoverage
