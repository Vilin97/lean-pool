/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
import LeanPool.NavierStokesAndEuler.NavierStokes.SolutionDifference
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Integration of periodic fields on the unit cube

The integral is product Lebesgue measure in the usual three coordinates, pulled
back along the standard continuous linear equivalence to Euclidean space.
Integration by parts is derived from Mathlib's proved box divergence theorem.
-/

@[expose] public section


noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology

namespace NavierStokes.PeriodicIntegration

open ProblemStatement

/-- Coords: an abbreviation for `Fin 3 → ℝ`. -/
abbrev Coords := Fin 3 → ℝ

/-- To space, given by `(EuclideanSpace.equiv (Fin 3) ℝ).symm`. -/
def toSpace : Coords ≃L[ℝ] Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm

/-- Cube, given by `Icc 0 1`. -/
def cube : Set Coords := Icc 0 1

/-- Cube measure, constructed using `volume.restrict`. -/
def cubeMeasure : Measure Coords := volume.restrict cube

instance : IsFiniteMeasure cubeMeasure := by
  change IsFiniteMeasure (volume.restrict (Icc (0 : Coords) 1))
  exact isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne

/-- Cube integral, given by `∫ y, f (toSpace y) ∂cubeMeasure`. -/
def cubeIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) : E := ∫ y, f (toSpace y) ∂cubeMeasure

/-- Unit periods, given by `∀ x i, f (x + coordinateVector i) = f x`. -/
def UnitPeriods {E : Type*} (f : Space → E) : Prop :=
  ∀ x i, f (x + coordinateVector i) = f x

/-- Spatial partial, given by `fderiv ℝ f x (coordinateVector i)`. -/
def spatialPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (f : Space → E) (x : Space) : E :=
  fderiv ℝ f x (coordinateVector i)

@[simp] theorem toSpace_apply (y : Coords) (i : Fin 3) : toSpace y i = y i := rfl

@[simp] theorem toSpace_single (i : Fin 3) :
    toSpace (Pi.single i 1) = coordinateVector i := rfl

theorem continuous_partial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ 1 f) (i : Fin 3) : Continuous (spatialPartial i f) :=
  SolutionDifference.continuous_partial hf i

theorem integrable_cube {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} (hf : Continuous f) : Integrable (fun y => f (toSpace y)) cubeMeasure :=
  (hf.comp toSpace.continuous).integrableOn_Icc

@[simp] theorem cubeIntegral_zero : cubeIntegral (fun _ : Space => (0 : ℝ)) = 0 := by
  simp [cubeIntegral]

theorem cubeIntegral_add {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g) :
    cubeIntegral (fun x => f x + g x) = cubeIntegral f + cubeIntegral g := by
  exact integral_add (integrable_cube hf) (integrable_cube hg)

theorem cubeIntegral_sub {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g) :
    cubeIntegral (fun x => f x - g x) = cubeIntegral f - cubeIntegral g := by
  exact integral_sub (integrable_cube hf) (integrable_cube hg)

theorem cubeIntegral_neg (f : Space → ℝ) :
    cubeIntegral (fun x => -f x) = -cubeIntegral f := by
  exact integral_neg _

theorem cubeIntegral_const_mul (c : ℝ) (f : Space → ℝ) :
    cubeIntegral (fun x => c * f x) = c * cubeIntegral f := by
  exact integral_const_mul _ _

theorem cubeIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → Space → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    cubeIntegral (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeIntegral (f i) := by
  exact MeasureTheory.integral_finsetSum s (fun i hi => integrable_cube (hf i hi))

theorem cubeIntegral_nonneg {f : Space → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeIntegral f := integral_nonneg fun y => hf (toSpace y)

theorem cubeIntegral_mono {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x ≤ g x) : cubeIntegral f ≤ cubeIntegral g :=
  integral_mono (integrable_cube hf) (integrable_cube hg) fun y => hfg (toSpace y)

theorem cubeIntegral_nonneg_on_cube {f : Space → ℝ}
    (hf : ∀ y ∈ cube, 0 ≤ f (toSpace y)) : 0 ≤ cubeIntegral f := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet cube from measurableSet_Icc)] with y hy
  exact hf y hy

theorem cubeIntegral_mono_on_cube {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ y ∈ cube, f (toSpace y) ≤ g (toSpace y)) : cubeIntegral f ≤ cubeIntegral g := by
  apply integral_mono_ae (integrable_cube hf) (integrable_cube hg)
  filter_upwards [ae_restrict_mem (show MeasurableSet cube from measurableSet_Icc)] with y hy
  exact hfg y hy

private theorem insertNth_one_eq (i : Fin 3) (y : Fin 2 → ℝ) :
    i.insertNth (1 : ℝ) y = (i.insertNth (0 : ℝ) y : Coords) + Pi.single i (1 : ℝ) := by
  ext k
  by_cases hk : k = i
  · subst k
    simp
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    simp

private theorem coord_partial_eq {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 3) (y : Coords) :
    fderiv ℝ (fun z : Coords => f (toSpace z)) y (Pi.single i 1) =
      spatialPartial i f (toSpace y) := by
  have hd := ((hf.differentiable (by norm_num) (toSpace y)).hasFDerivAt.comp y
    toSpace.hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ toSpace) y (Pi.single i 1) = _
  rw [hd]
  rfl

/-- A genuine coordinate derivative integrates to zero for a `C¹` unit-periodic field. -/
theorem cubeIntegral_partial_eq_zero {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : UnitPeriods f) (i : Fin 3) : cubeIntegral (spatialPartial i f) = 0 := by
  let g : Coords → ℝ := fun y => f (toSpace y)
  have hg : ContDiff ℝ 1 g := hf.comp toSpace.contDiff
  let F : Fin 3 → Coords → ℝ := fun k y => if k = i then g y else 0
  let F' : Fin 3 → Coords → Coords →L[ℝ] ℝ :=
    fun k y => if k = i then fderiv ℝ g y else 0
  have hsum (y : Coords) :
      (∑ k : Fin 3, F' k y (Pi.single k 1)) = fderiv ℝ g y (Pi.single i 1) := by
    rw [Finset.sum_eq_single i]
    · simp [F']
    · intro k _ hki
      simp [F', hki]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  have Hc : ∀ k, ContinuousOn (F k) (Icc (0 : Coords) 1) := by
    intro k
    by_cases hk : k = i
    · simpa [F, hk] using hg.continuous.continuousOn
    · simpa [F, hk] using (continuous_const : Continuous (fun _ : Coords => (0 : ℝ))).continuousOn
  have Hd : ∀ y ∈ (univ.pi fun k : Fin 3 => Ioo ((0 : Coords) k) ((1 : Coords) k)) \ ∅,
      ∀ k, HasFDerivAt (F k) (F' k y) y := by
    intro y _ k
    by_cases hk : k = i
    · simpa [F, F', hk] using (hg.differentiable (by norm_num) y).hasFDerivAt
    · simpa [F, F', hk] using (hasFDerivAt_const (0 : ℝ) y)
  have Hi : IntegrableOn (fun y => ∑ k : Fin 3, F' k y (Pi.single k 1))
      (Icc (0 : Coords) 1) := by
    simp_rw [hsum]
    have hc : Continuous (fun y : Coords => fderiv ℝ g y (Pi.single i 1)) :=
      (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hc.integrableOn_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable'
    (n := 2) (E := ℝ) (0 : Coords) 1 (by intro k; exact zero_le_one)
    F F' ∅ countable_empty Hc Hd Hi
  have hboundary : ∀ k : Fin 3, ∀ y : Fin 2 → ℝ,
      F k (k.insertNth 1 y) = F k (k.insertNth 0 y) := by
    intro k y
    by_cases hk : k = i
    · subst k
      simp only [F, ite_eq_left rfl, g]
      rw [insertNth_one_eq, map_add, toSpace_single]
      exact hp _ i
    · simp [F, hk]
  have hzero : (∫ y in Icc (0 : Coords) 1,
      fderiv ℝ g y (Pi.single i 1)) = 0 := by
    simpa [hsum, hboundary] using hdiv
  change (∫ y in Icc (0 : Coords) 1, spatialPartial i f (toSpace y)) = 0
  simpa only [g, coord_partial_eq hf i] using hzero

theorem partial_mul {f g : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => f y * g y) x =
      f x * spatialPartial i g x + g x * spatialPartial i f x := by
  simp only [spatialPartial, fderiv_fun_mul (hf.differentiable (by
      norm_num) x) (hg.differentiable (by norm_num) x),
    _root_.add_apply, _root_.smul_apply, smul_eq_mul]

/-- Integration by parts for actual coordinate partial derivatives on the unit torus. -/
theorem cubeIntegral_mul_partial {f g : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hpf : UnitPeriods f) (hpg : UnitPeriods g) (i : Fin 3) :
    cubeIntegral (fun x => f x * spatialPartial i g x) =
      -cubeIntegral (fun x => g x * spatialPartial i f x) := by
  have hp : UnitPeriods (fun x => f x * g x) := by
    intro x k
    change f (x + coordinateVector k) * g (x + coordinateVector k) = f x * g x
    rw [hpf x k, hpg x k]
  have hz := cubeIntegral_partial_eq_zero (hf.mul hg) hp i
  have hmul : spatialPartial i (fun y => f y * g y) =
      fun x => f x * spatialPartial i g x + g x * spatialPartial i f x :=
    funext (partial_mul hf hg i)
  rw [hmul] at hz
  rw [cubeIntegral_add (hf.continuous.fun_mul (continuous_partial hg i))
    (hg.continuous.fun_mul (continuous_partial hf i))] at hz
  exact eq_neg_of_add_eq_zero_left hz

private theorem cube_subset_closure_interior : cube ⊆ closure (interior cube) := by
  have h : closure (interior cube) = cube := by
    simp only [cube, ← pi_univ_Icc, interior_pi_set (Set.toFinite univ), interior_Icc,
      closure_pi_set, Pi.zero_apply, Pi.one_apply, closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
  exact h.symm.subset

/-- Zero integral of a continuous nonnegative field implies zero at every point
of the closed cube, including its faces. -/
theorem eq_zero_on_cube_of_nonneg_of_integral_eq_zero {f : Space → ℝ}
    (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) (hz : cubeIntegral f = 0) :
    ∀ y ∈ cube, f (toSpace y) = 0 := by
  have hae : (fun y => f (toSpace y)) =ᵐ[cubeMeasure] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => hn (toSpace y)) (integrable_cube hf)).mp hz
  exact Measure.eqOn_of_ae_eq hae (hf.comp toSpace.continuous).continuousOn
    continuousOn_const cube_subset_closure_interior

theorem eq_zero_on_cube_of_integral_norm_sq_eq_zero
    {E : Type*} [NormedAddCommGroup E] {u : Space → E}
    (hu : Continuous u) (hz : cubeIntegral (fun x => ‖u x‖ ^ 2) = 0) :
    ∀ y ∈ cube, u (toSpace y) = 0 := by
  have h := eq_zero_on_cube_of_nonneg_of_integral_eq_zero (hu.norm.pow 2)
    (fun _ => sq_nonneg _) hz
  intro y hy
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (h y hy))

section TimeDependent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I : Set ℝ} {F : ℝ × Space → E}

omit [NormedSpace ℝ E] in
private theorem continuous_space_slice
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I) :
    Continuous (fun x : Space => F (t, x)) := by
  rw [← continuousOn_univ]
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨ht, mem_univ _⟩)

omit [NormedSpace ℝ E] in
private theorem continuousOn_time_slice
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space))) (x : Space) :
    ContinuousOn (fun t : ℝ => F (t, x)) I :=
  hF.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, mem_univ _⟩)

omit [NormedSpace ℝ E] in
private theorem continuousOn_time_cube
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space))) :
    ContinuousOn (fun z : ℝ × Coords => F (z.1, toSpace z.2)) (I ×ˢ cube) :=
  hF.comp (continuous_fst.prodMk (toSpace.continuous.comp continuous_snd)).continuousOn
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

/-- Joint continuity on a compact time interval gives continuity of the actual
cube integral, including at the endpoints. -/
theorem cubeIntegral_continuousOn (hI : IsCompact I)
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t => cubeIntegral (fun x => F (t, x))) I := by
  obtain ⟨C, hC⟩ := (hI.prod (show IsCompact cube from isCompact_Icc)).exists_bound_of_continuousOn
    (continuousOn_time_cube hF)
  unfold cubeIntegral
  apply continuousOn_of_dominated (bound := fun _ : Coords => C)
  · intro t ht
    exact ((continuous_space_slice hF ht).comp toSpace.continuous).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem (show MeasurableSet cube from measurableSet_Icc)] with y hy
    exact hC (t, y) ⟨ht, hy⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun y => continuousOn_time_slice hF (toSpace y)

theorem cubeIntegral_continuousOn_Icc {a b : ℝ}
    (hF : ContinuousOn F (Icc a b ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t => cubeIntegral (fun x => F (t, x))) (Icc a b) :=
  cubeIntegral_continuousOn isCompact_Icc hF

/-- Compactness of the cube supplies the local integrable derivative majorant.
The derivative premise is the ordinary pointwise derivative of the integrand. -/
theorem hasDerivAt_cubeIntegral_of_hasDerivAt
    {G : ℝ × Space → E} (hI : IsOpen I)
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space)))
    (hG : ContinuousOn G (I ×ˢ (univ : Set Space)))
    (hd : ∀ t ∈ I, ∀ x : Space, HasDerivAt (fun s => F (s, x)) (G (t, x)) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => cubeIntegral (fun x => F (s, x)))
      (cubeIntegral (fun x => G (t, x))) t := by
  obtain ⟨ε, hε, hεI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  have hcompact : IsCompact (Metric.closedBall t ε ×ˢ cube) :=
    (isCompact_closedBall t ε).prod (show IsCompact cube from isCompact_Icc)
  have hc : ContinuousOn (fun z : ℝ × Coords => G (z.1, toSpace z.2))
      (Metric.closedBall t ε ×ˢ cube) :=
    (continuousOn_time_cube hG).mono (Set.prod_mono hεI Subset.rfl)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc
  unfold cubeIntegral
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (x₀ := t) (μ := cubeMeasure)
    (F := fun s y => F (s, toSpace y)) (F' := fun s y => G (s, toSpace y))
    (bound := fun _ : Coords => C) (Metric.ball_mem_nhds _ hε) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hI.mem_nhds ht] with s hs
    exact ((continuous_space_slice hF hs).comp toSpace.continuous).aestronglyMeasurable
  · exact integrable_cube (f := fun x : Space => F (t, x)) (continuous_space_slice hF ht)
  · exact ((continuous_space_slice hG ht).comp toSpace.continuous).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (show MeasurableSet cube from measurableSet_Icc)] with y hy
    intro s hs
    exact hC (s, y) ⟨Metric.ball_subset_closedBall hs, hy⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun y s hs => hd s (hεI (Metric.ball_subset_closedBall hs)) (toSpace
      y)

/-- Differentiation under the cube integral for a jointly `C¹` field on an open
time domain. The integrated quantity is its actual time-slice derivative. -/
theorem hasDerivAt_cubeIntegral_of_contDiffOn (hI : IsOpen I)
    (hF : ContDiffOn ℝ 1 F (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => cubeIntegral (fun x => F (s, x)))
      (cubeIntegral (fun x => deriv (fun s => F (s, x)) t)) t := by
  let G : ℝ × Space → E := fun z => fderiv ℝ F z (1, 0)
  have hprod : IsOpen (I ×ˢ (univ : Set Space)) := hI.prod isOpen_univ
  have hG : ContinuousOn G (I ×ˢ (univ : Set Space)) :=
    (hF.continuousOn_fderiv_of_isOpen hprod le_rfl).clm_apply continuousOn_const
  have hd : ∀ s ∈ I, ∀ x : Space,
      HasDerivAt (fun r => F (r, x)) (G (s, x)) s := by
    intro s hs x
    have hsx : (s, x) ∈ I ×ˢ (univ : Set Space) := ⟨hs, mem_univ x⟩
    have hfd : DifferentiableAt ℝ F (s, x) :=
      (hF.contDiffAt (hprod.mem_nhds hsx)).differentiableAt (by norm_num)
    exact hfd.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have heq : (fun x => deriv (fun s => F (s, x)) t) = fun x => G (t, x) :=
    funext fun x => (hd t ht x).deriv
  rw [heq]
  exact hasDerivAt_cubeIntegral_of_hasDerivAt hI hF.continuousOn hG hd ht

end TimeDependent

end NavierStokes.PeriodicIntegration
