/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.FrozenEstimates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Conditional H1-to-analytic reduction. Analytic dissipation and weak-solution
energy are inputs, not assertions that the corresponding PDE gates are proved. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization
open AVenhance AVenhance.Infra.Torus AVenhance.Infra.Heat
open scoped BigOperators

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraSection5H1ReductionMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraSection5H1ReductionMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraSection5H1ReductionIsProbabilityMeasure3 : IsProbabilityMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Section5

theorem H1Reduction.cube_finite : volume unitCube < ⊤ := by
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance avInfraSection5H1ReductionIsFiniteMeasure4 : IsFiniteMeasure (volume.restrict
    unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using H1Reduction.cube_finite⟩

theorem H1Reduction.l2_nonneg (f : Vec 2 → ℝ) : 0 ≤ l2NormSq f :=
  integral_nonneg fun x => sq_nonneg (f x)

theorem H1Reduction.grad_nonneg (Df : Vec 2 → Vec 2) : 0 ≤ gradNormSq Df :=
  integral_nonneg fun x => vecNormSq_nonneg (Df x)

theorem H1Reduction.st_nonneg (Df : ℝ → Vec 2 → Vec 2) : 0 ≤ spaceTimeGradNormSq Df :=
  integral_nonneg fun x => vecNormSq_nonneg (Df x.1 x.2)

theorem H1Reduction.memL2_real_pullback (G : C(UnitAddTorus (Fin 2), ℂ)) :
    MemL2On unitCube (fun x => (G (toUnitTorus 2 x)).re) := by
  have hcont : Continuous (fun x : Vec 2 => (G (toUnitTorus 2 x)).re) := by
    unfold toUnitTorus
    fun_prop
  exact MemLp.of_bound hcont.aestronglyMeasurable ‖G‖
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm _).trans (G.norm_coe_le_norm _))

/-- A real smooth representative of the datum's heat evolution. -/
def realHeatApprox {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) : Vec 2 → ℝ :=
  fun x => (heatTorusSmoothLift hs (frozenPeriodicH1ValueL2 hf) x).re

theorem H1Reduction.realHeatApprox_eq {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) :
    realHeatApprox hf hs = fun x =>
      (heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf) (toUnitTorus 2 x)).re := by
  funext x
  exact congrArg Complex.re (heatTorusSmoothLift_eq_heatTorusContinuous hs _ x)

theorem realHeatApprox_memL2 {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) :
    MemL2On unitCube (realHeatApprox hf hs) := by
  rw [H1Reduction.realHeatApprox_eq]
  exact H1Reduction.memL2_real_pullback _

theorem realHeatApprox_periodic {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) :
    IsZ2Periodic (realHeatApprox hf hs) := by
  rw [H1Reduction.realHeatApprox_eq]
  exact (isZdPeriodic_iff_frozen _).mp (isZdPeriodic_fromUnitTorus (fun x => (heatTorusContinuous hs
    (frozenPeriodicH1ValueL2 hf) x).re))

theorem H1Reduction.transfer_sub_realHeat_norm_le {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) :
    ‖frozenCellToTorusL2 (hf.2.2.1.sub (realHeatApprox_memL2 hf hs))‖ ≤
      ‖frozenPeriodicH1ValueL2 hf - heatTorusL2 s hs.le (frozenPeriodicH1ValueL2 hf)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  have h1 := (memLp_frozenCellTransfer hf.2.2.1).coeFn_toLp
  have h2 := (memLp_frozenCellTransfer (hf.2.2.1.sub (realHeatApprox_memL2 hf hs))).coeFn_toLp
  have h3 := (heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf)).coeFn_toLp (p := 2) (μ :=
      (volume : Measure (UnitAddTorus (Fin 2)))) (𝕜 := ℂ)
  filter_upwards [h1, h2, h3, Lp.coeFn_sub (frozenPeriodicH1ValueL2 hf)
    (heatTorusL2 s hs.le (frozenPeriodicH1ValueL2 hf))] with x hx1 hx2 hx3 hx4
  change (frozenCellToTorusL2 (hf.2.2.1.sub (realHeatApprox_memL2 hf hs)) :
    UnitAddTorus (Fin 2) → ℂ) x = _ at hx2
  change (frozenCellToTorusL2 hf.2.2.1 : UnitAddTorus (Fin 2) → ℂ) x = _ at hx1
  rw [hx2, hx4]
  change ‖((f (unitTorusRepresentative 2 x) - realHeatApprox hf hs
    (unitTorusRepresentative 2 x) : ℝ) : ℂ)‖ ≤ _
  rw [H1Reduction.realHeatApprox_eq]
  simp only [toUnitTorus_unitTorusRepresentative]
  change _ ≤ ‖(frozenCellToTorusL2 hf.2.2.1 : UnitAddTorus (Fin 2) → ℂ) x - _‖
  rw [hx1, ← heatTorusContinuous_toLp hs, hx3]
  simpa only [Complex.norm_real, Real.norm_eq_abs, periodicToTorus, Complex.sub_re,
      Complex.ofReal_re] using
    Complex.abs_re_le_norm ((f (unitTorusRepresentative 2 x) : ℂ) -
      heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf) x)

/-- the distance estimate: the missing distance estimate, in the actual real carriers. -/
theorem realHeatApprox_error_sq {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) :
    l2NormSq (fun x => f x - realHeatApprox hf hs x) ≤ s * gradNormSq Df := by
  change l2NormSq (f - realHeatApprox hf hs) ≤ _
  rw [← normSq_frozenCellToTorusL2_eq (hf.2.2.1.sub (realHeatApprox_memL2 hf hs))]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (H1Reduction.transfer_sub_realHeat_norm_le hf hs) |>.trans
      (normSq_sub_heatTorusL2_le_frozenPeriodicH1 hf hs.le)

theorem H1Reduction.transfer_real_pullback_norm_le (G : C(UnitAddTorus (Fin 2), ℂ)) :
    ‖frozenCellToTorusL2 (H1Reduction.memL2_real_pullback G)‖ ≤
      ‖ContinuousMap.toLp 2 volume ℂ G‖ := by
  apply Lp.norm_le_norm_of_ae_le
  have h1 := (memLp_frozenCellTransfer (H1Reduction.memL2_real_pullback G)).coeFn_toLp
  have h2 := G.coeFn_toLp (p := 2) (μ := (volume : Measure (UnitAddTorus (Fin 2)))) (𝕜 := ℂ)
  filter_upwards [h1, h2] with x hx1 hx2
  change (frozenCellToTorusL2 (H1Reduction.memL2_real_pullback G) : UnitAddTorus (Fin 2) → ℂ) x =
      _ at hx1
  rw [hx1, hx2]
  simpa only [periodicToTorus, toUnitTorus_unitTorusRepresentative, Complex.norm_real,
    Real.norm_eq_abs] using Complex.abs_re_le_norm (G x)

theorem H1Reduction.transfer_sub {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    (hg : MemL2On unitCube g) :
    frozenCellToTorusL2 (hf.sub hg) = frozenCellToTorusL2 hf - frozenCellToTorusL2 hg := by
  apply Lp.ext
  have h1 := (memLp_frozenCellTransfer hf).coeFn_toLp
  have h2 := (memLp_frozenCellTransfer hg).coeFn_toLp
  have h3 := (memLp_frozenCellTransfer (hf.sub hg)).coeFn_toLp
  filter_upwards [h1, h2, h3, Lp.coeFn_sub (frozenCellToTorusL2 hf)
    (frozenCellToTorusL2 hg)] with x hx1 hx2 hx3 hx4
  change (frozenCellToTorusL2 (hf.sub hg) : UnitAddTorus (Fin 2) → ℂ) x = _ at hx3
  change (frozenCellToTorusL2 hf : UnitAddTorus (Fin 2) → ℂ) x = _ at hx1
  change (frozenCellToTorusL2 hg : UnitAddTorus (Fin 2) → ℂ) x = _ at hx2
  rw [hx3, hx4]
  simp only [Pi.sub_apply]
  rw [hx1, hx2]
  simp only [periodicToTorus, Complex.ofReal_sub]

theorem H1Reduction.value_norm {f : Vec 2 → ℝ} (hf : MemL2On unitCube f) :
    ‖frozenCellToTorusL2 hf‖ = Real.sqrt (l2NormSq f) := by
  rw [← normSq_frozenCellToTorusL2_eq hf, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Heat evolution preserves the mean-zero condition. -/
theorem realHeatApprox_meanZero {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) {s : ℝ} (hs : 0 < s) :
    MeanZeroOn unitCube (realHeatApprox hf hs) := by
  have hmean : ∫ x : UnitAddTorus (Fin 2), frozenPeriodicH1ValueL2 hf x = 0 := by
    have heq := (memLp_frozenCellTransfer hf.2.2.1).coeFn_toLp
    change ∫ x : UnitAddTorus (Fin 2), frozenCellToTorusL2 hf.2.2.1 x = 0
    change (frozenCellToTorusL2 hf.2.2.1 : UnitAddTorus (Fin 2) → ℂ) =ᵐ[volume]
      periodicToTorus (fun x => (f x : ℂ)) at heq
    rw [integral_congr_ae heq, integral_periodicToTorus_eq_unitCell,
      integral_unitCell_eq_unitCube, integral_complex_ofReal]
    exact congrArg (fun x : ℝ => (x : ℂ)) hm
  have hmeanHeat := integral_heatTorusL2 hs.le (frozenPeriodicH1ValueL2 hf)
  rw [hmean] at hmeanHeat
  have heq := (heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf)).coeFn_toLp
    (p := 2) (μ := (volume : Measure (UnitAddTorus (Fin 2)))) (𝕜 := ℂ)
  rw [← heatTorusContinuous_toLp hs, integral_congr_ae heq] at hmeanHeat
  unfold MeanZeroOn
  rw [H1Reduction.realHeatApprox_eq]
  rw [← integral_unitCell_eq_unitCube]
  change (∫ x in unitCell 2, fromUnitTorus (fun y =>
    (heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf) y).re) x) = 0
  change (∫ x in unitCellAt 2 (fun _ => 0), fromUnitTorus (fun y =>
    (heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf) y).re) x) = 0
  rw [← integral_fromUnitTorus_eq_unitCellAt]
  have hInt : Integrable (heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf)) := by
    simpa only [integrableOn_univ] using
      (heatTorusContinuous hs (frozenPeriodicH1ValueL2
          hf)).continuous.continuousOn.integrableOn_compact isCompact_univ
  have hr := congrArg Complex.re hmeanHeat
  have he := Complex.reCLM.integral_comp_comm hInt
  change (∫ x : UnitAddTorus (Fin 2),
    (heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf) x).re) =
      (∫ x : UnitAddTorus (Fin 2), heatTorusContinuous hs (frozenPeriodicH1ValueL2 hf) x).re at he
  exact he.trans hr

/-- Multiplicity of a coordinate index in an ordered tuple of derivative directions. -/
def H1Reduction.tupleIndex {n : ℕ} (i : Fin n → Fin 2) (a : Fin 2) : ℕ :=
  Fintype.card {j : Fin n // i j = a}

theorem H1Reduction.tupleIndex_degree {n : ℕ} (i : Fin n → Fin 2) :
    multiIndexDegree (H1Reduction.tupleIndex i) = n := by
  classical
  change (∑ a : Fin 2, Fintype.card {j : Fin n // i j = a}) = n
  rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv i), Fintype.card_fin]

theorem H1Reduction.tupleIndex_factor {n : ℕ} (i : Fin n → Fin 2) (k : Frequency) :
    (2 * Real.pi * Complex.I) ^ n *
      (∏ j : Fin n, frequencyPhaseCLM k (basisVec (i j))) =
        multiIndexFourierFactor (H1Reduction.tupleIndex i) k := by
  classical
  have hp : (∏ a : Fin 2, (k a : ℝ) ^ H1Reduction.tupleIndex i a) = ∏ j : Fin n, (k (i j) : ℝ) := by
    simpa only [Finset.prod_const, Finset.card_univ, H1Reduction.tupleIndex] using
      Fintype.prod_fiberwise' i (fun a => (k a : ℝ))
  have he : n = H1Reduction.tupleIndex i 0 + H1Reduction.tupleIndex i 1 := by
    exact (H1Reduction.tupleIndex_degree i).symm.trans (degree_eq_zero_one _)
  have hv : ∀ a : Fin 2, frequencyPhaseCLM k (basisVec a) = (k a : ℝ) := by
    intro a
    fin_cases a <;> simp [frequencyPhaseCLM_apply, basisVec, Pi.single_apply]
  -- Use the fiber product before expanding the two coordinate powers.
  simp_rw [hv]
  rw [← hp]
  nth_rw 1 [he]
  simp only [multiIndexFourierFactor, Fin.prod_univ_two, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_intCast]
  rw [pow_add, mul_pow, mul_pow]
  ring

theorem H1Reduction.realHeatApprox_derivative_eq {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) (n : ℕ) (i : Fin n → Fin 2) (x : Vec 2) :
    iteratedFDeriv ℝ n (realHeatApprox hf hs) x (fun j => basisVec (i j)) =
      (heatDerivativeTorusContinuous hs (frozenPeriodicH1ValueL2 hf) (H1Reduction.tupleIndex i)
        (toUnitTorus 2 x)).re := by
  have hcd := heatTorusSmoothLift_contDiff hs (frozenPeriodicH1ValueL2 hf)
  rw [show realHeatApprox hf hs = Complex.reCLM ∘
    heatTorusSmoothLift hs (frozenPeriodicH1ValueL2 hf) from rfl,
    Complex.reCLM.iteratedFDeriv_comp_left hcd.contDiffAt (by simp)]
  change (iteratedFDeriv ℝ n (heatTorusSmoothLift hs (frozenPeriodicH1ValueL2 hf)) x
    (fun j => basisVec (i j))).re = _
  congr 1
  rw [heatTorusSmoothLift_iteratedFDeriv_apply,
    heatDerivativeTorusContinuous_apply_toUnitTorus]
  apply tsum_congr
  intro k
  rw [mFourierCoeff_heatTorusL2, heatDerivativeMultiplier, ← H1Reduction.tupleIndex_factor i k]
  ring

/-- The real heat approximation satisfies the ordered-coordinate derivative bound. -/
theorem realHeatApprox_derivative_bound {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) (n : ℕ) (i : Fin n → Fin 2) :
    Real.sqrt (∫ x in unitCube,
      (iteratedFDeriv ℝ n (realHeatApprox hf hs) x (fun j => basisVec (i j))) ^ 2) ≤
        (n.factorial : ℝ) * (1 / Real.sqrt s) ^ n * Real.sqrt (l2NormSq f) := by
  simp_rw [H1Reduction.realHeatApprox_derivative_eq hf hs n i]
  change Real.sqrt (l2NormSq (fun x =>
    (heatDerivativeTorusContinuous hs (frozenPeriodicH1ValueL2 hf) (H1Reduction.tupleIndex i)
      (toUnitTorus 2 x)).re)) ≤ _
  rw [← H1Reduction.value_norm (H1Reduction.memL2_real_pullback _)]
  have hn := norm_heatTorusSmoothLift_multiIndexDerivative_le_frozenH1 hf hs
      (H1Reduction.tupleIndex i)
  rw [H1Reduction.tupleIndex_degree] at hn
  exact (H1Reduction.transfer_real_pullback_norm_le _).trans hn

/-- The gradient-only length scale, including the total value at zero data. -/
def datumLength (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2) : ℝ :=
  Real.sqrt (l2NormSq f) / Real.sqrt (gradNormSq Df)

theorem H1Reduction.gradient_pos {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f) :
    0 < gradNormSq Df := by
  have hP := meanZero_frozenPeriodicH1_fourierPoincare hf hm
  by_contra h
  have hh := mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr (by positivity : 0 ≤ 4 * Real.pi ^ 2)) (le_of_not_gt h)
  exact (not_le_of_gt hA) (hP.trans hh)

theorem H1Reduction.datumLength_pos {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f) :
    0 < datumLength f Df :=
  div_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr (H1Reduction.gradient_pos hf hm hA))

theorem H1Reduction.scale_energy {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f) :
    datumLength f Df ^ 2 * gradNormSq Df = l2NormSq f := by
  unfold datumLength
  rw [div_pow, Real.sq_sqrt hA.le, Real.sq_sqrt (H1Reduction.gradient_pos hf hm hA).le,
    div_mul_cancel₀ _ (H1Reduction.gradient_pos hf hm hA).ne']

theorem H1Reduction.normalization_loss {N M r : ℝ} (hM : 0 ≤ M)
    (hNM : N ≤ 2 * M) (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) * (1 / r) ^ n * N ≤ M * ((n.factorial : ℝ) / (r / 2) ^ n) := by
  have he : (n.factorial : ℝ) / (r / 2) ^ n =
      (n.factorial : ℝ) * (1 / r) ^ n * (2 : ℝ) ^ n := by
    rw [div_pow, div_div_eq_mul_div, one_div, inv_pow]
    ring
  have hpow : (2 : ℝ) ≤ 2 ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have hfac : 0 ≤ (n.factorial : ℝ) * (1 / r) ^ n := by positivity
  rw [he]
  calc
    (n.factorial : ℝ) * (1 / r) ^ n * N ≤
        (n.factorial : ℝ) * (1 / r) ^ n * (2 * M) := mul_le_mul_of_nonneg_left hNM hfac
    _ ≤ (n.factorial : ℝ) * (1 / r) ^ n * (2 ^ n * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hM) hfac
    _ = _ := by ring

/-- Heat smoothing produces an actual analytic datum and closes the distance estimate. -/
theorem analytic_approximation {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f)
    {α : ℝ} (hα : 0 < α) (hαsmall : α ≤ 1 / 4) :
    ∃ g : Vec 2 → ℝ, MemL2On unitCube g ∧ IsZ2Periodic g ∧ MeanZeroOn unitCube g ∧
      ContDiff ℝ (⊤ : ℕ∞) g ∧ IsThetaAnalytic (α * datumLength f Df / 2) g ∧
      l2NormSq (f - g) ≤ α ^ 2 * l2NormSq f ∧
      l2NormSq f / 4 ≤ l2NormSq g := by
  have hL := H1Reduction.datumLength_pos hf hm hA
  let s := α ^ 2 * datumLength f Df ^ 2
  have hs : 0 < s := mul_pos (sq_pos_of_pos hα) (sq_pos_of_pos hL)
  let g := realHeatApprox hf hs
  have hg := realHeatApprox_memL2 hf hs
  have herr : l2NormSq (f - g) ≤ α ^ 2 * l2NormSq f := by
    have h := realHeatApprox_error_sq hf hs
    change l2NormSq (f - g) ≤ s * gradNormSq Df at h
    have he : s * gradNormSq Df = α ^ 2 * l2NormSq f := by
      dsimp [s]
      rw [mul_assoc, H1Reduction.scale_energy hf hm hA]
    exact h.trans_eq he
  have herrNorm : Real.sqrt (l2NormSq (f - g)) ≤ α * Real.sqrt (l2NormSq f) := by
    calc
      Real.sqrt (l2NormSq (f - g)) ≤ Real.sqrt (α ^ 2 * l2NormSq f) :=
        Real.sqrt_le_sqrt herr
      _ = α * Real.sqrt (l2NormSq f) := by
        rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq_eq_abs, abs_of_pos hα]
  have htri := norm_le_norm_sub_add (frozenCellToTorusL2 hf.2.2.1) (frozenCellToTorusL2 hg)
  rw [← H1Reduction.transfer_sub hf.2.2.1 hg, H1Reduction.value_norm, H1Reduction.value_norm,
      H1Reduction.value_norm] at htri
  change Real.sqrt (l2NormSq f) ≤ Real.sqrt (l2NormSq (f - g)) +
    Real.sqrt (l2NormSq g) at htri
  have hsmall := mul_le_mul_of_nonneg_right hαsmall (Real.sqrt_nonneg (l2NormSq f))
  have hnorm : Real.sqrt (l2NormSq f) ≤ 2 * Real.sqrt (l2NormSq g) := by
    linarith only [htri, herrNorm, hsmall, Real.sqrt_nonneg (l2NormSq f)]
  have hnormSq : l2NormSq f / 4 ≤ l2NormSq g := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (l2NormSq f))
      (by positivity : 0 ≤ 2 * Real.sqrt (l2NormSq g))).2 hnorm
    rw [mul_pow, Real.sq_sqrt (H1Reduction.l2_nonneg f), Real.sq_sqrt (H1Reduction.l2_nonneg g)]
        at hsq
    linarith only [hsq]
  have hsroot : Real.sqrt s = α * datumLength f Df := by
    dsimp [s]
    rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_pos hα, abs_of_pos hL]
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := by
    change ContDiff ℝ (⊤ : ℕ∞) (Complex.reCLM ∘
      heatTorusSmoothLift hs (frozenPeriodicH1ValueL2 hf))
    exact Complex.reCLM.contDiff.comp
      (heatTorusSmoothLift_contDiff hs (frozenPeriodicH1ValueL2 hf))
  refine ⟨g, hg, realHeatApprox_periodic hf hs, realHeatApprox_meanZero hf hm hs,
    hgc, ?_, herr, hnormSq⟩
  intro n hn i
  have hd := realHeatApprox_derivative_bound hf hs n i
  have hnormBound := H1Reduction.normalization_loss (Real.sqrt_nonneg (l2NormSq g)) hnorm
    (Real.sqrt_pos.mpr hs) hn
  rw [hsroot] at hd hnormBound
  exact hd.trans hnormBound

/-- Explicit smoothing parameter; p is the exponent of the squared energy. -/
def reductionAlpha (c p L : ℝ) : ℝ :=
  min (1 / 4) ((c * (L / 2) ^ p / 32) ^ (1 / (2 - p)))

theorem H1Reduction.reductionAlpha_pos {c p L : ℝ} (hc : 0 < c) (hL : 0 < L) :
    0 < reductionAlpha c p L := by
  unfold reductionAlpha
  exact lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)

theorem H1Reduction.reductionAlpha_small {c p L : ℝ}
    (hc : 0 < c) (hp : p < 2) (hL : 0 < L) :
    reductionAlpha c p L ^ 2 ≤ c * (reductionAlpha c p L * L / 2) ^ p / 32 := by
  let α := reductionAlpha c p L
  let B := c * (L / 2) ^ p / 32
  have hα : 0 < α := H1Reduction.reductionAlpha_pos hc hL
  have hB : 0 < B := by dsimp [B]; positivity
  have hle : α ≤ B ^ (2 - p)⁻¹ := by
    have hm : α ≤ B ^ (1 / (2 - p)) := min_le_right (1 / 4 : ℝ) (B ^ (1 / (2 - p)))
    simpa only [one_div] using hm
  have hpow := Real.rpow_le_rpow hα.le hle (sub_nonneg.mpr hp.le)
  rw [Real.rpow_inv_rpow hB.le (sub_pos.mpr hp).ne'] at hpow
  calc
    α ^ 2 = α ^ (2 - p) * α ^ p := by
      rw [← Real.rpow_add hα, sub_add_cancel, Real.rpow_two]
    _ ≤ B * α ^ p := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hα.le _)
    _ = c * (α * L / 2) ^ p / 32 := by
      rw [show α * L / 2 = α * (L / 2) by ring, Real.mul_rpow hα.le (by positivity)]
      dsimp [B]
      ring

/-- Total positive dissipation coefficient, capped at one as required by the H¹ reduction. -/
def reductionRho (c p L : ℝ) : ℝ :=
  if 0 < L then min 1 (Real.sqrt (c * (reductionAlpha c p L * L / 2) ^ p / 16)) else 1

theorem reductionRho_bounds {c p : ℝ} (hc : 0 < c) (L : ℝ) :
    0 < reductionRho c p L ∧ reductionRho c p L ≤ 1 := by
  unfold reductionRho
  split_ifs with hL
  · exact ⟨lt_min zero_lt_one (Real.sqrt_pos.mpr (by
      have hα := H1Reduction.reductionAlpha_pos (p := p) hc hL
      positivity)), min_le_left _ _⟩
  · exact ⟨zero_lt_one, le_rfl⟩

/-- Analytic-case input H1, using the literal analytic and solution carriers.
The exponent p acts on energy and is supplied by the §5.4 estimate. -/
def AnalyticDissipationInput (b : ℝ → Vec 2 → Vec 2) (c p : ℝ) : Prop :=
  ∀ (g : Vec 2 → ℝ) (R : ℝ), 0 < R → MemL2On unitCube g → IsZ2Periodic g →
    MeanZeroOn unitCube g → ContDiff ℝ (⊤ : ℕ∞) g → IsThetaAnalytic R g →
    ∀ (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2),
      (∀ κ, 0 < κ → IsWeakSolutionGrad b κ g (θ κ) (Dθ κ)) →
        c * R ^ p * l2NormSq g ≤
          limsup (fun κ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0)

/-- H2: the endpoint energy identity for the difference of two weak solutions. -/
def DifferenceEnergyInput (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ (κ : ℝ), 0 < κ → ∀ (f g : Vec 2 → ℝ),
    MemL2On unitCube f → MemL2On unitCube g →
    ∀ (θ η : ℝ → Vec 2 → ℝ) (Dθ Dη : ℝ → Vec 2 → Vec 2),
    IsWeakSolutionGrad b κ f θ Dθ → IsWeakSolutionGrad b κ g η Dη →
      l2NormSq (θ 1 - η 1) +
        2 * κ * spaceTimeGradNormSq (fun t x => Dθ t x - Dη t x) = l2NormSq (f - g)

/-- The weak well-posedness conclusion, copied literally, as a conditional data input.
Existence is necessary to instantiate H1; H1 alone could otherwise be vacuous. -/
def WeakWellposedInput (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ (κ : ℝ), 0 < κ → ∀ (θ₀ : Vec 2 → ℝ), MemL2On unitCube θ₀ →
    ∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolution b κ θ₀ θ ∧
      ∀ θ' : ℝ → Vec 2 → ℝ, IsWeakSolution b κ θ₀ θ' →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, θ' t =ᵐ[volume.restrict unitCube] θ t

theorem H1Reduction.zero_solution (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) :
    IsWeakSolutionGrad b κ (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
  simp only [IsWeakSolutionGrad, Set.mem_Icc, IsZ2Periodic, implies_true, MemL2On, MemLp.zero',
      and_self,
    l2NormSq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, and_imp,
        Pi.zero_apply,
    IsPeriodicH1With, GradMemL2On, HasWeakGradientOn, HasWeakPartialDerivOn, Set.subset_univ,
        Measure.restrict_univ,
    zero_mul, neg_zero, measurableSet_Ioo, ae_restrict_eq, eventually_true, vecDot,
        mul_zero,
    Finset.sum_const_zero, integrable_fun_zero, add_zero, and_true, true_and]
  constructor
  · exact ⟨0, by intros; exact le_rfl⟩
  · intros
    exact continuous_const.continuousOn

theorem H1Reduction.zero_datum_memL2 :
    MemL2On unitCube (fun _ : Vec 2 => (0 : ℝ)) := by
  apply MemLp.of_bound measurable_const.aestronglyMeasurable 0
  filter_upwards with x
  simp

theorem H1Reduction.st_integrable {D : ℝ → Vec 2 → Vec 2}
    (hD : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => D p.1 p.2 i) 2
      (volume.restrict timeCube)) :
    Integrable (fun p : ℝ × Vec 2 => vecNormSq (D p.1 p.2)) (volume.restrict timeCube) := by
  have hi : ∀ i : Fin 2, Integrable (fun p : ℝ × Vec 2 => D p.1 p.2 i ^ 2)
      (volume.restrict timeCube) := by
    intro i
    have h := (hD i).integrable_norm_rpow (by norm_num) (by norm_num)
    rw [show (2 : ENNReal).toReal = 2 by norm_num] at h
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using h
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [vecNormSq, vecDot, ← pow_two] using hsum

theorem H1Reduction.square_triangle (u v : ℝ) : v ^ 2 ≤ 2 * u ^ 2 + 2 * (u - v) ^ 2 := by
  nlinarith only [sq_nonneg (2 * u - v)]

theorem H1Reduction.st_triangle {D E : ℝ → Vec 2 → Vec 2}
    (hD : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => D p.1 p.2 i) 2 (volume.restrict timeCube))
    (hE : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => E p.1 p.2 i) 2 (volume.restrict timeCube)) :
    spaceTimeGradNormSq E ≤ 2 * spaceTimeGradNormSq D +
      2 * spaceTimeGradNormSq (fun t x => D t x - E t x) := by
  have hdiff := H1Reduction.st_integrable (D := fun t x => D t x - E t x) (fun i => (hD i).sub (hE
      i))
  have hInt := ((H1Reduction.st_integrable hD).const_mul 2).add (hdiff.const_mul 2)
  have hp : ∀ p : ℝ × Vec 2, vecNormSq (E p.1 p.2) ≤
      2 * vecNormSq (D p.1 p.2) + 2 * vecNormSq (D p.1 p.2 - E p.1 p.2) := by
    intro p
    simp only [vecNormSq, vecDot, ← pow_two, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.sub_apply]
    exact Finset.sum_le_sum (fun i _ => H1Reduction.square_triangle _ _)
  have h := integral_mono (H1Reduction.st_integrable hE) hInt hp
  simpa only [Pi.add_apply, integral_add ((H1Reduction.st_integrable hD).const_mul 2)
      (hdiff.const_mul 2),
    integral_const_mul, spaceTimeGradNormSq] using h

theorem H1Reduction.energy_bound {b : ℝ → Vec 2 → Vec 2} (hEnergy : DifferenceEnergyInput b)
    {κ : ℝ} (hκ : 0 < κ) {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    {D : ℝ → Vec 2 → Vec 2} (hf : MemL2On unitCube f)
    (hθ : IsWeakSolutionGrad b κ f θ D) :
    0 ≤ κ * spaceTimeGradNormSq D ∧ κ * spaceTimeGradNormSq D ≤ l2NormSq f / 2 := by
  have h := hEnergy κ hκ f (fun _ => 0) hf H1Reduction.zero_datum_memL2
    θ (fun _ _ => 0) D (fun _ _ => 0) hθ (H1Reduction.zero_solution b κ)
  simp only [Pi.sub_def, sub_zero] at h
  refine ⟨mul_nonneg hκ.le (H1Reduction.st_nonneg D), ?_⟩
  have hnon := H1Reduction.l2_nonneg (θ 1)
  linarith only [h, hnon]

theorem H1Reduction.energy_comparison {b : ℝ → Vec 2 → Vec 2}
    (hEnergy : DifferenceEnergyInput b) {κ : ℝ} (hκ : 0 < κ)
    {f g : Vec 2 → ℝ} {θ η : ℝ → Vec 2 → ℝ} {D E : ℝ → Vec 2 → Vec 2}
    (hf : MemL2On unitCube f) (hg : MemL2On unitCube g)
    (hθ : IsWeakSolutionGrad b κ f θ D) (hη : IsWeakSolutionGrad b κ g η E) :
    κ * spaceTimeGradNormSq E ≤ 2 * (κ * spaceTimeGradNormSq D) + l2NormSq (f - g) := by
  have ht := mul_le_mul_of_nonneg_left (H1Reduction.st_triangle hθ.2.2.2.1 hη.2.2.2.1) hκ.le
  have hid := hEnergy κ hκ f g hf hg θ η D E hθ hη
  have hnon := H1Reduction.l2_nonneg (θ 1 - η 1)
  linarith only [ht, hid, hnon]

theorem H1Reduction.limsup_transfer {ι : Type*} {F : Filter ι} [NeBot F]
    {u v : ι → ℝ} {B E : ℝ} (hu : F.IsBoundedUnder (· ≤ ·) u)
    (hv : ∀ᶠ i in F, 0 ≤ v i) (hcmp : ∀ᶠ i in F, v i ≤ 2 * u i + E)
    (hB : B ≤ limsup v F) : (B - E) / 2 ≤ limsup u F := by
  apply le_limsup_of_le hu
  intro z hz
  have hvc : F.IsCoboundedUnder (· ≤ ·) v :=
    (show F.IsBoundedUnder (· ≥ ·) v from ⟨0, hv⟩).isCoboundedUnder_le
  have hlim : limsup v F ≤ 2 * z + E := limsup_le_of_le hvc (by
    filter_upwards [hz, hcmp] with i hi hc
    linarith only [hi, hc])
  linarith only [hB, hlim]

theorem H1Reduction.variance_transfer {M A G E U : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hG : A / 4 ≤ G) (hE : E ≤ M * A / 32) (hU : (M * G - E) / 2 ≤ U) :
    M / 16 * A ≤ U := by
  have hMG := mul_le_mul_of_nonneg_left hG hM
  have hMA := mul_nonneg hM hA
  linarith only [hMG, hE, hU, hMA]

/-- Conditional reduction for a given general H1 datum and solution family.
No solution existence, analytic dissipation, or difference energy is proved here. -/
theorem h1_dissipation_conditional {b : ℝ → Vec 2 → Vec 2} {c p : ℝ}
    (hc : 0 < c) (hp : 0 < p ∧ p < 2) (hWP : WeakWellposedInput b)
    (hAnalytic : AnalyticDissipationInput b c p) (hEnergy : DifferenceEnergyInput b)
    {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2} (hf : IsPeriodicH1With f Df)
    (hm : MeanZeroOn unitCube f)
    (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2)
    (hθ : ∀ κ, 0 < κ → IsWeakSolutionGrad b κ f (θ κ) (Dθ κ)) :
    reductionRho c p (datumLength f Df) ^ 2 * l2NormSq f ≤
      limsup (fun κ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) := by
  have hk : ∀ᶠ κ : ℝ in 𝓝[>] 0, 0 < κ := self_mem_nhdsWithin
  have hu : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      (fun κ => κ * spaceTimeGradNormSq (Dθ κ)) := ⟨l2NormSq f / 2, hk.mono
        (fun κ hκ => (H1Reduction.energy_bound hEnergy hκ hf.2.2.1 (hθ κ hκ)).2)⟩
  by_cases hA : 0 < l2NormSq f
  · let L := datumLength f Df
    let α := reductionAlpha c p L
    let R := α * L / 2
    have hL : 0 < L := H1Reduction.datumLength_pos hf hm hA
    have hα : 0 < α := H1Reduction.reductionAlpha_pos hc hL
    have hαsmall : α ≤ 1 / 4 := min_le_left _ _
    have hR : 0 < R := by dsimp [R]; positivity
    obtain ⟨g, hg, hgper, hgmean, hgcd, hgan, herr, hnorm⟩ :=
      analytic_approximation hf hm hA hα hαsmall
    have hex : ∀ κ : ℝ, 0 < κ → ∃ η E, IsWeakSolutionGrad b κ g η E := by
      intro κ hκ
      obtain ⟨η, ⟨E, he⟩, _⟩ := hWP κ hκ g hg
      exact ⟨η, E, he⟩
    choose η E hη using hex
    let η' : ℝ → ℝ → Vec 2 → ℝ := fun κ => if hκ : 0 < κ then η κ hκ else fun _ _ => 0
    let E' : ℝ → ℝ → Vec 2 → Vec 2 := fun κ => if hκ : 0 < κ then E κ hκ else fun _ _ => 0
    have hη' : ∀ κ, 0 < κ → IsWeakSolutionGrad b κ g (η' κ) (E' κ) := by
      intro κ hκ
      simpa only [η', E', dite_eq_left hκ] using hη κ hκ
    have hB := hAnalytic g R hR hg hgper hgmean hgcd hgan η' E' hη'
    have hcmp : ∀ᶠ κ : ℝ in 𝓝[>] 0,
        κ * spaceTimeGradNormSq (E' κ) ≤
          2 * (κ * spaceTimeGradNormSq (Dθ κ)) + l2NormSq (f - g) :=
      hk.mono (fun κ hκ => H1Reduction.energy_comparison hEnergy hκ hf.2.2.1 hg
        (hθ κ hκ) (hη' κ hκ))
    have hv : ∀ᶠ κ : ℝ in 𝓝[>] 0, 0 ≤ κ * spaceTimeGradNormSq (E' κ) :=
      hk.mono (fun κ hκ => (H1Reduction.energy_bound hEnergy hκ hg (hη' κ hκ)).1)
    have ht := H1Reduction.limsup_transfer hu hv hcmp hB
    have hM : 0 ≤ c * R ^ p := mul_nonneg hc.le (Real.rpow_nonneg hR.le _)
    have herr' : l2NormSq (f - g) ≤ (c * R ^ p) * l2NormSq f / 32 := by
      calc
        l2NormSq (f - g) ≤ α ^ 2 * l2NormSq f := herr
        _ ≤ (c * R ^ p / 32) * l2NormSq f :=
          mul_le_mul_of_nonneg_right (H1Reduction.reductionAlpha_small hc hp.2 hL) hA.le
        _ = _ := by ring
    have hraw := H1Reduction.variance_transfer hM hA.le hnorm herr' ht
    have hρ : reductionRho c p L ^ 2 ≤ c * R ^ p / 16 := by
      have hpos : 0 ≤ c * R ^ p / 16 := by positivity
      have hr : reductionRho c p L ≤ Real.sqrt (c * R ^ p / 16) := by
        unfold reductionRho
        rw [ite_eq_left hL]
        exact min_le_right _ _
      have hsq := (sq_le_sq₀ (reductionRho_bounds hc L).1.le (Real.sqrt_nonneg _)).2 hr
      rwa [Real.sq_sqrt hpos] at hsq
    exact (mul_le_mul_of_nonneg_right hρ hA.le).trans hraw
  · have hz : l2NormSq f = 0 := le_antisymm (le_of_not_gt hA) (H1Reduction.l2_nonneg f)
    rw [hz, mul_zero]
    apply le_limsup_of_le hu
    intro z hz'
    have hnon := hk.mono (fun κ hκ => (H1Reduction.energy_bound hEnergy hκ hf.2.2.1
      (hθ κ hκ)).1)
    obtain ⟨κ, hκ0, hκz⟩ := (hnon.and hz').exists
    exact hκ0.trans hκz

/-- Conclusion of the H¹ reduction: a single explicit positive rho depending only on the ratio L,
with all analytic/PDE inputs exposed. -/
theorem h1_reduction_conditional {b : ℝ → Vec 2 → Vec 2} {c p : ℝ}
    (hc : 0 < c) (hp : 0 < p ∧ p < 2) (hWP : WeakWellposedInput b)
    (hAnalytic : AnalyticDissipationInput b c p) (hEnergy : DifferenceEnergyInput b) :
    ∃ ϱ : ℝ → ℝ, (∀ L, 0 < ϱ L ∧ ϱ L ≤ 1) ∧
      ∀ (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2), IsPeriodicH1With f Df →
        MeanZeroOn unitCube f →
        ∀ (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2),
          (∀ κ, 0 < κ → IsWeakSolutionGrad b κ f (θ κ) (Dθ κ)) →
          ϱ (datumLength f Df) ^ 2 * l2NormSq f ≤
            limsup (fun κ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) := by
  refine ⟨reductionRho c p, reductionRho_bounds hc, ?_⟩
  intro f Df hf hm θ Dθ hθ
  exact h1_dissipation_conditional hc hp hWP hAnalytic hEnergy hf hm θ Dθ hθ

end AVenhance.Infra.Section5
