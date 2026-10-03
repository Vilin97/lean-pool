/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Calculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Fourier
public import Mathlib.Analysis.Fourier.AddCircle

/-! Fourier coefficients of smooth periodic functions and their derivatives. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open scoped ComplexConjugate

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraTorusFourierCalculusMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraTorusFourierCalculusMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraTorusFourierCalculusIsProbabilityMeasure3 : IsProbabilityMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Torus

/-- The Euclidean representative of the torus character with frequency `k`,
using the sign convention in `mFourierCoeff`. -/
def torusCharacter {d : ℕ} (k : Fin d → ℤ) (x : Vec d) : ℂ :=
  UnitAddTorus.mFourier (-k) (toUnitTorus d x)

/-- The Fourier coefficient of a periodic Euclidean function over its unit cell. -/
def smoothFourierCoeff {d : ℕ} (f : Vec d → ℂ) (k : Fin d → ℤ) : ℂ :=
  ∫ x in unitCell d, torusCharacter k x * f x

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def FourierCalculus.closedCell (d : ℕ) : Set (Vec d) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem FourierCalculus.isCompact_closedCell (d : ℕ) : IsCompact (FourierCalculus.closedCell d) :=
    by
  simpa [FourierCalculus.closedCell] using (isCompact_univ_pi fun _ : Fin d => isCompact_Icc)

theorem FourierCalculus.unitTorusRepresentative_mem_closedCell {d : ℕ}
    (x : UnitAddTorus (Fin d)) : unitTorusRepresentative d x ∈ FourierCalculus.closedCell d := by
  simp only [FourierCalculus.closedCell, Set.mem_pi, mem_univ, forall_true_left]
  intro i
  have hi : unitTorusRepresentative d x i ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [unitTorusRepresentative] using (AddCircle.equivIoc (1 : ℝ) 0 (x i)).2
  exact ⟨le_of_lt hi.1, hi.2⟩

/-- The canonical torus representative is measurable as a map to Euclidean coordinates. -/
theorem measurable_unitTorusRepresentative (d : ℕ) :
    Measurable (unitTorusRepresentative d : UnitAddTorus (Fin d) → Vec d) := by
  have heq : unitTorusRepresentative d = fun x =>
      ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (0 : ℝ)) x).val) := by
    funext x i
    rfl
  rw [heq]
  exact measurable_subtype_coe.comp
    (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (0 : ℝ))).measurable

theorem measurable_periodicToTorus {d : ℕ} {f : Vec d → ℂ} (hf : Continuous f) :
    Measurable (periodicToTorus f) :=
  hf.measurable.comp (measurable_unitTorusRepresentative d)

/-- A continuous periodic transfer belongs to torus `L²`. Its boundedness follows
from continuity on the compact closed unit cell and the canonical representative. -/
theorem memLp_periodicToTorus {d : ℕ} {f : Vec d → ℂ} (hf : Continuous f) :
    MemLp (periodicToTorus f) 2 (volume : Measure (UnitAddTorus (Fin d))) := by
  have hbounded : Bornology.IsBounded ((fun x : Vec d => ‖f x‖) '' FourierCalculus.closedCell d) :=
    (FourierCalculus.isCompact_closedCell d).image hf.norm |>.isBounded
  obtain ⟨C, hCpos, hC⟩ := hbounded.subset_ball_lt 0 0
  have hmeas : AEStronglyMeasurable (periodicToTorus f)
      (volume : Measure (UnitAddTorus (Fin d))) :=
    (measurable_periodicToTorus hf).aestronglyMeasurable
  apply MemLp.of_bound hmeas C
  filter_upwards with x
  have hx : ‖periodicToTorus f x‖ ∈ (fun y : Vec d => ‖f y‖) '' FourierCalculus.closedCell d := by
    refine ⟨unitTorusRepresentative d x, FourierCalculus.unitTorusRepresentative_mem_closedCell x,
        ?_⟩
    rfl
  have hball := hC hx
  have hnorm : ‖periodicToTorus f x‖ < C := by
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  exact le_of_lt hnorm

/-- Put a continuous periodic transfer into the torus `L²` space. -/
noncomputable def periodicToTorusL2 {d : ℕ} (f : Vec d → ℂ) (hf : Continuous f) :
    TorusL2 d :=
  (memLp_periodicToTorus hf).toLp (periodicToTorus f)

theorem continuous_coordDeriv {d : ℕ} (i : Fin d) {f : Vec d → ℂ}
    (hf : ContDiff ℝ 1 f) : Continuous (coordDeriv i f) := by
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem torusCharacter_contDiff {d : ℕ} (k : Fin d → ℤ) :
    ContDiff ℝ ⊤ (torusCharacter k) := by
  have hformula : torusCharacter k = fun x : Vec d =>
      ∏ i : Fin d, Complex.exp (2 * Real.pi * Complex.I * (-(k i : ℂ)) * x i) := by
    funext x
    simp only [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      toUnitTorus, fourier_coe_apply]
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    push_cast
    simp only [Pi.neg_apply, Int.cast_neg]
    ring_nf
  rw [hformula]
  apply contDiff_prod
  intro i hi
  have hcoord : ContDiff ℝ ⊤ (fun x : Vec d => (x i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)
  have hcont := Complex.contDiff_exp.comp
    ((contDiff_const : ContDiff ℝ ⊤ (fun _ : Vec d =>
      2 * Real.pi * Complex.I * (-(k i : ℂ)))).mul hcoord)
  convert hcont using 1
  ext x
  congr 1

theorem torusCharacter_periodic {d : ℕ} (k : Fin d → ℤ) :
    IsZdPeriodic (torusCharacter k) := by
  exact isZdPeriodic_fromUnitTorus (fun x : UnitAddTorus (Fin d) =>
    UnitAddTorus.mFourier (-k) x)

theorem FourierCalculus.periodicToTorusL2_fourierCoeff_eq {d : ℕ}
    {f : Vec d → ℂ} (hf : Continuous f) (k : Fin d → ℤ) :
    periodicL2FourierCoeff (periodicToTorusL2 f hf) k = smoothFourierCoeff f k := by
  let hmem := memLp_periodicToTorus hf
  calc
    periodicL2FourierCoeff (periodicToTorusL2 f hf) k =
        ∫ y : UnitAddTorus (Fin d),
          UnitAddTorus.mFourier (-k) y * periodicToTorus f y := by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with y hy
      exact congrArg (fun z : ℂ => UnitAddTorus.mFourier (-k) y * z) hy
    _ = ∫ x in unitCell d, torusCharacter k x * f x := by
      rw [← integral_periodicToTorus_eq_unitCell
        (fun x : Vec d => torusCharacter k x * f x)]
      apply integral_congr_ae
      filter_upwards with y
      change UnitAddTorus.mFourier (-k) y * f (unitTorusRepresentative d y) =
        UnitAddTorus.mFourier (-k)
          (toUnitTorus d (unitTorusRepresentative d y)) *
            f (unitTorusRepresentative d y)
      rw [toUnitTorus_unitTorusRepresentative]

theorem FourierCalculus.integral_periodicToTorusL2_normSq_eq {d : ℕ}
    {f : Vec d → ℂ} (hf : Continuous f) :
    ∫ y : UnitAddTorus (Fin d), ‖periodicToTorusL2 f hf y‖ ^ 2 =
      ∫ x in unitCell d, ‖f x‖ ^ 2 := by
  have hmem := memLp_periodicToTorus hf
  calc
    ∫ y : UnitAddTorus (Fin d), ‖periodicToTorusL2 f hf y‖ ^ 2 =
        ∫ y, ‖periodicToTorus f y‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with y hy
      simp [periodicToTorusL2, hy]
    _ = ∫ x in unitCell d, ‖f x‖ ^ 2 := by
      simpa [periodicToTorus] using
        (integral_periodicToTorus_eq_unitCell (fun x : Vec d => ‖f x‖ ^ 2))

/-- Parseval for a continuous periodic Euclidean representative. -/
theorem hasSum_sq_smoothFourierCoeff {d : ℕ} {f : Vec d → ℂ}
    (hf : Continuous f) :
    HasSum (fun k : Fin d → ℤ => ‖smoothFourierCoeff f k‖ ^ 2)
      (∫ x in unitCell d, ‖f x‖ ^ 2) := by
  let u := periodicToTorusL2 f hf
  have hparseval := hasSum_sq_periodicL2FourierCoeff u
  have hrep :
      (∫ x in unitCell d, ‖periodicL2Representative u x‖ ^ 2) =
        ∫ y : UnitAddTorus (Fin d), ‖u y‖ ^ 2 := by
    simpa [u, periodicL2Representative, fromUnitTorus, unitCell, unitCellAt] using
      (integral_fromUnitTorus_eq_unitCellAt
        (fun y : UnitAddTorus (Fin d) => ‖u y‖ ^ 2) (fun _ => 0)).symm
  have henergy :
      (∫ y : UnitAddTorus (Fin d), ‖u y‖ ^ 2) =
        ∫ x in unitCell d, ‖f x‖ ^ 2 := by
    simpa [u] using FourierCalculus.integral_periodicToTorusL2_normSq_eq hf
  rw [hrep, henergy] at hparseval
  convert hparseval using 1
  · ext k
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
      (FourierCalculus.periodicToTorusL2_fourierCoeff_eq hf k).symm

theorem FourierCalculus.torusCharacter_line_eq {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (z : Vec n) (t : ℝ) :
    torusCharacter k (i.insertNth t z) =
      fourier (-(k i)) (t : UnitAddCircle) *
        ∏ j : Fin n, fourier (-(k (i.succAbove j))) (z j : UnitAddCircle) := by
  simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    toUnitTorus, i.prod_univ_succAbove]

theorem FourierCalculus.torusCharacter_line_hasDerivAt {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (z : Vec n) (t : ℝ) :
    HasDerivAt (fun s => torusCharacter k (i.insertNth s z))
      ((-2 * Real.pi * Complex.I * (k i : ℂ)) *
        torusCharacter k (i.insertNth t z)) t := by
  let c : ℂ := ∏ j : Fin n,
    fourier (-(k (i.succAbove j))) (z j : UnitAddCircle)
  have hline : ∀ s, torusCharacter k (i.insertNth s z) =
      fourier (-(k i)) (s : UnitAddCircle) * c := by
    intro s
    simpa [c] using FourierCalculus.torusCharacter_line_eq i k z s
  have h := (hasDerivAt_fourier_neg (T := 1) (k i) t).mul_const c
  convert h using 1
  · exact funext hline
  · rw [hline t]
    simp
    ring

theorem FourierCalculus.coordDeriv_torusCharacter {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (x : Vec (n + 1)) :
    coordDeriv i (torusCharacter k) x =
      (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x := by
  let z := i.removeNth x
  have hx : i.insertNth (x i) z = x := by
    exact Fin.insertNth_self_removeNth i x
  have h₁ :=
    ((torusCharacter_contDiff k).differentiable (by simp)
      (i.insertNth (x i) z)).hasFDerivAt.comp_hasDerivAt (x i)
      (Homogenization.hasDerivAt_insertNth i z (x i))
  have h₂ := FourierCalculus.torusCharacter_line_hasDerivAt i k z (x i)
  calc
    coordDeriv i (torusCharacter k) x =
        deriv (fun t => torusCharacter k (i.insertNth t z)) (x i) := by
      rw [← hx]
      simpa [coordDeriv, Function.comp_def] using h₁.deriv.symm
    _ = (-2 * Real.pi * Complex.I * (k i : ℂ)) *
        torusCharacter k (i.insertNth (x i) z) := h₂.deriv
    _ = (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x := by rw [hx]

/-- The Fourier multiplier identity for a coordinate derivative. -/
theorem smoothFourierCoeff_coordDeriv {n : ℕ} (i : Fin (n + 1))
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) (hpf : IsZdPeriodic f)
    (k : Fin (n + 1) → ℤ) :
    smoothFourierCoeff (coordDeriv i f) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * smoothFourierCoeff f k := by
  have hchar : ContDiff ℝ 1 (torusCharacter k) :=
    (torusCharacter_contDiff k).of_le (by simp)
  have hcharper := torusCharacter_periodic k
  have hderiv : ∀ x, coordDeriv i (torusCharacter k) x =
      (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x := by
    intro x
    exact FourierCalculus.coordDeriv_torusCharacter i k x
  have hIBP := integral_unitCell_coord_ibp i hchar hf hcharper hpf
  let c : ℂ := -2 * Real.pi * Complex.I * (k i : ℂ)
  have hreplace :
      (∫ x in unitCell (n + 1), coordDeriv i (torusCharacter k) x * f x) =
        c * smoothFourierCoeff f k := by
    calc
      ∫ x in unitCell (n + 1), coordDeriv i (torusCharacter k) x * f x =
          ∫ x in unitCell (n + 1), c * (torusCharacter k x * f x) := by
        apply setIntegral_congr_ae (measurableSet_unitCell (n + 1))
        filter_upwards with x _hx
        rw [hderiv x]
        ring
      _ = c * smoothFourierCoeff f k := by
        rw [integral_const_mul, smoothFourierCoeff]
  rw [hreplace] at hIBP
  change smoothFourierCoeff (coordDeriv i f) k = -(c * smoothFourierCoeff f k) at hIBP
  calc
    smoothFourierCoeff (coordDeriv i f) k = -(c * smoothFourierCoeff f k) := hIBP
    _ = (2 * Real.pi * Complex.I * (k i : ℂ)) * smoothFourierCoeff f k := by
      simp [c]

theorem FourierCalculus.hasSum_finset_sum {ι κ : Type*} {E : Type*}
    [NormedAddCommGroup E] (s : Finset ι) (F : ι → κ → E) (a : ι → E)
    (hF : ∀ i ∈ s, HasSum (F i) (a i)) :
    HasSum (fun k => ∑ i ∈ s, F i k) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hhead := hF i (by simp)
    have htail : ∀ j ∈ s, HasSum (F j) (a j) := by
      intro j hj
      exact hF j (Finset.mem_insert_of_mem hj)
    have hrest := ih htail
    simpa [Finset.sum_insert, hi] using hhead.add hrest

/-- Parseval for the full coordinate gradient, with the Euclidean cell energy
written as the sum of its coordinate energies. -/
theorem hasSum_sq_smoothGradientFourierCoeff {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) :
    HasSum
      (fun k : Fin (n + 1) → ℤ =>
        ∑ i : Fin (n + 1), ‖smoothFourierCoeff (coordDeriv i f) k‖ ^ 2)
      (∑ i : Fin (n + 1), ∫ x in unitCell (n + 1), ‖coordDeriv i f x‖ ^ 2) := by
  apply FourierCalculus.hasSum_finset_sum Finset.univ
    (fun i k => ‖smoothFourierCoeff (coordDeriv i f) k‖ ^ 2)
    (fun i => ∫ x in unitCell (n + 1), ‖coordDeriv i f x‖ ^ 2)
  intro i hi
  exact hasSum_sq_smoothFourierCoeff (continuous_coordDeriv i hf)

theorem FourierCalculus.continuous_integrableOn_closedCell {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Vec d → E}
    (hf : Continuous f) : IntegrableOn f (FourierCalculus.closedCell d) :=
  hf.continuousOn.integrableOn_compact (FourierCalculus.isCompact_closedCell d)

theorem FourierCalculus.cell_integral_coordinate_sum {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) :
    (∑ i : Fin (n + 1), ∫ x in unitCell (n + 1), ‖coordDeriv i f x‖ ^ 2) =
      ∫ x in unitCell (n + 1),
        ∑ i : Fin (n + 1), ‖coordDeriv i f x‖ ^ 2 := by
  have hInt : ∀ i : Fin (n + 1),
      IntegrableOn (fun x : Vec (n + 1) => ‖coordDeriv i f x‖ ^ 2)
        (unitCell (n + 1)) := by
    intro i
    have hcont : Continuous (fun x : Vec (n + 1) => ‖coordDeriv i f x‖ ^ 2) :=
      (continuous_coordDeriv i hf).norm.pow 2
    have hclosed := FourierCalculus.continuous_integrableOn_closedCell hcont
    have hsubset : unitCell (n + 1) ⊆ FourierCalculus.closedCell (n + 1) := by
      intro x hx
      simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
      simp only [FourierCalculus.closedCell, Set.mem_pi, mem_univ, forall_true_left]
      intro j
      exact ⟨le_of_lt (hx j).1, (hx j).2⟩
    exact hclosed.mono_set hsubset
  have hsum := MeasureTheory.integral_finsetSum
    (Finset.univ : Finset (Fin (n + 1)))
    (μ := (volume : Measure (Vec (n + 1))).restrict (unitCell (n + 1)))
    (f := fun i : Fin (n + 1) => fun x : Vec (n + 1) => ‖coordDeriv i f x‖ ^ 2)
    (fun i _hi => hInt i)
  simpa using hsum.symm

theorem integral_unitCell_gradSq_eq_sum_coord {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) :
    (∑ i : Fin (n + 1), ∫ x in unitCell (n + 1), ‖coordDeriv i f x‖ ^ 2) =
      ∫ x in unitCell (n + 1),
        ∑ i : Fin (n + 1), ‖coordDeriv i f x‖ ^ 2 :=
  FourierCalculus.cell_integral_coordinate_sum hf

theorem FourierCalculus.normSq_fourierMultiplier (m : ℤ) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I * (m : ℂ)) * z‖ ^ 2 =
      (4 * Real.pi ^ 2) * (m : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      Real.pi_pos.le,
    abs_of_nonneg, Complex.norm_I, mul_one, Complex.norm_intCast]
  calc
    (2 * Real.pi * |(m : ℝ)| * ‖z‖) ^ 2 =
        (2 * Real.pi) ^ 2 * |(m : ℝ)| ^ 2 * ‖z‖ ^ 2 := by ring
    _ = (4 * Real.pi ^ 2) * (m : ℝ) ^ 2 * ‖z‖ ^ 2 := by
      rw [sq_abs]
      ring

theorem FourierCalculus.smoothGradientFourierCoeff_eq_frequency {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) (hpf : IsZdPeriodic f)
    (k : Fin (n + 1) → ℤ) :
    (∑ i : Fin (n + 1), ‖smoothFourierCoeff (coordDeriv i f) k‖ ^ 2) =
      (4 * Real.pi ^ 2) * (∑ i : Fin (n + 1), (k i : ℝ) ^ 2) *
        ‖smoothFourierCoeff f k‖ ^ 2 := by
  calc
    ∑ i : Fin (n + 1), ‖smoothFourierCoeff (coordDeriv i f) k‖ ^ 2 =
        ∑ i : Fin (n + 1),
          (4 * Real.pi ^ 2) * (k i : ℝ) ^ 2 * ‖smoothFourierCoeff f k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [smoothFourierCoeff_coordDeriv i hf hpf k]
      exact FourierCalculus.normSq_fourierMultiplier (k i) (smoothFourierCoeff f k)
    _ = (4 * Real.pi ^ 2) * (∑ i : Fin (n + 1), (k i : ℝ) ^ 2) *
        ‖smoothFourierCoeff f k‖ ^ 2 := by
      calc
        _ = ∑ i : Fin (n + 1),
            (4 * Real.pi ^ 2) * ((k i : ℝ) ^ 2 * ‖smoothFourierCoeff f k‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (4 * Real.pi ^ 2) *
            ∑ i : Fin (n + 1), (k i : ℝ) ^ 2 * ‖smoothFourierCoeff f k‖ ^ 2 := by
          rw [Finset.mul_sum]
        _ = (4 * Real.pi ^ 2) *
            ((∑ i : Fin (n + 1), (k i : ℝ) ^ 2) * ‖smoothFourierCoeff f k‖ ^ 2) := by
          rw [Finset.sum_mul]
        _ = (4 * Real.pi ^ 2) * (∑ i : Fin (n + 1), (k i : ℝ) ^ 2) *
            ‖smoothFourierCoeff f k‖ ^ 2 := by
          ring

theorem FourierCalculus.intFrequencySq_ge_one {n : ℕ} {k : Fin (n + 1) → ℤ}
    (hk : k ≠ 0) : 1 ≤ ∑ i : Fin (n + 1), (k i : ℝ) ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have habs : (1 : ℤ) ≤ |k i| := by
    have hp : 0 < |k i| := abs_pos.mpr hi
    omega
  have habsR : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast habs
  have hsq : 1 ≤ (k i : ℝ) ^ 2 := by nlinarith [sq_abs (k i : ℝ)]
  have hsum : (k i : ℝ) ^ 2 ≤ ∑ j : Fin (n + 1), (k j : ℝ) ^ 2 := by
    simpa using (Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin (n + 1) => (k j : ℝ) ^ 2)
      (fun j hj => sq_nonneg (k j : ℝ)) (Finset.mem_univ i))
  exact hsq.trans hsum

theorem FourierCalculus.smoothFourierCoeff_zero_eq_integral {n : ℕ}
    (f : Vec (n + 1) → ℂ) :
    smoothFourierCoeff f (0 : Fin (n + 1) → ℤ) = ∫ x in unitCell (n + 1), f x := by
  simp [smoothFourierCoeff, torusCharacter,
    UnitAddTorus.mFourier_zero]

/-- Mean-zero Poincaré inequality for smooth periodic complex functions on
`(0,1]^(n+1)`, with the sharp first nonzero Fourier frequency `2π`. -/
theorem meanZero_smoothPeriodic_poincare {n : ℕ} {f : Vec (n + 1) → ℂ}
    (hf : ContDiff ℝ 1 f) (hpf : IsZdPeriodic f)
    (hmean : ∫ x in unitCell (n + 1), f x = 0) :
    ∫ x in unitCell (n + 1), ‖f x‖ ^ 2 ≤
      (4 * Real.pi ^ 2)⁻¹ *
        ∫ x in unitCell (n + 1),
          ∑ i : Fin (n + 1), ‖coordDeriv i f x‖ ^ 2 := by
  let F : (Fin (n + 1) → ℤ) → ℝ := fun k => ‖smoothFourierCoeff f k‖ ^ 2
  let G : (Fin (n + 1) → ℤ) → ℝ := fun k =>
    ∑ i : Fin (n + 1), ‖smoothFourierCoeff (coordDeriv i f) k‖ ^ 2
  have hF := hasSum_sq_smoothFourierCoeff hf.continuous
  have hG := hasSum_sq_smoothGradientFourierCoeff hf
  have hzero : smoothFourierCoeff f (0 : Fin (n + 1) → ℤ) = 0 := by
    rw [FourierCalculus.smoothFourierCoeff_zero_eq_integral]
    exact hmean
  have hterm : ∀ k : Fin (n + 1) → ℤ, F k ≤ (4 * Real.pi ^ 2)⁻¹ * G k := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp only [hzero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          mul_inv_rev, F, G]
      positivity
    · have hfreq := FourierCalculus.intFrequencySq_ge_one hk
      have hgradient := FourierCalculus.smoothGradientFourierCoeff_eq_frequency hf hpf k
      have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
      have hscalar : 0 ≤ ‖smoothFourierCoeff f k‖ ^ 2 := sq_nonneg _
      have hfreqπ : 4 * Real.pi ^ 2 ≤
          (4 * Real.pi ^ 2) * (∑ i : Fin (n + 1), (k i : ℝ) ^ 2) := by
        calc
          4 * Real.pi ^ 2 = (4 * Real.pi ^ 2) * 1 := by ring
          _ ≤ (4 * Real.pi ^ 2) * (∑ i : Fin (n + 1), (k i : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hfreq hπ.le
      have hmul :
          (4 * Real.pi ^ 2) * ‖smoothFourierCoeff f k‖ ^ 2 ≤
            (4 * Real.pi ^ 2) * (∑ i : Fin (n + 1), (k i : ℝ) ^ 2) *
              ‖smoothFourierCoeff f k‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hfreqπ hscalar
      change ‖smoothFourierCoeff f k‖ ^ 2 ≤
        (4 * Real.pi ^ 2)⁻¹ *
          (∑ i : Fin (n + 1), ‖smoothFourierCoeff (coordDeriv i f) k‖ ^ 2)
      calc
        ‖smoothFourierCoeff f k‖ ^ 2 =
            (4 * Real.pi ^ 2)⁻¹ *
              ((4 * Real.pi ^ 2) * ‖smoothFourierCoeff f k‖ ^ 2) := by
                field_simp [ne_of_gt hπ]
        _ ≤ (4 * Real.pi ^ 2)⁻¹ *
              ((4 * Real.pi ^ 2) * (∑ i : Fin (n + 1), (k i : ℝ) ^ 2) *
                ‖smoothFourierCoeff f k‖ ^ 2) := by
                exact mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hπ.le)
        _ = (4 * Real.pi ^ 2)⁻¹ *
              (∑ i : Fin (n + 1), ‖smoothFourierCoeff (coordDeriv i f) k‖ ^ 2) := by
                rw [← hgradient]
  have hGscaled := hG.mul_left ((4 * Real.pi ^ 2)⁻¹)
  have hsum := hF.summable.tsum_le_tsum hterm hGscaled.summable
  rw [hF.tsum_eq, hGscaled.tsum_eq] at hsum
  rw [← integral_unitCell_gradSq_eq_sum_coord hf]
  simpa [F, G] using hsum

end AVenhance.Infra.Torus
