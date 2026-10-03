/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragesL1
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # The corrected L² ergodic estimate -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

noncomputable section

/-- Coordinate line through a point, parametrized in the chosen basis direction. -/
def AveragesL2.coordinateLine {d : ℕ} (i : Fin d) (x : Vec d) (t : ℝ) : Vec d :=
  x + t • basisVec i

theorem AveragesL2.coordinateLine_hasDerivAt {d : ℕ} (i : Fin d) (x : Vec d) (t : ℝ) :
    HasDerivAt (AveragesL2.coordinateLine i x) (basisVec i) t := by
  have hline := ((hasDerivAt_id t).smul_const (basisVec i)).add_const x
  convert hline using 1
  · funext s
    funext j
    simp [AveragesL2.coordinateLine, add_comm]
  simp

theorem AveragesL2.coordinateLine_contDiff {d : ℕ} (i : Fin d) (x : Vec d) :
    ContDiff ℝ ∞ (AveragesL2.coordinateLine i x) := by
  apply contDiff_const.add
  exact contDiff_id.smul_const _

theorem AveragesL2.coordDerivIter_line_hasDerivAt {d : ℕ} (i : Fin d) (n : ℕ)
    {f : Vec d → ℂ} (hf : ContDiff ℝ ∞ f) (x : Vec d) (t : ℝ) :
    HasDerivAt (fun s => coordDerivIter i n f (AveragesL2.coordinateLine i x s))
      (coordDeriv i (coordDerivIter i n f) (AveragesL2.coordinateLine i x t)) t := by
  have hcont : ContDiffAt ℝ ∞ (coordDerivIter i n f) (AveragesL2.coordinateLine i x t) :=
    (coordDerivIter_contDiff_top i n hf).contDiffAt
  have hdiff : DifferentiableAt ℝ (coordDerivIter i n f) (AveragesL2.coordinateLine i x t) :=
    hcont.differentiableAt (by norm_num)
  exact hdiff.hasFDerivAt.comp_hasDerivAt t (AveragesL2.coordinateLine_hasDerivAt i x t)

theorem iteratedDeriv_coordinateLine {d : ℕ} (i : Fin d) (n : ℕ)
    {f : Vec d → ℂ} (hf : ContDiff ℝ ∞ f) (x : Vec d) (t : ℝ) :
    iteratedDeriv n (fun s => f (AveragesL2.coordinateLine i x s)) t =
      coordDerivIter i n f (AveragesL2.coordinateLine i x t) := by
  induction n generalizing t with
  | zero => simp [iteratedDeriv, coordDerivIter]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : (fun s => iteratedDeriv n (fun u => f (AveragesL2.coordinateLine i x u)) s) =
          fun s => coordDerivIter i n f (AveragesL2.coordinateLine i x s) := by
        funext s
        exact ih s
      change deriv (fun s => iteratedDeriv n (fun u => f (AveragesL2.coordinateLine i x u)) s) t = _
      rw [hfun]
      exact (AveragesL2.coordDerivIter_line_hasDerivAt i n hf x t).deriv

theorem coordDerivIter_mul {d : ℕ} (i : Fin d) (n : ℕ)
    {f g : Vec d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : Vec d) :
    coordDerivIter i n (fun y => f y * g y) x =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * coordDerivIter i j f x * coordDerivIter i (n - j) g x := by
  let u : ℝ → ℂ := fun t => f (AveragesL2.coordinateLine i x t)
  let v : ℝ → ℂ := fun t => g (AveragesL2.coordinateLine i x t)
  have hu : ContDiff ℝ ∞ u := by
    dsimp [u]
    exact hf.comp (AveragesL2.coordinateLine_contDiff i x)
  have hv : ContDiff ℝ ∞ v := by
    dsimp [v]
    exact hg.comp (AveragesL2.coordinateLine_contDiff i x)
  have huN : ContDiffAt ℝ n u 0 :=
    (hu.contDiffAt (x := 0)).of_le (by simp)
  have hvN : ContDiffAt ℝ n v 0 :=
    (hv.contDiffAt (x := 0)).of_le (by simp)
  have hmul := iteratedDeriv_mul (n := n) (x := (0 : ℝ)) huN hvN
  have hleft := iteratedDeriv_coordinateLine i n (hf.mul hg) x 0
  have hprod := hleft.symm.trans hmul
  have hlineF (j : ℕ) :
      iteratedDeriv j (fun t : ℝ => f (AveragesL2.coordinateLine i x t)) 0 =
        coordDerivIter i j f x := by
    simpa [AveragesL2.coordinateLine] using iteratedDeriv_coordinateLine i j hf x 0
  have hlineG (j : ℕ) :
      iteratedDeriv j (fun t : ℝ => g (AveragesL2.coordinateLine i x t)) 0 =
        coordDerivIter i j g x := by
    simpa [AveragesL2.coordinateLine] using iteratedDeriv_coordinateLine i j hg x 0
  dsimp [u, v] at hprod
  simp_rw [hlineF, hlineG] at hprod
  simpa [AveragesL2.coordinateLine] using hprod

/- The zero order is deliberately included: it is the `j = 0` and `j = n`
  input in the Leibniz estimate for a square. -/
/-- Factorial analytic bounds for all coordinate derivatives in the unit-cell L² norm. -/
def HasCoordinateAnalyticL2Bounds {d : ℕ} (f : Vec d → ℂ) (Cf r : ℝ) : Prop :=
  ∀ (i : Fin d) (n : ℕ),
    (∫ x in Torus.unitCell d, ‖coordDerivIter i n f x‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      Cf * (n.factorial : ℝ) / r ^ n

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def AveragesL2.closedUnitCube (d : ℕ) : Set (Vec d) :=
  Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1

theorem AveragesL2.unitCell_subset_closedUnitCube (d : ℕ) :
    Torus.unitCell d ⊆ AveragesL2.closedUnitCube d := by
  intro x hx
  simp only [AveragesL2.closedUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, by simpa using (hx i).2⟩

theorem AveragesL2.isCompact_closedUnitCube (d : ℕ) : IsCompact (AveragesL2.closedUnitCube d) := by
  simpa [AveragesL2.closedUnitCube] using isCompact_univ_pi fun _ : Fin d => isCompact_Icc

theorem continuous_unitCell_integrable {d : ℕ} {u : Vec d → ℝ}
    (hu : Continuous u) : IntegrableOn u (Torus.unitCell d) (volume : Measure (Vec d)) := by
  exact (hu.continuousOn.integrableOn_compact (AveragesL2.isCompact_closedUnitCube d)).mono_set
    (AveragesL2.unitCell_subset_closedUnitCube d)

theorem continuous_unitCell_memLp_two {d : ℕ} {u : Vec d → ℝ} (hu : Continuous u) :
    MemLp u (ENNReal.ofReal (2 : ℝ))
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) := by
  have hfinite : IsFiniteMeasure
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) := by
    rw [MeasureTheory.isFiniteMeasure_iff, Measure.restrict_apply_univ]
    exact (measure_mono (AveragesL2.unitCell_subset_closedUnitCube d)).trans_lt
      (AveragesL2.isCompact_closedUnitCube d).measure_lt_top
  let Q := AveragesL2.closedUnitCube d
  have hbdd : Bornology.IsBounded (u '' Q) :=
    (AveragesL2.isCompact_closedUnitCube d).image hu |>.isBounded
  obtain ⟨C, hCpos, hC⟩ := hbdd.subset_ball_lt 0 0
  have hmeas : AEStronglyMeasurable u
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) :=
    hu.measurable.aestronglyMeasurable.restrict
  apply MemLp.of_bound hmeas C
  filter_upwards [ae_restrict_mem (Torus.measurableSet_unitCell d)] with x hx
  have hux : u x ∈ u '' Q := ⟨x, AveragesL2.unitCell_subset_closedUnitCube d hx, rfl⟩
  have hball := hC hux
  have hnorm : ‖u x‖ < C := by
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  exact le_of_lt hnorm

theorem AveragesL2.factorial_plus_one_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by decide))
      calc
        n + 1 + 1 ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ n * 2 := by ring

theorem AveragesL2.coordDerivIter_square_hasL1Bounds {d : ℕ}
    {f : Vec d → ℂ} (hf : ContDiff ℝ ∞ f) (Cf r : ℝ)
    (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hL2 : HasCoordinateAnalyticL2Bounds f Cf r) :
    HasCoordinateAnalyticL1Bounds (fun x => f x * f x) (Cf ^ 2) (r / 2) := by
  intro i n hn
  have hformulaPoint (x : Vec d) :
      ‖coordDerivIter i n (fun y => f y * f y) x‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖coordDerivIter i j f x‖ *
            ‖coordDerivIter i (n - j) f x‖ := by
    rw [coordDerivIter_mul i n hf hf x]
    calc
      ‖∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℂ) * coordDerivIter i j f x *
            coordDerivIter i (n - j) f x‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          ‖(n.choose j : ℂ) * coordDerivIter i j f x *
            coordDerivIter i (n - j) f x‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖coordDerivIter i j f x‖ *
            ‖coordDerivIter i (n - j) f x‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp
  let term : ℕ → Vec d → ℝ := fun j x =>
    (n.choose j : ℝ) * ‖coordDerivIter i j f x‖ *
      ‖coordDerivIter i (n - j) f x‖
  have htermCont (j : ℕ) : Continuous (term j) := by
    dsimp [term]
    have hc₁ := (coordDerivIter_contDiff_top i j hf).continuous
    have hc₂ := (coordDerivIter_contDiff_top i (n - j) hf).continuous
    fun_prop
  have hsumCont : Continuous (fun x => ∑ j ∈ Finset.range (n + 1), term j x) := by
    exact continuous_finsetSum _ fun j hj => htermCont j
  have hleftInt : Integrable
      (fun x => ‖coordDerivIter i n (fun y => f y * f y) x‖)
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) := by
    apply continuous_unitCell_integrable
    exact (coordDerivIter_contDiff_top i n (hf.mul hf)).continuous.norm
  have hrightInt : Integrable
      (fun x => ∑ j ∈ Finset.range (n + 1), term j x)
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) :=
    continuous_unitCell_integrable hsumCont
  have hmono := integral_mono hleftInt hrightInt (fun x => hformulaPoint x)
  have hsumInt : (∫ x in Torus.unitCell d,
      ∑ j ∈ Finset.range (n + 1), term j x) =
      ∑ j ∈ Finset.range (n + 1),
        ∫ x in Torus.unitCell d, term j x := by
    rw [integral_finsetSum]
    intro j hj
    exact continuous_unitCell_integrable (htermCont j)
  have htermBound : ∀ j ∈ Finset.range (n + 1),
      (∫ x in Torus.unitCell d, term j x) ≤
        Cf ^ 2 * (n.factorial : ℝ) / r ^ n := by
    intro j hj
    have hjlt : j < n + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ n := by omega
    let a : Vec d → ℝ := fun x => ‖coordDerivIter i j f x‖
    let b : Vec d → ℝ := fun x => ‖coordDerivIter i (n - j) f x‖
    have haCont : Continuous a := by
      exact (coordDerivIter_contDiff_top i j hf).continuous.norm
    have hbCont : Continuous b := by
      exact (coordDerivIter_contDiff_top i (n - j) hf).continuous.norm
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (f := a) (g := b)
      (μ := (volume : Measure (Vec d)).restrict (Torus.unitCell d))
      Real.HolderConjugate.two_two
      (ae_of_all _ fun x => by dsimp [a]; positivity)
      (ae_of_all _ fun x => by dsimp [b]; positivity)
      (continuous_unitCell_memLp_two haCont) (continuous_unitCell_memLp_two hbCont)
    have hholder' :
        (∫ x in Torus.unitCell d, a x * b x) ≤
          ((∫ x in Torus.unitCell d, ‖coordDerivIter i j f x‖ ^ 2) ^
              (1 / 2 : ℝ) *
            (∫ x in Torus.unitCell d,
              ‖coordDerivIter i (n - j) f x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
      simpa [a, b, Real.rpow_natCast] using hholder
    have haBound := hL2 i j
    have hbBound := hL2 i (n - j)
    have hc : 0 ≤ (n.choose j : ℝ) := by positivity
    calc
      _ = (n.choose j : ℝ) *
          ∫ x in Torus.unitCell d, a x * b x := by
            have heq : (fun x => term j x) =
                fun x => (n.choose j : ℝ) * (a x * b x) := by
              funext x
              simp [term, a, b]
              ring
            rw [heq, integral_const_mul]
      _ ≤ (n.choose j : ℝ) *
          ((∫ x in Torus.unitCell d, ‖coordDerivIter i j f x‖ ^ 2) ^
              (1 / 2 : ℝ) *
            (∫ x in Torus.unitCell d,
              ‖coordDerivIter i (n - j) f x‖ ^ 2) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hholder' hc
      _ ≤ (n.choose j : ℝ) *
          ((Cf * (j.factorial : ℝ) / r ^ j) *
            (Cf * ((n - j).factorial : ℝ) / r ^ (n - j))) := by
            apply mul_le_mul_of_nonneg_left _ hc
            exact mul_le_mul haBound hbBound (by positivity) (by positivity)
      _ = Cf ^ 2 * (n.factorial : ℝ) / r ^ n := by
        have hfac : (n.choose j : ℝ) * (j.factorial : ℝ) *
            ((n - j).factorial : ℝ) = (n.factorial : ℝ) := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjle
        field_simp [hr.ne']
        calc
          (n.choose j : ℝ) * Cf ^ 2 * (j.factorial : ℝ) *
              ((n - j).factorial : ℝ) * r ^ n =
              Cf ^ 2 * ((n.choose j : ℝ) * (j.factorial : ℝ) *
                ((n - j).factorial : ℝ)) * r ^ n := by ring
          _ = Cf ^ 2 * (n.factorial : ℝ) * r ^ n := by rw [hfac]
          _ = Cf ^ 2 * (r ^ j * r ^ (n - j)) * (n.factorial : ℝ) := by
            have hexp : j + (n - j) = n := by omega
            rw [← pow_add, hexp]
            ring
          _ = Cf ^ 2 * r ^ j * r ^ (n - j) * (n.factorial : ℝ) := by ring
  have hsumBound : (∑ j ∈ Finset.range (n + 1),
      ∫ x in Torus.unitCell d, term j x) ≤
        (n + 1 : ℝ) * (Cf ^ 2 * (n.factorial : ℝ) / r ^ n) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          Cf ^ 2 * (n.factorial : ℝ) / r ^ n :=
        Finset.sum_le_sum fun j hj => htermBound j hj
      _ = _ := by simp [Finset.sum_const, Finset.card_range]
  have hmajor : (∫ x in Torus.unitCell d,
      ‖coordDerivIter i n (fun y => f y * f y) x‖) ≤
        (n + 1 : ℝ) * (Cf ^ 2 * (n.factorial : ℝ) / r ^ n) := by
    calc
      _ ≤ ∫ x in Torus.unitCell d,
          ∑ j ∈ Finset.range (n + 1), term j x := hmono
      _ = _ := hsumInt
      _ ≤ _ := hsumBound
  have hpow : (n + 1 : ℝ) ≤ 2 ^ n := by exact_mod_cast AveragesL2.factorial_plus_one_le_two_pow n
  have hfactor :
      (n + 1 : ℝ) * (Cf ^ 2 * (n.factorial : ℝ) / r ^ n) ≤
        Cf ^ 2 * (n.factorial : ℝ) / (r / 2) ^ n := by
    rw [div_pow]
    have hpos : 0 < r ^ n := by positivity
    have hnonneg : 0 ≤ Cf ^ 2 * (n.factorial : ℝ) := by positivity
    rw [div_div_eq_mul_div, div_eq_mul_inv]
    field_simp [hr.ne']
    nlinarith [mul_le_mul_of_nonneg_right hpow hnonneg]
  exact hmajor.trans hfactor

/-- The square version of the ergodic covariance estimate. The derivative
assumption includes order zero, and `rN ≥ 2` is needed because the L¹ estimate
is applied at radius `r / 2`. -/
theorem cellAverage_square_mul_sub_le_of_coordinateAnalyticL2Bounds
    {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hper : IsZPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderiv : HasCoordinateAnalyticL2Bounds (fun x => (f x : ℂ)) Cf r)
    {g : Vec d → ℝ} (hg2 : LocallyIntegrable (fun x => |g x| ^ 2)
      (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hNr : 2 ≤ r * (N : ℝ)) :
    |cellAverage (fun x => f x ^ 2 * g x ^ 2) -
      cellAverage (fun x => f x ^ 2) * cellAverage (fun x => g x ^ 2)| ≤
      512 * Cf ^ 2 * cellAverage (fun x => |g x| ^ 2) *
        (∑' k : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
        Real.exp (-((r / 2) * (N : ℝ)) / 1024) := by
  let fc : Vec d → ℂ := fun x => (f x : ℂ)
  have hfc : ContDiff ℝ ∞ fc := by
    dsimp [fc]
    exact Complex.ofRealCLM.contDiff.comp hf
  have hsqderiv := AveragesL2.coordDerivIter_square_hasL1Bounds hfc Cf r hCf hr hderiv
  have hsqderiv' : HasCoordinateAnalyticL1Bounds
      (fun x => ((f x ^ 2 : ℝ) : ℂ)) (Cf ^ 2) (r / 2) := by
    simpa [fc, Complex.ofReal_mul, pow_two] using hsqderiv
  have hNr' : 1 ≤ (r / 2) * (N : ℝ) := by
    have hhalf : (1 : ℝ) ≤ (r * (N : ℝ)) / 2 := by linarith
    convert hhalf using 1; ring
  have hgSq : LocallyIntegrable (fun x => g x ^ 2) (volume : Measure (Vec d)) := by
    simpa [sq_abs] using hg2
  have hfastSq : IsFastPeriodic N (fun x => g x ^ 2) := by
    intro x k
    exact congrArg (fun y : ℝ => y ^ 2) (hfast x k)
  have hperSq : IsZPeriodic (fun x => f x ^ 2) := by
    intro x k
    exact congrArg (fun y : ℝ => y ^ 2) (hper x k)
  have hbase := cellAverage_mul_sub_le_of_coordinateAnalyticL1Bounds
    hd hN (hf.pow 2) hperSq
    (Cf ^ 2) (r / 2) (sq_nonneg Cf) (by positivity) hsqderiv'
    hgSq hfastSq hNr'
  have havg : cellAverage (fun x => |g x ^ 2|) =
      cellAverage (fun x => |g x| ^ 2) := by
    simp [cellAverage, torusFunction, abs_pow, sq_abs]
  simpa [havg] using hbase

end

end AVenhance.Infra.Ergodic
