/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Volterra operator for bounded measurable linear coefficients

The interval path is represented by a `ContinuousMap` on `Icc a b`.  A continuous clamping
extension lets us state Bochner integrability on the ambient real line without adding arbitrary
measurability assumptions outside the interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace AVenhance.Infra.ODE

/-- A point of `[a,b]` obtained by clamping a real number to the interval. -/
def clampPoint (a b : ℝ) (hab : a ≤ b) (t : ℝ) : Icc a b :=
  ⟨max a (min b t), ⟨le_max_left _ _, (max_le_iff).2 ⟨hab, min_le_left _ _⟩⟩⟩

variable {E : Type*} [NormedAddCommGroup E]

/-- Extend a continuous path on `[a,b]` to the line by constant continuation at both endpoints. -/
def extendCurve {a b : ℝ} (hab : a ≤ b) (u : C(Icc a b, E)) : ℝ → E :=
  fun t => u (clampPoint a b hab t)

theorem continuous_extendCurve {a b : ℝ} (hab : a ≤ b) (u : C(Icc a b, E)) :
    Continuous (extendCurve hab u) := by
  apply u.continuous.comp
  have hval : Continuous (fun t : ℝ => max a (min b t)) := by fun_prop
  exact hval.subtype_mk (fun t => (clampPoint a b hab t).property)

@[simp]
theorem extendCurve_eq_of_mem {a b : ℝ} (hab : a ≤ b) (u : C(Icc a b, E))
    {t : ℝ} (ht : t ∈ Icc a b) : extendCurve hab u t = u ⟨t, ht⟩ := by
  simp [extendCurve, clampPoint, max_eq_right ht.1, min_eq_right ht.2]

variable [NormedSpace ℝ E]

/-- Data for a bounded measurable linear equation with an L¹ forcing on `[a,b]`. -/
structure LinearODEData (a b : ℝ) (hab : a ≤ b) where
  /-- Time-dependent bounded linear operator in the inhomogeneous ODE. -/
  A : ℝ → E →L[ℝ] E
  /-- Integrable forcing term in the inhomogeneous ODE. -/
  f : ℝ → E
  /-- Initial state at time zero for the inhomogeneous ODE. -/
  y₀ : E
  /-- Uniform operator-norm bound on the ODE coefficient. -/
  operatorBound : ℝ
  operatorBound_nonneg : 0 ≤ operatorBound
  operator_aestronglyMeasurable : AEStronglyMeasurable A volume
  operator_norm_le : ∀ t, ‖A t‖ ≤ operatorBound
  forcing_intervalIntegrable : IntervalIntegrable f volume a b

namespace LinearODEData

variable {a b : ℝ}
variable {hab : a ≤ b}

/-- The right-hand side evaluated along a continuous path. -/
def rhs (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E)) (t : ℝ) : E :=
  D.A t (extendCurve hab u t) + D.f t

theorem rhs_intervalIntegrable (D : LinearODEData (E := E) a b hab)
    (u : C(Icc a b, E)) : IntervalIntegrable (D.rhs u) volume a b := by
  apply intervalIntegrable_iff.mpr
  let g := extendCurve hab u
  have hgcont : Continuous g := continuous_extendCurve hab u
  have hAmeas : AEStronglyMeasurable D.A (volume.restrict (uIoc a b)) :=
    D.operator_aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hgmeas : AEStronglyMeasurable g (volume.restrict (uIoc a b)) :=
    hgcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have heval : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) := by fun_prop
  have htermmeas : AEStronglyMeasurable (fun t => D.A t (g t))
      (volume.restrict (uIoc a b)) :=
    heval.comp_aestronglyMeasurable (hAmeas.prodMk hgmeas)
  obtain ⟨C, hC⟩ :=
    isCompact_uIcc.exists_bound_of_continuousOn (hgcont.continuousOn : ContinuousOn g (uIcc a b))
  let C₀ := max C 0
  have hterm : IntegrableOn (fun t => D.A t (g t)) (uIoc a b) volume := by
    refine IntegrableOn.of_bound (s := uIoc a b) (μ := volume) ?_ htermmeas
      (D.operatorBound * C₀) ?_
    · rw [uIoc_of_le hab]
      exact measure_Ioc_lt_top
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    calc
      ‖D.A t (g t)‖ ≤ ‖D.A t‖ * ‖g t‖ := (D.A t).le_opNorm (g t)
      _ ≤ D.operatorBound * C₀ := by
        exact mul_le_mul (D.operator_norm_le t)
          ((hC t (uIoc_subset_uIcc ht)).trans (le_max_left C 0))
          (norm_nonneg _) D.operatorBound_nonneg
  have hsum : IntegrableOn (fun t => D.A t (g t) + D.f t) (uIoc a b) volume :=
    hterm.add (intervalIntegrable_iff.mp D.forcing_intervalIntegrable)
  change IntegrableOn (D.rhs u) (uIoc a b) volume
  exact hsum.congr_fun_ae (by filter_upwards with t; simp [rhs, g])

/-- The Volterra operator on continuous paths on `[a,b]`. -/
noncomputable def volterra (D : LinearODEData (E := E) a b hab) :
    C(Icc a b, E) → C(Icc a b, E) := fun u =>
  ⟨fun t => D.y₀ + ∫ s in a..(t : ℝ), D.rhs u s, by
    have hprim : ContinuousOn (fun x => ∫ s in a..x, D.rhs u s) (uIcc a b) :=
      continuousOn_intervalPrimitive (D.rhs_intervalIntegrable u)
    have hprim' : ContinuousOn (fun x => D.y₀ + ∫ s in a..x, D.rhs u s) (Icc a b) := by
      have hconst : ContinuousOn (fun _ : ℝ => D.y₀) (uIcc a b) := continuousOn_const
      have hsum := hconst.add hprim
      simpa only [uIcc_of_le hab] using hsum.congr (by intro x hx; rfl)
    exact continuousOn_iff_continuous_domRestrict.mp hprim'⟩

@[simp]
theorem volterra_apply (D : LinearODEData (E := E) a b hab)
    (u : C(Icc a b, E)) (t : Icc a b) :
    D.volterra u t = D.y₀ + ∫ s in a..(t : ℝ), D.rhs u s := rfl

/-- The `n`th Volterra iterates have the standard factorial difference bound. -/
theorem dist_iterate_volterra_apply_le (D : LinearODEData (E := E) a b hab)
    (u v : C(Icc a b, E)) (n : ℕ)
    (t : Icc a b) :
    dist (((D.volterra)^[n] u) t) (((D.volterra)^[n] v) t) ≤
      (D.operatorBound * |(t : ℝ) - a|) ^ n / Nat.factorial n * dist u v := by
  induction n generalizing t with
  | zero =>
      simpa using ContinuousMap.dist_apply_le_dist (f := u) (g := v) t
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        dist_eq_norm, volterra_apply, volterra_apply,
        add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub
          (by
            have hsrc := intervalIntegrable_iff.mp (D.rhs_intervalIntegrable ((D.volterra)^[n] u))
            rw [uIoc_of_le hab] at hsrc
            apply intervalIntegrable_iff.mpr
            rw [uIoc_of_le t.property.1]
            apply hsrc.mono_set
            intro s hs
            exact ⟨hs.1, hs.2.trans t.property.2⟩)
          (by
            have hsrc := intervalIntegrable_iff.mp (D.rhs_intervalIntegrable ((D.volterra)^[n] v))
            rw [uIoc_of_le hab] at hsrc
            apply intervalIntegrable_iff.mpr
            rw [uIoc_of_le t.property.1]
            apply hsrc.mono_set
            intro s hs
            exact ⟨hs.1, hs.2.trans t.property.2⟩)]
      calc
        ‖∫ s in a..(t : ℝ),
            (D.rhs ((D.volterra)^[n] u) s - D.rhs ((D.volterra)^[n] v) s)‖ ≤
            ∫ s in uIoc a t,
              D.operatorBound ^ (n + 1) * |s - a| ^ n / Nat.factorial n * dist u v := by
          rw [intervalIntegral.norm_intervalIntegral_eq]
          apply MeasureTheory.norm_integral_le_of_norm_le
            (Continuous.integrableOn_uIoc (by fun_prop))
          filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
          have hsIcc : s ∈ Icc a b := by
            have hs' : s ∈ Ioc a (t : ℝ) := by
              simpa [uIoc_of_le t.property.1] using hs
            rcases hs' with ⟨hsa, hst⟩
            exact ⟨le_of_lt hsa, hst.trans t.property.2⟩
          have hdiff :
              D.rhs ((D.volterra)^[n] u) s - D.rhs ((D.volterra)^[n] v) s =
                D.A s (((D.volterra)^[n] u) ⟨s, hsIcc⟩ - ((D.volterra)^[n] v) ⟨s, hsIcc⟩) := by
            simp only [rhs]
            rw [extendCurve_eq_of_mem hab _ hsIcc,
              extendCurve_eq_of_mem hab _ hsIcc, map_sub]
            abel
          rw [hdiff]
          calc
            ‖D.A s (((D.volterra)^[n] u) ⟨s, hsIcc⟩ - ((D.volterra)^[n] v) ⟨s, hsIcc⟩)‖ ≤
                ‖D.A s‖ * dist (((D.volterra)^[n] u) ⟨s, hsIcc⟩)
                  (((D.volterra)^[n] v) ⟨s, hsIcc⟩) := by
              rw [dist_eq_norm]
              exact (D.A s).le_opNorm _
            _ ≤ D.operatorBound * dist
                (((D.volterra)^[n] u) ⟨s, hsIcc⟩) (((D.volterra)^[n] v) ⟨s, hsIcc⟩) :=
              mul_le_mul_of_nonneg_right (D.operator_norm_le s) (dist_nonneg)
            _ ≤ D.operatorBound *
                ((D.operatorBound * |s - a|) ^ n / Nat.factorial n * dist u v) := by
              have ihs : dist (((D.volterra)^[n] u) ⟨s, hsIcc⟩)
                  (((D.volterra)^[n] v) ⟨s, hsIcc⟩) ≤
                  (D.operatorBound * |s - a|) ^ n / Nat.factorial n * dist u v := by
                simpa using ih ⟨s, hsIcc⟩
              exact mul_le_mul_of_nonneg_left ihs D.operatorBound_nonneg
            _ = D.operatorBound ^ (n + 1) * |s - a| ^ n / Nat.factorial n * dist u v := by
              rw [pow_succ]
              ring_nf
        _ ≤ (D.operatorBound * |(t : ℝ) - a|) ^ (n + 1) /
              Nat.factorial (n + 1) * dist u v := by
          have hscalar :
              ∫ s in uIoc a (t : ℝ),
                D.operatorBound ^ (n + 1) * |s - a| ^ n / Nat.factorial n * dist u v =
              (D.operatorBound * |(t : ℝ) - a|) ^ (n + 1) /
                Nat.factorial (n + 1) * dist u v := by
            have hfun : (fun s : ℝ =>
                D.operatorBound ^ (n + 1) * |s - a| ^ n / Nat.factorial n * dist u v) =
                fun s => (D.operatorBound ^ (n + 1) / Nat.factorial n * dist u v) * |s - a| ^ n :=
                    by
              funext s
              ring
            rw [hfun, integral_const_mul, integral_pow_abs_sub_uIoc]
            rw [Nat.factorial_succ]
            push_cast
            field_simp
            rw [mul_pow]
            ring
          rw [hscalar]

/-- A global sup-norm estimate for the iterates follows from compactness of the time interval. -/
theorem dist_iterate_volterra_le (D : LinearODEData (E := E) a b hab)
    (u v : C(Icc a b, E)) (n : ℕ) :
    dist ((D.volterra)^[n] u) ((D.volterra)^[n] v) ≤
      (D.operatorBound * (b - a)) ^ n / Nat.factorial n * dist u v := by
  have hbase : 0 ≤ D.operatorBound * (b - a) :=
    mul_nonneg D.operatorBound_nonneg (sub_nonneg.mpr hab)
  have hC : 0 ≤ (D.operatorBound * (b - a)) ^ n / Nat.factorial n * dist u v := by
    exact mul_nonneg (div_nonneg (pow_nonneg hbase _) (Nat.cast_nonneg _)) dist_nonneg
  rw [ContinuousMap.dist_le (f := (D.volterra)^[n] u) (g := (D.volterra)^[n] v) hC]
  intro t
  have htime : |(t : ℝ) - a| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr t.property.1)]
    exact sub_le_sub_right t.property.2 a
  calc
    dist (((D.volterra)^[n] u) t) (((D.volterra)^[n] v) t) ≤
        (D.operatorBound * |(t : ℝ) - a|) ^ n / Nat.factorial n * dist u v :=
      dist_iterate_volterra_apply_le D u v n t
    _ ≤ (D.operatorBound * (b - a)) ^ n / Nat.factorial n * dist u v := by
      have hlow : 0 ≤ D.operatorBound * |(t : ℝ) - a| :=
        mul_nonneg D.operatorBound_nonneg (abs_nonneg _)
      have hupp : D.operatorBound * |(t : ℝ) - a| ≤ D.operatorBound * (b - a) :=
        mul_le_mul_of_nonneg_left htime D.operatorBound_nonneg
      have hp := pow_le_pow_left₀ hlow hupp n
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hp (Nat.cast_nonneg _)) dist_nonneg

/-- The Volterra map has a contracting iterate on every finite interval. -/
theorem exists_contracting_volterra_iterate (D : LinearODEData (E := E) a b hab) :
    ∃ n : ℕ, ∃ K : NNReal, ContractingWith K ((D.volterra)^[n]) := by
  let c := D.operatorBound * (b - a)
  have hc : 0 ≤ c := mul_nonneg D.operatorBound_nonneg (sub_nonneg.mpr hab)
  obtain ⟨n, hn⟩ :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop c).eventually
      (gt_mem_nhds zero_lt_one) |>.exists
  let K : NNReal := ⟨c ^ n / Nat.factorial n, by positivity⟩
  have hK : (K : ℝ) < 1 := by
    change c ^ n / Nat.factorial n < 1
    exact hn
  refine ⟨n, K, hK, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  change dist ((D.volterra)^[n] u) ((D.volterra)^[n] v) ≤
    (c ^ n / Nat.factorial n) * dist u v
  simpa [c] using D.dist_iterate_volterra_le u v n

/-- A continuous path is an integral solution exactly when it is a fixed point of the
Volterra operator. -/
def IsSolution (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E)) : Prop :=
  D.volterra u = u

/-- There is exactly one continuous integral solution on the whole interval. -/
theorem existsUnique_solution [CompleteSpace E]
    (D : LinearODEData (E := E) a b hab) :
    ∃! u : C(Icc a b, E), D.IsSolution u := by
  obtain ⟨n, K, hcontract⟩ := D.exists_contracting_volterra_iterate
  let u : C(Icc a b, E) := hcontract.fixedPoint
  have hu : D.volterra u = u := hcontract.isFixedPt_fixedPoint_iterate
  refine ⟨u, hu, ?_⟩
  intro v hv
  change D.volterra v = v at hv
  have hiterate : ∀ m : ℕ, ∀ x : C(Icc a b, E), D.volterra x = x →
      ((D.volterra)^[m]) x = x := by
    intro m
    induction m with
    | zero => intro x hx; simp
    | succ m ih =>
        intro x hx
        rw [Function.iterate_succ_apply', ih x hx, hx]
  exact (hcontract.fixedPoint_unique' (hiterate n u hu) (hiterate n v hv)).symm

/-- A Volterra fixed point gives the integral equation on the ambient interval. -/
theorem IsSolution.integralSolution
    (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E))
    (hu : D.IsSolution u) :
    IsLinearIntegralSolution D.A D.f D.y₀ a b (extendCurve hab u) := by
  intro t ht
  let q : Icc a b := ⟨t, ht⟩
  have hfix := congrArg (fun w : C(Icc a b, E) => w q) hu
  calc
    extendCurve hab u t = u q := extendCurve_eq_of_mem hab u ht
    _ = D.volterra u q := hfix.symm
    _ = D.y₀ + ∫ s in a..t,
        linearRhs D.A D.f (extendCurve hab u) s := by
      simp [volterra_apply, rhs, linearRhs, q]

/-- On continuous interval paths, the fixed-point equation is equivalent to the integral form. -/
theorem isSolution_iff_integralSolution
    (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E)) :
    D.IsSolution u ↔
      IsLinearIntegralSolution D.A D.f D.y₀ a b (extendCurve hab u) := by
  constructor
  · exact IsSolution.integralSolution D u
  · intro hu
    apply ContinuousMap.ext
    intro q
    have hq := hu q q.property
    rw [extendCurve_eq_of_mem hab u q.property] at hq
    change u q = D.y₀ + ∫ s in a..(q : ℝ), D.rhs u s at hq
    rw [volterra_apply]
    exact hq.symm

/-- The continuous solution supplied by the fixed-point theorem is absolutely continuous. -/
theorem IsSolution.absolutelyContinuousOnInterval
    (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E))
    (hu : D.IsSolution u) :
    AbsolutelyContinuousOnInterval (extendCurve hab u) a b := by
  have hsol := hu.integralSolution D
  have h_rhs : IntervalIntegrable
      (linearRhs D.A D.f (extendCurve hab u)) volume a b := by
    change IntervalIntegrable (D.rhs u) volume a b
    exact D.rhs_intervalIntegrable u
  exact hsol.absolutelyContinuousOnInterval hab h_rhs

/-- Existence and uniqueness in the requested absolutely-continuous integral-solution class. -/
theorem existsUnique_absolutelyContinuous_integralSolution [CompleteSpace E]
    (D : LinearODEData (E := E) a b hab) :
    ∃! u : C(Icc a b, E),
      IsLinearIntegralSolution D.A D.f D.y₀ a b (extendCurve hab u) ∧
        AbsolutelyContinuousOnInterval (extendCurve hab u) a b := by
  obtain ⟨u, hu, huniq⟩ := D.existsUnique_solution
  refine ⟨u, ⟨hu.integralSolution D, hu.absolutelyContinuousOnInterval D⟩, ?_⟩
  intro v hv
  apply huniq
  exact (D.isSolution_iff_integralSolution v).2 hv.1

/-- The solution is differentiable almost everywhere and satisfies the ODE there. -/
theorem IsSolution.ae_hasDerivAt
    [CompleteSpace E]
    (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E))
    (hu : D.IsSolution u) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      HasDerivAt (extendCurve hab u)
        (D.A t (extendCurve hab u t) + D.f t) t := by
  have hsol := hu.integralSolution D
  have h_rhs : IntervalIntegrable
      (linearRhs D.A D.f (extendCurve hab u)) volume a b := by
    change IntervalIntegrable (D.rhs u) volume a b
    exact D.rhs_intervalIntegrable u
  simpa [linearRhs] using hsol.ae_hasDerivAt hab h_rhs

end LinearODEData

end AVenhance.Infra.ODE
