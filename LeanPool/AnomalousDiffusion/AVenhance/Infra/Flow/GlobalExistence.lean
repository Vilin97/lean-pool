/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FlowOn
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Algebra.Order.Floor

/-! Global existence for continuous, uniformly globally Lipschitz ODE fields. -/

@[expose] public section

open Homogenization
open MeasureTheory
open Set
open scoped NNReal Nat Topology

namespace AVenhance.Infra.Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Clamp a real parameter to a nonempty closed interval. -/
def GlobalExistence.clampPoint (a b : ℝ) (hab : a ≤ b) (t : ℝ) : Icc a b :=
  ⟨max a (min b t), ⟨le_max_left _ _, (max_le_iff).2 ⟨hab, min_le_left _ _⟩⟩⟩

/-- Extend an interval-valued continuous curve constantly past its endpoints. -/
def GlobalExistence.extendCurve {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, E)) : ℝ → E :=
  fun t => u (GlobalExistence.clampPoint a b hab t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem GlobalExistence.continuous_extendCurve {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, E)) : Continuous (GlobalExistence.extendCurve hab u) := by
  apply u.continuous.comp
  have hval : Continuous (fun t : ℝ => max a (min b t)) := by fun_prop
  exact hval.subtype_mk (fun t => (GlobalExistence.clampPoint a b hab t).property)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem GlobalExistence.extendCurve_eq_of_mem {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, E)) {t : ℝ} (ht : t ∈ Icc a b) :
    GlobalExistence.extendCurve hab u t = u ⟨t, ht⟩ := by
  simp [GlobalExistence.extendCurve, GlobalExistence.clampPoint, max_eq_right ht.1, min_eq_right
      ht.2]

/-- Evaluate the vector field along the clamped extension of a curve. -/
def GlobalExistence.curveRhs (b : ℝ → E → E) {a d : ℝ} (had : a ≤ d)
    (u : C(Icc a d, E)) (t : ℝ) : E :=
  b t (GlobalExistence.extendCurve had u t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem GlobalExistence.continuous_curveRhs (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {a d : ℝ} (had : a ≤ d) (u : C(Icc a d, E)) :
    Continuous (GlobalExistence.curveRhs b had u) := by
  have hp : Continuous (fun t : ℝ => (t, GlobalExistence.extendCurve had u t)) :=
    continuous_id.prodMk (GlobalExistence.continuous_extendCurve had u)
  exact hb.comp hp

/-- Volterra integral operator for the initial-value problem on a compact interval. -/
noncomputable def GlobalExistence.volterra (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {a d : ℝ} (had : a ≤ d) (s : ℝ) (x : E) :
    C(Icc a d, E) → C(Icc a d, E) := fun u =>
  ⟨fun t => x + ∫ r in s..(t : ℝ), GlobalExistence.curveRhs b had u r, by
    have hcont := GlobalExistence.continuous_curveRhs b hb had u
    have hprim : Continuous (fun t : ℝ => ∫ r in s..t, GlobalExistence.curveRhs b had u r) :=
      (intervalIntegral.differentiable_integral_of_continuous hcont).continuous
    exact (continuous_const.add hprim).comp continuous_subtype_val⟩

theorem GlobalExistence.volterra_apply (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {a d : ℝ} (had : a ≤ d) (s : ℝ) (x : E)
    (u : C(Icc a d, E)) (t : Icc a d) :
    GlobalExistence.volterra b hb had s x u t =
      x + ∫ r in s..(t : ℝ), GlobalExistence.curveRhs b had u r := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem GlobalExistence.dist_volterra_rhs_le (b : ℝ → E → E)
    {a d : ℝ} (had : a ≤ d)
    {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (u v : C(Icc a d, E)) (t : Icc a d) :
    dist (GlobalExistence.curveRhs b had u t) (GlobalExistence.curveRhs b had v t) ≤
      K * dist (u t) (v t) := by
  change dist (b (t : ℝ) (GlobalExistence.extendCurve had u t))
      (b (t : ℝ) (GlobalExistence.extendCurve had v t)) ≤ K * dist (u t) (v t)
  rw [GlobalExistence.extendCurve_eq_of_mem had u t.property,
    GlobalExistence.extendCurve_eq_of_mem had v t.property]
  exact (hLip t).dist_le_mul _ _

theorem GlobalExistence.dist_iterate_volterra_apply_le
    (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {a d : ℝ} (had : a ≤ d) {s : ℝ} (hs : s ∈ Icc a d)
    (x : E) {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (u v : C(Icc a d, E)) (n : ℕ) (t : Icc a d) :
    dist ((GlobalExistence.volterra b hb had s x)^[n] u t) ((GlobalExistence.volterra b hb had s
        x)^[n] v t) ≤
      ((K : ℝ) * |(t : ℝ) - s|) ^ n / Nat.factorial n * dist u v := by
  induction n generalizing t with
  | zero =>
      simpa using ContinuousMap.dist_apply_le_dist (f := u) (g := v) t
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dist_eq_norm,
        GlobalExistence.volterra_apply b hb had s x, GlobalExistence.volterra_apply b hb had s x,
        add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub
          ((GlobalExistence.continuous_curveRhs b hb had ((GlobalExistence.volterra b hb had s
              x)^[n] u)).intervalIntegrable s t)
          ((GlobalExistence.continuous_curveRhs b hb had ((GlobalExistence.volterra b hb had s
              x)^[n] v)).intervalIntegrable s t)]
      calc
        ‖∫ r in s..(t : ℝ),
            (GlobalExistence.curveRhs b had ((GlobalExistence.volterra b hb had s x)^[n] u) r -
              GlobalExistence.curveRhs b had ((GlobalExistence.volterra b hb had s x)^[n] v) r)‖ ≤
            ∫ r in uIoc s (t : ℝ),
              (K : ℝ) ^ (n + 1) * |r - s| ^ n / Nat.factorial n * dist u v := by
          rw [intervalIntegral.norm_intervalIntegral_eq]
          apply MeasureTheory.norm_integral_le_of_norm_le
            (Continuous.integrableOn_uIoc (by fun_prop))
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          have hr' : r ∈ Icc a d := by
            exact (uIcc_subset_Icc hs t.property) (uIoc_subset_uIcc hr)
          have hpoint := GlobalExistence.dist_volterra_rhs_le b had hLip
            ((GlobalExistence.volterra b hb had s x)^[n] u) ((GlobalExistence.volterra b hb had s
                x)^[n] v)
            ⟨r, hr'⟩
          have hiter := ih ⟨r, hr'⟩
          simp only [dist_eq_norm] at hpoint
          rw [dist_eq_norm] at hiter
          have hscalar : 0 ≤ (K : ℝ) := (K : ℝ≥0).property
          calc
            ‖GlobalExistence.curveRhs b had ((GlobalExistence.volterra b hb had s x)^[n] u) r -
                GlobalExistence.curveRhs b had ((GlobalExistence.volterra b hb had s x)^[n] v) r‖
                ≤ (K : ℝ) *
                  ‖((GlobalExistence.volterra b hb had s x)^[n] u) ⟨r, hr'⟩ -
                    ((GlobalExistence.volterra b hb had s x)^[n] v) ⟨r, hr'⟩‖ := hpoint
            _ ≤ (K : ℝ) *
                (((K : ℝ) * |r - s|) ^ n / n ! * dist u v) :=
                  mul_le_mul_of_nonneg_left hiter hscalar
            _ = (K : ℝ) ^ (n + 1) * |r - s| ^ n / n ! * dist u v := by
                  rw [pow_succ]
                  ring
        _ ≤ ((K : ℝ) * |(t : ℝ) - s|) ^ (n + 1) / Nat.factorial (n + 1) * dist u v := by
          apply le_of_abs_le
          rw [← intervalIntegral.abs_intervalIntegral_eq,
            intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
            intervalIntegral.integral_const_mul, abs_mul, abs_div, abs_mul,
            intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc,
            abs_div, abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs,
            mul_div, div_div, ← abs_mul, ← Nat.cast_succ, ← Nat.cast_mul,
            ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem GlobalExistence.dist_iterate_volterra_le
    (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {a d : ℝ} (had : a ≤ d) {s : ℝ} (hs : s ∈ Icc a d)
    (x : E) {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (u v : C(Icc a d, E)) (n : ℕ) :
    dist ((GlobalExistence.volterra b hb had s x)^[n] u) ((GlobalExistence.volterra b hb had s
        x)^[n] v) ≤
      ((K : ℝ) * max (d - s) (s - a)) ^ n / Nat.factorial n * dist u v := by
  have hR : 0 ≤ max (d - s) (s - a) :=
    le_max_of_le_right (sub_nonneg.mpr hs.1)
  have hfactor : 0 ≤
      ((K : ℝ) * max (d - s) (s - a)) ^ n / Nat.factorial n * dist u v := by
    positivity
  rw [ContinuousMap.dist_le (f := (GlobalExistence.volterra b hb had s x)^[n] u)
    (g := (GlobalExistence.volterra b hb had s x)^[n] v) hfactor]
  intro t
  have ht : |(t : ℝ) - s| ≤ max (d - s) (s - a) :=
    abs_sub_le_max_sub t.property.1 t.property.2 s
  have hpoint := GlobalExistence.dist_iterate_volterra_apply_le b hb had hs x hLip u v n t
  calc
    dist ((GlobalExistence.volterra b hb had s x)^[n] u t) ((GlobalExistence.volterra b hb had s
        x)^[n] v t)
        ≤ ((K : ℝ) * |(t : ℝ) - s|) ^ n / Nat.factorial n * dist u v := hpoint
    _ ≤ ((K : ℝ) * max (d - s) (s - a)) ^ n / Nat.factorial n * dist u v := by
      have hlow : 0 ≤ (K : ℝ) * |(t : ℝ) - s| := by positivity
      have hupp : (K : ℝ) * |(t : ℝ) - s| ≤
          (K : ℝ) * max (d - s) (s - a) := by gcongr
      have hp := pow_le_pow_left₀ hlow hupp n
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hp (Nat.cast_nonneg _)) dist_nonneg

theorem GlobalExistence.exists_contracting_volterra_iterate
    (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {a d : ℝ} (had : a ≤ d) {s : ℝ} (hs : s ∈ Icc a d)
    (x : E) {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t)) :
    ∃ n : ℕ, ∃ Q : ℝ≥0,
      ContractingWith Q ((GlobalExistence.volterra b hb had s x)^[n]) := by
  let c := (K : ℝ) * max (d - s) (s - a)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (NNReal.coe_nonneg K)
      (le_max_of_le_left (sub_nonneg.mpr hs.2))
  obtain ⟨n, hn⟩ :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop c).eventually
      (gt_mem_nhds zero_lt_one) |>.exists
  let Q : ℝ≥0 := ⟨c ^ n / Nat.factorial n, by positivity⟩
  have hQ : (Q : ℝ) < 1 := by
    change c ^ n / Nat.factorial n < 1
    exact hn
  refine ⟨n, Q, hQ, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  change dist ((GlobalExistence.volterra b hb had s x)^[n] u)
      ((GlobalExistence.volterra b hb had s x)^[n] v) ≤
        (c ^ n / Nat.factorial n) * dist u v
  simpa [c] using GlobalExistence.dist_iterate_volterra_le b hb had hs x hLip u v n

theorem GlobalExistence.exists_finite_integralCurve
    (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (s : ℝ) (x : E) (n : ℕ) :
    ∃ γ : ℝ → E, Continuous γ ∧ γ s = x ∧
      ∀ t ∈ Ioo (s - n) (s + n), HasDerivAt γ (b t (γ t)) t := by
  let a := s - (n : ℝ)
  let d := s + (n : ℝ)
  have had : a ≤ d := by dsimp [a, d]; linarith
  have hs : s ∈ Icc a d := by dsimp [a, d]; constructor <;> linarith
  obtain ⟨m, Q, hcontract⟩ := GlobalExistence.exists_contracting_volterra_iterate b hb had hs x hLip
  let T := GlobalExistence.volterra b hb had s x
  let u : C(Icc a d, E) := hcontract.fixedPoint
  have hu : T u = u := by
    exact hcontract.isFixedPt_fixedPoint_iterate
  have hinit : u ⟨s, hs⟩ = x := by
    have h := congrArg (fun w : C(Icc a d, E) => w ⟨s, hs⟩) hu
    change x + ∫ r in s..s, GlobalExistence.curveRhs b had u r = u ⟨s, hs⟩ at h
    simpa using h.symm
  let γ := GlobalExistence.extendCurve had u
  refine ⟨γ, GlobalExistence.continuous_extendCurve had u, ?_, ?_⟩
  · simpa [γ, GlobalExistence.extendCurve, GlobalExistence.clampPoint, max_eq_right hs.1,
      min_eq_right hs.2] using hinit
  · intro t ht
    have htI : t ∈ Icc a d := Ioo_subset_Icc_self ht
    have hcont := GlobalExistence.continuous_curveRhs b hb had u
    let H : ℝ → E := (fun _ : ℝ => x) + fun r => ∫ q in s..r, GlobalExistence.curveRhs b had u q
    have hH : HasDerivAt H (GlobalExistence.curveRhs b had u t) t := by
      have hi := intervalIntegral.integral_hasDerivAt_right
        (hcont.intervalIntegrable s t)
        hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
      have hadd : HasDerivAt
          ((fun _ : ℝ => x) + fun r => ∫ q in s..r, GlobalExistence.curveRhs b had u q)
          (GlobalExistence.curveRhs b had u t) t := by
        simpa only [zero_add] using (hasDerivAt_const t x).add hi
      have heq : H =ᶠ[𝓝 t]
          ((fun _ : ℝ => x) + fun r => ∫ q in s..r, GlobalExistence.curveRhs b had u q) :=
        Filter.Eventually.of_forall (fun _ => rfl)
      exact hadd.congr_of_eventuallyEq heq
    have hlocal : γ =ᶠ[𝓝 t] H := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      have hrI : r ∈ Icc a d := by
        dsimp [a, d]
        constructor <;> linarith [hr.1, hr.2]
      have hext := GlobalExistence.extendCurve_eq_of_mem had u hrI
      have hfix := congrArg (fun w : C(Icc a d, E) => w ⟨r, hrI⟩) hu
      change x + ∫ q in s..r, GlobalExistence.curveRhs b had u q = u ⟨r, hrI⟩ at hfix
      change GlobalExistence.extendCurve had u r = H r
      rw [hext]
      exact hfix.symm
    have hderiv := hH.congr_of_eventuallyEq hlocal
    have hval := GlobalExistence.extendCurve_eq_of_mem had u htI
    simpa [γ, GlobalExistence.curveRhs, hval] using hderiv

/-- Integral curve constructed on a finite time window about the starting time. -/
noncomputable def GlobalExistence.finiteCurve (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (s : ℝ) (x : E) (n : ℕ) : ℝ → E :=
  Classical.choose (GlobalExistence.exists_finite_integralCurve b hb hLip s x n)

theorem GlobalExistence.finiteCurve_spec (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (s : ℝ) (x : E) (n : ℕ) :
    Continuous (GlobalExistence.finiteCurve b hb hLip s x n) ∧
      GlobalExistence.finiteCurve b hb hLip s x n s = x ∧
      ∀ t ∈ Ioo (s - n) (s + n),
        HasDerivAt (GlobalExistence.finiteCurve b hb hLip s x n) (b t (GlobalExistence.finiteCurve
            b hb hLip s x n t)) t :=
  Classical.choose_spec (GlobalExistence.exists_finite_integralCurve b hb hLip s x n)

theorem GlobalExistence.finiteCurves_eqOn_overlap (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (s : ℝ) (x : E) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    EqOn (GlobalExistence.finiteCurve b hb hLip s x n) (GlobalExistence.finiteCurve b hb hLip s x m)
      (Icc (s - min n m) (s + min n m)) := by
  let k : ℝ := (min n m : ℕ)
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast (lt_min hn hm)
  have hkn : k ≤ (n : ℝ) := by
    dsimp [k]
    exact_mod_cast (min_le_left n m)
  have hkm : k ≤ (m : ℝ) := by
    dsimp [k]
    exact_mod_cast (min_le_right n m)
  have hcenter : s ∈ Ioo (s - k) (s + k) := by
    constructor <;> dsimp [k] <;> linarith
  have hleft : Ioo (s - k) (s + k) ⊆ Ioo (s - (n : ℝ)) (s + n) := by
    apply Ioo_subset_Ioo <;> linarith
  have hright : Ioo (s - k) (s + k) ⊆ Ioo (s - (m : ℝ)) (s + m) := by
    apply Ioo_subset_Ioo <;> linarith
  have hunique := ODE_solution_unique_of_mem_Icc
    (fun t _ => (hLip t).lipschitzOnWith) hcenter
    (GlobalExistence.finiteCurve_spec b hb hLip s x n).1.continuousOn
    (fun t ht => (GlobalExistence.finiteCurve_spec b hb hLip s x n).2.2 t (hleft ht))
    (fun _ _ => Set.mem_univ _)
    (GlobalExistence.finiteCurve_spec b hb hLip s x m).1.continuousOn
    (fun t ht => (GlobalExistence.finiteCurve_spec b hb hLip s x m).2.2 t (hright ht))
    (fun _ _ => Set.mem_univ _)
    ((GlobalExistence.finiteCurve_spec b hb hLip s x n).2.1.trans
      (GlobalExistence.finiteCurve_spec b hb hLip s x m).2.1.symm)
  intro t ht
  have hunique' : EqOn (GlobalExistence.finiteCurve b hb hLip s x n) (GlobalExistence.finiteCurve
      b hb hLip s x m)
      (Icc (s - min n m) (s + min n m)) := by
    simpa [k, Nat.cast_min] using hunique
  exact hunique' ht

/-- Least natural radius strictly greater than the elapsed time. -/
noncomputable def GlobalExistence.radiusIndex (s t : ℝ) : ℕ :=
  Nat.find (exists_nat_gt |t - s|)

theorem GlobalExistence.abs_lt_radiusIndex (s t : ℝ) :
    |t - s| < (GlobalExistence.radiusIndex s t : ℝ) :=
  Nat.find_spec (exists_nat_gt |t - s|)

theorem GlobalExistence.radiusIndex_pos (s t : ℝ) : 0 < GlobalExistence.radiusIndex s t := by
  have h := GlobalExistence.abs_lt_radiusIndex s t
  have habs : 0 ≤ |t - s| := abs_nonneg _
  exact_mod_cast (lt_of_le_of_lt habs h)

/-- Global integral curve obtained from compatible finite-window constructions. -/
noncomputable def GlobalExistence.globalIntegralCurve (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (s : ℝ) (x : E) : ℝ → E := fun t =>
  GlobalExistence.finiteCurve b hb hLip s x (GlobalExistence.radiusIndex s t) t

theorem GlobalExistence.globalIntegralCurve_initial (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (s : ℝ) (x : E) : GlobalExistence.globalIntegralCurve b hb hLip s x s = x := by
  exact (GlobalExistence.finiteCurve_spec b hb hLip s x (GlobalExistence.radiusIndex s s)).2.1

theorem GlobalExistence.globalIntegralCurve_hasDerivAt (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (b t))
    (s : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (GlobalExistence.globalIntegralCurve b hb hLip s x)
      (b t (GlobalExistence.globalIntegralCurve b hb hLip s x t)) t := by
  let n := GlobalExistence.radiusIndex s t
  let N := n + 1
  have hn : 0 < n := GlobalExistence.radiusIndex_pos s t
  have hrad : |t - s| < (N : ℝ) := by
    dsimp [N]
    exact lt_trans (GlobalExistence.abs_lt_radiusIndex s t) (Nat.cast_lt.mpr (Nat.lt_succ_self n))
  have hNleft : s - (N : ℝ) < t := by
    have := (abs_lt.mp hrad).1
    dsimp [N] at this ⊢
    linarith
  have hNright : t < s + (N : ℝ) := by
    have := (abs_lt.mp hrad).2
    dsimp [N] at this ⊢
    linarith
  have hlocal : GlobalExistence.globalIntegralCurve b hb hLip s x =ᶠ[𝓝 t]
      GlobalExistence.finiteCurve b hb hLip s x N := by
    filter_upwards [Ioo_mem_nhds hNleft hNright] with r hr
    let m := GlobalExistence.radiusIndex s r
    have hm : |r - s| < (m : ℝ) := GlobalExistence.abs_lt_radiusIndex s r
    have hmpos : 0 < m := GlobalExistence.radiusIndex_pos s r
    have hrm : r ∈ Ioo (s - m) (s + m) := by
      have h := abs_lt.mp hm
      constructor <;> dsimp [m] <;> linarith
    have hrN : r ∈ Ioo (s - N) (s + N) := hr
    have hmn := GlobalExistence.finiteCurves_eqOn_overlap b hb hLip s x m N hmpos (Nat.succ_pos n)
    have hcast : (min m N : ℝ) = min (m : ℝ) (N : ℝ) := by simp
    have hrNabs : |r - s| < (N : ℝ) := by
      apply abs_lt.mpr
      constructor <;> dsimp [N] <;> linarith [hrN.1, hrN.2]
    have hrmin := lt_min hm hrNabs
    rw [hcast] at hrmin
    have hrmin' := abs_lt.mp hrmin
    have hinterval : r ∈ Icc (s - min (m : ℝ) (N : ℝ))
        (s + min (m : ℝ) (N : ℝ)) := by
      constructor <;> linarith [hrmin'.1, hrmin'.2]
    have hinterval' : r ∈ Icc (s - min m N) (s + min m N) := by
      simpa only [Nat.cast_min] using hinterval
    exact hmn hinterval'
  have hN : t ∈ Ioo (s - N) (s + N) := ⟨hNleft, hNright⟩
  have hfinite := (GlobalExistence.finiteCurve_spec b hb hLip s x N).2.2 t hN
  have hderiv := hfinite.congr_of_eventuallyEq hlocal
  have hval : GlobalExistence.globalIntegralCurve b hb hLip s x t =
      GlobalExistence.finiteCurve b hb hLip s x N t := hlocal.self_of_nhds
  simpa [hval] using hderiv

/-- Every continuous uniformly globally Lipschitz vector field on a complete
normed state space has a unique characterized global flow. -/
theorem existsUnique_flowOn_uniform (b : ℝ → E → E)
    (hb : Continuous (fun p : ℝ × E => b p.1 p.2))
    (hLip : ∃ K : ℝ≥0, ∀ t, LipschitzWith K (b t)) :
    ∃! Y : ℝ → E → ℝ → E, IsFlowOn b Y := by
  obtain ⟨K, hK⟩ := hLip
  let Y : ℝ → E → ℝ → E := fun t x s => GlobalExistence.globalIntegralCurve b hb hK s x t
  have hY : IsFlowOn b Y := by
    constructor
    · intro x s
      exact GlobalExistence.globalIntegralCurve_initial b hb hK s x
    · intro x s t
      exact GlobalExistence.globalIntegralCurve_hasDerivAt b hb hK s x t
  refine ⟨Y, hY, ?_⟩
  intro Z hZ
  funext t
  funext x
  funext s
  have hcurves := ODE_solution_unique_univ
    (v := b) (s := fun _ => Set.univ) (K := K)
    (f := fun r => Y r x s) (g := fun r => Z r x s) (t₀ := s)
    (fun r => (hK r).lipschitzOnWith)
    (fun r => ⟨hY.2 x s r, Set.mem_univ _⟩)
    (fun r => ⟨hZ.2 x s r, Set.mem_univ _⟩)
    (by rw [hY.1 x s, hZ.1 x s])
  exact (congrFun hcurves t).symm

/-- Every continuous vector field with a uniform global spatial Lipschitz bound
has a unique global flow. -/
theorem existsUnique_flow (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) :
    ∃! X, AVenhance.IsFlow b X := by
  obtain ⟨L, hL⟩ := hL
  let K : ℝ≥0 := ⟨max L 0, le_max_right L 0⟩
  have hLip : ∀ t, LipschitzWith K (b t) := by
    simpa only [K] using lipschitzWith_of_uniform_bound b hL
  let X : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun t x s => GlobalExistence.globalIntegralCurve b hb hLip s x t
  have hX : AVenhance.IsFlow b X := by
    constructor
    · intro x s
      exact GlobalExistence.globalIntegralCurve_initial b hb hLip s x
    · intro x s t
      exact GlobalExistence.globalIntegralCurve_hasDerivAt b hb hLip s x t
  refine ⟨X, hX, ?_⟩
  intro Y hY
  exact (flow_eq_of_isFlow b ⟨L, hL⟩ (X := X) (Y := Y) hX hY).symm

end AVenhance.Infra.Flow
