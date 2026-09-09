/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketGrowth
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Packet Existence
-/

@[expose] public section

noncomputable section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace EulerPacketExistence

section GlobalPicard

variable {E : Type*} [NormedAddCommGroup E]
  {a b : ℝ} (t₀ : Icc a b)

/-- Extend a continuous curve from a compact interval by endpoint values. -/
noncomputable def extendCurve (α : C(Icc a b, E)) (t : ℝ) : E :=
  α (projIcc a b (t₀.2.1.trans t₀.2.2) t)

theorem continuous_extendCurve (α : C(Icc a b, E)) : Continuous (extendCurve t₀ α) :=
  α.continuous.comp continuous_projIcc

theorem extendCurve_of_mem (α : C(Icc a b, E)) {t : ℝ} (ht : t ∈ Icc a b) :
    extendCurve t₀ α t = α ⟨t, ht⟩ := by
  simp only [extendCurve, projIcc_of_mem _ ht]

variable {f : ℝ → E → E} (hf : Continuous (uncurry f))

include hf

theorem continuous_comp_extendCurve (α : C(Icc a b, E)) :
    Continuous (fun t => f t (extendCurve t₀ α t)) :=
  hf.comp (continuous_id.prodMk (continuous_extendCurve t₀ α))

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The Volterra map on all continuous curves, without a spatial-radius
restriction.  Global Lipschitz continuity makes an iterate contractive. -/
noncomputable def picardStep (x : E) (α : C(Icc a b, E)) : C(Icc a b, E) :=
  ⟨fun t => x + ∫ s in t₀.1..t.1, f s (extendCurve t₀ α s),
    (continuous_const.add (intervalIntegral.differentiable_integral_of_continuous
      (continuous_comp_extendCurve t₀ hf α)).continuous).comp continuous_subtype_val⟩

theorem picardStep_apply (x : E) (α : C(Icc a b, E)) (t : Icc a b) :
    picardStep t₀ hf x α t = x + ∫ s in t₀.1..t.1, f s (extendCurve t₀ α s) := rfl

variable {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (f t))

include hLip

theorem picard_iterate_point_bound (x : E) (α β : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist (((picardStep t₀ hf x)^[n]) α t) (((picardStep t₀ hf x)^[n]) β t) ≤
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, picardStep_apply,
      picardStep_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub
        ((continuous_comp_extendCurve t₀ hf _).intervalIntegrable _ _)
        ((continuous_comp_extendCurve t₀ hf _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ s in uIoc t₀.1 t.1, K ^ (n + 1) * |s - t₀.1| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hsi : s ∈ Icc a b := (uIcc_subset_Icc t₀.2 t.2) (uIoc_subset_uIcc hs)
        rw [← dist_eq_norm, extendCurve_of_mem t₀ _ hsi, extendCurve_of_mem t₀ _ hsi]
        calc
          _ ≤ K * dist (((picardStep t₀ hf x)^[n]) α ⟨s, hsi⟩)
              (((picardStep t₀ hf x)^[n]) β ⟨s, hsi⟩) := (hLip s).dist_le_mul _ _
          _ ≤ K ^ (n + 1) * |s - t₀.1| ^ n / n ! * dist α β := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [mul_pow] using hn ⟨s, hsi⟩
      _ ≤ (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem picard_iterate_bound (x : E) (α β : C(Icc a b, E)) (n : ℕ) :
    dist (((picardStep t₀ hf x)^[n]) α) (((picardStep t₀ hf x)^[n]) β) ≤
      (K * max (b - t₀.1) (t₀.1 - a)) ^ n / n ! * dist α β := by
  rw [ContinuousMap.dist_le]
  · intro t
    apply le_trans (picard_iterate_point_bound t₀ hf hLip x α β n t)
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  · have hmax : 0 ≤ max (b - t₀.1) (t₀.1 - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity

theorem exists_picard_fixed_point (x : E) :
    ∃ α : C(Icc a b, E), IsFixedPt (picardStep t₀ hf x) α := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (b - t₀.1) (t₀.1 - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : (0 : ℝ) ≤ (K * max (b - t₀.1) (t₀.1 - a)) ^ n / n ! := by
    have hmax : 0 ≤ max (b - t₀.1) (t₀.1 - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity
  let C : ℝ≥0 := ⟨(K * max (b - t₀.1) (t₀.1 - a)) ^ n / n !, hnonneg⟩
  have hcontract : ContractingWith C ((picardStep t₀ hf x)^[n]) :=
    ⟨hn, LipschitzWith.of_dist_le_mul fun α β => picard_iterate_bound t₀ hf hLip x α β n⟩
  exact ⟨_, hcontract.isFixedPt_fixedPoint_iterate⟩

/-- A globally Lipschitz time-dependent vector field has a solution on
every finite interval.  Full derivatives also hold at the endpoints. -/
theorem exists_solution_on_compact_interval (x : E) :
    ∃ α : ℝ → E, α t₀.1 = x ∧
      ∀ t ∈ Icc a b, HasDerivAt α (f t (α t)) t := by
  obtain ⟨α, hfixed⟩ := exists_picard_fixed_point t₀ hf hLip x
  let u : ℝ → E := fun t => x + ∫ s in t₀.1..t, f s (extendCurve t₀ α s)
  have heq : ∀ t ∈ Icc a b, u t = extendCurve t₀ α t := by
    intro t ht
    have hh := congrArg (fun v : C(Icc a b, E) => v ⟨t, ht⟩) hfixed
    rw [extendCurve_of_mem t₀ α ht]
    exact hh
  have hc := continuous_comp_extendCurve t₀ hf α
  refine ⟨u, by simp [u], ?_⟩
  intro t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right (a := t₀.1) (b := t)
      (hc.intervalIntegrable t₀.1 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x
  change HasDerivAt u (f t (u t)) t
  rw [heq t ht]
  exact hd

end GlobalPicard

/-- Global existence for a jointly continuous vector field with a uniform
global Lipschitz constant in the state variable.  Finite-interval solutions
are glued using the proved ODE uniqueness theorem. -/
theorem exists_global_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {K : ℝ≥0}
    (hf : Continuous (uncurry f)) (hLip : ∀ t, LipschitzWith K (f t)) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (f t (u t)) t := by
  classical
  have hlocal : ∀ R : ℝ, 0 < R → ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc (-R) R, HasDerivAt u (f t (u t)) t := by
    intro R hR
    let t₀ : Icc (-R) R := ⟨0, by constructor <;> linarith⟩
    exact exists_solution_on_compact_interval t₀ hf hLip x
  choose v hv0 hvd using hlocal
  let u : ℝ → E := fun t => v (|t| + 1) (by positivity) t
  have hagree : ∀ R (hR : 0 < R), EqOn u (v R hR) (Ioo (-R) R) := by
    intro R hR s hs
    let R' := |s| + 1
    have hR' : 0 < R' := by dsimp [R']; positivity
    let B := min R R'
    have hB : 0 < B := lt_min hR hR'
    have hBR : B ≤ R := min_le_left _ _
    have hBR' : B ≤ R' := min_le_right _ _
    have hzero : (0 : ℝ) ∈ Ioo (-B) B := by constructor <;> linarith
    have hsB : s ∈ Ioo (-B) B := by
      apply abs_lt.mp
      apply lt_min (abs_lt.mpr hs)
      dsimp [R']
      linarith
    have heq := ODE_solution_unique_of_mem_Ioo (v := f) (s := fun _ => (univ : Set E))
      (fun t _ => (hLip t).lipschitzOnWith) hzero
      (fun t ht => ⟨hvd R hR t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (fun t ht => ⟨hvd R' hR' t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (by rw [hv0 R hR, hv0 R' hR'])
    exact (heq hsB).symm
  refine ⟨u, ?_, ?_⟩
  · exact hv0 (|0| + 1) (by positivity)
  · intro t
    let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (-R) R := by
      apply abs_lt.mp
      dsimp [R]
      linarith
    have heq : u =ᶠ[𝓝 t] v R hR := Filter.eventually_of_mem
      (Ioo_mem_nhds ht.1 ht.2) (fun s hs => hagree R hR hs)
    have hd := hvd R hR t (Ioo_subset_Icc_self ht)
    rw [hagree R hR ht]
    exact hd.congr_of_eventuallyEq heq

/-- The displacement coefficient in the first-order form of equation (30). -/
noncomputable def scalarCoefficientA (β t : ℝ) : ℝ :=
  2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2)

/-- The velocity coefficient in the first-order form of equation (30). -/
noncomputable def scalarCoefficientB (β t : ℝ) : ℝ :=
  -(4 * β ^ 2 * t ^ 3) / (1 + (β * t ^ 2) ^ 2)

/-- The scalar equation as a globally Lipschitz two-dimensional system. -/
noncomputable def scalarVectorField (β t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2)

theorem scalar_coefficient_bounds
    {β t : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) :
    |scalarCoefficientA β t| ≤ 3 ∧ |scalarCoefficientB β t| ≤ 4 := by
  have hD : 0 < 1 + (β * t ^ 2) ^ 2 := by positivity
  have hx : 0 ≤ β * t ^ 2 := mul_nonneg hβ (sq_nonneg t)
  have hβx : β * (β * t ^ 2) ≤ β * t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hβupper hx
    simpa only [one_mul] using hh
  have hβx0 : 0 ≤ β * (β * t ^ 2) := mul_nonneg hβ hx
  constructor
  · unfold scalarCoefficientA
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    apply abs_le.mpr
    constructor <;> nlinarith only [hβx, hβx0, sq_nonneg (β * t ^ 2 - 1), sq_nonneg (β * t ^ 2)]
  · have hβ2 : β ^ 2 ≤ 1 := by nlinarith only [hβ, hβupper]
    have ht3 : β ^ 2 * |t| ^ 3 ≤ 1 + (β * t ^ 2) ^ 2 := by
      by_cases ht : |t| ≤ 1
      · have hh : |t| ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg t) ht 3
        have hm := mul_le_mul hβ2 hh (pow_nonneg (abs_nonneg t) 3) (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith only [hm, sq_nonneg (β * t ^ 2)]
      · have hh : |t| ^ 3 ≤ |t| ^ 4 := pow_le_pow_right₀ (le_of_not_ge ht) (by decide)
        have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg β)
        have ht4 : |t| ^ 4 = t ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ t ^ 4)]
        rw [ht4] at hm
        nlinarith only [hm]
    unfold scalarCoefficientB
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (sq_nonneg β), abs_pow, abs_of_pos hD, div_le_iff₀ hD]
    nlinarith only [ht3]

theorem continuous_scalarVectorField (β : ℝ) : Continuous (uncurry (scalarVectorField β)) := by
  have hden : ∀ p : ℝ × (ℝ × ℝ), 1 + (β * p.1 ^ 2) ^ 2 ≠ 0 := by intro p; positivity
  unfold scalarVectorField scalarCoefficientA scalarCoefficientB Function.uncurry
  fun_prop

theorem lipschitz_scalarVectorField
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) (t : ℝ) :
    LipschitzWith 7 (scalarVectorField β t) := by
  obtain ⟨ha, hb⟩ := scalar_coefficient_bounds (t := t) hβ hβupper
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hfst : |x.1 - y.1| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hsnd : |x.2 - y.2| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  change max (dist x.2 y.2)
    (dist (scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2)
      (scalarCoefficientA β t * y.1 + scalarCoefficientB β t * y.2)) ≤ (7 : ℝ) * dist x y
  apply max_le
  · rw [Real.dist_eq]
    nlinarith only [hsnd, dist_nonneg (x := x) (y := y)]
  · rw [Real.dist_eq]
    have h₁ := mul_le_mul ha hfst (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    have h₂ := mul_le_mul hb hsnd (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    have hh := abs_add_le (scalarCoefficientA β t * (x.1 - y.1))
      (scalarCoefficientB β t * (x.2 - y.2))
    rw [abs_mul, abs_mul] at hh
    have hid : scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2 -
        (scalarCoefficientA β t * y.1 + scalarCoefficientB β t * y.2) =
        scalarCoefficientA β t * (x.1 - y.1) + scalarCoefficientB β t * (x.2 - y.2) := by ring
    rw [hid]
    nlinarith only [h₁, h₂, hh]

/-- Global construction of equation (30) for arbitrary real initial data. -/
theorem equation30_exists_global
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) (v₀ v₁ : ℝ) :
    ∃ V V₁ : ℝ → ℝ, V 0 = v₀ ∧ V₁ 0 = v₁ ∧
      (∀ t, HasDerivAt V (V₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t) := by
  obtain ⟨u, hu0, hud⟩ := exists_global_solution (continuous_scalarVectorField β)
    (lipschitz_scalarVectorField hβ hβupper) (v₀, v₁)
  let V : ℝ → ℝ := fun t => (u t).1
  let V₁ : ℝ → ℝ := fun t => (u t).2
  refine ⟨V, V₁, ?_, ?_, ?_, ?_⟩
  · exact congrArg Prod.fst hu0
  · exact congrArg Prod.snd hu0
  · intro t
    exact (hud t).fst
  · intro t
    have hV₁ := (hud t).snd
    have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
      convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
      simp only [Pi.pow_apply, id_eq]
      ring
    have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
    apply (hD.mul hV₁).congr_deriv
    dsimp [scalarVectorField, scalarCoefficientA, scalarCoefficientB, V, V₁]
    field_simp
    ring

/-- A constructed primary scalar solution has the exponential growth,
positivity, and uniform logarithmic-slope properties used in the source.
There is no solution-existence hypothesis in this statement. -/
theorem equation30_exists_growing_primary
    {ε lam : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hlam : 0 ≤ lam) :
    ∃ V V₁ : ℝ → ℝ, V 0 = 1 ∧ V₁ 0 = lam ∧
      (∀ t, HasDerivAt V (V₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t) ∧
      Real.exp (1 / (4 * ε)) ≤ V (1 / ε) ∧
      (∀ t, 0 ≤ t → 0 < V t) ∧
      (∀ t, 1 ≤ t → |V₁ t / V t| ≤ 4) ∧
      (∀ y, 0 < y → y ≤ 1 / 2 →
        let z := -ε * EulerPacketGrowth.invertedScalarDeriv ε V V₁ y /
          EulerPacketGrowth.invertedScalar ε V y
        |z ^ 2 - 2 / (1 + y ^ 4)| ≤ 360 * ε) := by
  have hβ : ε ^ 2 ≤ 1 := by nlinarith only [hε, hεsmall]
  obtain ⟨V, V₁, hV0, hV₁0, hV, hflux⟩ := equation30_exists_global (sq_nonneg ε) hβ 1 lam
  have hV₁0pos : 0 ≤ V₁ 0 := by rw [hV₁0]; exact hlam
  have hgrowth := EulerPacketGrowth.equation30_endpoint_exponential (sq_pos_of_pos hε)
    (by nlinarith only [hε, hεsmall] : ε ^ 2 ≤ 1 / 16)
    (fun t _ => hV t) (fun t _ => hflux t) hV0 hV₁0pos
  rw [Real.sqrt_sq hε.le] at hgrowth
  refine ⟨V, V₁, hV0, hV₁0, hV, hflux, hgrowth, ?_, ?_, ?_⟩
  · exact EulerPacketGrowth.equation30_global_positive hε hεsmall
      (fun t _ => hV t) (fun t _ => hflux t) hV0 hV₁0pos
  · exact EulerPacketFrameStability.equation30_primary_logderivative_bound hε hεsmall
      (fun t _ => hV t) (fun t _ => hflux t) hV0 hV₁0pos
  · exact EulerPacketGrowth.equation30_inverted_riccati_error hε hεsmall
      (fun t _ => hV t) (fun t _ => hflux t) hV0 hV₁0pos

/-- Construction of the two exact fundamental solutions required by the
relative propagator and Duhamel estimates. -/
theorem equation30_exists_fundamental_system
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) :
    ∃ F F₁ G G₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ G 0 = 0 ∧ G₁ 0 = 1 ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧
      (∀ t, HasDerivAt G (G₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - β * (β * t ^ 2)) * F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * G₁ s)
        (2 * (1 - β * (β * t ^ 2)) * G t) t) := by
  obtain ⟨F, F₁, hF0, hF₁0, hF, hfluxF⟩ := equation30_exists_global hβ hβupper 1 0
  obtain ⟨G, G₁, hG0, hG₁0, hG, hfluxG⟩ := equation30_exists_global hβ hβupper 0 1
  exact ⟨F, F₁, G, G₁, hF0, hF₁0, hG0, hG₁0, hF, hG, hfluxF, hfluxG⟩

end EulerPacketExistence
