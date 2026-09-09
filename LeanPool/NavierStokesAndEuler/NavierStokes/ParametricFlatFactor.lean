/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatPrimitiveFactor
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricKernelBounds
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Joint dependence of terminal flat primitive factors

The coefficient depends on a finite-dimensional auxiliary parameter and the
edge coordinate. The factor is the actual transformed improper integral.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ContDiff

namespace NavierStokes.ParametricFlatFactor

section PartialJets

variable {P Y Z : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Actual iterated partial derivatives retain local joint smoothness.
The proof uses the derivative recursion, not independently supplied jets. -/
theorem contDiffAt_partial_iteratedFDeriv (F : P → Y → Z) (n : ℕ) (p : P) (y : Y)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (p, y)) :
    ContDiffAt ℝ ∞ (fun z : P × Y => iteratedFDeriv ℝ n (F z.1) z.2) (p, y) := by
  induction n with
  | zero =>
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact hF.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ Y Z).symm : Z →L[ℝ] Y [×0]→L[ℝ] Z)
  | succ n ih =>
      have hdup : ContDiffAt ℝ ∞
          (fun q : (P × Y) × Y => iteratedFDeriv ℝ n (F q.1.1) q.2)
          ((p, y), y) :=
        ih.comp ((p, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun z : P × Y => fderiv ℝ (iteratedFDeriv ℝ n (F z.1)) z.2) (p, y) :=
        hdup.fderiv contDiffAt_snd (by simp)
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Y) Z).symm :
            (Y →L[ℝ] Y [×n]→L[ℝ] Z) →L[ℝ] Y [×(n + 1)]→L[ℝ] Z)

end PartialJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def kernel (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ) (y : E × ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp (-c * t) *
    (FlatPrimitiveFactor.denominator y.2 t ^ j /
      FlatPrimitiveFactor.denominator y.2 t ^ 3) *
    b (y.1, FlatPrimitiveFactor.coordinate y.2 t)

def factor (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ) (y : E × ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), kernel c j b y t

def primitive (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ) (y : E × ℝ) : ℝ :=
  FlatPrimitive.primitive c j (fun u => b (y.1, u)) y.2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem factor_eq_scalar (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ) (p : E) (x : ℝ) :
    factor c j b (p, x) = FlatPrimitiveFactor.factor c j (fun u => b (p, u)) x := rfl

theorem coefficient_slice_contDiff {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (p : E) :
    ContDiff ℝ ∞ (fun u : ℝ => b (p, u)) :=
  hb.comp (contDiff_const.prodMk contDiff_id)

theorem factor_slice_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ) {b : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (p : E) : ContDiff ℝ ∞ (fun x => factor c j b (p, x)) :=
  FlatPrimitiveFactor.factor_contDiff hc j (coefficient_slice_contDiff hb p)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem factor_at_zero {c : ℝ} (hc : 0 < c) (j : ℕ) (b : E × ℝ → ℝ) (p : E) :
    factor c j b (p, 0) = b (p, 0) / (2 * c) :=
  FlatPrimitiveFactor.factor_at_zero hc j (fun u => b (p, u))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem primitive_factorization (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ)
    (p : E) {x : ℝ} (hx : 0 < x) :
    FlatPrimitive.primitive c j (fun u => b (p, u)) x =
      FlatPrimitive.scale c j x * factor c j b (p, x) :=
  FlatPrimitiveFactor.primitive_eq_scale_mul_factor c j (fun u => b (p, u)) hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem primitive_eq_scale_mul_factor (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ)
    (y : E × ℝ) :
    primitive c j b y = FlatPrimitive.scale c j y.2 * factor c j b y := by
  by_cases hx : y.2 ≤ 0
  · simp [primitive, FlatPrimitive.primitive_of_nonpos c j _ hx,
      FlatPrimitive.scale, FlatCutoff.edge_of_nonpos c hx]
  · exact primitive_factorization c j b y.1 (lt_of_not_ge hx)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem integral_original_factorization (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ)
    (p : E) {x : ℝ} (hx : 0 < x) :
    (∫ u in (0 : ℝ)..x, (Real.exp (-c / u ^ 2) / u ^ j) * b (p, u)) =
      Real.exp (-c / x ^ 2) * x ^ (3 - (j : ℝ)) * factor c j b (p, x) := by
  rw [FlatPrimitiveFactor.integral_exp_eq_primitive c j (fun u => b (p, u)) hx.le,
    primitive_factorization c j b p hx, FlatPrimitiveFactor.scale_eq_rpow c j hx]

theorem kernel_joint_contDiffAt (c : ℝ) (j : ℕ) {b : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (y : E × ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (E × ℝ) => kernel c j b q.2 q.1) (t, y) := by
  have hinner : ContDiffAt ℝ ∞
      (fun q : ℝ × (E × ℝ) => 1 + q.2.2 ^ 2 * q.1) (t, y) :=
    contDiffAt_const.add ((contDiffAt_snd.snd.pow 2).mul contDiffAt_fst)
  have hd : ContDiffAt ℝ ∞
      (fun q : ℝ × (E × ℝ) => FlatPrimitiveFactor.denominator q.2.2 q.1) (t, y) :=
    hinner.sqrt (FlatPrimitiveFactor.denominator_inner_pos y.2 ht.le).ne'
  have hcoord : ContDiffAt ℝ ∞
      (fun q : ℝ × (E × ℝ) => FlatPrimitiveFactor.coordinate q.2.2 q.1) (t, y) :=
    contDiffAt_snd.snd.div hd (FlatPrimitiveFactor.denominator_pos y.2 ht.le).ne'
  have hcoef : ContDiffAt ℝ ∞
      (fun q : ℝ × (E × ℝ) => b (q.2.1, FlatPrimitiveFactor.coordinate q.2.2 q.1))
      (t, y) :=
    hb.contDiffAt.comp (t, y) (contDiffAt_snd.fst.prodMk hcoord)
  have he : ContDiffAt ℝ ∞ (fun q : ℝ × (E × ℝ) => Real.exp (-c * q.1)) (t, y) :=
    (contDiffAt_const.mul contDiffAt_fst).exp
  exact ((contDiffAt_const.mul he).mul
    ((hd.pow j).div (hd.pow 3)
      (pow_ne_zero 3 (FlatPrimitiveFactor.denominator_pos y.2 ht.le).ne'))).mul hcoef

theorem kernel_contDiff_param (c : ℝ) (j : ℕ) {b : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (fun y : E × ℝ => kernel c j b y t) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact (kernel_joint_contDiffAt c j hb y ht).comp y
    (contDiffAt_const.prodMk contDiffAt_id)

theorem kernel_ae_contDiff (c : ℝ) (j : ℕ) {b : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ContDiff ℝ ∞ (fun y : E × ℝ => kernel c j b y t) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact kernel_contDiff_param c j hb ht

/-- Joint smoothness gives measurability of every actual parameter derivative
in the integration variable. -/
theorem kernel_jet_continuousOn (c : ℝ) (j : ℕ) {b : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (n : ℕ) (y : E × ℝ) :
    ContinuousOn (fun t => iteratedFDeriv ℝ n (fun z => kernel c j b z t) y) (Ioi 0) := by
  intro t ht
  have hp := contDiffAt_partial_iteratedFDeriv (fun t z => kernel c j b z t) n t y
    (kernel_joint_contDiffAt c j hb y ht)
  exact (hp.comp t (contDiffAt_id.prodMk contDiffAt_const)).continuousAt.continuousWithinAt

theorem kernel_jet_measurable (c : ℝ) (j : ℕ) {b : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (n : ℕ) (y : E × ℝ) :
    AEStronglyMeasurable
      (fun t => iteratedFDeriv ℝ n (fun z => kernel c j b z t) y)
      (volume.restrict (Ioi 0)) :=
  (kernel_jet_continuousOn c j hb n y).aestronglyMeasurable measurableSet_Ioi

section FiniteParameters

variable [FiniteDimensional ℝ E]

/-- Finitely many actual coefficient derivatives have one common bound on
each bounded closed parameter-coordinate ball. -/
theorem bounded_coefficient_jets {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (R : ℝ) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≤ n, ∀ z : E × ℝ, ‖z‖ ≤ R →
      ‖iteratedFDeriv ℝ k b z‖ ≤ B := by
  have hkbound (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : E × ℝ, ‖z‖ ≤ R →
      ‖iteratedFDeriv ℝ k b z‖ ≤ B := by
    have hcont := hb.continuous_iteratedFDeriv
      (m := k) (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E × ℝ) R).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro z hz
    exact (hB z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).trans
      (le_max_left _ _)
  induction n with
  | zero =>
      obtain ⟨B, hB, hbnd⟩ := hkbound 0
      refine ⟨B, hB, ?_⟩
      intro k hk z hz
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact hbnd z hz
  | succ n ih =>
      obtain ⟨B, hB, hprev⟩ := ih
      obtain ⟨C, _hC, hcur⟩ := hkbound (n + 1)
      refine ⟨max B C, hB.trans (le_max_left _ _), ?_⟩
      intro k hk z hz
      rcases lt_or_eq_of_le hk with hlt | rfl
      · exact (hprev k (Nat.le_of_lt_succ hlt) z hz).trans (le_max_left _ _)
      · exact (hcur z hz).trans (le_max_right _ _)

/-- Uniform bounds for the coefficient jets on compact parameter sets,
together with the concrete joint kernel estimate, provide the integrable
majorants required for actual Fréchet differentiation under the integral. -/
theorem kernel_locallyDominated {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    SmoothParameterIntegral.LocallyDominated
      (kernel c j b) (volume.restrict (Ioi 0)) := by
  intro n y
  obtain ⟨B, hB, hjets⟩ := bounded_coefficient_jets hb (‖y‖ + 1) n
  have hR : 0 ≤ ‖y‖ + 1 := by positivity
  obtain ⟨C, N, _hC, hbound⟩ :=
    ParametricKernelBounds.kernel_iteratedFDeriv_bound_of_jetBounds hb c j n hR hB hjets
  refine ⟨1, by norm_num, (fun t => C * (1 + t) ^ N * Real.exp (-c * t)),
    FlatPrimitiveFactor.const_polynomial_exp_integrable hc C N, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  intro z hz
  have hdist : ‖z - y‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hzR : ‖z‖ ≤ ‖y‖ + 1 := by
    have htri : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - y) y
    linarith
  exact hbound z t hzR ht.le

/-- The constructed normalized factor is jointly smooth in every auxiliary
parameter and the edge coordinate. -/
theorem factor_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (factor c j b) :=
  SmoothParameterIntegral.contDiff_integral (kernel_ae_contDiff c j hb)
    (kernel_jet_measurable c j hb) (kernel_locallyDominated hc j hb)

/-- This formula includes all mixed parameter/edge derivatives as genuine
Fréchet derivatives, with the corresponding multilinear maps integrated. -/
theorem factor_iteratedFDeriv {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (n : ℕ) (y : E × ℝ) :
    iteratedFDeriv ℝ n (factor c j b) y =
      ∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ n (fun z => kernel c j b z t) y :=
  SmoothParameterIntegral.iteratedFDeriv_integral (kernel_ae_contDiff c j hb)
    (kernel_jet_measurable c j hb) (kernel_locallyDominated hc j hb) n y

theorem primitive_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (primitive c j b) := by
  have heq : primitive c j b =
      fun y => FlatPrimitive.scale c j y.2 * factor c j b y :=
    funext (primitive_eq_scale_mul_factor c j b)
  rw [heq]
  exact ((FlatPrimitive.scale_contDiff hc j).comp contDiff_snd).mul
    (factor_contDiff hc j hb)

/-- Jointly smooth factorization with no assumed factor smoothness or
integrable derivative bounds in its hypotheses. -/
theorem exists_joint_smooth_factor {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    ∃ F : E × ℝ → ℝ, ContDiff ℝ ∞ F ∧
      (∀ p : E, F (p, 0) = b (p, 0) / (2 * c)) ∧
      ∀ (p : E) (x : ℝ), 0 < x →
        (∫ u in (0 : ℝ)..x, (Real.exp (-c / u ^ 2) / u ^ j) * b (p, u)) =
          Real.exp (-c / x ^ 2) * x ^ (3 - (j : ℝ)) * F (p, x) :=
  ⟨factor c j b, factor_contDiff hc j hb, factor_at_zero hc j b,
    fun p _x hx => integral_original_factorization c j b p hx⟩

theorem factor_sqrt_contDiffAt_zero {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (p : E) (hbp : 0 < b (p, 0)) :
    ContDiffAt ℝ ∞ (fun y => Real.sqrt (factor c j b y)) (p, 0) := by
  apply (factor_contDiff hc j hb).contDiffAt.sqrt
  rw [factor_at_zero hc j b p]
  exact (div_pos hbp (mul_pos (by norm_num) hc)).ne'

end FiniteParameters

end NavierStokes.ParametricFlatFactor
