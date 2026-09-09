/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TangentProjection
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-!
# Existence on finite intervals for the projected tangent equation

We first extend the contracting-iterate Picard argument to all continuous
curves on a compact interval. A globally Lipschitz vector field therefore
has a solution on the whole prescribed interval, without a small-time
assumption. Continuous linear coefficients provide the required bound.
-/

namespace NavierStokes.TangentODE

noncomputable section

open Filter Function Set Metric intervalIntegral MeasureTheory
open scoped Topology NNReal ENNReal Nat Interval InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

/-- Continuous vector field, globally Lipschitz in its state variable,
on a prescribed compact time interval. -/
structure IntervalSystem (E : Type*) [NormedAddCommGroup E] where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  initial : E
  field : ℝ → E → E
  lip : ℝ≥0
  lipschitz : ∀ t ∈ Icc left right, LipschitzWith lip (field t)
  continuous : Continuous (fun p : Icc left right × E => field p.1 p.2)

namespace IntervalSystem

variable (v : IntervalSystem E)

def proj : ℝ → Icc v.left v.right := projIcc v.left v.right v.ordered

theorem proj_of_mem {t : ℝ} (ht : t ∈ Icc v.left v.right) :
    (v.proj t : ℝ) = t := by simp only [proj, projIcc_of_mem v.ordered ht]

theorem proj_coe (t : Icc v.left v.right) : v.proj t = t := projIcc_val _ _

theorem continuous_proj : Continuous v.proj := continuous_projIcc

def composeField (f : C(Icc v.left v.right, E)) (t : ℝ) : E :=
  v.field (v.proj t) (f (v.proj t))

theorem continuous_composeField (f : C(Icc v.left v.right, E)) :
    Continuous (v.composeField f) :=
  v.continuous.comp (v.continuous_proj.prodMk (f.continuous.comp v.continuous_proj))

theorem integrable_composeField (f : C(Icc v.left v.right, E)) (a b : ℝ) :
    IntervalIntegrable (v.composeField f) volume a b :=
  (v.continuous_composeField f).intervalIntegrable _ _

variable [NormedSpace ℝ E] [CompleteSpace E]

def integralCurve (f : C(Icc v.left v.right, E)) (t : ℝ) : E :=
  v.initial + ∫ s in v.left..t, v.composeField f s

theorem hasDerivAt_integralCurve (f : C(Icc v.left v.right, E)) (t : ℝ) :
    HasDerivAt (v.integralCurve f) (v.composeField f t) t :=
  (integral_hasDerivAt_right (v.integrable_composeField f _ _)
    ((v.continuous_composeField f).stronglyMeasurableAtFilter _ _)
    (v.continuous_composeField f).continuousAt).const_add v.initial

def next (f : C(Icc v.left v.right, E)) : C(Icc v.left v.right, E) :=
  ⟨fun t => v.integralCurve f t,
    (continuous_iff_continuousAt.mpr (fun t =>
      (v.hasDerivAt_integralCurve f t).continuousAt)).comp continuous_subtype_val⟩

theorem next_apply (f : C(Icc v.left v.right, E)) (t : Icc v.left v.right) :
    v.next f t = v.initial + ∫ s in v.left..t, v.composeField f s := rfl

theorem dist_next_apply_le_of_le {f g : C(Icc v.left v.right, E)} {n : ℕ} {d : ℝ}
    (h : ∀ t, dist (f t) (g t) ≤ (v.lip * |t.1 - v.left|) ^ n / n ! * d)
    (t : Icc v.left v.right) :
    dist (v.next f t) (v.next g t) ≤
      (v.lip * |t.1 - v.left|) ^ (n + 1) / (n + 1)! * d := by
  simp only [dist_eq_norm, next_apply, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub (v.integrable_composeField f _ _)
      (v.integrable_composeField g _ _),
    norm_integral_eq_norm_integral_uIoc] at *
  calc
    ‖∫ s in Ι v.left t, v.composeField f s - v.composeField g s‖ ≤
        ∫ s in Ι v.left t, v.lip * ((v.lip * |s - v.left|) ^ n / n ! * d) := by
      refine norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop)) ?_
      refine (ae_restrict_mem measurableSet_Ioc).mono fun s hs => ?_
      have hs' : s ∈ Icc v.left v.right :=
        uIcc_subset_Icc ⟨le_rfl, v.ordered⟩ t.2 (Ioc_subset_Icc_self hs)
      have hh := h (v.proj s)
      rw [v.proj_of_mem hs'] at hh
      exact ((v.lipschitz (v.proj s) (v.proj s).2).norm_sub_le _ _).trans
        (mul_le_mul_of_nonneg_left hh v.lip.2)
    _ = (v.lip * |t.1 - v.left|) ^ (n + 1) / (n + 1)! * d := by
      simp_rw [mul_pow, div_eq_mul_inv, mul_assoc, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_mul_const, integral_pow_abs_sub_uIoc, div_eq_mul_inv,
        pow_succ' (v.lip : ℝ), Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
        mul_inv, mul_assoc]

theorem dist_iterate_next_apply_le (f g : C(Icc v.left v.right, E))
    (n : ℕ) (t : Icc v.left v.right) :
    dist (v.next^[n] f t) (v.next^[n] g t) ≤
      (v.lip * |t.1 - v.left|) ^ n / n ! * dist f g := by
  induction n generalizing t with
  | zero =>
    rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    exact ContinuousMap.dist_apply_le_dist t
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact v.dist_next_apply_le_of_le ih t

theorem dist_iterate_next_le (f g : C(Icc v.left v.right, E)) (n : ℕ) :
    dist (v.next^[n] f) (v.next^[n] g) ≤
      (v.lip * (v.right - v.left)) ^ n / n ! * dist f g := by
  have : Nonempty (Icc v.left v.right) := ⟨⟨v.left, le_rfl, v.ordered⟩⟩
  refine ContinuousMap.dist_le_iff_of_nonempty.mpr fun t =>
    (v.dist_iterate_next_apply_le f g n t).trans ?_
  have ht : |t.1 - v.left| ≤ v.right - v.left := by
    rw [abs_of_nonneg (sub_nonneg.mpr t.2.1)]
    exact sub_le_sub_right t.2.2 _
  gcongr

theorem exists_contracting_iterate :
    ∃ (N : ℕ) (K : ℝ≥0), ContractingWith K v.next^[N] := by
  obtain ⟨N, hN⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop
    (v.lip * (v.right - v.left))).eventually (gt_mem_nhds zero_lt_one)).exists
  have hnonneg : 0 ≤ (v.lip * (v.right - v.left)) ^ N / N ! :=
    div_nonneg (pow_nonneg (mul_nonneg v.lip.2 (sub_nonneg.mpr v.ordered)) _)
      (Nat.cast_nonneg _)
  exact ⟨N, ⟨_, hnonneg⟩, hN, LipschitzWith.of_dist_le_mul fun f g =>
    v.dist_iterate_next_le f g N⟩

theorem exists_fixed : ∃ f : C(Icc v.left v.right, E), v.next f = f := by
  obtain ⟨N, K, hK⟩ := v.exists_contracting_iterate
  exact ⟨_, hK.isFixedPt_fixedPoint_iterate⟩

/-- Finite-interval existence with no smallness condition on interval length or
Lipschitz constant. The resulting extension is differentiable at the endpoints too. -/
theorem exists_solution :
    ∃ u : ℝ → E, u v.left = v.initial ∧
      ∀ t ∈ Icc v.left v.right, HasDerivAt u (v.field t (u t)) t := by
  obtain ⟨f, hf⟩ := v.exists_fixed
  refine ⟨v.integralCurve f, by simp [integralCurve], fun t ht => ?_⟩
  have hval : v.integralCurve f t = f (v.proj t) := by
    have hh := congrArg (fun g : C(Icc v.left v.right, E) => g (v.proj t)) hf
    simpa only [next, ContinuousMap.coe_mk, v.proj_of_mem ht] using hh
  have hd := v.hasDerivAt_integralCurve f t
  simpa only [composeField, v.proj_of_mem ht, hval] using hd

end IntervalSystem

variable [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A continuous operator coefficient on a compact interval has a common
global Lipschitz bound, including an arbitrary additive forcing. -/
theorem linear_uniform_lipschitz {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (g : ℝ → E) (hA : ContinuousOn A (Icc a b)) :
    ∃ L : ℝ≥0, ∀ t ∈ Icc a b, LipschitzWith L (fun x => A t x + g t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hC0 : 0 ≤ C := (norm_nonneg (A a)).trans (hC a ⟨le_rfl, hab⟩)
  refine ⟨⟨C, hC0⟩, fun t ht => LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [dist_add_right]
  exact ((A t).lipschitzWith.dist_le_mul x y).trans
    (mul_le_mul_of_nonneg_right (hC t ht) dist_nonneg)

/-- Actual existence for a continuous-coefficient inhomogeneous linear ODE
on any finite closed interval. -/
theorem exists_linear_solution {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (g : ℝ → E)
    (hA : ContinuousOn A (Icc a b)) (hg : ContinuousOn g (Icc a b)) (x₀ : E) :
    ∃ u : ℝ → E, u a = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivAt u (A t (u t) + g t) t := by
  obtain ⟨L, hL⟩ := linear_uniform_lipschitz hab A g hA
  let v : IntervalSystem E := {
    left := a
    right := b
    ordered := hab
    initial := x₀
    field := fun t x => A t x + g t
    lip := L
    lipschitz := hL
    continuous := by
      have hcA : Continuous (fun t : Icc a b => A t) := hA.domRestrict
      have hcg : Continuous (fun t : Icc a b => g t) := hg.domRestrict
      exact ((hcA.comp continuous_fst).clm_apply continuous_snd).add
        (hcg.comp continuous_fst) }
  exact v.exists_solution

omit [CompleteSpace E] in
/-- Uniqueness on the complete finite interval follows from Grönwall's inequality. -/
theorem linear_solution_unique {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (g : ℝ → E) (hA : ContinuousOn A (Icc a b))
    {u w : ℝ → E}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (A t (u t) + g t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (A t (w t) + g t) t)
    (hinit : u a = w a) : EqOn u w (Icc a b) := by
  obtain ⟨L, hL⟩ := linear_uniform_lipschitz hab A g hA
  exact ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => Set.univ) (v := fun t x => A t x + g t)
    (fun t ht => (hL t (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hu t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hu t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _)
    (fun t ht => (hw t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hw t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _) hinit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Continuous linear part of equation (27), including the moving-normal term. -/
def projectedOperator (n n' : H) (K : H →L[ℝ] H) (δ : ℝ) : H →L[ℝ] H :=
  -K + (((innerSL ℝ n).comp K - innerSL ℝ n').smulRight ((⟪n, n⟫_ℝ)⁻¹ • n)) -
    δ • ContinuousLinearMap.id ℝ H

theorem projectedOperator_apply (n n' x f : H) (K : H →L[ℝ] H) (δ : ℝ) :
    projectedOperator n n' K δ x - TangentProjection.tangentProj n f =
      TangentProjection.projectedRhs n n' x (K x) f δ := by
  simp only [projectedOperator, sub_apply, add_apply,
    neg_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_apply,
    ContinuousLinearMap.id_apply, TangentProjection.projectedRhs, smul_smul]
  congr 3

/-- Continuity of the true linear operator follows from the coefficient hypotheses;
division is justified by the nonvanishing normal. -/
theorem continuousOn_projectedOperator {s : Set ℝ}
    (n n' : ℝ → H) (K : ℝ → H →L[ℝ] H) (δ : ℝ → ℝ)
    (hn : ContinuousOn n s) (hn' : ContinuousOn n' s)
    (hK : ContinuousOn K s) (hδ : ContinuousOn δ s)
    (hn0 : ∀ t ∈ s, n t ≠ 0) :
    ContinuousOn (fun t => projectedOperator (n t) (n' t) (K t) (δ t)) s := by
  have hlin : ContinuousOn
      (fun t => (innerSL ℝ (n t)).comp (K t) - innerSL ℝ (n' t)) s :=
    (((innerSL ℝ).continuous.comp_continuousOn hn).clm_comp hK).sub
      ((innerSL ℝ).continuous.comp_continuousOn hn')
  have hnorm : ContinuousOn (fun t => (⟪n t, n t⟫_ℝ)⁻¹ • n t) s :=
    ((hn.inner hn).inv₀ (fun t ht => inner_self_ne_zero.mpr (hn0 t ht))).smul hn
  have houter : ContinuousOn (fun t =>
      ((innerSL ℝ (n t)).comp (K t) - innerSL ℝ (n' t)).smulRight
        ((⟪n t, n t⟫_ℝ)⁻¹ • n t)) s :=
    isBoundedBilinearMap_smulRight.continuous.comp_continuousOn (hlin.prodMk hnorm)
  exact (hK.neg.add houter).sub (hδ.smul continuousOn_const)

theorem continuousOn_projectedForcing {s : Set ℝ}
    (n f : ℝ → H) (hn : ContinuousOn n s) (hf : ContinuousOn f s)
    (hn0 : ∀ t ∈ s, n t ≠ 0) :
    ContinuousOn (fun t => -TangentProjection.tangentProj (n t) (f t)) s := by
  exact (hf.sub (((hn.inner hf).div (hn.inner hn)
    (fun t ht => inner_self_ne_zero.mpr (hn0 t ht))).smul hn)).neg

variable [CompleteSpace H]

/-- The actual projected tangent equation has a solution on the entire finite
interval when its coefficients are continuous and its normal never vanishes. -/
theorem exists_projected_solution {a b : ℝ} (hab : a ≤ b)
    (n n' f : ℝ → H) (K : ℝ → H →L[ℝ] H) (δ : ℝ → ℝ)
    (hn : ContinuousOn n (Icc a b)) (hn' : ContinuousOn n' (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hK : ContinuousOn K (Icc a b))
    (hδ : ContinuousOn δ (Icc a b)) (hn0 : ∀ t ∈ Icc a b, n t ≠ 0)
    (x₀ : H) :
    ∃ u : ℝ → H, u a = x₀ ∧ ∀ t ∈ Icc a b,
      HasDerivAt u (TangentProjection.projectedRhs (n t) (n' t) (u t)
        (K t (u t)) (f t) (δ t)) t := by
  obtain ⟨u, hu, hdu⟩ := exists_linear_solution hab
    (fun t => projectedOperator (n t) (n' t) (K t) (δ t))
    (fun t => -TangentProjection.tangentProj (n t) (f t))
    (continuousOn_projectedOperator n n' K δ hn hn' hK hδ hn0)
    (continuousOn_projectedForcing n f hn hf hn0) x₀
  refine ⟨u, hu, fun t ht => ?_⟩
  simpa only [← sub_eq_add_neg, projectedOperator_apply] using hdu t ht

omit [CompleteSpace H] in
/-- Uniqueness holds for all solutions of equation (27), independent of whether
their common initial value is tangent. -/
theorem projected_solution_unique {a b : ℝ} (hab : a ≤ b)
    (n n' f : ℝ → H) (K : ℝ → H →L[ℝ] H) (δ : ℝ → ℝ)
    (hn : ContinuousOn n (Icc a b)) (hn' : ContinuousOn n' (Icc a b))
    (hK : ContinuousOn K (Icc a b)) (hδ : ContinuousOn δ (Icc a b))
    (hn0 : ∀ t ∈ Icc a b, n t ≠ 0) {u w : ℝ → H}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u
      (TangentProjection.projectedRhs (n t) (n' t) (u t) (K t (u t)) (f t) (δ t)) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w
      (TangentProjection.projectedRhs (n t) (n' t) (w t) (K t (w t)) (f t) (δ t)) t)
    (hinit : u a = w a) : EqOn u w (Icc a b) := by
  apply linear_solution_unique hab
    (fun t => projectedOperator (n t) (n' t) (K t) (δ t))
    (fun t => -TangentProjection.tangentProj (n t) (f t))
    (continuousOn_projectedOperator n n' K δ hn hn' hK hδ hn0)
    (u := u) (w := w) _ _ hinit
  · intro t ht
    simpa only [← sub_eq_add_neg, projectedOperator_apply] using hu t ht
  · intro t ht
    simpa only [← sub_eq_add_neg, projectedOperator_apply] using hw t ht

omit [CompleteSpace H] in
/-- On the finite interval, tangency propagates from the left endpoint.
No primitive or globally defined solution is assumed. -/
theorem projected_tangency_preserved {a b : ℝ} (hab : a ≤ b)
    (n n' f u : ℝ → H) (K : ℝ → H →L[ℝ] H) (δ : ℝ → ℝ)
    (hδ : ContinuousOn δ (Icc a b)) (hn0 : ∀ t ∈ Icc a b, n t ≠ 0)
    (hn : ∀ t ∈ Icc a b, HasDerivAt n (n' t) t)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u
      (TangentProjection.projectedRhs (n t) (n' t) (u t) (K t (u t)) (f t) (δ t)) t)
    (hinit : ⟪n a, u a⟫_ℝ = 0) : ∀ t ∈ Icc a b, ⟪n t, u t⟫_ℝ = 0 := by
  let A : ℝ → ℝ →L[ℝ] ℝ := fun t => -δ t • ContinuousLinearMap.id ℝ ℝ
  have hA : ContinuousOn A (Icc a b) := hδ.neg.smul continuousOn_const
  have hd : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => ⟪n s, u s⟫_ℝ) (A t ⟪n t, u t⟫_ℝ + 0) t := by
    intro t ht
    simpa [A] using TangentProjection.tangency_defect_derivative (hn0 t ht) (hn t ht) (hu t ht)
  have hzero : ∀ t ∈ Icc a b, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (A t 0 + 0) t := by
    intro t ht
    simpa using hasDerivAt_const t (0 : ℝ)
  exact linear_solution_unique hab A (fun _ => 0) hA hd hzero hinit

/-- Combined finite-interval existence, uniqueness, and moving tangency for
equation (27). All analytic coefficient hypotheses are explicit. -/
theorem exists_unique_tangent_solution {a b : ℝ} (hab : a ≤ b)
    (n n' f : ℝ → H) (K : ℝ → H →L[ℝ] H) (δ : ℝ → ℝ)
    (hn : ∀ t ∈ Icc a b, HasDerivAt n (n' t) t)
    (hn' : ContinuousOn n' (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hK : ContinuousOn K (Icc a b)) (hδ : ContinuousOn δ (Icc a b))
    (hn0 : ∀ t ∈ Icc a b, n t ≠ 0) (x₀ : H) (hx₀ : ⟪n a, x₀⟫_ℝ = 0) :
    ∃ u : ℝ → H, u a = x₀ ∧
      (∀ t ∈ Icc a b, HasDerivAt u
        (TangentProjection.projectedRhs (n t) (n' t) (u t) (K t (u t)) (f t) (δ t)) t) ∧
      (∀ t ∈ Icc a b, ⟪n t, u t⟫_ℝ = 0) ∧
      ∀ w : ℝ → H, w a = x₀ →
        (∀ t ∈ Icc a b, HasDerivAt w
          (TangentProjection.projectedRhs (n t) (n' t) (w t) (K t (w t)) (f t) (δ t)) t) →
        EqOn w u (Icc a b) := by
  have hncont : ContinuousOn n (Icc a b) :=
    fun t ht => (hn t ht).continuousAt.continuousWithinAt
  obtain ⟨u, hu, hdu⟩ := exists_projected_solution hab n n' f K δ
    hncont hn' hf hK hδ hn0 x₀
  refine ⟨u, hu, hdu, ?_, ?_⟩
  · exact projected_tangency_preserved hab n n' f u K δ hδ hn0 hn hdu
      (by simpa only [hu] using hx₀)
  · intro w hw hdw
    exact projected_solution_unique hab n n' f K δ hncont hn' hK hδ hn0 hdw hdu
      (hw.trans hu.symm)

end

end NavierStokes.TangentODE
