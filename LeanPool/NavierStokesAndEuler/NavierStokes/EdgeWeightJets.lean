/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedQuotients
public import Mathlib.Analysis.InnerProductSpace.Basic
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricKernelBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Genuine derivative bounds for polynomially weighted Gaussian edges

The scalar derivative polynomials are the actual ones from `FlatCutoff`.
Compactness bounds the derivatives of the smooth coefficient; the full
Fréchet product rule then gives estimates for all joint derivative tensors.
-/

@[expose] public section


noncomputable section

open Set Function Filter Polynomial
open scoped BigOperators ContDiff Topology

namespace NavierStokes.EdgeWeightJets

theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- Coefficient mass, given by `∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|`. -/
noncomputable def coefficientMass (p : ℝ[X]) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

theorem coefficientMass_nonneg (p : ℝ[X]) : 0 ≤ coefficientMass p :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem polynomial_eval_bound (p : ℝ[X]) {x T : ℝ} (hT : 1 ≤ T) (hx : |x| ≤ T) :
    |p.eval x| ≤ coefficientMass p * T ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i * x ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * T ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ (abs_nonneg x) hx i).trans
        (pow_le_pow_right₀ hT (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- Jet mass, given by `1 + ∑ i ∈ Finset.range (n + 1), coefficientMass
(FlatCutoff.jetPolynomial c p i)`. -/
noncomputable def jetMass (c : ℝ) (p : ℝ[X]) (n : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n + 1), coefficientMass (FlatCutoff.jetPolynomial c p i)

/-- Jet order, given by `∑ i ∈ Finset.range (n + 1), (FlatCutoff.jetPolynomial c p
i).natDegree`. -/
noncomputable def jetOrder (c : ℝ) (p : ℝ[X]) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (FlatCutoff.jetPolynomial c p i).natDegree

theorem jetMass_pos (c : ℝ) (p : ℝ[X]) (n : ℕ) : 0 < jetMass c p n := by
  have hs := Finset.sum_nonneg (s := Finset.range (n + 1))
    (fun i _ => coefficientMass_nonneg (FlatCutoff.jetPolynomial c p i))
  dsimp [jetMass]
  linarith

theorem jetMass_bound (c : ℝ) (p : ℝ[X]) {i n : ℕ} (hi : i ≤ n) :
    coefficientMass (FlatCutoff.jetPolynomial c p i) ≤ jetMass c p n := by
  have h := Finset.single_le_sum
    (fun j _ => coefficientMass_nonneg (FlatCutoff.jetPolynomial c p j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  dsimp [jetMass]
  linarith

theorem jetOrder_bound (c : ℝ) (p : ℝ[X]) {i n : ℕ} (hi : i ≤ n) :
    (FlatCutoff.jetPolynomial c p i).natDegree ≤ jetOrder c p n := by
  exact Finset.single_le_sum (f := fun k => (FlatCutoff.jetPolynomial c p k).natDegree)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem polynomialEdge_jets_bound {c : ℝ} (hc : 0 < c) (p : ℝ[X]) (n : ℕ)
    {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ x : ℝ, 0 < x → x ≤ d →
      ‖iteratedFDeriv ℝ i (FlatCutoff.polynomialEdge c p) x‖ ≤
        C * FlatCutoff.edge c x / x ^ N := by
  let M := jetMass c p n
  let N := jetOrder c p n
  refine ⟨M * (d + 1) ^ N, mul_pos (jetMass_pos c p n) (pow_pos (by linarith) _), N, ?_⟩
  intro i hi x hx hxd
  let T := max 1 x⁻¹
  have hT : 1 ≤ T := le_max_left _ _
  have hxi : |x⁻¹| ≤ T := by rw [abs_of_pos (inv_pos.mpr hx)]; exact le_max_right _ _
  have hscale : T ≤ (d + 1) / x := by
    apply max_le
    · apply (le_div_iff₀ hx).2
      linarith
    · apply (le_div_iff₀ hx).2
      rw [inv_mul_cancel₀ hx.ne']
      linarith
  have hpoly : |(FlatCutoff.jetPolynomial c p i).eval x⁻¹| ≤ M * T ^ N := by
    exact (polynomial_eval_bound _ hT hxi).trans
      (mul_le_mul (jetMass_bound c p hi)
        (pow_le_pow_right₀ hT (jetOrder_bound c p hi))
        (pow_nonneg (zero_le_one.trans hT) _) (jetMass_pos c p n).le)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    FlatCutoff.iteratedDeriv_polynomialEdge hc p i]
  simp only [FlatCutoff.polynomialEdge, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (FlatCutoff.edge_nonneg c x)]
  calc
    _ ≤ (M * T ^ N) * FlatCutoff.edge c x :=
      mul_le_mul_of_nonneg_right hpoly (FlatCutoff.edge_nonneg c x)
    _ ≤ (M * ((d + 1) / x) ^ N) * FlatCutoff.edge c x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hT) hscale N)
          (jetMass_pos c p n).le) (FlatCutoff.edge_nonneg c x)
    _ = _ := by rw [div_pow]; ring

theorem edge_div_pow_eq_polynomial (c : ℝ) (j : ℕ) :
    (fun x => FlatCutoff.edge c x / x ^ j) =
      FlatCutoff.polynomialEdge c (X ^ j) := by
  rw [← FlatCutoff.polynomialEdge_one c, FlatCutoff.polynomialEdge_div_pow]
  simp only [one_mul]

theorem edge_div_pow_jets_bound {c : ℝ} (hc : 0 < c) (j n : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ x : ℝ, 0 < x → x ≤ d →
      ‖iteratedFDeriv ℝ i (fun x => FlatCutoff.edge c x / x ^ j) x‖ ≤
        C * FlatCutoff.edge c x / x ^ N := by
  rw [edge_div_pow_eq_polynomial]
  exact polynomialEdge_jets_bound hc (X ^ j) n hd

section Joint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_snd_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (y : E × ℝ) :
    ‖iteratedFDeriv ℝ n (fun y : E × ℝ => f y.2) y‖ ≤ ‖iteratedFDeriv ℝ n f y.2‖ := by
  let L : E × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  change ‖iteratedFDeriv ℝ n (f ∘ L) y‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf y (nat_le_infty n)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hprod : (∏ _i : Fin n, ‖L‖) ≤ 1 := by
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_snd_le
        _ _ _)
  exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg (iteratedFDeriv ℝ n f (L y)))).trans_eq
      (mul_one _)

theorem compact_coefficient_jets {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : E × ℝ → F} (hB : ContDiff ℝ ∞ B) {S : Set E} (hS : IsCompact S)
    (n : ℕ) (d : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ p ∈ S, ∀ x ∈ Icc (0 : ℝ) d,
      ‖iteratedFDeriv ℝ i B (p, x)‖ ≤ C := by
  have hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ S ×ˢ Icc (0 : ℝ) d,
      ‖iteratedFDeriv ℝ i B y‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (hS.prod isCompact_Icc).exists_bound_of_continuousOn
      (hB.continuous_iteratedFDeriv (nat_le_infty i)).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩
  choose C hC hbound using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n + 1), C i, ?_, ?_⟩
  · have hs := Finset.sum_nonneg (s := Finset.range (n + 1)) (fun i _ => hC i)
    linarith
  · intro i hi p hp x hx
    have hs := Finset.single_le_sum (fun i _ => hC i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact (hbound i (p, x) ⟨hp, hx⟩).trans (by linarith)

/-- Weighted, given by `(FlatCutoff.edge c y.2 / y.2 ^ j) * B y`. -/
noncomputable def weighted (c : ℝ) (j : ℕ) (B : E × ℝ → ℝ) (y : E × ℝ) : ℝ :=
  (FlatCutoff.edge c y.2 / y.2 ^ j) * B y

theorem weighted_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ) {B : E × ℝ → ℝ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (weighted c j B) :=
  ((FlatCutoff.edge_div_pow_contDiff hc j).comp contDiff_snd).mul hB

/-- A bound for every actual joint derivative tensor through a fixed order.
Only smoothness of the coefficient and compactness of the parameter set are
assumed; no weighted derivative estimates are inputs. -/
theorem edge_mul_iteratedFDeriv_bound {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → ℝ} (hB : ContDiff ℝ ∞ B) {S : Set E} (hS : IsCompact S)
    (n : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ S, ∀ x : ℝ, 0 < x → x ≤ d →
      ‖iteratedFDeriv ℝ i (weighted c j B) (p, x)‖ ≤
        C * FlatCutoff.edge c x / x ^ N := by
  obtain ⟨A, hA, N, hweight⟩ := edge_div_pow_jets_bound hc j n hd
  obtain ⟨D, hD, hcoef⟩ := compact_coefficient_jets hB hS n d
  refine ⟨(2 : ℝ) ^ n * A * D, by positivity, N, ?_⟩
  intro i hi p hp x hx hxd
  have he := FlatCutoff.edge_nonneg c x
  have hw : ContDiff ℝ ∞ (fun y : E × ℝ => FlatCutoff.edge c y.2 / y.2 ^ j) :=
    (FlatCutoff.edge_div_pow_contDiff hc j).comp contDiff_snd
  have hwbound : ∀ k ≤ i,
      ‖iteratedFDeriv ℝ k (fun y : E × ℝ => FlatCutoff.edge c y.2 / y.2 ^ j) (p, x)‖ ≤
        A * FlatCutoff.edge c x / x ^ N := by
    intro k hk
    exact (norm_iteratedFDeriv_snd_le (FlatCutoff.edge_div_pow_contDiff hc j) k (p, x)).trans
      (hweight k (hk.trans hi) x hx hxd)
  have hbnd := ParametricKernelBounds.norm_iteratedFDeriv_mul_le_of_bounds hw hB i (p, x)
    (by positivity : 0 ≤ A * FlatCutoff.edge c x / x ^ N) hD.le hwbound
    (fun k hk => hcoef k (hk.trans hi) p hp x ⟨hx.le, hxd⟩)
  have hsum : (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)) = (2 : ℝ) ^ i := by
    exact_mod_cast Nat.sum_range_choose i
  rw [hsum] at hbnd
  change ‖iteratedFDeriv ℝ i (fun y => (FlatCutoff.edge c y.2 / y.2 ^ j) * B y) (p, x)‖ ≤ _
  apply hbnd.trans
  calc
    _ = ((2 : ℝ) ^ i * A * D) * FlatCutoff.edge c x / x ^ N := by ring
    _ ≤ _ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi) hA.le)
            hD.le) he) (pow_nonneg hx.le N)

theorem edge_mul_iteratedFDeriv_bound_unit {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → ℝ} (hB : ContDiff ℝ ∞ B) {S : Set E} (hS : IsCompact S) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p ∈ S, ∀ x ∈ Ioo (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (fun y : E × ℝ =>
        (FlatCutoff.edge c y.2 / y.2 ^ j) * B y) (p, x)‖ ≤
          C * FlatCutoff.edge c x / x ^ N := by
  obtain ⟨C, hC, N, hbound⟩ := edge_mul_iteratedFDeriv_bound hc j hB hS n (by
      norm_num : (0 : ℝ) < 1)
  exact ⟨C, hC, N, fun p hp x hx => hbound n le_rfl p hp x hx.1 hx.2.le⟩

theorem weightedJets_of_isCompact_closure {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → ℝ} (hB : ContDiff ℝ ∞ B) {U : Set E} (hU : IsCompact (closure U)) :
    WeightedQuotients.WeightedJets c U (fun _ => 1) (weighted c j B) := by
  apply WeightedQuotients.WeightedJets.of_bounds (fun _ _ => le_rfl)
  intro n
  obtain ⟨C, hC, N, hbound⟩ := edge_mul_iteratedFDeriv_bound_unit hc j hB hU n
  refine ⟨C, hC.le, 0, N, ?_⟩
  intro y hy
  unfold weighted
  simpa only [pow_zero, mul_one, Prod.eta] using hbound y.1 (subset_closure hy.1) y.2 hy.2

theorem edge_div_pow_iteratedFDeriv_zero {c : ℝ} (hc : 0 < c) (j n : ℕ) :
    iteratedFDeriv ℝ n (fun x => FlatCutoff.edge c x / x ^ j) 0 = 0 := by
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, edge_div_pow_eq_polynomial,
    FlatCutoff.iteratedDeriv_polynomialEdge hc (X ^ j) n, FlatCutoff.polynomialEdge_zero, norm_zero]

/-- Every full derivative tensor vanishes on the joining hyperplane. -/
theorem weighted_iteratedFDeriv_zero {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → ℝ} (hB : ContDiff ℝ ∞ B) (n : ℕ) (p : E) :
    iteratedFDeriv ℝ n (weighted c j B) (p, 0) = 0 := by
  have hz (k : ℕ) : iteratedFDeriv ℝ k
      (fun y : E × ℝ => FlatCutoff.edge c y.2 / y.2 ^ j) (p, 0) = 0 := by
    apply norm_le_zero_iff.mp
    have h := norm_iteratedFDeriv_snd_le (FlatCutoff.edge_div_pow_contDiff hc j) k (p, 0)
    simpa only [edge_div_pow_iteratedFDeriv_zero hc j k, norm_zero] using h
  have hw : ContDiff ℝ ∞ (fun y : E × ℝ => FlatCutoff.edge c y.2 / y.2 ^ j) :=
    (FlatCutoff.edge_div_pow_contDiff hc j).comp contDiff_snd
  have h := norm_iteratedFDeriv_mul_le hw hB (p, 0) (nat_le_infty n)
  apply norm_le_zero_iff.mp
  unfold weighted
  simpa only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weighted_of_nonpos (c : ℝ) (j : ℕ) (B : E × ℝ → ℝ) {y : E × ℝ}
    (hy : y.2 ≤ 0) : weighted c j B y = 0 := by
  simp [weighted, FlatCutoff.edge_of_nonpos c hy]

end Joint

section MixedDerivatives

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_comp_linear_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → ℝ} (hf : ContDiff ℝ ∞ f) (L : G →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (n : ℕ) (x : G) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (nat_le_infty n)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏ _i : Fin n, ‖L‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ n f (L x)))

theorem norm_iteratedFDeriv_parameter_le {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (p : E) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun p => f (p, x)) p‖ ≤ ‖iteratedFDeriv ℝ n f (p, x)‖ := by
  let L : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod 0
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simp [L]
  let g : E × ℝ → ℝ := fun y => f (y + (0, x))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have h := norm_iteratedFDeriv_comp_linear_le hg L hL n p
  have heq : g ∘ L = fun p => f (p, x) := by ext q; simp [g, L]
  rw [heq] at h
  simpa only [g, iteratedFDeriv_comp_add_right, L, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, _root_.zero_apply, Prod.mk_add_mk, add_zero, zero_add] using h

/-- Radial iterate as an element of `ℕ → E × ℝ → ℝ | 0 => f | n + 1 => fun y => fderiv ℝ
(radialIterate f n) y (0, 1)`. -/
noncomputable def radialIterate (f : E × ℝ → ℝ) : ℕ → E × ℝ → ℝ
  | 0 => f
  | n + 1 => fun y => fderiv ℝ (radialIterate f n) y (0, 1)

theorem radialIterate_contDiff {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (radialIterate f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem deriv_slice {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (p : E) (x : ℝ) :
    deriv (fun t => f (p, t)) x = fderiv ℝ f (p, x) (0, 1) := by
  have hpair : HasDerivAt (fun t : ℝ => (p, t)) (0, 1) x :=
    (hasDerivAt_const x p).prodMk (hasDerivAt_id x)
  exact ((hf.differentiable (by simp) (p, x)).hasFDerivAt.comp_hasDerivAt x hpair).deriv

theorem radialIterate_eq {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (p : E) (x : ℝ) :
    radialIterate f n (p, x) = iteratedDeriv n (fun t => f (p, t)) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n (fun t => f (p, t)) = fun t => radialIterate f n (p, t) :=
        funext (fun t => (ih t).symm)
      rw [heq, deriv_slice (radialIterate_contDiff hf n)]
      rfl

theorem norm_radialIterate_le {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n m : ℕ) (y : E × ℝ) :
    ‖iteratedFDeriv ℝ m (radialIterate f n) y‖ ≤ ‖iteratedFDeriv ℝ (m + n) f y‖ := by
  induction n generalizing m with
  | zero => simp [radialIterate]
  | succ n ih =>
      have h := norm_iteratedFDeriv_clm_apply_const
        (c := ((0 : E), (1 : ℝ)))
        (((radialIterate_contDiff hf n).fderiv_right (by simp)).contDiffAt (x := y))
        (nat_le_infty m)
      have hn : ‖((0 : E), (1 : ℝ))‖ = 1 := by simp
      rw [hn, one_mul, norm_iteratedFDeriv_fderiv] at h
      have hi := ih (m + 1)
      rw [show m + 1 + n = m + (n + 1) by omega] at hi
      exact h.trans hi

/-- The left side contains the actual nested radial and parameter derivatives,
and is controlled by the full joint tensor of total order. -/
theorem norm_mixed_derivatives_le {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (m n : ℕ) (p : E) (x : ℝ) :
    ‖iteratedFDeriv ℝ m (fun q => iteratedDeriv n (fun t => f (q, t)) x) p‖ ≤
      ‖iteratedFDeriv ℝ (m + n) f (p, x)‖ := by
  have heq : (fun q => iteratedDeriv n (fun t => f (q, t)) x) =
      fun q => radialIterate f n (q, x) := funext (fun q => (radialIterate_eq hf n q x).symm)
  rw [heq]
  exact (norm_iteratedFDeriv_parameter_le (radialIterate_contDiff hf n) m p x).trans
    (norm_radialIterate_le hf n m (p, x))

theorem edge_mul_mixed_derivatives_bound {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → ℝ} (hB : ContDiff ℝ ∞ B) {S : Set E} (hS : IsCompact S)
    (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ m n : ℕ, m + n ≤ k → ∀ p ∈ S,
      ∀ x : ℝ, 0 < x → x ≤ d →
        ‖iteratedFDeriv ℝ m (fun q => iteratedDeriv n
          (fun t => weighted c j B (q, t)) x) p‖ ≤ C * FlatCutoff.edge c x / x ^ N := by
  obtain ⟨C, hC, N, hbound⟩ := edge_mul_iteratedFDeriv_bound hc j hB hS k hd
  exact ⟨C, hC, N, fun m n hmn p hp x hx hxd =>
    (norm_mixed_derivatives_le (weighted_contDiff hc j hB) m n p x).trans
      (hbound (m + n) hmn p hp x hx hxd)⟩

end MixedDerivatives

section VectorCoefficients

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_coefficient_jets_on {B : E × ℝ → F} {V : Set (E × ℝ)}
    (hV : IsOpen V) (hB : ContDiffOn ℝ ∞ B V) {S : Set E} (hS : IsCompact S)
    (n : ℕ) (d : ℝ) (hSV : S ×ˢ Icc (0 : ℝ) d ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ p ∈ S, ∀ x ∈ Icc (0 : ℝ) d,
      ‖iteratedFDeriv ℝ i B (p, x)‖ ≤ C := by
  have hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ S ×ˢ Icc (0 : ℝ) d,
      ‖iteratedFDeriv ℝ i B y‖ ≤ C := by
    intro i
    have hcont : ContinuousOn (iteratedFDeriv ℝ i B) V := by
      intro y hy
      have hi : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ i B) y :=
        (hB.contDiffAt (hV.mem_nhds hy)).iteratedFDeriv_right
          (WithTop.coe_le_coe.mpr le_top)
      exact hi.continuousAt.continuousWithinAt
    obtain ⟨C, hC⟩ := (hS.prod isCompact_Icc).exists_bound_of_continuousOn (hcont.mono hSV)
    exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩
  choose C hC hbound using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n + 1), C i, ?_, ?_⟩
  · have hs := Finset.sum_nonneg (s := Finset.range (n + 1)) (fun i _ => hC i)
    linarith
  · intro i hi p hp x hx
    have hs := Finset.single_le_sum (fun i _ => hC i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact (hbound i (p, x) ⟨hp, hx⟩).trans (by linarith)

/-- The vector-valued local version needs only genuine smoothness on an open
neighborhood of the compact parameter-coordinate region. -/
theorem edge_smul_iteratedFDeriv_bound_on {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → F} {V : Set (E × ℝ)} (hV : IsOpen V) (hB : ContDiffOn ℝ ∞ B V)
    {S : Set E} (hS : IsCompact S) (n : ℕ) {d : ℝ} (hd : 0 < d)
    (hSV : S ×ˢ Icc (0 : ℝ) d ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ S, ∀ x : ℝ, 0 < x → x ≤ d →
      ‖iteratedFDeriv ℝ i (fun y : E × ℝ =>
        (FlatCutoff.edge c y.2 / y.2 ^ j) • B y) (p, x)‖ ≤
          C * FlatCutoff.edge c x / x ^ N := by
  obtain ⟨A, hA, N, hweight⟩ := edge_div_pow_jets_bound hc j n hd
  obtain ⟨D, hD, hcoef⟩ := compact_coefficient_jets_on hV hB hS n d hSV
  refine ⟨(2 : ℝ) ^ n * A * D, by positivity, N, ?_⟩
  intro i hi p hp x hx hxd
  have he := FlatCutoff.edge_nonneg c x
  have hy : (p, x) ∈ V := hSV ⟨hp, hx.le, hxd⟩
  have hw : ContDiff ℝ ∞ (fun y : E × ℝ => FlatCutoff.edge c y.2 / y.2 ^ j) :=
    (FlatCutoff.edge_div_pow_contDiff hc j).comp contDiff_snd
  have hwbound : ∀ k ≤ i,
      ‖iteratedFDeriv ℝ k (fun y : E × ℝ => FlatCutoff.edge c y.2 / y.2 ^ j) (p, x)‖ ≤
        A * FlatCutoff.edge c x / x ^ N := by
    intro k hk
    exact (norm_iteratedFDeriv_snd_le (FlatCutoff.edge_div_pow_contDiff hc j) k (p, x)).trans
      (hweight k (hk.trans hi) x hx hxd)
  have hprod := norm_iteratedFDerivWithin_smul_le hw.contDiffOn hB hV.uniqueDiffOn hy (nat_le_infty
      i)
  simp only [iteratedFDerivWithin_of_isOpen _ hV hy] at hprod
  apply hprod.trans
  calc
    _ ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (A * FlatCutoff.edge c x / x ^ N) * D := by
      apply Finset.sum_le_sum
      intro k hk
      have hki : k ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hwbound k hki) (Nat.cast_nonneg _))
        (hcoef (i - k) ((Nat.sub_le i k).trans hi) p hp x ⟨hx.le, hxd⟩)
        (norm_nonneg _) (by positivity)
    _ = ((2 : ℝ) ^ i * A * D) * FlatCutoff.edge c x / x ^ N := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)) = (2 : ℝ) ^ i := by
        exact_mod_cast Nat.sum_range_choose i
      rw [hsum]
      ring
    _ ≤ _ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi) hA.le)
            hD.le) he) (pow_nonneg hx.le N)

theorem edge_smul_iteratedFDeriv_bound {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → F} (hB : ContDiff ℝ ∞ B) {S : Set E} (hS : IsCompact S)
    (n : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ S, ∀ x : ℝ, 0 < x → x ≤ d →
      ‖iteratedFDeriv ℝ i (fun y : E × ℝ =>
        (FlatCutoff.edge c y.2 / y.2 ^ j) • B y) (p, x)‖ ≤
          C * FlatCutoff.edge c x / x ^ N :=
  edge_smul_iteratedFDeriv_bound_on hc j isOpen_univ hB.contDiffOn hS n hd (subset_univ _)

theorem edge_mul_iteratedFDeriv_bound_on {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → ℝ} {V : Set (E × ℝ)} (hV : IsOpen V) (hB : ContDiffOn ℝ ∞ B V)
    {S : Set E} (hS : IsCompact S) (n : ℕ) {d : ℝ} (hd : 0 < d)
    (hSV : S ×ˢ Icc (0 : ℝ) d ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ S, ∀ x : ℝ, 0 < x → x ≤ d →
      ‖iteratedFDeriv ℝ i (weighted c j B) (p, x)‖ ≤
        C * FlatCutoff.edge c x / x ^ N := by
  unfold weighted
  simpa only [smul_eq_mul] using
    edge_smul_iteratedFDeriv_bound_on hc j hV hB hS n hd hSV

end VectorCoefficients

section Products

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem edge_mul_edge (c d x : ℝ) :
    FlatCutoff.edge c x * FlatCutoff.edge d x = FlatCutoff.edge (c + d) x := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos _ hx]
  · have hp := lt_of_not_ge hx
    rw [FlatCutoff.edge_of_pos c hp, FlatCutoff.edge_of_pos d hp,
      FlatCutoff.edge_of_pos (c + d) hp, ← Real.exp_add]
    congr 1
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weighted_mul (c d : ℝ) (j k : ℕ) (B D : E × ℝ → ℝ) :
    (fun y => weighted c j B y * weighted d k D y) =
      weighted (c + d) (j + k) (fun y => B y * D y) := by
  funext y
  simp only [weighted, pow_add]
  rw [show (FlatCutoff.edge c y.2 / y.2 ^ j * B y) *
      (FlatCutoff.edge d y.2 / y.2 ^ k * D y) =
      (FlatCutoff.edge c y.2 * FlatCutoff.edge d y.2) /
        (y.2 ^ j * y.2 ^ k) * (B y * D y) by ring]
  rw [edge_mul_edge]

theorem weighted_mul_iteratedFDeriv_bound {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (j k : ℕ) {B D : E × ℝ → ℝ} (hB : ContDiff ℝ ∞ B) (hD : ContDiff ℝ ∞ D)
    {S : Set E} (hS : IsCompact S) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ S, ∀ x : ℝ, 0 < x → x ≤ a →
      ‖iteratedFDeriv ℝ i (fun y => weighted c j B y * weighted d k D y) (p, x)‖ ≤
        C * FlatCutoff.edge (c + d) x / x ^ N := by
  rw [weighted_mul]
  exact edge_mul_iteratedFDeriv_bound (add_pos hc hd) (j + k) (hB.mul hD) hS n ha

/-- Any fixed nonnegative power of the radial coordinate can be retained
inside the actual smooth coefficient. Inverse powers are already arbitrary. -/
theorem radial_power_iteratedFDeriv_bound {c : ℝ} (hc : 0 < c) (j k : ℕ)
    {B : E × ℝ → ℝ} (hB : ContDiff ℝ ∞ B) {S : Set E} (hS : IsCompact S)
    (n : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ S, ∀ x : ℝ, 0 < x → x ≤ d →
      ‖iteratedFDeriv ℝ i (fun y : E × ℝ =>
        (FlatCutoff.edge c y.2 / y.2 ^ j) * (y.2 ^ k * B y)) (p, x)‖ ≤
          C * FlatCutoff.edge c x / x ^ N :=
  edge_mul_iteratedFDeriv_bound hc j ((contDiff_snd.pow k).mul hB) hS n hd

theorem edge_pow (c x : ℝ) {k : ℕ} (hk : 0 < k) :
    FlatCutoff.edge c x ^ k = FlatCutoff.edge ((k : ℝ) * c) x := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos _ hx, hk.ne']
  · have hp := lt_of_not_ge hx
    rw [FlatCutoff.edge_of_pos c hp, FlatCutoff.edge_of_pos ((k : ℝ) * c) hp,
      ← Real.exp_nat_mul]
    congr 1
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weighted_pow (c : ℝ) (j : ℕ) (B : E × ℝ → ℝ) {k : ℕ} (hk : 0 < k) :
    (fun y => weighted c j B y ^ k) =
      weighted ((k : ℝ) * c) (j * k) (fun y => B y ^ k) := by
  funext y
  simp only [weighted, mul_pow, div_pow, edge_pow c y.2 hk, pow_mul]

theorem weighted_pow_iteratedFDeriv_bound {c : ℝ} (hc : 0 < c) (j : ℕ)
    {B : E × ℝ → ℝ} (hB : ContDiff ℝ ∞ B) {S : Set E} (hS : IsCompact S)
    {k : ℕ} (hk : 0 < k) (n : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ S, ∀ x : ℝ, 0 < x → x ≤ d →
      ‖iteratedFDeriv ℝ i (fun y => weighted c j B y ^ k) (p, x)‖ ≤
        C * FlatCutoff.edge ((k : ℝ) * c) x / x ^ N := by
  rw [weighted_pow c j B hk]
  exact edge_mul_iteratedFDeriv_bound (mul_pos (Nat.cast_pos.mpr hk) hc)
    (j * k) (hB.pow k) hS n hd

end Products

end NavierStokes.EdgeWeightJets
