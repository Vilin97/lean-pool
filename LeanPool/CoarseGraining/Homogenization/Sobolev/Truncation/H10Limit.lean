/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.Basic

/-! # H10Limit -/

namespace Homogenization

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# `H¹₀` is closed under `H¹` limits

`memH10_of_tendsto_H1`: if `f : H¹(U)` is the `L²` limit (function and every
gradient coordinate) of a sequence `Fₙ` of `H¹(U)` functions each lying in
`H¹₀(U)`, then `f ∈ H¹₀(U)`.

Each `MemH10 U Fₙ` supplies an `H¹₀` witness `Wₙ` bundling smooth compactly
supported approximants `Wₙ.approx k` (support `⊆ U`) converging in `L²` to
`Wₙ.toFun = Fₙ.toFun` and to `Wₙ.grad`.  A diagonal choice picks `kₙ` with all
`d+1` distances below `1/(n+1)`; the resulting `ψₙ := Wₙ.approx kₙ` is smooth,
compactly supported in `U`, and converges to `f` and `∇f`.  Weak-gradient
uniqueness bridges `Wₙ.grad` and `Fₙ.grad`, which agree a.e.
-/

/-- Commuting `eLpNorm` of a pointwise difference of two functions. -/
theorem eLpNorm_sub_swap {d : ℕ} {μ : Measure (Vec d)} (a b : Vec d → ℝ) {p : ℝ≥0∞} :
    eLpNorm (fun x => a x - b x) p μ = eLpNorm (fun x => b x - a x) p μ := by
  rw [show (fun x => a x - b x) = -(fun x => b x - a x) from by
    funext x; simp only [Pi.neg_apply]; ring, eLpNorm_neg]

/-- **`H¹₀(U)` closed under `L²` limits.**  It is closed under `L²` limits of the function together
with all its gradient coordinates. -/
theorem memH10_of_tendsto_H1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (f : H1Function U) (F : ℕ → H1Function U)
    (hmem : ∀ n, MemH10 U (F n).toFun)
    (hfun : Tendsto
      (fun n => eLpNorm (fun x => f.toFun x - (F n).toFun x) 2 (volumeMeasureOn U))
      atTop (nhds 0))
    (hgrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => f.grad x i - (F n).grad x i) 2 (volumeMeasureOn U))
      atTop (nhds 0)) :
    MemH10 U f.toFun := by
  classical
  set μU : Measure (Vec d) := volumeMeasureOn U with hμU
  -- H¹₀ witnesses of the `Fₙ`.
  choose W hW using hmem
  -- Local integrability of gradient coordinates, for weak-gradient uniqueness.
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  -- `Wₙ.grad =ᵐ Fₙ.grad` (same function ⟹ same weak gradient a.e.).
  have hbridge : ∀ n (i : Fin d),
      (fun x => (W n).toH1Function.grad x i) =ᵐ[μU] (fun x => (F n).grad x i) := by
    intro n i
    have hw := (W n).toH1Function.hasWeakGradient i
    rw [hW n] at hw
    exact HasWeakPartialDerivOn.ae_eq hU.isOpen (hloc _ i) (hloc _ i) hw
      ((F n).hasWeakGradient i)
  -- Diagonal tolerance.
  set ε : ℕ → ℝ≥0∞ := fun n => (↑(n + 1))⁻¹ with hε
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    simp only [hε]
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (n + 1))
  have hε_tendsto : Tendsto ε atTop (nhds 0) :=
    (ENNReal.tendsto_inv_nat_nhds_zero).comp (tendsto_add_atTop_nat 1)
  -- Diagonal existence.
  have hex : ∀ n, ∃ k,
      eLpNorm (fun x => (W n).approx k x - (W n).toH1Function.toFun x) 2 μU < ε n ∧
      ∀ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n := by
    intro n
    have e1 : ∀ᶠ k in atTop,
        eLpNorm (fun x => (W n).approx k x - (W n).toH1Function.toFun x) 2 μU < ε n :=
      (W n).tendsto_approx.eventually_lt_const (hε_pos n)
    have e2 : ∀ i : Fin d, ∀ᶠ k in atTop,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n :=
      fun i => ((W n).tendsto_approx_grad i).eventually_lt_const (hε_pos n)
    have e2' : ∀ᶠ k in atTop, ∀ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n :=
      Filter.eventually_all.2 e2
    exact (e1.and e2').exists
  choose k hk using hex
  set ψ : ℕ → Vec d → ℝ := fun n => (W n).approx (k n) with hψ
  -- Function-side upper bound sequence tends to 0.
  have htf : Tendsto
      (fun n => eLpNorm (fun x => (W n).toH1Function.toFun x - f.toFun x) 2 μU)
      atTop (nhds 0) := by
    refine hfun.congr (fun n => ?_)
    rw [eLpNorm_sub_swap ((W n).toH1Function.toFun) (f.toFun), hW n]
  have hfun_bound : Tendsto (fun n => ε n +
      eLpNorm (fun x => (W n).toH1Function.toFun x - f.toFun x) 2 μU) atTop (nhds 0) := by
    simpa using hε_tendsto.add htf
  -- Gradient-side upper bound sequences tend to 0.
  have hgi : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (W n).toH1Function.grad x i - f.grad x i) 2 μU)
      atTop (nhds 0) := by
    intro i
    refine (hgrad i).congr (fun n => ?_)
    rw [eLpNorm_sub_swap (fun x => (W n).toH1Function.grad x i) (fun x => f.grad x i)]
    exact eLpNorm_congr_ae (by filter_upwards [hbridge n i] with x hx; rw [hx])
  have hgrad_bound : ∀ i : Fin d, Tendsto (fun n => ε n +
      eLpNorm (fun x => (W n).toH1Function.grad x i - f.grad x i) 2 μU) atTop (nhds 0) := by
    intro i
    simpa using hε_tendsto.add (hgi i)
  -- Package the target as an `H¹₀` function with the diagonal approximants.
  refine ⟨{ toH1Function := f
            approx := ψ
            approx_smooth := fun n => (W n).approx_smooth (k n)
            approx_hasCompactSupport := fun n => (W n).approx_hasCompactSupport (k n)
            approx_support_subset := fun n => (W n).approx_support_subset (k n)
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, rfl⟩
  · -- `ψₙ → f` in `L²`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfun_bound
      (fun n => zero_le) (fun n => ?_)
    have hsm_ψ : AEStronglyMeasurable (ψ n) μU :=
      ((W n).approx_smooth (k n)).continuous.aestronglyMeasurable
    have hsm_Wtf : AEStronglyMeasurable (W n).toH1Function.toFun μU :=
      (W n).toH1Function.memL2.1
    have heq :
        (fun x => ψ n x - f.toFun x) =
          (fun x => ψ n x - (W n).toH1Function.toFun x) +
            (fun x => (W n).toH1Function.toFun x - f.toFun x) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [heq]
    refine (eLpNorm_add_le (hsm_ψ.sub hsm_Wtf) (hsm_Wtf.sub f.memL2.1) (by norm_num)).trans ?_
    exact add_le_add (le_of_lt (hk n).1) le_rfl
  · -- `∇ψₙ → ∇f` in `L²`, coordinatewise.
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hgrad_bound i)
      (fun n => zero_le) (fun n => ?_)
    have hsm_dψ : AEStronglyMeasurable
        (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) μU := by
      have : ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) :=
        (((W n).approx_smooth (k n)).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
          contDiff_const
      exact this.continuous.aestronglyMeasurable
    have hsm_Wg : AEStronglyMeasurable (fun x => (W n).toH1Function.grad x i) μU :=
      (W n).toH1Function.gradMemL2 i |>.1
    have heq :
        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - f.grad x i) =
          (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - (W n).toH1Function.grad x i) +
            (fun x => (W n).toH1Function.grad x i - f.grad x i) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [heq]
    refine (eLpNorm_add_le (hsm_dψ.sub hsm_Wg) (hsm_Wg.sub (f.gradMemL2 i).1)
      (by norm_num)).trans ?_
    exact add_le_add (le_of_lt ((hk n).2 i)) le_rfl

end Homogenization
