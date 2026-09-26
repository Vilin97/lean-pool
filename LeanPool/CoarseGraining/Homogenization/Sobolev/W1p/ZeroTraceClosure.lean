/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.WeakGradientClosure

/-!
# Finite-exponent zero-trace closure

This module closes the concrete `W^{1,p}_0` carrier under coordinatewise
`L^p` convergence.  It is independent of cubes and of any PDE estimate: the
only input is a sequence of already bundled zero-trace approximants.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

/-- Interchanging the two functions leaves the `L^p` norm of their difference unchanged. -/
theorem eLpNorm_sub_swap_finiteLp
    {d : ℕ} {μ : Measure (Vec d)} {p : ℝ≥0∞}
    (a b : Vec d → ℝ) :
    eLpNorm (fun x => a x - b x) p μ =
      eLpNorm (fun x => b x - a x) p μ := by
  rw [show (fun x => a x - b x) = -(fun x => b x - a x) from by
    funext x
    simp only [Pi.neg_apply]
    ring, eLpNorm_neg]

namespace W10pFunction

/-- A coordinatewise `L^p` limit of bundled zero-trace functions is again a
bundled zero-trace function.  The smooth approximation in the result is an
internally selected diagonal of the supplied approximations; callers provide
only convergence of the original sequence. -/
noncomputable def ofTendstoELpNorm
    {d : ℕ} {U : Set (Vec d)} (p : FiniteLpExponent)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hDu : GradMemLpOn U p.exponent Du)
    (u_n : ℕ → W10pFunction U p.exponent)
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_Du : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (u_n n).grad x i - Du x i) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    W10pFunction U p.exponent := by
  classical
  let μ : Measure (Vec d) := volume.restrict U
  let target : W1pFunction U p.exponent :=
    { toFun := u
      grad := Du
      memLp := hu
      gradMemLp := hDu
      hasWeakGradient := HasWeakGradientOn.of_tendsto_eLpNorm_finiteLp p hu hDu
        (fun n => (u_n n).memLp) (fun n => (u_n n).gradMemLp)
        (fun n => (u_n n).hasWeakGradient)
        (by simpa only [μ] using htend_u)
        (by
          intro i
          simpa only [μ] using htend_Du i) }
  let ε : ℕ → ℝ≥0∞ := fun n => (↑(n + 1))⁻¹
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    simp only [ε]
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (n + 1))
  have hε_tendsto : Tendsto ε atTop (nhds 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hex : ∀ n, ∃ k,
      eLpNorm (fun x => (u_n n).approx k x - (u_n n).toFun x) p.exponent μ < ε n ∧
      ∀ i : Fin d, eLpNorm
        (fun x => (fderiv ℝ ((u_n n).approx k) x) (basisVec i) -
          (u_n n).grad x i) p.exponent μ < ε n := by
    intro n
    have e1 : ∀ᶠ k in atTop,
        eLpNorm (fun x => (u_n n).approx k x - (u_n n).toFun x) p.exponent μ < ε n :=
      (u_n n).tendsto_approx.eventually_lt_const (hε_pos n)
    have e2 : ∀ i : Fin d, ∀ᶠ k in atTop, eLpNorm
        (fun x => (fderiv ℝ ((u_n n).approx k) x) (basisVec i) -
          (u_n n).grad x i) p.exponent μ < ε n :=
      fun i => ((u_n n).tendsto_approx_grad i).eventually_lt_const (hε_pos n)
    have e2' : ∀ᶠ k in atTop, ∀ i : Fin d, eLpNorm
        (fun x => (fderiv ℝ ((u_n n).approx k) x) (basisVec i) -
          (u_n n).grad x i) p.exponent μ < ε n :=
      Filter.eventually_all.2 e2
    exact (e1.and e2').exists
  choose k hk using hex
  let ψ : ℕ → Vec d → ℝ := fun n => (u_n n).approx (k n)
  have htarget_fun : Tendsto
      (fun n => eLpNorm (fun x => (u_n n).toFun x - target.toFun x) p.exponent μ)
      atTop (nhds 0) := by
    refine htend_u.congr (fun n => ?_)
    rw [eLpNorm_sub_swap_finiteLp (u_n n).toFun target.toFun]
  have hfun_bound : Tendsto (fun n => ε n +
      eLpNorm (fun x => (u_n n).toFun x - target.toFun x) p.exponent μ)
      atTop (nhds 0) := by
    simpa using hε_tendsto.add htarget_fun
  have htarget_grad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (u_n n).grad x i - target.grad x i) p.exponent μ)
      atTop (nhds 0) := by
    intro i
    refine (htend_Du i).congr (fun n => ?_)
    rw [eLpNorm_sub_swap_finiteLp
      (fun x => (u_n n).grad x i) (fun x => target.grad x i)]
  have hgrad_bound : ∀ i : Fin d, Tendsto (fun n => ε n + eLpNorm
      (fun x => (u_n n).grad x i - target.grad x i) p.exponent μ)
      atTop (nhds 0) := by
    intro i
    simpa using hε_tendsto.add (htarget_grad i)
  exact
    { toW1pFunction := target
      approx := ψ
      approx_smooth := fun n => (u_n n).approx_smooth (k n)
      approx_hasCompactSupport := fun n => (u_n n).approx_hasCompactSupport (k n)
      approx_support_subset := fun n => (u_n n).approx_support_subset (k n)
      tendsto_approx := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfun_bound
          (fun n => zero_le) (fun n => ?_)
        have hsm_ψ : AEStronglyMeasurable (ψ n) μ :=
          ((u_n n).approx_smooth (k n)).continuous.aestronglyMeasurable
        have hsm_un : AEStronglyMeasurable (u_n n).toFun μ :=
          (u_n n).memLp.aestronglyMeasurable
        have hsm_target : AEStronglyMeasurable target.toFun μ :=
          target.memLp.aestronglyMeasurable
        have heq :
            (fun x => ψ n x - target.toFun x) =
              (fun x => ψ n x - (u_n n).toFun x) +
                (fun x => (u_n n).toFun x - target.toFun x) := by
          funext x
          simp only [Pi.add_apply]
          ring
        rw [heq]
        refine (eLpNorm_add_le p.one_lt.le).trans ?_
        exact add_le_add (le_of_lt (hk n).1) le_rfl
      tendsto_approx_grad := by
        intro i
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (hgrad_bound i) (fun n => zero_le) (fun n => ?_)
        have hsm_dψ : AEStronglyMeasurable
            (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) μ := by
          have hcont : ContDiff ℝ (⊤ : ℕ∞)
              (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) :=
            (((u_n n).approx_smooth (k n)).fderiv_right (m := (⊤ : ℕ∞))
              (by norm_cast)).clm_apply contDiff_const
          exact hcont.continuous.aestronglyMeasurable
        have hsm_un : AEStronglyMeasurable (fun x => (u_n n).grad x i) μ :=
          (u_n n).gradMemLp i |>.aestronglyMeasurable
        have hsm_target : AEStronglyMeasurable (fun x => target.grad x i) μ :=
          target.gradMemLp i |>.aestronglyMeasurable
        have heq :
            (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - target.grad x i) =
              (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - (u_n n).grad x i) +
                (fun x => (u_n n).grad x i - target.grad x i) := by
          funext x
          simp only [Pi.add_apply]
          ring
        rw [heq]
        refine (eLpNorm_add_le p.one_lt.le).trans ?_
        exact add_le_add (le_of_lt ((hk n).2 i)) le_rfl }

@[simp] theorem ofTendstoELpNorm_toFun
    {d : ℕ} {U : Set (Vec d)} (p : FiniteLpExponent)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hDu : GradMemLpOn U p.exponent Du)
    (u_n : ℕ → W10pFunction U p.exponent)
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_Du : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (u_n n).grad x i - Du x i) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    (ofTendstoELpNorm p hu hDu u_n htend_u htend_Du).toFun = u :=
  rfl

@[simp] theorem ofTendstoELpNorm_grad
    {d : ℕ} {U : Set (Vec d)} (p : FiniteLpExponent)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hDu : GradMemLpOn U p.exponent Du)
    (u_n : ℕ → W10pFunction U p.exponent)
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_Du : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (u_n n).grad x i - Du x i) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    (ofTendstoELpNorm p hu hDu u_n htend_u htend_Du).grad = Du :=
  rfl

end W10pFunction

end
end Homogenization
