/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.L.SlitContinuation
public import LeanPool.CarlsonFunctions.Carlson.L.Properties
public import LeanPool.CarlsonFunctions.Carlson.L.Deriv

/-!
# Symmetry, aggregation, and scaling on slit-plane nodes

Carlson (1987), (2.2)–(2.5), with arbitrary complex parameters. Positive real
scaling is branch-safe on the whole slit plane; arbitrary complex scaling would
require additional branch assumptions. Zero-parameter deletion retains a nonempty
remaining index type. Coincident-node and singleton formulas also cover Gamma zeros
in the regularized normalization.
-/

open Complex Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Equal nodes may be combined by any surjective partition, on the full slit domain. -/
theorem regCarlsonLSlit_aggregate {κ : Type*} [Fintype κ]
    {q : ι → κ} (hq : Function.Surjective q) (t : ℂ) (b : ι → ℂ)
    {z : κ → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonLSlit t b (z ∘ q) = regCarlsonLSlit t (stdSimplexAggregate q b) z := by
  have hleft : AnalyticOnNhd ℂ (fun w : κ → ℂ => regCarlsonLSlit t b (w ∘ q))
      carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_regCarlsonLSlit_comp analyticAt_const analyticAt_const _ (fun i => hw (q i))
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (q i) : (κ → ℂ) →L[ℂ] ℂ).analyticAt w
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft (analyticOnNhd_regCarlsonLSlit t _) ?_ hz
  intro w hw
  change regCarlsonLSlit t b (w ∘ q) = regCarlsonLSlit t (stdSimplexAggregate q b) w
  dsimp only [Function.comp_def]
  rw [regCarlsonLSlit_eq_continued t b (fun i => hw (q i)), regCarlsonLSlit_eq_continued t _ hw]
  exact regCarlsonLContinued_aggregate hq t hw b

/-- A zero parameter and its node may be deleted if at least one node remains. -/
theorem regCarlsonLSlit_option_zero [Nonempty ι] (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = 0) {z : Option ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonLSlit t b z = regCarlsonLSlit t (b ∘ some) (z ∘ some) := by
  have hright : AnalyticOnNhd ℂ (fun w : Option ι → ℂ =>
      regCarlsonLSlit t (b ∘ some) (w ∘ some)) carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_regCarlsonLSlit_comp analyticAt_const analyticAt_const _ (fun i => hw (some i))
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt w
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (analyticOnNhd_regCarlsonLSlit t b) hright ?_ hz
  intro w hw
  change regCarlsonLSlit t b w = regCarlsonLSlit t (b ∘ some) (w ∘ some)
  dsimp only [Function.comp_def]
  rw [regCarlsonLSlit_eq_continued t b hw, regCarlsonLSlit_eq_continued t _ (fun i => hw (some i))]
  exact regCarlsonLContinued_option_zero t hb hw

/-- Simultaneous permutation of nodes and parameters leaves L unchanged. -/
theorem regCarlsonLSlit_perm (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) (σ : Equiv.Perm ι) :
    regCarlsonLSlit t (b ∘ σ) (z ∘ σ) = regCarlsonLSlit t b z := by
  have hleft : AnalyticOnNhd ℂ (fun w : ι → ℂ => regCarlsonLSlit t (b ∘ σ) (w ∘ σ))
      carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_regCarlsonLSlit_comp analyticAt_const analyticAt_const _ (fun i => hw (σ i))
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (σ i) : (ι → ℂ) →L[ℂ] ℂ).analyticAt w
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft (analyticOnNhd_regCarlsonLSlit t b) ?_ hz
  intro w hw
  change regCarlsonLSlit t (b ∘ σ) (w ∘ σ) = regCarlsonLSlit t b w
  dsimp only [Function.comp_def]
  rw [regCarlsonLSlit_eq_continued t _ (fun i => hw (σ i)), regCarlsonLSlit_eq_continued t b hw]
  exact regCarlsonLContinued_perm t b hw σ

/-- Coincident slit-plane nodes give the elementary power-logarithm kernel. -/
theorem regCarlsonLSlit_const (t w : ℂ) (hw : w ∈ slitPlane) (b : ι → ℂ) :
    regCarlsonLSlit t b (fun _ => w) = (w ^ t * log w) / Gamma (∑ i, b i) := by
  have hleft : AnalyticOnNhd ℂ (fun v : ℂ => regCarlsonLSlit t b (fun _ => v)) slitPlane := by
    intro v hv
    exact analyticAt_regCarlsonLSlit_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun _ => analyticAt_id) (fun _ => hv)
  have hright := (analyticOnNhd_carlsonLKernel t).div_const (c := Gamma (∑ i, b i))
  apply hleft.eqOn_of_preconnected_of_eventuallyEq hright
    ((starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected)
    (by simp : (1 : ℂ) ∈ slitPlane) ?_ hw
  filter_upwards [isOpen_carlsonRightHalfPlane.mem_nhds
    (by norm_num [carlsonRightHalfPlane] : (1 : ℂ) ∈ carlsonRightHalfPlane)] with v hv
  change regCarlsonLSlit t b (fun _ => v) = (v ^ t * log v) / Gamma (∑ i, b i)
  rw [regCarlsonLSlit_eq_continued t b (fun _ => hv)]
  exact regCarlsonLContinued_const t v hv b

@[simp] theorem regCarlsonLSlit_one (t : ℂ) (b : ι → ℂ) :
    regCarlsonLSlit t b (fun _ => 1) = 0 := by
  simpa using regCarlsonLSlit_const t 1 (by simp) b

/-- The singleton convention, including the reciprocal Gamma regularization. -/
theorem regCarlsonLSlit_unique [Unique ι] (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonLSlit t b z = (z default ^ t * log (z default)) / Gamma (b default) := by
  have heq : z = fun _ => z default := funext fun i => congrArg z (Subsingleton.elim i default)
  simpa only [← heq, Fintype.sum_unique] using regCarlsonLSlit_const t (z default) (hz default) b

omit [Fintype ι] in
/-- Positive real scaling preserves the principal-branch node domain. -/
theorem carlsonRSlitDomain_smul_pos {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain)
    {a : ℝ} (ha : 0 < a) : (fun i => (a : ℂ) * z i) ∈ carlsonRSlitDomain := by
  intro i
  rcases mem_slitPlane_iff.mp (hz i) with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by simpa using mul_pos ha h))
  · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using mul_ne_zero ha.ne' h))

/-- Equation (2.5) on slit-plane nodes: scaling contributes the logarithmic R-term. -/
theorem regCarlsonLSlit_smul_of_pos (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) {a : ℝ} (ha : 0 < a) :
    regCarlsonLSlit t b (fun i => (a : ℂ) * z i) =
      (a : ℂ) ^ t * (regCarlsonLSlit t b z + regCarlsonRSlit t b z * log (a : ℂ)) := by
  have hleft : AnalyticOnNhd ℂ (fun w : ι → ℂ => regCarlsonLSlit t b (fun i => (a : ℂ) * w i))
      carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_regCarlsonLSlit_comp analyticAt_const analyticAt_const _
      (carlsonRSlitDomain_smul_pos hw ha)
    exact analyticAt_pi_iff.mpr fun i =>
      analyticAt_const.mul ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)
  have hright : AnalyticOnNhd ℂ (fun w : ι → ℂ =>
      (a : ℂ) ^ t * (regCarlsonLSlit t b w + regCarlsonRSlit t b w * log (a : ℂ)))
      carlsonRSlitDomain :=
    analyticOnNhd_const.mul ((analyticOnNhd_regCarlsonLSlit t b).add
      ((analyticOnNhd_regCarlsonRSlit t b).mul analyticOnNhd_const))
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft hright ?_ hz
  intro w hw
  change regCarlsonLSlit t b (fun i => (a : ℂ) * w i) =
    (a : ℂ) ^ t * (regCarlsonLSlit t b w + regCarlsonRSlit t b w * log (a : ℂ))
  rw [regCarlsonLSlit_eq_continued t b (carlsonRVariableDomain_smul_pos hw ha),
    regCarlsonLSlit_eq_continued t b hw, regCarlsonRSlit_eq_continued t b hw]
  exact regCarlsonLContinued_smul_of_pos t b hw ha

end DirichletTransform
