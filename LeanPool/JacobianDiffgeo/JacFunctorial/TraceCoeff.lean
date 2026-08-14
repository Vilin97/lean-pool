/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.FormTrace.TraceZkForm
import LeanPool.JacobianDiffgeo.Surface.Identity
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# `traceCoeff`: the repaired planar trace coefficient (jacobian-functoriality §6, planar layer)

Unit: jacobian-functoriality. `RS.FormTrace.traceZkForm h k` (the Jacobian-weighted planar trace
atom) has a *removable singularity* at the branch coordinate `0`: its literal value there is junk
(`traceZk`'s `w = 0` convention), and for `k > 1` does **not** equal the limit from the punctured
neighborhood — the precise defect that blocked the previous builder (see the root LEDGER). This
file REPAIRS the value at `0` via mathlib's meromorphic normal form (`toMeromorphicNFAt`), and
proves the repair is genuinely analytic across `0`:

* `RS.traceCoeff h k := toMeromorphicNFAt (traceZkForm h k) 0` — agrees with `traceZkForm h k`
  at every `w ≠ 0` (`traceCoeff_apply_of_ne_zero`), analytic at `0` once `h` is
  (`analyticAt_traceCoeff_zero`), and analytic on the whole ball `ball 0 (ρ ^ k)` once `h` is
  analytic on `ball 0 ρ` (`analyticOnNhd_traceCoeff` — THE branch-point analyticity).
* Route for the `0`-analyticity (design §6.3, route (a)): `traceZkForm h k` is meromorphic at `0`
  (`meromorphicAt_traceZkForm`), and its Laurent coefficients at negative indices all vanish by
  the already-proved shift formula `laurentCoeffAt_traceZkForm` plus analyticity of `h` — hence
  its meromorphic order is `≥ 0` (`forall_neg_laurentCoeffAt_eq_zero_iff`), hence the normal-form
  repair is analytic (`MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`).
* `traceZk_one`/`traceZkForm_one`/`traceCoeff_one` — the `k = 1` (unramified) trivializations.
* `traceZkForm_fun_add`/`traceCoeff_fun_add`, `traceZkForm_const_mul`/`traceCoeff_const_mul` —
  `ℂ`-linearity in `h`, including at the repaired point `0` (by uniqueness of limits).
-/

open Filter Topology Set
open RS.FormTrace RS.MTrace

namespace RS

variable {h h' : ℂ → ℂ} {k : ℕ} {w : ℂ}

/-! ### `k = 1` trivializations -/

theorem MTrace.traceZk_one (h : ℂ → ℂ) (w : ℂ) : RS.MTrace.traceZk h 1 w = h w := by
  rw [RS.MTrace.traceZk_def]
  have hset : {z : ℂ | z ^ 1 = w} = {w} := by
    ext z; simp [pow_one]
  rw [hset, finsum_mem_singleton]

theorem FormTrace.traceZkForm_one (h : ℂ → ℂ) : traceZkForm h 1 = h := by
  funext w
  rw [traceZkForm_def, RS.MTrace.traceZk_one]
  norm_num

/-! ### Linearity of `traceZkForm` in `h` (valid at every `w`, including `0`) -/

theorem FormTrace.traceZkForm_fun_add (hk : k ≠ 0) :
    traceZkForm (fun v => h v + h' v) k
      = fun w => traceZkForm h k w + traceZkForm h' k w := by
  funext w
  simp only [traceZkForm_def]
  have heq : (fun v => (h v + h' v) * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹)
      = fun v => h v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹
        + h' v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹ := by
    funext v; ring
  rw [heq, RS.MTrace.traceZk_fun_add hk]

theorem FormTrace.traceZkForm_const_mul (c : ℂ) (k : ℕ) :
    traceZkForm (fun v => c * h v) k = fun w => c * traceZkForm h k w := by
  funext w
  simp only [traceZkForm_def]
  have heq : (fun v => (c * h v) * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹)
      = fun v => c * (h v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹) := by
    funext v; ring
  rw [heq, RS.MTrace.traceZk_const_mul]

/-! ### The repaired coefficient -/

/-- The repaired planar trace coefficient: `traceZkForm h k` with its removable singularity at
the branch coordinate `0` repaired via mathlib's meromorphic normal form. -/
noncomputable def traceCoeff (h : ℂ → ℂ) (k : ℕ) : ℂ → ℂ :=
  toMeromorphicNFAt (traceZkForm h k) 0

theorem meromorphicAt_traceZkForm_of_analyticAt (hh : AnalyticAt ℂ h 0) (hk : k ≠ 0) :
    MeromorphicAt (traceZkForm h k) 0 :=
  meromorphicAt_traceZkForm hh.meromorphicAt hk

/-- Off the branch coordinate, the repair is literal. -/
theorem traceCoeff_apply_of_ne_zero (hh : AnalyticAt ℂ h 0) (hk : k ≠ 0) (hw : w ≠ 0) :
    traceCoeff h k w = traceZkForm h k w :=
  ((meromorphicAt_traceZkForm_of_analyticAt hh hk).eqOn_compl_singleton_toMeromorphicNFAt
    (by simpa using hw)).symm

/-- `traceZkForm h k` has no negative Laurent coefficients at `0` when `h` is analytic there:
its meromorphic order is nonnegative (design §6.3, the Laurent route). -/
theorem meromorphicOrderAt_traceZkForm_nonneg (hh : AnalyticAt ℂ h 0) (hk : k ≠ 0) :
    0 ≤ meromorphicOrderAt (traceZkForm h k) 0 := by
  rw [← forall_neg_laurentCoeffAt_eq_zero_iff (meromorphicAt_traceZkForm_of_analyticAt hh hk)]
  intro j hj
  rw [laurentCoeffAt_traceZkForm hh.meromorphicAt hk j, laurentCoeffAt_of_analyticAt hh,
    ite_eq_right]
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hj1 : j ≤ -1 := by omega
  have hmul : (k : ℤ) * j ≤ (k : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left hj1 (by omega)
  omega

/-- **The branch-point analyticity of the repaired coefficient** (the previous builder's
blocker, resolved): once `h` is analytic at `0`, the repaired `traceCoeff h k` is honestly
analytic at the branch coordinate `0`. -/
theorem analyticAt_traceCoeff_zero (hh : AnalyticAt ℂ h 0) (hk : k ≠ 0) :
    AnalyticAt ℂ (traceCoeff h k) 0 := by
  have hmero := meromorphicAt_traceZkForm_of_analyticAt hh hk
  have hNF : MeromorphicNFAt (traceCoeff h k) 0 := meromorphicNFAt_toMeromorphicNFAt
  rw [← hNF.meromorphicOrderAt_nonneg_iff_analyticAt]
  unfold traceCoeff
  rw [meromorphicOrderAt_congr hmero.eq_nhdsNE_toMeromorphicNFAt.symm]
  exact meromorphicOrderAt_traceZkForm_nonneg hh hk

/-- Off-branch analyticity of the un-repaired `traceZkForm` (a re-packaging of
`RS.MTrace.analyticAt_traceZk` with the Jacobian factor divided in). -/
theorem analyticAt_traceZkForm_of_ne_zero {ρ : ℝ} (hρ : 0 < ρ) (hk : k ≠ 0)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 ρ)) (hw : w ≠ 0) (hwρ : ‖w‖ < ρ ^ k) :
    AnalyticAt ℂ (traceZkForm h k) w := by
  change AnalyticAt ℂ
    (RS.MTrace.traceZk (fun v => h v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹) k) w
  apply RS.MTrace.analyticAt_traceZk hk hρ ?_ hw hwρ
  rintro v ⟨hv1, hv2⟩
  have hv0 : v ≠ 0 := by simpa using hv2
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hzp : AnalyticAt ℂ (fun v : ℂ => v ^ ((k : ℤ) - 1)) v := by
    simpa using (analyticAt_id (𝕜 := ℂ) (z := v)).fun_zpow (n := (k : ℤ) - 1) hv0
  have hJ : AnalyticAt ℂ (fun v : ℂ => ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹) v := by
    apply AnalyticAt.inv (analyticAt_const.mul hzp)
    exact mul_ne_zero hkC (zpow_ne_zero _ hv0)
  exact (hh v hv1).mul hJ

/-- **The master repair lemma**: if `h` is analytic on `ball 0 ρ`, the repaired trace
coefficient `traceCoeff h k` is analytic on the whole ball `ball 0 (ρ ^ k)` — branch point
included. -/
theorem analyticOnNhd_traceCoeff {ρ : ℝ} (hρ : 0 < ρ) (hk : k ≠ 0)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 ρ)) :
    AnalyticOnNhd ℂ (traceCoeff h k) (Metric.ball 0 (ρ ^ k)) := by
  intro w hw
  have hh0 : AnalyticAt ℂ h 0 := hh 0 (Metric.mem_ball_self hρ)
  rcases eq_or_ne w 0 with rfl | hw0
  · exact analyticAt_traceCoeff_zero hh0 hk
  · have hA := analyticAt_traceZkForm_of_ne_zero hρ hk hh hw0 (mem_ball_zero_iff.mp hw)
    apply hA.congr
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (by simpa using hw0 : w ∈ ({(0 : ℂ)}ᶜ : Set ℂ))] with z hz
    exact (meromorphicAt_traceZkForm_of_analyticAt hh0 hk).eqOn_compl_singleton_toMeromorphicNFAt
      hz

/-- `k = 1`: the repair is literally `h` (no branching, nothing to repair). -/
theorem traceCoeff_one (hh : AnalyticAt ℂ h 0) : traceCoeff h 1 = h := by
  unfold traceCoeff
  rw [FormTrace.traceZkForm_one]
  exact toMeromorphicNFAt_eq_self.2 hh.meromorphicNFAt

/-! ### Linearity of the repaired coefficient -/

private theorem eq_at_zero_of_analyticAt_of_eventuallyEq {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (heq : f =ᶠ[𝓝[≠] (0 : ℂ)] g) :
    f 0 = g 0 :=
  tendsto_nhds_unique_of_eventuallyEq
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) heq

theorem traceCoeff_fun_add (hk : k ≠ 0) (hh : AnalyticAt ℂ h 0) (hh' : AnalyticAt ℂ h' 0) :
    traceCoeff (fun v => h v + h' v) k
      = fun w => traceCoeff h k w + traceCoeff h' k w := by
  have hsum : AnalyticAt ℂ (fun v => h v + h' v) 0 := hh.fun_add hh'
  have hne : ∀ z : ℂ, z ≠ 0 → traceCoeff (fun v => h v + h' v) k z
      = traceCoeff h k z + traceCoeff h' k z := by
    intro z hz0
    rw [traceCoeff_apply_of_ne_zero hsum hk hz0, traceCoeff_apply_of_ne_zero hh hk hz0,
      traceCoeff_apply_of_ne_zero hh' hk hz0, FormTrace.traceZkForm_fun_add hk]
  funext w
  rcases eq_or_ne w 0 with rfl | hw0
  · apply eq_at_zero_of_analyticAt_of_eventuallyEq (analyticAt_traceCoeff_zero hsum hk)
      ((analyticAt_traceCoeff_zero hh hk).fun_add (analyticAt_traceCoeff_zero hh' hk))
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hne z hz
  · exact hne w hw0

theorem traceCoeff_const_mul (hk : k ≠ 0) (hh : AnalyticAt ℂ h 0) (c : ℂ) :
    traceCoeff (fun v => c * h v) k = fun w => c * traceCoeff h k w := by
  have hcm : AnalyticAt ℂ (fun v => c * h v) 0 := analyticAt_const.fun_mul hh
  have hne : ∀ z : ℂ, z ≠ 0 → traceCoeff (fun v => c * h v) k z
      = c * traceCoeff h k z := by
    intro z hz0
    rw [traceCoeff_apply_of_ne_zero hcm hk hz0, traceCoeff_apply_of_ne_zero hh hk hz0,
      FormTrace.traceZkForm_const_mul]
  funext w
  rcases eq_or_ne w 0 with rfl | hw0
  · apply eq_at_zero_of_analyticAt_of_eventuallyEq (analyticAt_traceCoeff_zero hcm hk)
      (analyticAt_const.fun_mul (analyticAt_traceCoeff_zero hh hk))
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hne z hz
  · exact hne w hw0

end RS
