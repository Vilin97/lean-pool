/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Estimate
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Time cutoff reducing the open half-line energy setup to `ForcedSetup`

The forced energy estimate (`Energy/*`) is stated for a comparison function `v` that is jointly
`C²` on the closed half-line `[0,∞) × ℝ²`.  For the ansatz `θTilde_m` this fails at `t = 0`.  Here
    `v`
is only jointly `C²` on `(0,∞) × ℝ²`.  For `s > 0`, multiplying `v` by a smooth time cutoff that
vanishes on `t ≤ s/3` and equals `1` on `t ≥ s/2` gives a function `cutoffV s v` satisfying all
the hypotheses of `ForcedSetup` and agreeing with `v` on `[s/2, ∞)`; every pointwise-in-time
statement of the `Energy` development at times `≥ s` then transfers to `v`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.EnergyIoi

open AVenhance AVenhance.Infra.Section5.Integration.Energy

/-- Standing hypotheses of the open half-line forced energy estimate. -/
structure IoiSetup (φ : ℝ → Vec 2 → ℝ) (κ : ℝ) (θ₀ : Vec 2 → ℝ) (u v : ℝ → Vec 2 → ℝ) :
    Prop where
  hφ : IsAdmissibleStream φ
  hκ : 0 < κ
  hu : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) θ₀ u
  hv : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => v p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
  hvs : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (v t)
  hvp : ∀ t, 0 < t → IsZ2Periodic (v t)

/-- The time cutoff: `0` on `t ≤ s/3`, `1` on `t ≥ s/2`. -/
def cutoffTime (s t : ℝ) : ℝ := Real.smoothTransition ((t - s / 3) * (6 / s))

/-- The cut-off comparison function. -/
def cutoffV (s : ℝ) (v : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ := fun t x => cutoffTime s t * v t x

theorem cutoffTime_eq_one {s t : ℝ} (hs : 0 < s) (ht : s / 2 ≤ t) : cutoffTime s t = 1 := by
  unfold cutoffTime
  apply Real.smoothTransition.one_of_one_le
  have h6 : (0 : ℝ) ≤ 6 / s := by positivity
  calc (1 : ℝ) = (s / 6) * (6 / s) := by field_simp
    _ ≤ (t - s / 3) * (6 / s) := mul_le_mul_of_nonneg_right (by linarith) h6

theorem cutoffTime_eq_zero {s t : ℝ} (hs : 0 < s) (ht : t ≤ s / 3) : cutoffTime s t = 0 := by
  unfold cutoffTime
  apply Real.smoothTransition.zero_of_nonpos
  have h6 : (0 : ℝ) ≤ 6 / s := by positivity
  exact mul_nonpos_iff.2 (Or.inr ⟨by linarith, h6⟩)

theorem cutoffTime_contDiff (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoffTime s) := by
  unfold cutoffTime
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).mul contDiff_const)

/-- The cut-off function agrees with `v` on `[s/2, ∞)`, as a function of space. -/
theorem cutoffV_slice_eq {s : ℝ} (hs : 0 < s) (v : ℝ → Vec 2 → ℝ) {t : ℝ} (ht : s / 2 ≤ t) :
    cutoffV s v t = v t := by
  funext x
  simp [cutoffV, cutoffTime_eq_one hs ht]

theorem cutoffV_slice_zero {s : ℝ} (hs : 0 < s) (v : ℝ → Vec 2 → ℝ) {t : ℝ} (ht : t ≤ 0) :
    cutoffV s v t = fun _ => 0 := by
  funext x
  simp [cutoffV, cutoffTime_eq_zero hs (by linarith : t ≤ s / 3)]

theorem cutoffV_contDiff {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}
    (S : IoiSetup φ κ θ₀ u v) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 2 (fun p : ℝ × Vec 2 => cutoffV s v p.1 p.2) := by
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  by_cases hp : 0 < p.1
  · have hχ : ContDiffAt ℝ 2 (fun q : ℝ × Vec 2 => cutoffTime s q.1) p :=
      (((cutoffTime_contDiff s).of_le (WithTop.coe_le_coe.2 le_top)).comp contDiff_fst).contDiffAt
    have hmem : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ∈ 𝓝 p :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩
    exact hχ.mul (S.hv.contDiffAt hmem)
  · have hlt : p.1 < s / 3 := by linarith [not_lt.1 hp]
    have hev : ∀ᶠ q in 𝓝 p, q.1 < s / 3 :=
      (continuous_fst.tendsto p).eventually (eventually_lt_nhds hlt)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    simp [cutoffV, cutoffTime_eq_zero hs hq.le]

/-- The cut-off function satisfies the hypotheses of the closed half-line energy estimate. -/
theorem IoiSetup.cutoff {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}
    (S : IoiSetup φ κ θ₀ u v) {s : ℝ} (hs : 0 < s) :
    ForcedSetup φ κ θ₀ u (cutoffV s v) where
  hφ := S.hφ
  hκ := S.hκ
  hu := S.hu
  hv := (cutoffV_contDiff S hs).contDiffOn
  hvs t ht := by
    rcases lt_or_ge 0 t with hpos | hneg
    · exact (contDiff_const.mul (S.hvs t hpos) :
        ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffTime s t * v t x))
    · rw [cutoffV_slice_zero hs v hneg]
      exact contDiff_const
  hvp t ht := by
    rcases lt_or_ge 0 t with hpos | hneg
    · intro n x
      change cutoffTime s t * v t (x + latticeShift n) = cutoffTime s t * v t x
      rw [S.hvp t hpos n x]
    · rw [cutoffV_slice_zero hs v hneg]
      intro n x
      rfl

/-- The defect of the cut-off function agrees with that of `v` for `t > s/2`. -/
theorem advDiffOp_cutoffV (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) {s : ℝ} (hs : 0 < s)
    (v : ℝ → Vec 2 → ℝ) {r : ℝ} (hr : s / 2 < r) (x : Vec 2) :
    advDiffOp b κ (cutoffV s v) r x = advDiffOp b κ v r x := by
  have hev : (fun r' => cutoffV s v r' x) =ᶠ[𝓝 r] fun r' => v r' x := by
    filter_upwards [Ioi_mem_nhds hr] with r' hr'
    rw [cutoffV_slice_eq hs v (le_of_lt hr')]
  unfold advDiffOp
  rw [hev.deriv_eq, cutoffV_slice_eq hs v hr.le]

theorem advDiffOp_cutoffV_slice (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) {s : ℝ} (hs : 0 < s)
    (v : ℝ → Vec 2 → ℝ) {r : ℝ} (hr : s / 2 < r) :
    advDiffOp b κ (cutoffV s v) r = advDiffOp b κ v r :=
  funext (advDiffOp_cutoffV b κ hs v hr)

/-- The slice gradient energy of the cut-off function agrees with that of `v` for `t ≥ s/2`. -/
theorem errGrad_cutoffV (u : ℝ → Vec 2 → ℝ) {s : ℝ} (hs : 0 < s) (v : ℝ → Vec 2 → ℝ) {r : ℝ}
    (hr : s / 2 ≤ r) : errGrad u (cutoffV s v) r = errGrad u v r := by
  unfold errGrad
  rw [cutoffV_slice_eq hs v hr]

/-- The defect of `v` is jointly continuous on `(0,∞) × ℝ²`. -/
theorem IoiSetup.forcing_continuousOn {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {u v : ℝ → Vec 2 → ℝ} (S : IoiSetup φ κ θ₀ u v) :
    ContinuousOn (fun p : ℝ × Vec 2 => advDiffOp (streamVel φ) κ v p.1 p.2)
      classicalPositiveTimeDomain := by
  refine continuousOn_of_forall_continuousAt fun p hp => ?_
  have hp0 : 0 < p.1 := hp.1
  have hcont := (S.cutoff hp0).forcing_continuousOn.continuousAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  refine hcont.congr ?_
  have hev : ∀ᶠ q in 𝓝 p, p.1 / 2 < q.1 :=
    (continuous_fst.tendsto p).eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hev] with q hq
  exact advDiffOp_cutoffV (streamVel φ) κ hp0 v hq q.2

end AVenhance.Infra.Section5.Integration.EnergyIoi

end
