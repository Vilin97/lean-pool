/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMKCorrector

/-! # Generic tools for the joint continuity of the pointwise §5.1 terms

Everything is stated on the open half space `tcU = (0,∞) × ℝ²`.

* `tc_contDiffOn_tsum`: a locally finite `tsum` of `C^n` functions is `C^n`;
* `tc_odd_contDiffOn_tsum`: the same for the `{k // Odd k}` sums weighted by `ξ_{m,k}` (or its
  time derivative), using `exists_active_finset`;
* `tc_spaceGrad_contDiffOn`: the spatial gradient of a jointly `C^{n+1}` field is jointly `C^n`;
* divergence, `gradDiv`, `matDiv` and composition with the inverse flow of jointly smooth fields. -/

@[expose] public section

noncomputable section

open Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

/-- The open half space `(0,∞) × ℝ²`. -/
abbrev tcU : Set (ℝ × Vec 2) := Set.Ioi (0 : ℝ) ×ˢ Set.univ

theorem tcU_isOpen : IsOpen tcU := isOpen_Ioi.prod isOpen_univ

theorem tcU_uniqueDiffOn : UniqueDiffOn ℝ tcU := tcU_isOpen.uniqueDiffOn

/-! ### Locally finite sums -/

/-- A locally finite sum of `C^n` functions on a set is `C^n` there. -/
theorem tc_contDiffOn_tsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {s : Set E} {g : ι → E → F}
    (hg : ∀ i, ContDiffOn ℝ n (g i) s)
    (hloc : ∀ x ∈ s, ∃ S : Finset ι, ∀ᶠ y in 𝓝 x, ∀ i, i ∉ S → g i y = 0) :
    ContDiffOn ℝ n (fun y => ∑' i, g i y) s := by
  classical
  intro x hx
  obtain ⟨S, hS⟩ := hloc x hx
  have heq : (fun y => ∑' i, g i y) =ᶠ[𝓝 x] fun y => ∑ i ∈ S, g i y := by
    filter_upwards [hS] with y hy using tsum_eq_sum (fun i hi => hy i hi)
  have h : ContDiffWithinAt ℝ n (fun y => ∑ i ∈ S, g i y) s x :=
    (ContDiffOn.sum (fun i _ => hg i)) x hx
  exact h.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds

variable {β : ℝ} (I : Ingredients β)

/-- Odd cutoff sums.  The summand `g k` vanishes at `(t, x)` as soon as `ξ_{m,k}` vanishes
identically near `t`. -/
theorem tc_odd_contDiffOn_tsum (m : ℕ) {n : WithTop ℕ∞} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : {k : ℤ // Odd k} → ℝ × Vec 2 → F}
    (hg : ∀ k, ContDiffOn ℝ n (g k) tcU)
    (hz : ∀ k : {k : ℤ // Odd k}, ∀ t : ℝ, (∀ᶠ s in 𝓝 t, I.xiMK m k.1 s = 0) →
      ∀ x : Vec 2, g k (t, x) = 0) :
    ContDiffOn ℝ n (fun p => ∑' k, g k p) tcU := by
  classical
  refine tc_contDiffOn_tsum hg fun p _ => ?_
  obtain ⟨S, hS⟩ := Integration.exists_active_finset I m p.1
  refine ⟨S.subtype Odd, ?_⟩
  have hopen : IsOpen {q : ℝ × Vec 2 | |q.1 - p.1| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds (show |p.1 - p.1| < 1 by simp)] with q hq k hk
  have hkS : k.1 ∉ S := fun h => hk (Finset.mem_subtype.mpr h)
  have hev : ∀ᶠ s in 𝓝 q.1, I.xiMK m k.1 s = 0 := by
    have hopen' : IsOpen {s : ℝ | |s - p.1| < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen'.mem_nhds hq] with s hs using hS k.1 hkS s hs
  exact hz k q.1 hev q.2

/-- Continuity version of `tc_odd_contDiffOn_tsum`. -/
theorem tc_odd_continuousOn_tsum (m : ℕ) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : {k : ℤ // Odd k} → ℝ × Vec 2 → F}
    (hg : ∀ k, ContinuousOn (g k) tcU)
    (hz : ∀ k : {k : ℤ // Odd k}, ∀ t : ℝ, (∀ᶠ s in 𝓝 t, I.xiMK m k.1 s = 0) →
      ∀ x : Vec 2, g k (t, x) = 0) :
    ContinuousOn (fun p => ∑' k, g k p) tcU :=
  (tc_odd_contDiffOn_tsum I m (n := 0) (fun k => contDiffOn_zero.mpr (hg k)) hz).continuousOn

/-- If `ξ_{m,k}` vanishes near `t`, so does its derivative at `t`. -/
theorem tc_deriv_xiMK_eq_zero (m : ℕ) (k : ℤ) {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, I.xiMK m k s = 0) : deriv (I.xiMK m k) t = 0 := by
  have : I.xiMK m k =ᶠ[𝓝 t] fun _ => (0 : ℝ) := h
  rw [this.deriv_eq]
  simp

/-! ### Spatial gradients and divergences -/

/-- The spatial gradient of a jointly `C^n` field on the open half space is jointly `C^m`
for `m + 1 ≤ n`. -/
theorem tc_spaceGrad_contDiffOn {F : ℝ → Vec 2 → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hF : ContDiffOn ℝ n (fun p : ℝ × Vec 2 => F p.1 p.2) tcU) (j : Fin 2) :
    ContDiffOn ℝ m (fun p : ℝ × Vec 2 => spaceGrad (F p.1) p.2 j) tcU := by
  have h1 : ContDiffOn ℝ m
      (fun p : ℝ × Vec 2 =>
        fderivWithin ℝ (fun q : ℝ × Vec 2 => F q.1 q.2) tcU p (0, basisVec j)) tcU :=
    (hF.fderivWithin tcU_uniqueDiffOn hmn).clm_apply contDiffOn_const
  refine h1.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact Section5.RelativeError.spaceGrad_slice_eq_fderivWithin
    (F := fun q : ℝ × Vec 2 => F q.1 q.2) (s := tcU) t x
    (fun y => ⟨ht, trivial⟩) (hF.differentiableOn (zero_lt_one.trans_le (le_add_self.trans
        hmn)).ne' (t, x) ⟨ht, trivial⟩) j

/-- The divergence of a jointly `C^n` field is jointly `C^m` for `m + 1 ≤ n`. -/
theorem tc_vecDiv_contDiffOn {V : ℝ → Vec 2 → Vec 2} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hV : ∀ i, ContDiffOn ℝ n (fun p : ℝ × Vec 2 => V p.1 p.2 i) tcU) :
    ContDiffOn ℝ m (fun p : ℝ × Vec 2 => vecDiv (V p.1) p.2) tcU := by
  unfold vecDiv
  exact ContDiffOn.sum fun i _ => tc_spaceGrad_contDiffOn (F := fun t y => V t y i) hmn (hV i) i

/-- The gradient of the divergence of a jointly `C^n` field is jointly `C^m` for `m + 2 ≤ n`. -/
theorem tc_gradDiv_contDiffOn {V : ℝ → Vec 2 → Vec 2} {m n : WithTop ℕ∞}
    (hmn : m + 1 + 1 ≤ n)
    (hV : ∀ i, ContDiffOn ℝ n (fun p : ℝ × Vec 2 => V p.1 p.2 i) tcU) (j : Fin 2) :
    ContDiffOn ℝ m (fun p : ℝ × Vec 2 => gradDiv V p.1 p.2 j) tcU :=
  tc_spaceGrad_contDiffOn (F := fun t y => vecDiv (V t) y) le_rfl
    (tc_vecDiv_contDiffOn (m := m + 1) hmn hV) j

/-- Composition with the (jointly smooth) inverse flow preserves joint regularity on the open
half space, up to order `∞`. -/
theorem tc_comp_xFlowInv {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ)
    {n : WithTop ℕ∞} (hn : n ≤ ∞) {f : ℝ → Vec 2 → ℝ}
    (hf : ContDiffOn ℝ n (fun p : ℝ × Vec 2 => f p.1 p.2) tcU) :
    ContDiffOn ℝ n (fun p : ℝ × Vec 2 => f p.1 (I.xFlowInv hΦ m l p.1 p.2)) tcU := by
  have hΨ : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, I.xFlowInv hΦ m l p.1 p.2)) :=
    contDiff_fst.prodMk (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m l)
  exact hf.comp (hΨ.of_le hn).contDiffOn (fun p hp => ⟨hp.1, trivial⟩)

end AVenhance.Infra.Section5.Contracts
