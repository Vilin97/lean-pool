/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Abel.LogPiece
import LeanPool.JacobianDiffgeo.Abel.ChartSupported
import LeanPool.JacobianDiffgeo.Abel.SerreFunctional
import LeanPool.JacobianDiffgeo.AbelWeak.WeakSolution

/-!
# abel-theorem: the per-link construction (design §4.1 steps 5-7, link layer)

Unit: abel-theorem. Namespace `RS.Abel`.

`exists_link` lifts one planar `LogPieceData` into a chart of the surface: given two points
`A` (pole) and `B` (zero) inside a common chart ball — exactly what one `ChartChain` link
supplies — it produces the piece function `f : X → ℂ` (the `SingleChart.lean` recipe:
`g ∘ e` on the chart source, `1` outside) TOGETHER with its packaged global `(0,1)`-form
`η = dbar log f` (via `ChartSupportedData.form`) and the five facts the assembly
(`UpgradeDischarge.lean`) needs:

1. real-smoothness off the pole;
2. non-vanishing off the divisor;
3. the `dbar log`-matching `dbar(f ∘ chart⁻¹) = η-coefficient · f` at every preferred-chart center
   off the divisor;
4. the punctured-limit factorization `f(z)·(z - z₀)^(-linkOrd) → C ≠ 0` at EVERY point (the
   `Rechart`-free order bookkeeping input);
5. the pairing identity `∫∫ η ∧ θ = π (Gp(eB) - Gp(eA))` for any chart primitive `Gp` of `θ`
   (`pairing_form` + `integral_dlog_mul`).

Also here: the planar promotion lemma `meromorphicAt_of_tendsto_factor` (punctured holomorphy
plus a factor limit pin `meromorphicOrderAt`, via mathlib's removable-singularity theorem and
`tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`) and the `dbar` finite product rule
`wirtingerDbar_finset_prod`.
-/

open scoped ContDiff Manifold
open IsManifold Metric Set MeasureTheory Filter Topology


noncomputable section

namespace RS.Abel

/-! ## The planar promotion lemma -/

/-- **Promotion**: punctured holomorphy near `z₀` plus the factor limit
`F(z)(z-z₀)^{-m} → C ≠ 0` force `F` meromorphic at `z₀` of order exactly `m`. -/
theorem meromorphicAt_of_tendsto_factor {F : ℂ → ℂ} {z₀ C : ℂ} {m : ℤ} {V : Set ℂ}
    (hV : V ∈ nhds z₀) (hF : DifferentiableOn ℂ F (V \ {z₀})) (hC : C ≠ 0)
    (h : Tendsto (fun z => F z * (z - z₀) ^ (-m)) (nhdsWithin z₀ {z₀}ᶜ) (nhds C)) :
    MeromorphicAt F z₀ ∧ meromorphicOrderAt F z₀ = m := by
  obtain ⟨U, hUV, hUopen, hz₀U⟩ := _root_.mem_nhds_iff.mp hV
  have hFU : ∀ z ∈ U \ {z₀}, DifferentiableAt ℂ F z := by
    intro z hz
    exact (hF.mono (Set.sdiff_subset_sdiff_left hUV)).differentiableAt
      ((hUopen.sdiff isClosed_singleton).mem_nhds hz)
  set G : ℂ → ℂ := Function.update (fun z => F z * (z - z₀) ^ (-m)) z₀ C with hG_def
  have hGoff : ∀ z, z ≠ z₀ → G z = F z * (z - z₀) ^ (-m) := fun z hz =>
    Function.update_of_ne hz _ _
  have hGtendsto : Tendsto G (nhdsWithin z₀ {z₀}ᶜ) (nhds C) := by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hGoff z (by simpa using hz)).symm
  have hGval : G z₀ = C := by
    rw [hG_def]
    exact Function.update_self _ _ _
  have hGcont : ContinuousAt G z₀ := by
    have hpure : Tendsto G (pure z₀) (nhds C) := by
      rw [← hGval]
      exact tendsto_pure_nhds G z₀
    rw [ContinuousAt, hGval, ← nhdsNE_sup_pure z₀]
    exact tendsto_sup.mpr ⟨hGtendsto, hpure⟩
  have hGdiffAt : ∀ z ∈ U \ {z₀}, DifferentiableAt ℂ G z := by
    intro z hz
    have hzz : z ≠ z₀ := by simpa using hz.2
    have hd : DifferentiableAt ℂ (fun w => F w * (w - z₀) ^ (-m)) z :=
      (hFU z hz).mul (DifferentiableAt.zpow
        (differentiableAt_id.sub (differentiableAt_const _))
        (Or.inl (sub_ne_zero.mpr hzz)))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hzz] with w hw
    exact hGoff w hw
  have hGdiffOn : DifferentiableOn ℂ G U :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (hUopen.mem_nhds hz₀U)).mp
      ⟨fun z hz => (hGdiffAt z hz).differentiableWithinAt, hGcont⟩
  have hGan : AnalyticAt ℂ G z₀ := hGdiffOn.analyticAt (hUopen.mem_nhds hz₀U)
  have hzpow : MeromorphicAt (fun z : ℂ => (z - z₀) ^ m) z₀ :=
    ((MeromorphicAt.id z₀).sub (MeromorphicAt.const z₀ z₀)).zpow m
  have hev : F =ᶠ[nhdsWithin z₀ {z₀}ᶜ] fun z => G z * (z - z₀) ^ m := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzz : z ≠ z₀ := by simpa using hz
    rw [hGoff z hzz, mul_assoc, ← zpow_add₀ (sub_ne_zero.mpr hzz), neg_add_cancel,
      zpow_zero, mul_one]
  have hmul : MeromorphicAt (fun z => G z * (z - z₀) ^ m) z₀ :=
    hGan.meromorphicAt.mul hzpow
  have hmero : MeromorphicAt F z₀ := hmul.congr hev.symm
  refine ⟨hmero, ?_⟩
  rw [meromorphicOrderAt_congr hev]
  have hmul_ord := meromorphicOrderAt_mul hGan.meromorphicAt hzpow
  rw [show (fun z => G z * (z - z₀) ^ m) = G * fun z : ℂ => (z - z₀) ^ m from rfl, hmul_ord]
  have hordG : meromorphicOrderAt G z₀ = 0 := by
    rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hGan.meromorphicAt]
    exact ⟨C, hC, hGtendsto⟩
  have hzo : meromorphicOrderAt (fun z : ℂ => (z - z₀) ^ m) z₀ = (m : WithTop ℤ) := by
    rw [show (fun z : ℂ => (z - z₀) ^ m) = (fun z : ℂ => z - z₀) ^ m from rfl]
    exact meromorphicOrderAt_zpow_id_sub_const
  rw [hordG, hzo, zero_add]

/-! ## The `dbar` finite product rule -/

theorem differentiableAt_finset_prod {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    DifferentiableAt ℝ (fun w => ∏ i ∈ s, f i w) z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hshape : (fun w => ∏ i ∈ Finset.cons a s ha, f i w)
          = fun w => f a w * ∏ i ∈ s, f i w := by
        funext w
        rw [Finset.prod_cons]
      rw [hshape]
      exact (hf a (Finset.mem_cons_self a s)).mul
        (ih (fun i hi => hf i (Finset.mem_cons_of_mem hi)))

theorem wirtingerDbar_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : ι → ℂ → ℂ} {z : ℂ} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    RS.wirtingerDbar (fun w => ∏ i ∈ s, f i w) z
      = ∑ i ∈ s, RS.wirtingerDbar (f i) z * ∏ j ∈ s.erase i, f j z := by
  induction s using Finset.induction_on with
  | empty => simpa using RS.wirtingerDbar_const z 1
  | insert a s ha ih =>
      have hfa : DifferentiableAt ℝ (f a) z := hf a (Finset.mem_insert_self a s)
      have hfs : DifferentiableAt ℝ (fun w => ∏ i ∈ s, f i w) z :=
        differentiableAt_finset_prod s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hshape : (fun w => ∏ i ∈ insert a s, f i w)
          = fun w => f a w * ∏ i ∈ s, f i w := by
        funext w
        rw [Finset.prod_insert ha]
      rw [hshape, RS.wirtingerDbar_mul hfa hfs,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha,
        Finset.erase_insert ha, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hne : i ≠ a := fun heq => ha (heq ▸ hi)
      rw [Finset.erase_insert_of_ne (Ne.symm hne), Finset.prod_insert
        (fun hmem => ha (Finset.mem_of_mem_erase hmem))]
      ring

/-! ## The link order and the per-link construction -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The contribution of the link `(A ↦ pole, B ↦ zero)` to the order at `x`. -/
def linkOrd [DecidableEq X] (A B x : X) : ℤ :=
  (if x = B then 1 else 0) - (if x = A then 1 else 0)

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    in
theorem linkOrd_self_eq_zero [DecidableEq X] (A x : X) : linkOrd A A x = 0 := by
  rw [linkOrd, sub_self]

omit [CompactSpace X] [T2Space X] in
/-- Every point has a nonzero limit for `f` divided out by its `linkOrd` factor: the local
factorization behind `exists_link`'s fourth component. Split out to keep that proof under the
200-line size we hold ourselves to. -/
private theorem exists_linkOrd_factor [DecidableEq X] {A B : X} (hAB : A ≠ B)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    (hA : A ∈ e.source) (hB : B ∈ e.source) {P : LogPieceData}
    (hPα : P.α = e A) (hPβ : P.β = e B) (hαβ : P.α ≠ P.β) {f : X → ℂ}
    (hf_source : ∀ x ∈ e.source, f x = P.g (e x))
    (hlocal_out : ∀ {x : X}, x ∉ e.source →
      (f ∘ ⇑(chartAt ℂ x).symm) =ᶠ[nhds (chartAt ℂ x x)] (fun _ => (1 : ℂ))) :
    ∀ x : X, ∃ C : ℂ, C ≠ 0 ∧ Tendsto
      (fun z => f ((chartAt ℂ x).symm z) * (z - chartAt ℂ x x) ^ (-(linkOrd A B x)))
      (nhdsWithin (chartAt ℂ x x) {chartAt ℂ x x}ᶜ) (nhds C) := by
  intro x
  by_cases hxe : x ∈ e.source
  · set z₀ : ℂ := chartAt ℂ x x with hz₀_def
    set τ : ℂ → ℂ := ⇑e ∘ ⇑(chartAt ℂ x).symm with hτ_def
    have hz₀mem : z₀ ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ e.source) :=
      ⟨x, ⟨mem_chart_source ℂ x, hxe⟩, rfl⟩
    have hSopen : IsOpen (⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ e.source)) :=
      (chartAt ℂ x).isOpen_image_of_subset_source
        ((chartAt ℂ x).open_source.inter e.open_source) inter_subset_left
    have hτz₀ : τ z₀ = e x := by
      rw [hτ_def, hz₀_def]
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    have hτan : AnalyticAt ℂ τ z₀ :=
      RS.analyticAt_trans he (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
        (by rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hxe)
    have hτderiv : HasDerivAt τ (deriv τ z₀) z₀ :=
      hτan.differentiableAt.hasDerivAt
    have hz₀mem' : z₀ ∈ ⇑(chartAt ℂ x) '' (e.source ∩ (chartAt ℂ x).source) :=
      ⟨x, ⟨hxe, mem_chart_source ℂ x⟩, rfl⟩
    have hτderiv_ne : deriv τ z₀ ≠ 0 :=
      deriv_trans_ne_zero he (IsManifold.chart_mem_maximalAtlas x) hz₀mem'
    -- τ maps the punctured filter into the punctured filter at `e x`
    have hτpunct : Tendsto τ (nhdsWithin z₀ {z₀}ᶜ)
        (nhdsWithin (e x) {e x}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hcont : Tendsto τ (nhds z₀) (nhds (τ z₀)) := hτan.continuousAt
        rw [hτz₀] at hcont
        exact hcont.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (hSopen.mem_nhds hz₀mem)] with z hz1 hz2
        obtain ⟨q, hq, rfl⟩ := hz2
        have hq1 : (chartAt ℂ x).symm (chartAt ℂ x q) = q :=
          (chartAt ℂ x).left_inv hq.1
        have hτq : τ (chartAt ℂ x q) = e q := by
          rw [hτ_def]
          simp only [Function.comp_apply, hq1]
        intro heq
        rw [Set.mem_singleton_iff, hτq] at heq
        have hqx : q = x := e.injOn hq.2 hxe heq
        apply hz1
        rw [Set.mem_singleton_iff, hz₀_def, hqx]
    -- slope limit
    have hslope : Tendsto (fun z => (τ z - τ z₀) * (z - z₀)⁻¹)
        (nhdsWithin z₀ {z₀}ᶜ) (nhds (deriv τ z₀)) := by
      have hts := hasDerivAt_iff_tendsto_slope.mp hτderiv
      refine hts.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzz : z ≠ z₀ := by simpa using hz
      have h1 : z₀ - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzz)
      have h2 : z - z₀ ≠ 0 := sub_ne_zero.mpr hzz
      rw [slope_def_field]
      field_simp
    rcases eq_or_ne x B with rfl | hxB
    · -- the zero: `linkOrd = 1`
      have hxA : x ≠ A := fun heq => hAB heq.symm
      have hord : linkOrd A x x = 1 := by
        rw [linkOrd, if_pos rfl, if_neg hxA, sub_zero]
      refine ⟨(P.β - P.α)⁻¹ * deriv τ z₀, mul_ne_zero (inv_ne_zero
        (sub_ne_zero.mpr (Ne.symm hαβ))) hτderiv_ne, ?_⟩
      have hzero := P.tendsto_zero_factor
      have hβval : P.β = e x := hPβ
      have hcomp : Tendsto (fun z => P.g (τ z) * (τ z - P.β)⁻¹)
          (nhdsWithin z₀ {z₀}ᶜ) (nhds ((P.β - P.α)⁻¹)) := by
        refine hzero.comp ?_
        rw [hβval]
        exact hτpunct
      have hmain : Tendsto (fun z => (P.g (τ z) * (τ z - P.β)⁻¹) *
          ((τ z - τ z₀) * (z - z₀)⁻¹))
          (nhdsWithin z₀ {z₀}ᶜ) (nhds ((P.β - P.α)⁻¹ * deriv τ z₀)) :=
        hcomp.mul hslope
      refine hmain.congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hSopen.mem_nhds hz₀mem),
        hτpunct.eventually self_mem_nhdsWithin] with z hz1 hz2 hz3
      have hτβ : τ z - P.β ≠ 0 := by
        rw [hβval]
        exact sub_ne_zero.mpr (by simpa using hz3)
      obtain ⟨q, hq, rfl⟩ := hz2
      have hq1 : (chartAt ℂ x).symm (chartAt ℂ x q) = q :=
        (chartAt ℂ x).left_inv hq.1
      rw [hord]
      change P.g (τ (chartAt ℂ x q)) * (τ (chartAt ℂ x q) - P.β)⁻¹ *
          ((τ (chartAt ℂ x q) - τ z₀) * (chartAt ℂ x q - z₀)⁻¹)
        = f ((chartAt ℂ x).symm (chartAt ℂ x q)) *
          (chartAt ℂ x q - z₀) ^ (-(1 : ℤ))
      have hfq : f ((chartAt ℂ x).symm (chartAt ℂ x q)) = P.g (τ (chartAt ℂ x q)) := by
        rw [hq1, hf_source q hq.2, hτ_def]
        simp only [Function.comp_apply, hq1]
      rw [hfq, zpow_neg_one, show τ z₀ = P.β from hτz₀.trans hβval.symm]
      rw [mul_assoc, ← mul_assoc ((τ (chartAt ℂ x q) - P.β)⁻¹),
        inv_mul_cancel₀ hτβ, one_mul]
    · rcases eq_or_ne x A with rfl | hxA
      · -- the pole: `linkOrd = -1`
        have hord : linkOrd x B x = -1 := by
          rw [linkOrd, if_neg hAB, if_pos rfl, zero_sub]
        have hslope_inv : Tendsto (fun z => (z - z₀) * (τ z - τ z₀)⁻¹)
            (nhdsWithin z₀ {z₀}ᶜ) (nhds ((deriv τ z₀)⁻¹)) := by
          have h1 := hslope.inv₀ hτderiv_ne
          refine h1.congr' ?_
          filter_upwards [self_mem_nhdsWithin,
            hτpunct.eventually self_mem_nhdsWithin] with z hz1 hz3
          have hzz : z - z₀ ≠ 0 := sub_ne_zero.mpr (by simpa using hz1)
          have hττ : τ z - τ z₀ ≠ 0 := by
            rw [hτz₀]
            exact sub_ne_zero.mpr (by simpa [hτz₀] using hz3)
          simp only [mul_inv, inv_inv]
          exact mul_comm _ _
        refine ⟨(P.α - P.β) * (deriv τ z₀)⁻¹, mul_ne_zero
          (sub_ne_zero.mpr hαβ) (inv_ne_zero hτderiv_ne), ?_⟩
        have hpole := P.tendsto_pole_factor
        have hαval : P.α = e x := hPα
        have hcomp : Tendsto (fun z => P.g (τ z) * (τ z - P.α))
            (nhdsWithin z₀ {z₀}ᶜ) (nhds (P.α - P.β)) := by
          refine hpole.comp ?_
          rw [hαval]
          exact hτpunct
        have hmain : Tendsto (fun z => (P.g (τ z) * (τ z - P.α)) *
            ((z - z₀) * (τ z - τ z₀)⁻¹))
            (nhdsWithin z₀ {z₀}ᶜ) (nhds ((P.α - P.β) * (deriv τ z₀)⁻¹)) :=
          hcomp.mul hslope_inv
        refine hmain.congr' ?_
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (hSopen.mem_nhds hz₀mem),
          hτpunct.eventually self_mem_nhdsWithin] with z hz1 hz2 hz3
        have hτα : τ z - P.α ≠ 0 := by
          rw [hαval]
          exact sub_ne_zero.mpr (by simpa using hz3)
        obtain ⟨q, hq, rfl⟩ := hz2
        have hq1 : (chartAt ℂ x).symm (chartAt ℂ x q) = q :=
          (chartAt ℂ x).left_inv hq.1
        rw [hord]
        change P.g (τ (chartAt ℂ x q)) * (τ (chartAt ℂ x q) - P.α) *
            ((chartAt ℂ x q - z₀) * (τ (chartAt ℂ x q) - τ z₀)⁻¹)
          = f ((chartAt ℂ x).symm (chartAt ℂ x q)) *
            (chartAt ℂ x q - z₀) ^ (-(-1 : ℤ))
        have hfq : f ((chartAt ℂ x).symm (chartAt ℂ x q))
            = P.g (τ (chartAt ℂ x q)) := by
          rw [hq1, hf_source q hq.2, hτ_def]
          simp only [Function.comp_apply, hq1]
        rw [hfq, neg_neg, zpow_one, show τ z₀ = P.α from hτz₀.trans hαval.symm]
        rw [mul_assoc, mul_comm (chartAt ℂ x q - z₀) ((τ (chartAt ℂ x q) - P.α)⁻¹),
          ← mul_assoc (τ (chartAt ℂ x q) - P.α), mul_inv_cancel₀ hτα, one_mul]
      · -- a regular point: `linkOrd = 0`
        have hord : linkOrd A B x = 0 := by
          rw [linkOrd, if_neg hxB, if_neg hxA, sub_zero]
        have hexA : e x ≠ P.α := fun heq => hxA (e.injOn hxe hA (hPα ▸ heq))
        have hexB : e x ≠ P.β := fun heq => hxB (e.injOn hxe hB (hPβ ▸ heq))
        refine ⟨P.g (e x), P.g_ne_zero hexA hexB, ?_⟩
        have hcont : ContinuousAt (P.g ∘ τ) z₀ := by
          refine ContinuousAt.comp ?_ hτan.continuousAt
          rw [hτz₀]
          exact (P.g_contDiffAt hexA).continuousAt
        have hgoal : Tendsto (P.g ∘ τ) (nhdsWithin z₀ {z₀}ᶜ) (nhds (P.g (e x))) := by
          have h1 : Tendsto (P.g ∘ τ) (nhds z₀) (nhds ((P.g ∘ τ) z₀)) := hcont
          rw [Function.comp_apply, hτz₀] at h1
          exact h1.mono_left nhdsWithin_le_nhds
        refine hgoal.congr' ?_
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hSopen.mem_nhds hz₀mem)] with z hz2
        obtain ⟨q, hq, rfl⟩ := hz2
        have hq1 : (chartAt ℂ x).symm (chartAt ℂ x q) = q :=
          (chartAt ℂ x).left_inv hq.1
        rw [hord]
        change P.g (τ (chartAt ℂ x q))
          = f ((chartAt ℂ x).symm (chartAt ℂ x q)) * (chartAt ℂ x q - z₀) ^ (-(0 : ℤ))
        rw [neg_zero, zpow_zero, mul_one, hq1, hf_source q hq.2, hτ_def]
        simp only [Function.comp_apply, hq1]
  · -- off the chart: `f ≡ 1` near `x`, `linkOrd = 0`
    have hxA : x ≠ A := fun heq => hxe (heq ▸ hA)
    have hxB : x ≠ B := fun heq => hxe (heq ▸ hB)
    have hord : linkOrd A B x = 0 := by
      rw [linkOrd, if_neg hxB, if_neg hxA, sub_zero]
    refine ⟨1, one_ne_zero, ?_⟩
    have hev := hlocal_out hxe
    refine (tendsto_const_nhds).congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with z hz
    rw [hord]
    show (1 : ℂ) = f ((chartAt ℂ x).symm z) * (z - chartAt ℂ x x) ^ (-(0 : ℤ))
    rw [neg_zero, zpow_zero, mul_one]
    exact hz.symm

omit [CompactSpace X] in
/-- **The link construction** (design §4.1 step 5, one chain link): the piece function `f`,
its packaged `(0,1)`-form `η`, and the five assembly facts. Degenerate links (`A = B`) yield
the constant `1` and the zero form. -/
theorem exists_link [DecidableEq X] {A B : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (hA : A ∈ e.source) (hB : B ∈ e.source)
    {c : ℂ} {r : ℝ} (hball : ball c r ⊆ e.target)
    (hAm : e A ∈ ball c r) (hBm : e B ∈ ball c r) :
    ∃ (f : X → ℂ) (η : RS.Form01 X),
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {A}ᶜ
      ∧ (∀ x, x ≠ A → x ≠ B → f x ≠ 0)
      ∧ (∀ x, x ≠ A → x ≠ B → RS.wirtingerDbar (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
          = η.coeffAt x (chartAt ℂ x x) * f x)
      ∧ (∀ x : X, ∃ C : ℂ, C ≠ 0 ∧ Tendsto
          (fun z => f ((chartAt ℂ x).symm z) * (z - chartAt ℂ x x) ^ (-(linkOrd A B x)))
          (nhdsWithin (chartAt ℂ x x) {chartAt ℂ x x}ᶜ) (nhds C))
      ∧ (∀ (PU : SurfPoU X) (θ : RS.Form1 X) (Gp : ℂ → ℂ),
          (∀ z ∈ ball c r, HasDerivAt Gp (RS.coeffIn e θ z) z) →
          pairing PU η θ = (Real.pi : ℂ) * (Gp (e B) - Gp (e A))) := by
  classical
  by_cases hAB : A = B
  · -- the degenerate link
    subst hAB
    refine ⟨fun _ => 1, 0, contMDiffOn_const, fun x _ _ => one_ne_zero, ?_, ?_, ?_⟩
    · intro x _ _
      rw [RS.Form01.coeffAt_zero, zero_mul]
      exact RS.wirtingerDbar_const (chartAt ℂ x x) 1
    · intro x
      refine ⟨1, one_ne_zero, ?_⟩
      have hshape : (fun z => (1 : ℂ) * (z - chartAt ℂ x x) ^ (-(linkOrd A A x)))
          = fun _ => (1 : ℂ) := by
        funext z
        rw [linkOrd_self_eq_zero, neg_zero, zpow_zero, mul_one]
      rw [hshape]
      exact tendsto_const_nhds
    · intro PU θ Gp _
      have hzero : (0 : RS.Form01 X) = (0 : ℂ) • (0 : RS.Form01 X) := (zero_smul ℂ _).symm
      rw [hzero, pairing_smul_left, zero_mul, sub_self, mul_zero]
  · -- the genuine link
    have hr : 0 < r := by
      rcases Metric.mem_ball.mp hAm with h1
      exact lt_of_le_of_lt dist_nonneg h1
    have heAB : e A ≠ e B := fun heq => hAB (e.injOn hA hB heq)
    -- radii
    set δm : ℝ := max ‖e A - c‖ ‖e B - c‖ with hδm_def
    have hδm_lt : δm < r := by
      rw [hδm_def, max_lt_iff]
      constructor
      · rw [← dist_eq_norm]; exact Metric.mem_ball.mp hAm
      · rw [← dist_eq_norm]; exact Metric.mem_ball.mp hBm
    have hδm_nonneg : 0 ≤ δm := le_trans (norm_nonneg _) (le_max_left _ _)
    set ε : ℝ := r - δm with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    set ρ : ℝ := δm + ε / 4 with hρ_def
    have hρpos : 0 < ρ := by rw [hρ_def]; linarith
    set χ : ContDiffBump (0 : ℂ) := ⟨δm + ε / 2, δm + 3 * ε / 4, by linarith, by linarith⟩
      with hχ_def
    have hρχin : ρ < χ.rIn := by
      change δm + ε / 4 < δm + ε / 2
      linarith
    have hχout_lt : χ.rOut < r := by
      change δm + 3 * ε / 4 < r
      rw [hε_def]
      linarith
    have hAρ : e A - c ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball, dist_zero_right, hρ_def]
      have : ‖e A - c‖ ≤ δm := le_max_left _ _
      linarith
    have hBρ : e B - c ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball, dist_zero_right, hρ_def]
      have : ‖e B - c‖ ≤ δm := le_max_right _ _
      linarith
    -- the branch and the piece
    obtain ⟨L, hL, hLexp⟩ := RS.AbelWeak.exists_exteriorLogBranch hρpos hAρ hBρ
    set P : LogPieceData := ⟨c, ρ, hρpos, e A, e B, heAB, hAρ, hBρ, χ, hρχin, L, hL, hLexp⟩
      with hP_def
    -- the packaged form
    have hKcompact : IsCompact (closedBall c χ.rOut \ ball c χ.rIn) :=
      (isCompact_closedBall c χ.rOut).diff isOpen_ball
    have hKsub : closedBall c χ.rOut \ ball c χ.rIn ⊆ e.target := by
      intro z hz
      refine hball ?_
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz.1) hχout_lt
    set D : ChartSupportedData X :=
      ⟨e, he, P.dlog, P.contDiff_dlog, closedBall c χ.rOut \ ball c χ.rIn, hKcompact,
        hKsub, P.support_dlog_subset⟩ with hD_def
    -- the piece function on the surface
    set f : X → ℂ := Set.piecewise e.source (fun x => P.g (e x)) (fun _ => 1) with hf_def
    have hf_source : ∀ x ∈ e.source, f x = P.g (e x) := fun x hx =>
      Set.piecewise_eq_of_mem _ _ _ hx
    have hf_not_source : ∀ x, x ∉ e.source → f x = 1 := fun x hx =>
      Set.piecewise_eq_of_notMem _ _ _ hx
    -- the compact carrier on the surface and `f ≡ 1` off it
    set Kf : Set X := ⇑e.symm '' closedBall c χ.rOut with hKf_def
    have hKf_sub_source : Kf ⊆ e.source := by
      rintro y ⟨z, hz, rfl⟩
      refine e.map_target (hball ?_)
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hχout_lt
    have hKf_compact : IsCompact Kf := (isCompact_closedBall c χ.rOut).image_of_continuousOn
      (e.symm.continuousOn.mono (fun z hz => hball (by
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hχout_lt)))
    have hf_one_off_Kf : ∀ y, y ∉ Kf → f y = 1 := by
      intro y hyK
      by_cases hye : y ∈ e.source
      · have hnotmem : e y ∉ closedBall c χ.rOut := by
          intro hmem
          exact hyK ⟨e y, hmem, e.left_inv hye⟩
        rw [Metric.mem_closedBall, not_le] at hnotmem
        rw [hf_source y hye, P.g_one (by rw [← dist_eq_norm]; exact hnotmem.le)]
      · exact hf_not_source y hye
    -- membership bookkeeping
    have himg_mem : ∀ {x : X}, x ∈ e.source →
        e x ≠ P.α → ContDiffAt ℝ ∞ P.g (e x) := by
      intro x _ hx
      exact P.g_contDiffAt hx
    -- (1) smoothness off the pole
    have hsmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {A}ᶜ := by
      intro x hx
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      by_cases hxe : x ∈ e.source
      · have hexA : e x ≠ P.α := fun heq => hx (e.injOn hxe hA heq)
        have hcm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.g ∘ ⇑e) x :=
          RS.AbelWeak.contMDiffAt_comp_of_contDiffAt he hxe (P.g_contDiffAt hexA)
        have heqf : f =ᶠ[nhds x] (P.g ∘ ⇑e) := by
          filter_upwards [e.open_source.mem_nhds hxe] with y hy
          exact hf_source y hy
        exact (hcm.congr_of_eventuallyEq heqf).contMDiffWithinAt
      · have hxK : x ∉ Kf := fun hxK' => hxe (hKf_sub_source hxK')
        have heqf : f =ᶠ[nhds x] (fun _ : X => (1 : ℂ)) := by
          filter_upwards [hKf_compact.isClosed.isOpen_compl.mem_nhds hxK] with y hy
          exact hf_one_off_Kf y hy
        exact (contMDiffAt_const.congr_of_eventuallyEq heqf).contMDiffWithinAt
    -- (2) non-vanishing
    have hne_zero : ∀ x, x ≠ A → x ≠ B → f x ≠ 0 := by
      intro x hxA hxB
      by_cases hxe : x ∈ e.source
      · rw [hf_source x hxe]
        exact P.g_ne_zero (fun heq => hxA (e.injOn hxe hA heq))
          (fun heq => hxB (e.injOn hxe hB heq))
      · rw [hf_not_source x hxe]
        exact one_ne_zero
    -- local eventual descriptions of `f ∘ (chartAt x).symm` near the center
    have hlocal_in : ∀ {x : X}, x ∈ e.source →
        (f ∘ ⇑(chartAt ℂ x).symm) =ᶠ[nhds (chartAt ℂ x x)]
          (P.g ∘ (⇑e ∘ ⇑(chartAt ℂ x).symm)) := by
      intro x hxe
      have hsymm_cont : ContinuousAt (⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
        (chartAt ℂ x).symm.continuousAt (by simp)
      have hpre : (⇑(chartAt ℂ x).symm) ⁻¹' e.source ∈ nhds (chartAt ℂ x x) := by
        refine hsymm_cont.preimage_mem_nhds (e.open_source.mem_nhds ?_)
        rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
        exact hxe
      filter_upwards [hpre] with z hz
      exact hf_source _ hz
    have hlocal_out : ∀ {x : X}, x ∉ e.source →
        (f ∘ ⇑(chartAt ℂ x).symm) =ᶠ[nhds (chartAt ℂ x x)] (fun _ => (1 : ℂ)) := by
      intro x hxe
      have hxK : x ∉ Kf := fun hxK' => hxe (hKf_sub_source hxK')
      have hsymm_cont : ContinuousAt (⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
        (chartAt ℂ x).symm.continuousAt (by simp)
      have hpre : (⇑(chartAt ℂ x).symm) ⁻¹' (Kf)ᶜ ∈ nhds (chartAt ℂ x x) := by
        refine hsymm_cont.preimage_mem_nhds
          (hKf_compact.isClosed.isOpen_compl.mem_nhds ?_)
        rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
        exact hxK
      filter_upwards [hpre] with z hz
      exact hf_one_off_Kf _ hz
    -- (3) the dbar log matching at chart centers
    have hdlog : ∀ x, x ≠ A → x ≠ B →
        RS.wirtingerDbar (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
          = D.form.coeffAt x (chartAt ℂ x x) * f x := by
      intro x hxA hxB
      by_cases hxe : x ∈ e.source
      · set τ : ℂ → ℂ := ⇑e ∘ ⇑(chartAt ℂ x).symm with hτ_def
        have hz₀mem : chartAt ℂ x x ∈
            ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ e.source) :=
          ⟨x, ⟨mem_chart_source ℂ x, hxe⟩, rfl⟩
        have hτz₀ : τ (chartAt ℂ x x) = e x := by
          rw [hτ_def]
          simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
        have hτdiff : DifferentiableAt ℂ τ (chartAt ℂ x x) :=
          (RS.analyticAt_trans he (IsManifold.chart_mem_maximalAtlas x)
            (mem_chart_target ℂ x)
            (by rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hxe)).differentiableAt
        have hexA : e x ≠ P.α := fun heq => hxA (e.injOn hxe hA heq)
        have hexB : e x ≠ P.β := fun heq => hxB (e.injOn hxe hB heq)
        have hgd : DifferentiableAt ℝ P.g (τ (chartAt ℂ x x)) := by
          rw [hτz₀]
          exact (P.g_contDiffAt hexA).differentiableAt (by norm_num)
        calc RS.wirtingerDbar (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
            = RS.wirtingerDbar (P.g ∘ τ) (chartAt ℂ x x) := by
              refine RS.wirtingerDbar_congr_nhds _ _ _ ?_
              refine (hlocal_in hxe).trans (Filter.Eventually.of_forall (fun z => rfl))
          _ = (starRingEnd ℂ) (deriv τ (chartAt ℂ x x)) *
              RS.wirtingerDbar P.g (τ (chartAt ℂ x x)) :=
              RS.wirtingerDbar_comp_differentiableAt P.g (chartAt ℂ x x) hgd hτdiff
          _ = (starRingEnd ℂ) (deriv τ (chartAt ℂ x x)) *
              (P.dlog (e x) * P.g (e x)) := by
              rw [hτz₀, P.wirtingerDbar_g hexA hexB]
          _ = D.form.coeffAt x (chartAt ℂ x x) * f x := by
              rw [D.form_coeffAt_center hxe, hf_source x hxe]
              show _ = (starRingEnd ℂ) (deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) *
                D.h (D.e x) * P.g (e x)
              rw [hD_def]
              ring
      · have hev := hlocal_out hxe
        rw [RS.wirtingerDbar_congr_nhds _ _ _ hev,
          D.form_coeffAt_center_of_notMem hxe, zero_mul]
        exact RS.wirtingerDbar_const (chartAt ℂ x x) 1
    -- (4) the factor limits
    have hfactor := exists_linkOrd_factor hAB he hA hB rfl rfl heAB hf_source hlocal_out
    -- (5) the pairing identity
    have hpairing : ∀ (PU : SurfPoU X) (θ : RS.Form1 X) (Gp : ℂ → ℂ),
        (∀ z ∈ ball c r, HasDerivAt Gp (RS.coeffIn e θ z) z) →
        pairing PU D.form θ = (Real.pi : ℂ) * (Gp (e B) - Gp (e A)) := by
      intro PU θ Gp hGp
      rw [pairing_form PU D θ]
      have := P.integral_dlog_mul (r := r) hχout_lt (w := RS.coeffIn e θ) (Gp := Gp) hGp
      exact this
    exact ⟨f, D.form, hsmooth, hne_zero, hdlog, hfactor, hpairing⟩

end RS.Abel

end
