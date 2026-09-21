/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.FoldExtensionFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.GagliardoNirenbergSobolevFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AxisCube
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Finite-`p` coordinate GNS input for cube localization

This module records the coordinate form of the ambient finite-`p`
Gagliardo--Nirenberg--Sobolev theorem.  It is the analytic estimate applied to
compactly supported smooth folded approximants in the cube localization step.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

private theorem tendsto_eLpNorm_mul_of_norm_le_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {χ : α → ℝ} {F : ℕ → α → ℝ} {f : α → ℝ} (hχ : ∀ x, ‖χ x‖ ≤ 1)
    (htend : Filter.Tendsto (fun n => eLpNorm (fun x => F n x - f x) p μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (fun x => χ x * F n x - χ x * f x) p μ)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ n, eLpNorm (fun x => χ x * F n x - χ x * f x) p μ
      ≤ eLpNorm (fun x => F n x - f x) p μ := by
    intro n
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [show χ x * F n x - χ x * f x = χ x * (F n x - f x) by ring, norm_mul]
    simpa [mul_comm] using
      (mul_le_of_le_one_right (norm_nonneg (F n x - f x)) (hχ x))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
    (fun n => zero_le) hbound

private theorem tendsto_eLpNorm_mul_of_norm_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {χ : α → ℝ} {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hχ : ∀ x, ‖χ x‖ ≤ C)
    (htend : Filter.Tendsto (fun n => eLpNorm (fun x => F n x - f x) p μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (fun x => χ x * F n x - χ x * f x) p μ)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ n, eLpNorm (fun x => χ x * F n x - χ x * f x) p μ
      ≤ ENNReal.ofReal C * eLpNorm (fun x => F n x - f x) p μ := by
    intro n
    have hmono : eLpNorm (fun x => χ x * F n x - χ x * f x) p μ
        ≤ eLpNorm (C • fun x => F n x - f x) p μ :=
      eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => by
        rw [show χ x * F n x - χ x * f x = χ x * (F n x - f x) by ring, norm_mul,
          Pi.smul_apply, smul_eq_mul, norm_mul,
          Real.norm_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (hχ x) (norm_nonneg _))
    refine hmono.trans ?_
    simpa [Real.enorm_eq_ofReal hC] using
      (eLpNorm_const_smul_le (c := C) (f := fun x => F n x - f x) (p := p) (μ := μ))
  have hscaled : Filter.Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun x => F n x - f x) p μ)
      Filter.atTop (nhds (ENNReal.ofReal C * 0)) :=
    ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.ofReal_ne_top)
  have hscaled0 : Filter.Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun x => F n x - f x) p μ)
      Filter.atTop (nhds 0) := by
    simpa using hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled0
    (fun n => zero_le) hbound

private theorem tendsto_eLpNorm_of_tendsto_sub_finiteLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {r : ℝ≥0∞} (hr : 1 ≤ r)
    {F : ℕ → α → ℝ} {f : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hf : AEStronglyMeasurable f μ)
    (hfin : eLpNorm f r μ ≠ ⊤)
    (h : Filter.Tendsto (fun n => eLpNorm (fun x => F n x - f x) r μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (F n) r μ) Filter.atTop (nhds (eLpNorm f r μ)) := by
  have hupper : ∀ n, eLpNorm (F n) r μ ≤
      eLpNorm f r μ + eLpNorm (fun x => F n x - f x) r μ := by
    intro n
    refine (le_of_eq ?_).trans (eLpNorm_add_le hf ((hF n).sub hf) hr)
    congr 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hneg : ∀ n, eLpNorm (fun x => f x - F n x) r μ =
      eLpNorm (fun x => F n x - f x) r μ := by
    intro n
    rw [show (fun x => f x - F n x) = -(fun x => F n x - f x) by
      funext x
      simp only [Pi.neg_apply]
      ring, eLpNorm_neg]
  have hlower : ∀ n, eLpNorm f r μ - eLpNorm (fun x => F n x - f x) r μ ≤
      eLpNorm (F n) r μ := by
    intro n
    rw [tsub_le_iff_right]
    calc eLpNorm f r μ = eLpNorm (fun x => F n x + (f x - F n x)) r μ := by
          congr 1
          funext x
          ring
      _ ≤ eLpNorm (F n) r μ + eLpNorm (fun x => f x - F n x) r μ :=
        eLpNorm_add_le (hF n) (hf.sub (hF n)) hr
      _ = eLpNorm (F n) r μ + eLpNorm (fun x => F n x - f x) r μ := by rw [hneg]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => eLpNorm f r μ - eLpNorm (fun x => F n x - f x) r μ)
    (h := fun n => eLpNorm f r μ + eLpNorm (fun x => F n x - f x) r μ) ?_ ?_ hlower hupper
  · have ht := ENNReal.Tendsto.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => eLpNorm f r μ) Filter.atTop
        (nhds (eLpNorm f r μ))) h (Or.inl hfin)
    simpa using ht
  · simpa using Filter.Tendsto.const_add (eLpNorm f r μ) h

/-- The operator norm of a scalar functional on `Vec d` is bounded by its
values on the coordinate basis. -/
theorem clm_norm_le_sum_basisVec_finiteLp {d : ℕ} (T : (Vec d) →L[ℝ] ℝ) :
    ‖T‖ ≤ ∑ i, ‖T (basisVec i)‖ := by
  refine T.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun x => ?_
  have hx : x = ∑ i, x i • basisVec i := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, basisVec_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ j (fun i => x i)]
    simp
  calc
    ‖T x‖ = ‖T (∑ i, x i • basisVec i)‖ := by rw [← hx]
    _ = ‖∑ i, x i • T (basisVec i)‖ := by rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i, ‖x i • T (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖T (basisVec i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i, ‖x‖ * ‖T (basisVec i)‖ :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i, ‖T (basisVec i)‖) * ‖x‖ := by rw [← Finset.mul_sum]; ring

/-- Coordinate form of the ambient finite-`p` GNS inequality. -/
theorem gns_coord_finiteLp {d : ℕ} (hd : 0 < d) (p q : FiniteLpExponent)
    (hp : p.exponent.toReal < d)
    (hpq : (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcs : HasCompactSupport ψ) :
    eLpNorm ψ q.exponent (volume : Measure (Vec d))
      ≤ SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) p.exponent.toNNReal *
        ∑ i, eLpNorm (fun x => fderiv ℝ ψ x (basisVec i)) p.exponent
          (volume : Measure (Vec d)) := by
  refine (gns_contDiff_compactSupport_finiteLp hd p q hp hpq hψ hcs).trans
    (mul_le_mul_right ?_ _)
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hsum_eq : (fun x => ∑ i, ‖fderiv ℝ ψ x (basisVec i)‖)
      = ∑ i, (fun x => ‖fderiv ℝ ψ x (basisVec i)‖) := by
    funext x
    rw [Finset.sum_apply]
  calc
    eLpNorm (fderiv ℝ ψ) p.exponent (volume : Measure (Vec d))
      ≤ eLpNorm (fun x => ∑ i, ‖fderiv ℝ ψ x (basisVec i)‖) p.exponent volume :=
        eLpNorm_mono (fun x =>
          (clm_norm_le_sum_basisVec_finiteLp (fderiv ℝ ψ x)).trans_eq
            (Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).symm)
    _ ≤ ∑ i, eLpNorm (fun x => ‖fderiv ℝ ψ x (basisVec i)‖) p.exponent volume := by
        rw [hsum_eq]
        exact eLpNorm_sum_le
          (fun i _ => ((hcont.clm_apply continuous_const).norm).aestronglyMeasurable)
          p.one_lt.le
    _ = ∑ i, eLpNorm (fun x => fderiv ℝ ψ x (basisVec i)) p.exponent volume :=
        Finset.sum_congr rfl fun i _ => eLpNorm_norm _

/-! ## The finite-exponent cube embedding -/

/-- The finite-exponent axis-cube Sobolev inequality.  The constant is chosen
before the cube, its scale, and the Sobolev function; its displayed formula
uses only the dimension and the input exponent. -/
theorem cubeSobolevEmbedding_finiteLp {d : ℕ} (hd : 0 < d)
    (p : FiniteLpExponent) (hp : p.exponent.toReal < d) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (q : FiniteLpExponent),
        (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹ →
        ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ u : W1pFunction (axisCube z L) p.exponent,
          eLpNorm u.toFun q.exponent (volumeMeasureOn (axisCube z L))
            ≤ (C : ℝ≥0∞) *
                ((∑ i : Fin d,
                      eLpNorm (fun x => u.grad x i) p.exponent
                        (volumeMeasureOn (axisCube z L)))
                  + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent
                      (volumeMeasureOn (axisCube z L))) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hd' : 0 < m + 1 := hd
  set Cgns : ℝ≥0∞ :=
    (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec (m + 1)))
      p.exponent.toNNReal : ℝ≥0∞) with hCgns
  set Cd : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal) with hCd
  have hp_pos : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne
  have hCd_lt : Cd < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp_pos.le)
      (ENNReal.pow_ne_top (by simp))
  have hCgns_lt : Cgns < ⊤ := by
    rw [hCgns]
    exact ENNReal.coe_lt_top
  set C0 : ℝ≥0∞ := Cgns * Cd * ((((m + 1) * 32 : ℕ)) : ℝ≥0∞) with hC0
  have hC0_lt : C0 < ⊤ := by
    rw [hC0]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hCgns_lt hCd_lt)
      (ENNReal.natCast_lt_top _)
  refine ⟨C0.toNNReal + 1, add_pos_of_nonneg_of_pos (zero_le) one_pos,
    fun q hpq z L hL u => ?_⟩
  set hi : Vec (m + 1) := fun k => z k + L with hhi
  have hlt : ∀ k, z k < hi k := fun k => by simp only [hhi]; linarith
  have hval : ∀ k, hi k = z k + L := fun k => by simp only [hhi]
  show eLpNorm u.toFun q.exponent (volume.restrict (Box z hi)) ≤
    (↑(C0.toNNReal + 1) : ℝ≥0∞) *
      ((∑ i, eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi))) +
        ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi)))
  have hV : IsOpenBoundedConvexDomain (Box3 z hi) :=
    isOpenBoundedConvexDomain_Box _ _
  let : IsFiniteMeasure (volume.restrict (Box3 z hi)) :=
    hV.isFiniteMeasure_restrict_volume
  let : IsLocallyFiniteMeasure (volume.restrict (Box3 z hi)) := inferInstance
  set Ext := foldExtensionFiniteP z hi hlt p u
  set Eu : W1pFunction (Box3 z hi) p.exponent := Ext.Eu with hEu
  have hℓ : (0 : ℝ) < L / 2 := by linarith
  set χ : Vec (m + 1) → ℝ := boxCutoff z hi (L / 2) with hχ
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := boxCutoff_contDiff
  have hχ_one : ∀ x ∈ Box z hi, χ x = 1 := by
    intro x hx
    exact boxCutoff_eq_one hℓ (Set.mem_Icc.2
      ⟨fun k => (Set.mem_univ_pi.1 hx k).1.le,
        fun k => (Set.mem_univ_pi.1 hx k).2.le⟩)
  have hχ_sub : tsupport χ ⊆ Box3 z hi := by
    have hsupp : Function.support χ ⊆
        Set.Icc (fun k => z k - L / 2) (fun k => hi k + L / 2) :=
      fun x hx => by by_contra hxn; exact hx (boxCutoff_eq_zero hℓ hxn)
    refine (closure_minimal hsupp isClosed_Icc).trans ?_
    rw [Box3_eq_Box]
    intro x hx
    rw [Set.mem_Icc] at hx
    refine Set.mem_univ_pi.2 fun k => ?_
    exact ⟨by have := hx.1 k; have := hval k; linarith,
      by have := hx.2 k; have := hval k; linarith⟩
  have hχ_le1 : ∀ x, ‖χ x‖ ≤ 1 := fun x => by
    rw [Real.norm_of_nonneg (boxCutoff_nonneg x)]
    exact boxCutoff_le_one x
  have hχ_deriv : ∀ x i, |fderiv ℝ χ x (basisVec i)| ≤ 32 / L := by
    intro x i
    have h := boxCutoff_deriv_bound (lo := z) (hi := hi) hℓ x i
    have h2 : (16 : ℝ) / (L / 2) = 32 / L := by field_simp; ring
    simpa [χ, basisVec, h2] using h
  set x0 : Vec (m + 1) := fun k => (z k + hi k) / 2 with hx0
  set r : ℝ := L / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hball : Metric.closedBall x0 r ⊆ Box3 z hi := by
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff hr.le] at hx
    rw [Box3_eq_Box]
    refine Set.mem_univ_pi.2 fun k => ?_
    have hxk : dist (x k) (x0 k) ≤ r := hx k
    rw [Real.dist_eq, abs_le] at hxk
    rw [hx0, hrdef] at hxk
    rw [hhi]
    constructor <;> nlinarith [hxk.1, hxk.2, hL]
  set A : ℕ → W1pFunction (Box3 z hi) p.exponent :=
    W1pFunction.convexApproxSmoothW1p hV p.one_lt.le Eu x0 hr
  have hA_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (A n).toFun := by
    intro n
    simp [A, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
    exact contDiff_convexApproxSmoothRepresentative hV.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel) p.one_lt.le Eu.memLp hr
      (W1pFunction.unitConvexApproxScale_pos n)
  have hA_grad : ∀ n x i, (A n).grad x i =
      fderiv ℝ ((A n).toFun) x (basisVec i) := by
    intro n x i
    simp [A, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
  set ψ : ℕ → Vec (m + 1) → ℝ := fun n x => χ x * (A n).toFun x
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) :=
    fun n => hχ_smooth.mul (hA_smooth n)
  have hψ_cptsupp : ∀ n, HasCompactSupport (ψ n) :=
    fun n => by
      apply HasCompactSupport.intro
        (K := Set.Icc (fun k => z k - L / 2) (fun k => hi k + L / 2)) isCompact_Icc
      intro x hx
      dsimp [ψ]
      rw [hχ, boxCutoff_eq_zero hℓ hx, zero_mul]
  have hψ_supp : ∀ n, tsupport (ψ n) ⊆ Box3 z hi := by
    intro n x hx
    change x ∈ closure (Function.support (ψ n)) at hx
    apply hχ_sub
    refine closure_minimal ?_ (isClosed_tsupport χ) hx
    intro y hy
    apply subset_tsupport χ
    rw [Function.mem_support] at hy ⊢
    intro hzero
    apply hy
    simp only [ψ, hzero, zero_mul]
  have hψ_dsupp : ∀ n i,
      Function.support (fun x => fderiv ℝ (ψ n) x (basisVec i)) ⊆ Box3 z hi := by
    intro n i x hx
    by_contra hxb
    have hx_nots : x ∉ tsupport (ψ n) := fun hc => hxb (hψ_supp n hc)
    have hzero : ψ n =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (ψ n)).isOpen_compl.eventually_mem hx_nots |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    exact (Function.mem_support.1 hx) (by
      rw [Filter.EventuallyEq.fderiv_eq hzero]
      simp)
  have hrestr : ∀ (f : Vec (m + 1) → ℝ) (a : ℝ≥0∞),
      Function.support f ⊆ Box3 z hi →
      eLpNorm f a (volume.restrict (Box3 z hi)) = eLpNorm f a volume :=
    fun f a hf => eLpNorm_restrict_eq_of_support_subset hf
  set a : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (ψ n) q.exponent (volume.restrict (Box3 z hi))
  set b : ℕ → ℝ≥0∞ := fun n => Cgns * ∑ i,
    eLpNorm (fun x => fderiv ℝ (ψ n) x (basisVec i)) p.exponent
      (volume.restrict (Box3 z hi))
  have hab : ∀ n, a n ≤ b n := by
    intro n
    show eLpNorm (ψ n) q.exponent (volume.restrict (Box3 z hi)) ≤
      Cgns * ∑ i, eLpNorm (fun x => fderiv ℝ (ψ n) x (basisVec i)) p.exponent
        (volume.restrict (Box3 z hi))
    rw [hrestr _ _ ((subset_tsupport _).trans (hψ_supp n))]
    refine (gns_coord_finiteLp hd' p q hp hpq
      ((hψ_smooth n).of_le (by exact_mod_cast le_top)) (hψ_cptsupp n)).trans ?_
    refine mul_le_mul_right (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) _
    exact (hrestr _ _ (hψ_dsupp n i)).symm
  have hA_tend := W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
    hV p.one_lt.le p.lt_top.ne Eu hball hr
  have hψ_tend : Filter.Tendsto (fun n =>
      eLpNorm (fun x => ψ n x - χ x * Eu.toFun x) p.exponent
        (volume.restrict (Box3 z hi))) Filter.atTop (nhds 0) := by
    simpa [ψ, volumeMeasureOn] using
      tendsto_eLpNorm_mul_of_norm_le_one hχ_le1 hA_tend
  have hDform : ∀ n x i, fderiv ℝ (ψ n) x (basisVec i) =
      χ x * (A n).grad x i + (A n).toFun x * fderiv ℝ χ x (basisVec i) := by
    intro n x i
    rw [show ψ n = χ * (A n).toFun by rfl,
      fderiv_mul ((hχ_smooth.differentiable (by simp)) x)
        (((hA_smooth n).differentiable (by simp)) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, hA_grad]
  set G : Fin (m + 1) → Vec (m + 1) → ℝ := fun i x =>
    χ x * Eu.grad x i + Eu.toFun x * fderiv ℝ χ x (basisVec i)
  have hG_meas : ∀ i, AEStronglyMeasurable (G i) (volume.restrict (Box3 z hi)) := by
    intro i
    exact hχ_smooth.continuous.aestronglyMeasurable.mul
      (Eu.grad_memLp i).aestronglyMeasurable |>.add
        (Eu.memLp.aestronglyMeasurable.mul
          (((hχ_smooth.continuous_fderiv (by simp)).clm_apply
            continuous_const).aestronglyMeasurable))
  have hgrad_tend : ∀ i, Filter.Tendsto (fun n =>
      eLpNorm (fun x => fderiv ℝ (ψ n) x (basisVec i) - G i x) p.exponent
        (volume.restrict (Box3 z hi))) Filter.atTop (nhds 0) := by
    intro i
    have hAgrad := W1pFunction.tendsto_convexApproxSmoothW1p_grad_eLpNorm_sub
      hV p.one_lt.le p.lt_top.ne Eu hball hr i
    have h1 : Filter.Tendsto (fun n => eLpNorm
        (fun x => χ x * ((A n).grad x i - Eu.grad x i)) p.exponent
          (volume.restrict (Box3 z hi))) Filter.atTop (nhds 0) := by
      have hraw := tendsto_eLpNorm_mul_of_norm_le_one hχ_le1 hAgrad
      refine hraw.congr' ?_
      filter_upwards with n
      apply eLpNorm_congr_ae
      filter_upwards with x
      simp only [A]
      ring
    have h2 : Filter.Tendsto (fun n => eLpNorm
        (fun x => ((A n).toFun x - Eu.toFun x) * fderiv ℝ χ x (basisVec i))
          p.exponent (volume.restrict (Box3 z hi))) Filter.atTop (nhds 0) := by
      have h := tendsto_eLpNorm_mul_of_norm_le
        (C := 32 / L) (by positivity) (fun x => by
          rw [Real.norm_eq_abs]
          exact hχ_deriv x i) hA_tend
      refine h.congr' ?_
      filter_upwards with n
      apply eLpNorm_congr_ae
      filter_upwards with x
      simp only [A]
      ring
    have hsum : Filter.Tendsto (fun n =>
        eLpNorm (fun x => χ x * ((A n).grad x i - Eu.grad x i) +
          ((A n).toFun x - Eu.toFun x) * fderiv ℝ χ x (basisVec i)) p.exponent
          (volume.restrict (Box3 z hi))) Filter.atTop (nhds 0) := by
      have hbound : ∀ n, eLpNorm
          (fun x => χ x * ((A n).grad x i - Eu.grad x i) +
            ((A n).toFun x - Eu.toFun x) * fderiv ℝ χ x (basisVec i)) p.exponent
            (volume.restrict (Box3 z hi)) ≤
          eLpNorm (fun x => χ x * ((A n).grad x i - Eu.grad x i)) p.exponent
              (volume.restrict (Box3 z hi)) +
            eLpNorm (fun x => ((A n).toFun x - Eu.toFun x) *
              fderiv ℝ χ x (basisVec i)) p.exponent (volume.restrict (Box3 z hi)) := by
        intro n
        exact eLpNorm_add_le
          (hχ_smooth.continuous.aestronglyMeasurable.mul
            (((A n).grad_memLp i).aestronglyMeasurable.sub
              (Eu.grad_memLp i).aestronglyMeasurable))
          (((A n).memLp.aestronglyMeasurable.sub Eu.memLp.aestronglyMeasurable).mul
            (((hχ_smooth.continuous_fderiv (by simp)).clm_apply
              continuous_const).aestronglyMeasurable)) p.one_lt.le
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using h1.add h2) (fun n => zero_le) hbound
    refine hsum.congr' ?_
    filter_upwards with n
    congr 1
    funext x
    rw [hDform n x i]
    simp only [G]
    ring
  have hG_fin : ∀ i, eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi)) < ⊤ := by
    intro i
    have hfirst : eLpNorm (fun x => χ x * Eu.grad x i) p.exponent
        (volume.restrict (Box3 z hi)) ≤
        Cd * eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi)) := by
      change eLpNorm (fun x => χ x * Ext.Eu.grad x i) p.exponent _ ≤ _
      refine (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)).trans
        (Ext.grad_eLpNorm_le i)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ_le1 x)
    have hsecond : eLpNorm (fun x => Eu.toFun x * fderiv ℝ χ x (basisVec i)) p.exponent
        (volume.restrict (Box3 z hi)) ≤
        ENNReal.ofReal (32 / L) * eLpNorm Eu.toFun p.exponent
          (volume.restrict (Box3 z hi)) := by
      have hmono : eLpNorm (fun x => Eu.toFun x * fderiv ℝ χ x (basisVec i)) p.exponent
          (volume.restrict (Box3 z hi)) ≤
          eLpNorm ((32 / L : ℝ) • Eu.toFun) p.exponent (volume.restrict (Box3 z hi)) := by
        refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 32 / L)]
        calc ‖Eu.toFun x‖ * ‖fderiv ℝ χ x (basisVec i)‖
            ≤ ‖Eu.toFun x‖ * (32 / L) :=
              mul_le_mul_of_nonneg_left
                (by rw [Real.norm_eq_abs]; exact hχ_deriv x i) (norm_nonneg _)
          _ = (32 / L) * ‖Eu.toFun x‖ := by ring
      exact hmono.trans ((eLpNorm_const_smul_le (c := (32 / L : ℝ)) (f := Eu.toFun)).trans
        (le_of_eq (by congr 1; rw [Real.enorm_eq_ofReal (by positivity)])))
    change eLpNorm ((fun x => χ x * Eu.grad x i) +
      fun x => Eu.toFun x * fderiv ℝ χ x (basisVec i)) p.exponent _ < ⊤
    refine lt_of_le_of_lt (eLpNorm_add_le
      (hχ_smooth.continuous.aestronglyMeasurable.mul (Eu.grad_memLp i).aestronglyMeasurable)
      ?_ p.one_lt.le) ?_
    · exact Eu.memLp.aestronglyMeasurable.mul
        (((hχ_smooth.continuous_fderiv (by simp)).clm_apply
          continuous_const).aestronglyMeasurable)
    · have hEu_fin : eLpNorm Eu.toFun p.exponent (volume.restrict (Box3 z hi)) < ⊤ := by
        change eLpNorm Ext.Eu.toFun p.exponent _ < ⊤
        exact lt_of_le_of_lt Ext.eLpNorm_le
          (ENNReal.mul_lt_top hCd_lt u.memLp.eLpNorm_lt_top)
      exact lt_of_le_of_lt (add_le_add hfirst hsecond)
        (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hCd_lt (u.grad_memLp i).eLpNorm_lt_top,
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            hEu_fin⟩)
  set binf : ℝ≥0∞ := Cgns * ∑ i,
    eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi))
  have hb_tend : Filter.Tendsto b Filter.atTop (nhds binf) := by
    change Filter.Tendsto
      (fun n => Cgns * ∑ i, eLpNorm (fun x => fderiv ℝ (ψ n) x (basisVec i))
        p.exponent (volume.restrict (Box3 z hi))) Filter.atTop
      (nhds (Cgns * ∑ i, eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi))))
    refine ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun i _ => ?_)
      (Or.inr hCgns_lt.ne)
    exact tendsto_eLpNorm_of_tendsto_sub_finiteLp p.one_lt.le
      (fun n => ((hψ_smooth n).continuous_fderiv (by simp)
        |>.clm_apply continuous_const).aestronglyMeasurable)
      (hG_meas i) (hG_fin i).ne (hgrad_tend i)
  have hBox_sub : Box z hi ⊆ Box3 z hi := by
    rw [Box3_eq_Box]
    intro x hx
    refine Set.mem_univ_pi.2 fun k => ?_
    have h := Set.mem_univ_pi.1 hx k
    rw [hhi] at h ⊢
    exact ⟨by linarith [h.1, hL], by linarith [h.2, hL]⟩
  have hwu : (fun x => χ x * Eu.toFun x) =ᵐ[volume.restrict (Box z hi)] u.toFun := by
    filter_upwards [ae_restrict_mem (isOpen_Box z hi).measurableSet, Ext.toFun_ae]
      with x hx hEu
    rw [hχ_one x hx, one_mul, hEu]
  have hL1 : eLpNorm u.toFun q.exponent (volume.restrict (Box z hi)) ≤
      eLpNorm (fun x => χ x * Eu.toFun x) q.exponent (volume.restrict (Box3 z hi)) := by
    rw [← eLpNorm_congr_ae hwu]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hBox_sub le_rfl)
  have htim : TendstoInMeasure (volume.restrict (Box3 z hi)) (fun n => ψ n)
      Filter.atTop (fun x => χ x * Eu.toFun x) :=
    tendstoInMeasure_of_tendsto_eLpNorm
      (ne_of_gt (zero_lt_one.trans p.one_lt))
      (fun n => (hψ_smooth n).continuous.aestronglyMeasurable)
      (hχ_smooth.continuous.aestronglyMeasurable.mul Eu.memLp.aestronglyMeasurable) hψ_tend
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := htim.exists_seq_tendsto_ae
  have hL2 : eLpNorm (fun x => χ x * Eu.toFun x) q.exponent
      (volume.restrict (Box3 z hi)) ≤ Filter.liminf (fun j => a (σ j)) Filter.atTop :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun j => (hψ_smooth (σ j)).continuous.aestronglyMeasurable)
      _ hσ_ae
  have hbσ : Filter.Tendsto (fun j => b (σ j)) Filter.atTop (nhds binf) :=
    hb_tend.comp hσ_mono.tendsto_atTop
  have hL3 : Filter.liminf (fun j => a (σ j)) Filter.atTop ≤ binf := by
    calc Filter.liminf (fun j => a (σ j)) Filter.atTop
        ≤ Filter.liminf (fun j => b (σ j)) Filter.atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall fun j => hab (σ j))
      _ = binf := hbσ.liminf_eq
  have hG_bound : ∀ i, eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi)) ≤
      Cd * eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi)) +
        ENNReal.ofReal (32 / L) *
          (Cd * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi))) := by
    intro i
    have hfirst : eLpNorm (fun x => χ x * Eu.grad x i) p.exponent
        (volume.restrict (Box3 z hi)) ≤
        Cd * eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi)) := by
      change eLpNorm (fun x => χ x * Ext.Eu.grad x i) p.exponent _ ≤ _
      refine (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)).trans
        (Ext.grad_eLpNorm_le i)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ_le1 x)
    have hsecond : eLpNorm (fun x => Eu.toFun x * fderiv ℝ χ x (basisVec i)) p.exponent
        (volume.restrict (Box3 z hi)) ≤
        ENNReal.ofReal (32 / L) * eLpNorm Eu.toFun p.exponent
          (volume.restrict (Box3 z hi)) := by
      have hmono : eLpNorm (fun x => Eu.toFun x * fderiv ℝ χ x (basisVec i)) p.exponent
          (volume.restrict (Box3 z hi)) ≤
          eLpNorm ((32 / L : ℝ) • Eu.toFun) p.exponent (volume.restrict (Box3 z hi)) := by
        refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 32 / L)]
        calc ‖Eu.toFun x‖ * ‖fderiv ℝ χ x (basisVec i)‖
            ≤ ‖Eu.toFun x‖ * (32 / L) :=
              mul_le_mul_of_nonneg_left
                (by rw [Real.norm_eq_abs]; exact hχ_deriv x i) (norm_nonneg _)
          _ = (32 / L) * ‖Eu.toFun x‖ := by ring
      exact hmono.trans ((eLpNorm_const_smul_le (c := (32 / L : ℝ)) (f := Eu.toFun)).trans
        (le_of_eq (by congr 1; rw [Real.enorm_eq_ofReal (by positivity)])))
    change eLpNorm ((fun x => χ x * Eu.grad x i) +
      fun x => Eu.toFun x * fderiv ℝ χ x (basisVec i)) p.exponent _ ≤ _
    refine (eLpNorm_add_le
      (hχ_smooth.continuous.aestronglyMeasurable.mul (Eu.grad_memLp i).aestronglyMeasurable)
      (Eu.memLp.aestronglyMeasurable.mul
        (((hχ_smooth.continuous_fderiv (by simp)).clm_apply
          continuous_const).aestronglyMeasurable)) p.one_lt.le).trans (add_le_add hfirst ?_)
    exact hsecond.trans (mul_le_mul_right Ext.eLpNorm_le _)
  have hL4 : binf ≤ C0 *
      ((∑ i, eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi))) +
        ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi))) := by
    have hsum : ∑ i, eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi)) ≤
        Cd * (∑ i, eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi))) +
          ((m + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (32 / L) *
              (Cd * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi)))) := by
      refine (Finset.sum_le_sum fun i _ => hG_bound i).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hofReal : ENNReal.ofReal (32 / L) = ((32 : ℕ) : ℝ≥0∞) * ENNReal.ofReal L⁻¹ := by
      rw [show (32 : ℝ) / L = 32 * L⁻¹ by ring, ENNReal.ofReal_mul (by norm_num)]
      norm_num
    have hN1 : (1 : ℝ≥0∞) ≤ ((((m + 1) * 32 : ℕ)) : ℝ≥0∞) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    change Cgns * ∑ i, eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi)) ≤ _
    refine (mul_le_mul_right hsum Cgns).trans ?_
    rw [hofReal, hC0]
    simp only [mul_add]
    refine add_le_add ?_ (le_of_eq ?_)
    · rw [show Cgns * (Cd * ∑ i, eLpNorm (fun x => u.grad x i) p.exponent
          (volume.restrict (Box z hi))) = (Cgns * Cd) * ∑ i,
          eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi)) by ring]
      exact mul_le_mul_left (le_mul_of_one_le_right' hN1) _
    · push_cast
      ring
  have hmain : eLpNorm u.toFun q.exponent (volume.restrict (Box z hi)) ≤ C0 *
      ((∑ i, eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi))) +
        ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi))) :=
    hL1.trans (hL2.trans (hL3.trans hL4))
  have hC0le : C0 ≤ (↑(C0.toNNReal + 1) : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hC0_lt.ne, ENNReal.coe_one]
    exact le_self_add
  exact hmain.trans (mul_le_mul_left hC0le _)

end

end Homogenization
