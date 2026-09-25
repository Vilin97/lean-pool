/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.Extension
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.GagliardoNirenbergSobolev
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AxisCube
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Limit -/

@[expose] public section

namespace Homogenization

open MeasureTheory Homogenization Homogenization.H1Function
open scoped ENNReal NNReal BigOperators Topology

/-!
# The cube Sobolev embedding endgame

Cut off the fold extension `Eu` of `u ∈ H¹(axisCube)` to compact support inside
the tripled box, package `χ · Eu` as an `H¹₀` function with smooth compactly
supported approximants `ψ_k`, apply the Gagliardo–Nirenberg–Sobolev inequality
to each `ψ_k`, and pass to the limit (`L^{2*}` lower semicontinuity of `eLpNorm`
along an a.e.-convergent subsequence).  The reflection/cutoff constants and the
`L⁻¹` factor are collected into a single dimensional constant.
-/

noncomputable section

/-! ## Operator norm versus coordinate values -/

theorem clm_norm_le_sum_basisVec {n : ℕ} (T : (Vec n) →L[ℝ] ℝ) :
    ‖T‖ ≤ ∑ i, ‖T (basisVec i)‖ := by
  refine T.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun x => ?_
  have hx : x = ∑ i, x i • basisVec i := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, basisVec_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ j (fun i => x i)]
    simp
  calc ‖T x‖ = ‖T (∑ i, x i • basisVec i)‖ := by rw [← hx]
    _ = ‖∑ i, x i • T (basisVec i)‖ := by rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i, ‖x i • T (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖T (basisVec i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i, ‖x‖ * ‖T (basisVec i)‖ :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i, ‖T (basisVec i)‖) * ‖x‖ := by rw [← Finset.mul_sum]; ring

/-- **GNS in coordinate form.**  For a `C¹`, compactly supported function on
`Vec (m+1)` with `d = m+1 ≥ 3`, the `L^{2*}` norm is controlled by the sum of the
coordinate gradient `L²` norms. -/
theorem gns_coord {m : ℕ} (hd : 3 ≤ m + 1) {ψ : Vec (m + 1) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcs : HasCompactSupport ψ) :
    eLpNorm ψ (twoStar (m + 1)) (volume : Measure (Vec (m + 1)))
      ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec (m + 1))) 2 : ℝ≥0∞)
        * ∑ i, eLpNorm (fun x => fderiv ℝ ψ x (basisVec i)) 2
          (volume : Measure (Vec (m + 1))) := by
  refine (gns_contDiff_compactSupport hd hψ hcs).trans (mul_le_mul_right ?_ _)
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hsum_eq : (fun x => ∑ i, ‖fderiv ℝ ψ x (basisVec i)‖)
      = ∑ i, (fun x => ‖fderiv ℝ ψ x (basisVec i)‖) := by
    funext x; rw [Finset.sum_apply]
  calc eLpNorm (fderiv ℝ ψ) 2 (volume : Measure (Vec (m + 1)))
      ≤ eLpNorm (fun x => ∑ i, ‖fderiv ℝ ψ x (basisVec i)‖) 2 volume :=
        eLpNorm_mono (fun x => (clm_norm_le_sum_basisVec (fderiv ℝ ψ x)).trans_eq
          (Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).symm)
    _ ≤ ∑ i, eLpNorm (fun x => ‖fderiv ℝ ψ x (basisVec i)‖) 2 volume := by
        rw [hsum_eq]
        exact eLpNorm_sum_le
          (fun i _ => ((hcont.clm_apply continuous_const).norm).aestronglyMeasurable) (by norm_num)
    _ = ∑ i, eLpNorm (fun x => fderiv ℝ ψ x (basisVec i)) 2 volume :=
        Finset.sum_congr rfl (fun i _ => eLpNorm_norm _)

/-- `eLpNorm` is continuous along `Lᵖ`-convergent sequences (`p ≥ 1`, finite
target norm). -/
theorem tendsto_eLpNorm_of_tendsto_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) (hg : AEStronglyMeasurable g μ)
    (hfin : eLpNorm g p μ ≠ ⊤)
    (h : Filter.Tendsto (fun k => eLpNorm (fun x => f k x - g x) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => eLpNorm (f k) p μ) Filter.atTop (nhds (eLpNorm g p μ)) := by
  have hupper : ∀ k, eLpNorm (f k) p μ
      ≤ eLpNorm g p μ + eLpNorm (fun x => f k x - g x) p μ := by
    intro k
    refine (le_of_eq ?_).trans (eLpNorm_add_le hg ((hf k).sub hg) hp)
    congr 1; funext x; simp only [Pi.add_apply]; ring
  have hneg : ∀ k, eLpNorm (fun x => g x - f k x) p μ = eLpNorm (fun x => f k x - g x) p μ := by
    intro k
    rw [show (fun x => g x - f k x) = -(fun x => f k x - g x) from by
      funext x; simp only [Pi.neg_apply]; ring, eLpNorm_neg]
  have hlower : ∀ k, eLpNorm g p μ - eLpNorm (fun x => f k x - g x) p μ ≤ eLpNorm (f k) p μ := by
    intro k
    rw [tsub_le_iff_right]
    calc eLpNorm g p μ
        = eLpNorm (fun x => f k x + (g x - f k x)) p μ := by
          congr 1; funext x; ring
      _ ≤ eLpNorm (f k) p μ + eLpNorm (fun x => g x - f k x) p μ :=
          eLpNorm_add_le (hf k) (hg.sub (hf k)) hp
      _ = eLpNorm (f k) p μ + eLpNorm (fun x => f k x - g x) p μ := by rw [hneg]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun k => eLpNorm g p μ - eLpNorm (fun x => f k x - g x) p μ)
    (h := fun k => eLpNorm g p μ + eLpNorm (fun x => f k x - g x) p μ) ?_ ?_ hlower hupper
  · have := ENNReal.Tendsto.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => eLpNorm g p μ) Filter.atTop
        (nhds (eLpNorm g p μ))) h (Or.inl hfin)
    simpa using this
  · have := Filter.Tendsto.const_add (eLpNorm g p μ) h
    simpa using this

/-! ## The cube Sobolev embedding -/

/-- **Cube Sobolev embedding.**  Full statement. -/
theorem cubeSobolevEmbedding {d : ℕ} (hd : 3 ≤ d) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ u : H1Function (axisCube z L),
        eLpNorm u.toFun (twoStar d) (volumeMeasureOn (axisCube z L))
          ≤ (C : ℝ≥0∞) *
              ((∑ i : Fin d,
                    eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L)))
                + ENNReal.ofReal L⁻¹
                    * eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hd3 : 3 ≤ m + 1 := hd
  set Cgns : ℝ≥0∞ := (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec (m + 1))) 2 : ℝ≥0∞)
    with hCgns
  set Cd : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ (m + 1)) ^ ((1 : ℝ) / 2) with hCdDef
  have hCd_lt : Cd < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.pow_ne_top (by simp))
  have hCgns_lt : Cgns < ⊤ := by rw [hCgns]; exact ENNReal.coe_lt_top
  set C0 : ℝ≥0∞ := Cgns * Cd * ((((m + 1) * 32 : ℕ)) : ℝ≥0∞) with hC0
  have hC0_lt : C0 < ⊤ := by
    rw [hC0]; exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hCgns_lt hCd_lt) (ENNReal.natCast_lt_top _)
  refine ⟨C0.toNNReal + 1, add_pos_of_nonneg_of_pos (zero_le) one_pos, fun z L hL u => ?_⟩
  -- geometry
  set hi : Vec (m + 1) := fun k => z k + L with hhi
  have hlt : ∀ k, z k < hi k := fun k => by simp only [hhi]; linarith
  have hval : ∀ k, hi k = z k + L := fun k => by simp only [hhi]
  show eLpNorm u.toFun (twoStar (m + 1)) (volume.restrict (Box z hi))
    ≤ (↑(C0.toNNReal + 1) : ℝ≥0∞) *
        ((∑ i, eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box z hi)))
          + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun 2 (volume.restrict (Box z hi)))
  have hUbox : IsOpenBoundedConvexDomain (Box z hi) := isOpenBoundedConvexDomain_Box z hi
  have hU3 : IsOpenBoundedConvexDomain (Box3 z hi) := isOpenBoundedConvexDomain_Box _ _
  have hfin3 : IsFiniteMeasure (volume.restrict (Box3 z hi)) :=
    hU3.isFiniteMeasure_restrict_volume
  have hlf3 : IsLocallyFiniteMeasure (volume.restrict (Box3 z hi)) := inferInstance
  -- fold extension
  have Ext := foldExtension z hi hlt u
  set Eu : H1Function (Box3 z hi) := Ext.Eu with hEu
  -- cutoff
  have hℓ : (0 : ℝ) < L / 2 := by linarith
  set χ : Vec (m + 1) → ℝ := boxCutoff z hi (L / 2) with hχ
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := boxCutoff_contDiff
  have hχ_cptsupp : HasCompactSupport χ := by
    apply HasCompactSupport.intro
      (K := Set.Icc (fun k => z k - L / 2) (fun k => hi k + L / 2)) isCompact_Icc
    intro x hx; exact boxCutoff_eq_zero hℓ hx
  have hχ_one : ∀ x ∈ Box z hi, χ x = 1 := by
    intro x hx
    exact boxCutoff_eq_one hℓ (Set.mem_Icc.2
      ⟨fun k => (Set.mem_univ_pi.1 hx k).1.le, fun k => (Set.mem_univ_pi.1 hx k).2.le⟩)
  have hχ_sub : tsupport χ ⊆ Box3 z hi := by
    have hsupp : Function.support χ ⊆ Set.Icc (fun k => z k - L / 2) (fun k => hi k + L / 2) :=
      fun x hx => by by_contra hxn; exact hx (boxCutoff_eq_zero hℓ hxn)
    refine (closure_minimal hsupp isClosed_Icc).trans ?_
    rw [Box3_eq_Box]
    intro x hx
    rw [Set.mem_Icc] at hx
    refine Set.mem_univ_pi.2 fun k => ?_
    exact ⟨by have := hx.1 k; have := hval k; simp only [] at *; linarith,
      by have := hx.2 k; have := hval k; simp only [] at *; linarith⟩
  have hχ_deriv : ∀ x i, |fderiv ℝ χ x (basisVec i)| ≤ 32 / L := by
    intro x i
    have := boxCutoff_deriv_bound (lo := z) (hi := hi) hℓ x i
    have h2 : (16 : ℝ) / (L / 2) = 32 / L := by field_simp; ring
    simpa [hχ, basisVec, h2] using this
  -- the H¹₀ package and its H¹ twin
  set w : H10Function (Box3 z hi) :=
    Eu.mulContDiffHasCompactSupportToH10 hU3 hχ_smooth hχ_cptsupp hχ_sub with hw
  have hw_toFun : w.toH1Function.toFun = fun x => χ x * Eu.toFun x :=
    Eu.mulContDiffHasCompactSupportToH10_toFun hU3 hχ_smooth hχ_cptsupp hχ_sub
  set wH1 : H1Function (Box3 z hi) := Eu.mulContDiffHasCompactSupport hχ_smooth hχ_cptsupp with hwH1
  have hwH1_toFun : wH1.toFun = fun x => χ x * Eu.toFun x := by
    rw [hwH1, mulContDiffHasCompactSupport_toFun]
  have hwH1_grad : ∀ x i, wH1.grad x i
      = χ x * Eu.grad x i + Eu.toFun x * (fderiv ℝ χ x) (basisVec i) := by
    intro x i; rw [hwH1]; simp only [mulContDiffHasCompactSupport_grad]
  -- w.grad =ᵐ wH1.grad (uniqueness of the weak gradient)
  have hgrad_ae : ∀ i, (fun x => w.grad x i) =ᵐ[volume.restrict (Box3 z hi)]
      (fun x => wH1.grad x i) := by
    intro i
    have htoFun : w.toH1Function.toFun = wH1.toFun := by rw [hw_toFun, hwH1_toFun]
    have hint_w : IntegrableOn (fun x => w.grad x i) (Box3 z hi) volume :=
      (w.toH1Function.gradMemL2 i).integrable (by norm_num)
    have hint_wH1 : IntegrableOn (fun x => wH1.grad x i) (Box3 z hi) volume :=
      (wH1.gradMemL2 i).integrable (by norm_num)
    have hloc_w := hint_w.locallyIntegrableOn
    have hloc_wH1 := hint_wH1.locallyIntegrableOn
    refine HasWeakPartialDerivOn.ae_eq hU3.isOpen hloc_w hloc_wH1
      (w.toH1Function.hasWeakGradient i) ?_
    have := wH1.hasWeakGradient i
    rwa [← htoFun] at this
  -- smooth approximants
  set ψ : ℕ → Vec (m + 1) → ℝ := w.approx with hψdef
  have hψ_supp : ∀ k, Function.support (ψ k) ⊆ Box3 z hi :=
    fun k => (subset_tsupport _).trans (w.approx_support_subset k)
  have hψ_dsupp : ∀ k i, Function.support (fun x => fderiv ℝ (ψ k) x (basisVec i)) ⊆ Box3 z hi := by
    intro k i x hx
    by_contra hxb
    have hx_nots : x ∉ tsupport (ψ k) := fun hc => hxb (w.approx_support_subset k hc)
    have hzero : ψ k =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (ψ k)).isOpen_compl.eventually_mem hx_nots |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    exact (Function.mem_support.1 hx) (by rw [Filter.EventuallyEq.fderiv_eq hzero]; simp)
  -- eLpNorm over the restricted measure equals over volume for these supports
  have hrestr : ∀ (f : Vec (m + 1) → ℝ) (p : ℝ≥0∞), Function.support f ⊆ Box3 z hi →
      eLpNorm f p (volume.restrict (Box3 z hi)) = eLpNorm f p volume :=
    fun f p hf => eLpNorm_restrict_eq_of_support_subset hf
  -- abbreviations for the sequences
  set a : ℕ → ℝ≥0∞ := fun k => eLpNorm (ψ k) (twoStar (m + 1)) (volume.restrict (Box3 z hi))
    with hadef
  set b : ℕ → ℝ≥0∞ := fun k =>
    Cgns * ∑ i, eLpNorm (fun x => fderiv ℝ (ψ k) x (basisVec i)) 2 (volume.restrict (Box3 z hi))
    with hbdef
  have hab : ∀ k, a k ≤ b k := by
    intro k
    show eLpNorm (ψ k) (twoStar (m + 1)) (volume.restrict (Box3 z hi))
      ≤ Cgns * ∑ i, eLpNorm (fun x => fderiv ℝ (ψ k) x (basisVec i)) 2
          (volume.restrict (Box3 z hi))
    rw [hrestr _ _ (hψ_supp k)]
    refine (gns_coord hd3 ((w.approx_smooth k).of_le (by exact_mod_cast le_top))
      (w.approx_hasCompactSupport k)).trans ?_
    refine mul_le_mul_right (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) _
    exact (hrestr _ _ (hψ_dsupp k i)).symm
  -- b converges to binf
  set binf : ℝ≥0∞ := Cgns * ∑ i, eLpNorm (fun x => w.grad x i) 2 (volume.restrict (Box3 z hi))
    with hbinf
  have hb_tend : Filter.Tendsto b Filter.atTop (nhds binf) := by
    rw [hbdef, hbinf]
    refine ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun i _ => ?_) (Or.inr hCgns_lt.ne)
    refine tendsto_eLpNorm_of_tendsto_sub (by norm_num)
      (fun k => ((((w.approx_smooth k).of_le (by exact_mod_cast le_top) :
          ContDiff ℝ 1 (ψ k)).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable)
      (w.toH1Function.gradMemL2 i).aestronglyMeasurable
      (w.toH1Function.gradMemL2 i).eLpNorm_lt_top.ne ?_
    exact w.tendsto_approx_grad i
  -- pointwise cutoff bounds
  have hχ_le1 : ∀ x, ‖χ x‖ ≤ 1 := fun x => by
    rw [Real.norm_of_nonneg (boxCutoff_nonneg x)]; exact boxCutoff_le_one x
  have hBox_sub : Box z hi ⊆ Box3 z hi := by
    rw [Box3_eq_Box]; intro x hx
    refine Set.mem_univ_pi.2 fun k => ?_
    have := Set.mem_univ_pi.1 hx k
    exact ⟨by have := this.1; linarith [hlt k], by have := this.2; linarith [hlt k]⟩
  -- L1 : restrict to the base cube where χ = 1 and Eu = u
  have hwu : (fun x => χ x * Eu.toFun x) =ᵐ[volume.restrict (Box z hi)] u.toFun := by
    filter_upwards [ae_restrict_mem (isOpen_Box z hi).measurableSet, Ext.toFun_ae]
      with x hxU hEux
    rw [hχ_one x hxU, one_mul, hEux]
  have hL1 : eLpNorm u.toFun (twoStar (m + 1)) (volume.restrict (Box z hi))
      ≤ eLpNorm w.toFun (twoStar (m + 1)) (volume.restrict (Box3 z hi)) := by
    rw [show w.toFun = fun x => χ x * Eu.toFun x from hw_toFun, ← eLpNorm_congr_ae hwu]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hBox_sub le_rfl)
  -- L2 : Fatou along an a.e.-convergent subsequence
  have htim : TendstoInMeasure (volume.restrict (Box3 z hi)) (fun k => ψ k) Filter.atTop w.toFun :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun k => (w.approx_smooth k).continuous.aestronglyMeasurable)
      w.toH1Function.memL2.aestronglyMeasurable w.tendsto_approx
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := htim.exists_seq_tendsto_ae
  have hL2 : eLpNorm w.toFun (twoStar (m + 1)) (volume.restrict (Box3 z hi))
      ≤ Filter.liminf (fun j => a (σ j)) Filter.atTop :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun j => (w.approx_smooth (σ j)).continuous.aestronglyMeasurable) w.toFun hσ_ae
  -- L3 : liminf (a ∘ σ) ≤ binf
  have hbσ : Filter.Tendsto (fun j => b (σ j)) Filter.atTop (nhds binf) :=
    hb_tend.comp (hσ_mono.tendsto_atTop)
  have hL3 : Filter.liminf (fun j => a (σ j)) Filter.atTop ≤ binf := by
    calc Filter.liminf (fun j => a (σ j)) Filter.atTop
        ≤ Filter.liminf (fun j => b (σ j)) Filter.atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall fun j => hab (σ j))
      _ = binf := hbσ.liminf_eq
  -- L4 : bound each coordinate weak gradient of χ·Eu
  have hb2 : ∀ i, eLpNorm (fun x => Eu.toFun x * (fderiv ℝ χ x) (basisVec i)) 2
      (volume.restrict (Box3 z hi))
      ≤ ENNReal.ofReal (32 / L) * eLpNorm Eu.toFun 2 (volume.restrict (Box3 z hi)) := by
    intro i
    refine le_trans (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_))
      (le_trans (eLpNorm_const_smul_le (c := (32 / L : ℝ)) (f := Eu.toFun)) (le_of_eq ?_))
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul,
        Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 32 / L)]
      calc ‖Eu.toFun x‖ * ‖(fderiv ℝ χ x) (basisVec i)‖
          ≤ ‖Eu.toFun x‖ * (32 / L) :=
            mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hχ_deriv x i) (norm_nonneg _)
        _ = 32 / L * ‖Eu.toFun x‖ := by ring
    · congr 1
      rw [Real.enorm_eq_ofReal (by positivity)]
  have hwgrad_bound : ∀ i, eLpNorm (fun x => w.grad x i) 2 (volume.restrict (Box3 z hi))
      ≤ Cd * eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box z hi))
        + ENNReal.ofReal (32 / L) * (Cd * eLpNorm u.toFun 2 (volume.restrict (Box z hi))) := by
    intro i
    rw [eLpNorm_congr_ae (hgrad_ae i),
      show (fun x => wH1.grad x i)
        = (fun x => χ x * Eu.grad x i) + fun x => Eu.toFun x * (fderiv ℝ χ x) (basisVec i) from by
        funext x; rw [Pi.add_apply, hwH1_grad x i]]
    have haesm1 : AEStronglyMeasurable (fun x => χ x * Eu.grad x i) (volume.restrict (Box3 z hi)) :=
      hχ_smooth.continuous.aestronglyMeasurable.mul (Eu.gradMemL2 i).aestronglyMeasurable
    have haesm2 : AEStronglyMeasurable (fun x => Eu.toFun x * (fderiv ℝ χ x) (basisVec i))
        (volume.restrict (Box3 z hi)) :=
      Eu.memL2.aestronglyMeasurable.mul
        (((hχ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)
    refine (eLpNorm_add_le haesm1 haesm2 (by norm_num)).trans (add_le_add ?_ ?_)
    · refine le_trans (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_))
        (Ext.grad_eLpNorm_le i)
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hχ_le1 x)
    · exact (hb2 i).trans (mul_le_mul_right Ext.eLpNorm_le _)
  -- L4 assembled
  have hL4 : binf ≤ (C0 : ℝ≥0∞)
      * ((∑ i, eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box z hi)))
          + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun 2 (volume.restrict (Box z hi))) := by
    have hsum : ∑ i, eLpNorm (fun x => w.grad x i) 2 (volume.restrict (Box3 z hi))
        ≤ Cd * (∑ i, eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box z hi)))
          + ((m + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (32 / L)
              * (Cd * eLpNorm u.toFun 2 (volume.restrict (Box z hi)))) := by
      refine (Finset.sum_le_sum fun i _ => hwgrad_bound i).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hofReal : ENNReal.ofReal (32 / L) = ((32 : ℕ) : ℝ≥0∞) * ENNReal.ofReal L⁻¹ := by
      rw [show (32 : ℝ) / L = 32 * L⁻¹ by ring, ENNReal.ofReal_mul (by norm_num)]
      norm_num
    have hN1 : (1 : ℝ≥0∞) ≤ ((((m + 1) * 32 : ℕ)) : ℝ≥0∞) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [hbinf]
    refine (mul_le_mul_right hsum Cgns).trans ?_
    rw [hofReal, hC0]
    simp only [mul_add]
    refine add_le_add ?_ (le_of_eq ?_)
    · rw [show Cgns * (Cd * ∑ i, eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box z hi)))
          = (Cgns * Cd) * ∑ i, eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box z hi)) from by
        ring]
      exact mul_le_mul_left (le_mul_of_one_le_right' hN1) _
    · push_cast; ring
  -- combine
  have hmain : eLpNorm u.toFun (twoStar (m + 1)) (volume.restrict (Box z hi))
      ≤ (C0 : ℝ≥0∞)
        * ((∑ i, eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box z hi)))
            + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun 2 (volume.restrict (Box z hi))) :=
    hL1.trans (hL2.trans (hL3.trans hL4))
  have hC0le : (C0 : ℝ≥0∞) ≤ (↑(C0.toNNReal + 1) : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hC0_lt.ne, ENNReal.coe_one]
    exact le_self_add
  exact hmain.trans (mul_le_mul_left hC0le _)

end

end Homogenization
