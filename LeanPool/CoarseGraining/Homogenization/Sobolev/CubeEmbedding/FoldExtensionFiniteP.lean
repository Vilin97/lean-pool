/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.Extension
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.FoldNormFiniteP
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.ConvexApproxTendsto
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Finite-`p` even-fold extension on an axis box

The `W^{1,p}` companion to `foldExtension`.  Smooth convex-domain
approximants are cut off outside the tripled box, transported by the fold, and
closed using finite-exponent Hölder pairings against compactly supported test
functions.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {d : ℕ}

private theorem finiteLpExponent_ne_zero' (p : FiniteLpExponent) : p.exponent ≠ 0 :=
  (zero_lt_one.trans p.one_lt).ne'

private theorem tendsto_eLpNorm_convexApproxSmoothW1p {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (p : FiniteLpExponent)
    (u : W1pFunction U p.exponent) {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto
      (fun n => eLpNorm
        (fun x => (W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr n).toFun x -
          u.toFun x) p.exponent (volume.restrict U))
      atTop (nhds 0) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  let ψ : ℕ → W1pFunction U p.exponent :=
    W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hevent_lt_one : ∀ᶠ n : ℕ in atTop, unitConvexApproxScale n < 1 :=
    (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      fun _ hn => hn)
  have hraw :
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun x => convexApproxSmoothing ρ u.toFun x0 r (unitConvexApproxScale n) x -
            u.toFun x) p.exponent (volume.restrict U))
        atTop (nhds 0) := by
    simpa [ρ, volumeMeasureOn] using
      (tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ p.one_lt.le p.lt_top.ne u.memLp hball hr
        tendsto_unitConvexApproxScale_zero
        (Eventually.of_forall W1pFunction.unitConvexApproxScale_pos) hevent_lt_one)
  have hrep :
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun x => convexApproxSmoothRepresentative U ρ u.toFun x0 r
              (unitConvexApproxScale n) x - u.toFun x)
          p.exponent (volume.restrict U))
        atTop (nhds 0) := by
    refine hraw.congr' ?_
    filter_upwards [hevent_lt_one] with n hε_lt_one
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := u.toFun) hU hρ hx hball hr
      (W1pFunction.unitConvexApproxScale_pos n) hε_lt_one]
  refine hrep.congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with x
  simp [ρ, W1pFunction.convexApproxSmoothW1p,
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    W1pFunction.ofContDiffOnIsSobolevRegularDomain]

private theorem tendsto_eLpNorm_grad_convexApproxSmoothW1p {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (p : FiniteLpExponent)
    (u : W1pFunction U p.exponent) {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (i : Fin d) :
    Tendsto
      (fun n => eLpNorm
        (fun x => (W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr n).grad x i -
          u.grad x i) p.exponent (volume.restrict U))
      atTop (nhds 0) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  let ψ : ℕ → W1pFunction U p.exponent :=
    W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hevent_lt_one : ∀ᶠ n : ℕ in atTop, unitConvexApproxScale n < 1 :=
    (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      fun _ hn => hn)
  have hraw :
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun x => (1 - unitConvexApproxScale n) *
              convexApproxSmoothing ρ (fun y => u.grad y i) x0 r
                (unitConvexApproxScale n) x - u.grad x i)
          p.exponent (volume.restrict U))
        atTop (nhds 0) := by
    simpa [ρ, volumeMeasureOn] using
      (tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ p.one_lt.le p.lt_top.ne (u.grad_memLp i) hball hr
        tendsto_unitConvexApproxScale_zero
        (Eventually.of_forall W1pFunction.unitConvexApproxScale_pos) hevent_lt_one)
  have hrep :
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun x => (fderiv ℝ
              (convexApproxSmoothRepresentative U ρ u.toFun x0 r
                (unitConvexApproxScale n)) x) (basisVec i) - u.grad x i)
          p.exponent (volume.restrict U))
        atTop (nhds 0) := by
    refine hraw.congr' ?_
    filter_upwards [hevent_lt_one] with n hε_lt_one
    apply eLpNorm_congr_ae
    have hbridge := ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
      (U := U) (ρ := ρ) (u := u.toFun) (gi := fun y => u.grad y i)
      (i := i) (p := p.exponent) hU hρ p.one_lt.le u.memLp (u.grad_memLp i)
      (u.hasWeakPartialDerivOn i) hball hr
      (W1pFunction.unitConvexApproxScale_pos n) hε_lt_one
    filter_upwards [hbridge, ae_restrict_mem hU.isOpen.measurableSet] with x hxbridge hxU
    rw [hxbridge]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := fun y => u.grad y i) hU hρ hxU hball hr
      (W1pFunction.unitConvexApproxScale_pos n) hε_lt_one]
  refine hrep.congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with x
  simp [ρ, W1pFunction.convexApproxSmoothW1p,
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    W1pFunction.ofContDiffOnIsSobolevRegularDomain]

private theorem tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp
    {U : Set (Vec d)} (p : FiniteLpExponent) {h : Vec d → ℝ}
    {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hh : MemLp h p.conjugate.exponent (volume.restrict U))
    (hf : ∀ n, MemLp (f n) p.exponent (volume.restrict U))
    (hg : MemLp g p.exponent (volume.restrict U))
    (htend : Tendsto
      (fun n => eLpNorm (fun x => f n x - g x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in U, f n x * h x ∂volume)
      atTop (nhds (∫ x in U, g x * h x ∂volume)) := by
  let : ENNReal.HolderConjugate p.exponent p.conjugate.exponent := p.holderConjugate
  let : ENNReal.HolderConjugate p.conjugate.exponent p.exponent := inferInstance
  set μ : Measure (Vec d) := volume.restrict U with hμ
  have hfh_int : ∀ n, Integrable (fun x => f n x * h x) μ := by
    intro n
    simpa [μ, mul_comm] using
      (memLp_one_iff_integrable.mp (hh.mul' (hf n)))
  have hgh_int : Integrable (fun x => g x * h x) μ := by
    simpa [μ, mul_comm] using (memLp_one_iff_integrable.mp (hh.mul' hg))
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff_eq : ∀ n,
      (∫ x, f n x * h x ∂μ) - (∫ x, g x * h x ∂μ)
        = ∫ x, (f n x - g x) * h x ∂μ := by
    intro n
    rw [← integral_sub (hfh_int n) hgh_int]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  set B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => f n x - g x) p.exponent μ *
      eLpNorm h p.conjugate.exponent μ with hB
  have hBtend : Tendsto (fun n => (B n).toReal) atTop (nhds 0) := by
    have hprod : Tendsto B atTop (nhds (0 * eLpNorm h p.conjugate.exponent μ)) := by
      refine ENNReal.Tendsto.mul (by simpa [μ] using htend) (Or.inr hh.2.ne)
        tendsto_const_nhds (Or.inr (by simp))
    rw [zero_mul] at hprod
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprod
    simpa using! hreal
  refine squeeze_zero_norm ?_ hBtend
  intro n
  rw [hdiff_eq n]
  have hbound : ∀ᵐ x ∂μ,
      ‖(f n x - g x) * h x‖₊ ≤ 1 * ‖f n x - g x‖₊ * ‖h x‖₊ :=
    Eventually.of_forall fun x => by rw [nnnorm_mul]; simp
  have hHolder : eLpNorm (fun x => (f n x - g x) * h x) 1 μ ≤ B n := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p.exponent) (q := p.conjugate.exponent) (r := 1)
      ((hf n).sub hg).1 hh.1 (fun a b => a * b) 1 hbound
    simpa [B] using! h
  calc
    ‖∫ x, (f n x - g x) * h x ∂μ‖
      ≤ (∫⁻ x, ENNReal.ofReal ‖(f n x - g x) * h x‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (eLpNorm (fun x => (f n x - g x) * h x) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      simp_rw [ofReal_norm]
    _ ≤ (B n).toReal := by
      apply ENNReal.toReal_mono _ hHolder
      exact ENNReal.mul_ne_top ((hf n).sub hg).2.ne hh.2.ne

private theorem HasWeakPartialDerivOn.of_tendsto_eLpNorm_finiteLp
    {U : Set (Vec d)} (p : FiniteLpExponent) {i : Fin d}
    {u gi : Vec d → ℝ} {u_n g_n : ℕ → Vec d → ℝ}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hgi : MemLp gi p.exponent (volume.restrict U))
    (hu_n : ∀ n, MemLp (u_n n) p.exponent (volume.restrict U))
    (hg_n : ∀ n, MemLp (g_n n) p.exponent (volume.restrict U))
    (hweak : ∀ n, HasWeakPartialDerivOn U i (u_n n) (g_n n))
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_g : Tendsto
      (fun n => eLpNorm (fun x => g_n n x - gi x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    HasWeakPartialDerivOn U i u gi := by
  intro φ hφ hφ_compact hφ_sub
  have hDφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) p.conjugate.exponent
      (volume.restrict U) := by
    have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) := by
      apply HasCompactSupport.mono' (hφ_compact.fderiv ℝ)
      intro x hx
      apply subset_tsupport (fderiv ℝ φ)
      rw [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [h0]
      simp
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict U
  have hφmem : MemLp φ p.conjugate.exponent (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict U
  have hlhs := tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp p hDφ hu_n hu htend_u
  have hrhs := tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp p hφmem hg_n hgi htend_g
  have heq_n : ∀ n,
      (∫ x in U, u_n n x * (fderiv ℝ φ x) (basisVec i) ∂volume)
        = -(∫ x in U, g_n n x * φ x ∂volume) :=
    fun n => hweak n φ hφ hφ_compact hφ_sub
  have hlhs' : Tendsto
      (fun n => -(∫ x in U, g_n n x * φ x ∂volume))
      atTop (nhds (∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume)) := by
    refine hlhs.congr ?_
    intro n
    rw [heq_n n]
  exact tendsto_nhds_unique hlhs' hrhs.neg

private theorem HasWeakGradientOn.of_tendsto_eLpNorm_finiteLp
    {U : Set (Vec d)} (p : FiniteLpExponent)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {u_n : ℕ → Vec d → ℝ} {Du_n : ℕ → Vec d → Vec d}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hDu : GradMemLpOn U p.exponent Du)
    (hu_n : ∀ n, MemLp (u_n n) p.exponent (volume.restrict U))
    (hDu_n : ∀ n, GradMemLpOn U p.exponent (Du_n n))
    (hweak : ∀ n, HasWeakGradientOn U (u_n n) (Du_n n))
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_Du : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => Du_n n x i - Du x i) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    HasWeakGradientOn U u Du := by
  intro i
  exact HasWeakPartialDerivOn.of_tendsto_eLpNorm_finiteLp p hu (hDu i)
    hu_n (fun n => hDu_n n i) (fun n => hweak n i) htend_u (htend_Du i)

/-- Data of the finite-`p` even-fold extension. -/
structure FoldExtensionFiniteP (lo hi : Vec d) (p : FiniteLpExponent)
    (u : W1pFunction (Box lo hi) p.exponent) where
  Eu : W1pFunction (Box3 lo hi) p.exponent
  toFun_ae : Eu.toFun =ᵐ[volume.restrict (Box lo hi)] u.toFun
  grad_ae : ∀ i, (fun x => Eu.grad x i) =ᵐ[volume.restrict (Box lo hi)]
    fun x => u.grad x i
  eLpNorm_le : eLpNorm Eu.toFun p.exponent (volume.restrict (Box3 lo hi))
    ≤ ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
      eLpNorm u.toFun p.exponent (volume.restrict (Box lo hi))
  grad_eLpNorm_le : ∀ i,
    eLpNorm (fun x => Eu.grad x i) p.exponent (volume.restrict (Box3 lo hi))
      ≤ ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box lo hi))

private theorem finiteLpExponent_toReal_pos' (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (finiteLpExponent_ne_zero' p) p.lt_top.ne

/-- The finite-`p` even-fold extension of a Sobolev function on an open axis
box. -/
def foldExtensionFiniteP {m : ℕ} (lo hi : Vec (m + 1)) (hlt : ∀ k, lo k < hi k)
    (p : FiniteLpExponent) (u : W1pFunction (Box lo hi) p.exponent) :
    FoldExtensionFiniteP lo hi p u := by
  classical
  set lo3 : Vec (m + 1) := fun k => 2 * lo k - hi k with hlo3
  set hi3 : Vec (m + 1) := fun k => 2 * hi k - lo k with hhi3
  have hlt3 : ∀ k, lo3 k < hi3 k := fun k => by
    simp only [hlo3, hhi3]
    linarith [hlt k]
  have hbox3 : Box3 lo hi = Box lo3 hi3 := rfl
  have hU : IsOpenBoundedConvexDomain (Box lo hi) := isOpenBoundedConvexDomain_Box lo hi
  have hFold_cont : Continuous (Fold lo hi) := continuous_Fold lo hi (fun k => (hlt k).le)
  have hFold_meas : Measurable (Fold lo hi) := hFold_cont.measurable
  set Cd : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal) with hCd
  have hCd_lt : Cd < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg
      (one_div_nonneg.mpr (finiteLpExponent_toReal_pos' p).le)
      (ENNReal.pow_ne_top (by simp))
  have hg_asm : AEStronglyMeasurable u.toFun (volume.restrict (Box lo hi)) :=
    u.memLp.aestronglyMeasurable
  set g : Vec (m + 1) → ℝ := hg_asm.mk u.toFun with hg_def
  have hg_meas : Measurable g := hg_asm.stronglyMeasurable_mk.measurable
  have hg_ae : u.toFun =ᵐ[volume.restrict (Box lo hi)] g := hg_asm.ae_eq_mk
  have hgi_asm : ∀ i, AEStronglyMeasurable (fun x => u.grad x i)
      (volume.restrict (Box lo hi)) := fun i => (u.grad_memLp i).aestronglyMeasurable
  set gi : Fin (m + 1) → Vec (m + 1) → ℝ :=
    fun i => (hgi_asm i).mk (fun x => u.grad x i) with hgi_def
  have hgi_meas : ∀ i, Measurable (gi i) :=
    fun i => (hgi_asm i).stronglyMeasurable_mk.measurable
  have hgi_ae : ∀ i, (fun x => u.grad x i) =ᵐ[volume.restrict (Box lo hi)] gi i :=
    fun i => (hgi_asm i).ae_eq_mk
  set x0 : Vec (m + 1) := fun k => (lo k + hi k) / 2 with hx0
  set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun k => hi k - lo k) with hδ
  have hδ_pos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff Finset.univ_nonempty]
    exact fun k _ => by linarith [hlt k]
  set r : ℝ := δ / 3 with hrdef
  have hr : 0 < r := by
    rw [hrdef]
    linarith
  have hball : Metric.closedBall x0 r ⊆ Box lo hi := by
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff hr.le] at hx
    refine Set.mem_univ_pi.2 fun k => ?_
    have hxk : dist (x k) (x0 k) ≤ r := hx k
    rw [Real.dist_eq, abs_le] at hxk
    have hmk : δ ≤ hi k - lo k := Finset.inf'_le _ (Finset.mem_univ k)
    simp only [hx0, hrdef] at hxk
    exact ⟨by nlinarith [hxk.1], by nlinarith [hxk.2]⟩
  set A : ℕ → W1pFunction (Box lo hi) p.exponent :=
    W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr with hA
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (A n).toFun := by
    intro n
    simp [A, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
    exact contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel) p.one_lt.le u.memLp hr
      (W1pFunction.unitConvexApproxScale_pos n)
  have hφ_grad : ∀ n x i, (A n).grad x i = fderiv ℝ ((A n).toFun) x (basisVec i) := by
    intro n x i
    simp [A, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
  set χ : Vec (m + 1) → ℝ := boxCutoff lo3 hi3 1 with hχ
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := boxCutoff_contDiff
  have hχ_cptsupp : HasCompactSupport χ := by
    apply HasCompactSupport.intro (K := Set.Icc (fun k => lo3 k - 1) (fun k => hi3 k + 1))
      isCompact_Icc
    intro x hx
    exact boxCutoff_eq_zero (by norm_num) hx
  have hχ_one : ∀ x ∈ Set.Icc lo3 hi3, χ x = 1 :=
    fun x hx => boxCutoff_eq_one (by norm_num) hx
  have hBox_Icc : ∀ x ∈ Box lo hi, x ∈ Set.Icc lo3 hi3 := by
    intro x hx
    have hx' := Set.mem_univ_pi.1 hx
    refine Set.mem_Icc.2 ⟨fun k => ?_, fun k => ?_⟩
    · have := (hx' k).1
      simp only [hlo3]
      linarith [hlt k]
    · have := (hx' k).2
      simp only [hhi3]
      linarith [hlt k]
  set wn : ℕ → Vec (m + 1) → ℝ := fun n x => χ x * (A n).toFun x with hwn
  have hw_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (wn n) :=
    fun n => hχ_smooth.mul (hφ_smooth n)
  have hw_cont : ∀ n, Continuous (wn n) := fun n => (hw_smooth n).continuous
  have hw_meas : ∀ n, Measurable (wn n) := fun n => (hw_cont n).measurable
  have hw_cptsupp : ∀ n, HasCompactSupport (wn n) := fun n => hχ_cptsupp.mul_right
  have hw_eq_φ : ∀ n, ∀ x ∈ Set.Icc lo3 hi3, wn n x = (A n).toFun x := by
    intro n x hx
    simp only [hwn, hχ_one x hx, one_mul]
  have hfderiv_eq : ∀ n, ∀ y ∈ Box lo hi,
      fderiv ℝ (wn n) y = fderiv ℝ ((A n).toFun) y := by
    intro n y hy
    have hy3 : y ∈ Box3 lo hi := by
      rw [hbox3]
      refine Set.mem_univ_pi.2 fun k => ?_
      have hyk := Set.mem_univ_pi.1 hy k
      exact ⟨by
        simp only [hlo3]
        linarith [hyk.1, hlt k], by
        simp only [hhi3]
        linarith [hyk.2, hlt k]⟩
    have hnbhd : Box3 lo hi ∈ 𝓝 y :=
      (by rw [hbox3]; exact isOpen_Box lo3 hi3 : IsOpen (Box3 lo hi)).mem_nhds hy3
    have heq : wn n =ᶠ[𝓝 y] (A n).toFun := by
      refine eventuallyEq_of_mem hnbhd fun x hx => ?_
      refine hw_eq_φ n x ?_
      rw [hbox3] at hx
      have hx' := Set.mem_univ_pi.1 hx
      exact Set.mem_Icc.2 ⟨fun k => (hx' k).1.le, fun k => (hx' k).2.le⟩
    exact heq.fderiv_eq
  have hEu_mem : MemLp (fun x => g (Fold lo hi x)) p.exponent
      (volume.restrict (Box3 lo hi)) := by
    refine ⟨(hg_meas.comp hFold_meas).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_foldComp_finiteLp p hg_meas lo hi hlt, ← eLpNorm_congr_ae hg_ae]
    exact ENNReal.mul_lt_top hCd_lt u.memLp.eLpNorm_lt_top
  have hEu_grad_mem : ∀ i, MemLp
      (fun x => gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)) p.exponent
      (volume.restrict (Box3 lo hi)) := by
    intro i
    refine ⟨(((hgi_meas i).comp hFold_meas).mul
      (measurable_foldSign_comp lo hi i)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt
      (eLpNorm_foldComp_mul_foldSign_le_finiteLp p (hgi_meas i) lo hi hlt i) ?_
    rw [← eLpNorm_congr_ae (hgi_ae i)]
    exact ENNReal.mul_lt_top hCd_lt (u.grad_memLp i).eLpNorm_lt_top
  have hEn_mem : ∀ n, MemLp (fun x => wn n (Fold lo hi x)) p.exponent
      (volume.restrict (Box3 lo hi)) := by
    intro n
    refine ⟨((hw_cont n).comp hFold_cont).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_foldComp_finiteLp p (hw_meas n) lo hi hlt]
    have hmem : MemLp (wn n) p.exponent (volume.restrict (Box lo hi)) :=
      ((hw_cont n).memLp_of_hasCompactSupport (hw_cptsupp n)).restrict _
    exact ENNReal.mul_lt_top hCd_lt hmem.eLpNorm_lt_top
  have hDEn_mem : ∀ n, GradMemLpOn (Box3 lo hi) p.exponent
      (fun x i => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
        foldSign (lo i) (hi i) (x i)) := by
    intro n i
    have hcont : Continuous (fun y => fderiv ℝ (wn n) y (basisVec i)) :=
      (((hw_smooth n).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 (wn n)).continuous_fderiv
        (by simp)).clm_apply continuous_const
    refine ⟨((hcont.measurable.comp hFold_meas).mul
      (measurable_foldSign_comp lo hi i)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt
      (eLpNorm_foldComp_mul_foldSign_le_finiteLp p hcont.measurable lo hi hlt i) ?_
    have hmem : MemLp (fun y => fderiv ℝ (wn n) y (basisVec i)) p.exponent
        (volume.restrict (Box lo hi)) :=
      (hcont.memLp_of_hasCompactSupport
        ((hw_cptsupp n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict _
    exact ENNReal.mul_lt_top hCd_lt hmem.eLpNorm_lt_top
  have hweak : ∀ n, HasWeakGradientOn (Box3 lo hi) (fun x => wn n (Fold lo hi x))
      (fun x i => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
        foldSign (lo i) (hi i) (x i)) := by
    intro n i
    have huniv := hasWeakPartialDerivOn_univ_foldComp
      ((hw_smooth n).of_le (by exact_mod_cast le_top)) (hw_cptsupp n) lo hi
      (fun k => (hlt k).le) i
    exact huniv.restrict (by rw [hbox3]; exact isOpen_Box lo3 hi3) (Set.subset_univ _)
  have htend_u : Tendsto (fun n => eLpNorm
      (fun x => wn n (Fold lo hi x) - g (Fold lo hi x)) p.exponent
        (volume.restrict (Box3 lo hi))) atTop (nhds 0) := by
    have heq : ∀ n, eLpNorm (fun x => wn n (Fold lo hi x) - g (Fold lo hi x)) p.exponent
        (volume.restrict (Box3 lo hi))
        = Cd * eLpNorm (fun x => (A n).toFun x - u.toFun x) p.exponent
          (volume.restrict (Box lo hi)) := by
      intro n
      rw [show (fun x => wn n (Fold lo hi x) - g (Fold lo hi x))
          = fun x => (wn n - g) (Fold lo hi x) from rfl,
        eLpNorm_foldComp_finiteLp p ((hw_meas n).sub hg_meas) lo hi hlt]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hg_ae] with x hxU hgx
      have hχ1 : χ x = 1 := hχ_one x (hBox_Icc x hxU)
      simp only [Pi.sub_apply, hwn, hχ1, one_mul, hgx]
    have hmul : Tendsto
        (fun n => Cd * eLpNorm (fun x => (A n).toFun x - u.toFun x) p.exponent
          (volume.restrict (Box lo hi))) atTop (nhds (Cd * 0)) :=
      ENNReal.Tendsto.const_mul
        (tendsto_eLpNorm_convexApproxSmoothW1p hU p u hball hr) (Or.inr hCd_lt.ne)
    rw [mul_zero] at hmul
    exact hmul.congr (fun n => (heq n).symm)
  have htend_Du : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
          foldSign (lo i) (hi i) (x i) -
        gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
      p.exponent (volume.restrict (Box3 lo hi))) atTop (nhds 0) := by
    intro i
    have hbound : ∀ n, eLpNorm
        (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
            foldSign (lo i) (hi i) (x i) -
          gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
        p.exponent (volume.restrict (Box3 lo hi))
        ≤ Cd * eLpNorm (fun x => (A n).grad x i - u.grad x i) p.exponent
          (volume.restrict (Box lo hi)) := by
      intro n
      rw [show (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
              foldSign (lo i) (hi i) (x i) -
            gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
          = fun x => (fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) -
              gi i (Fold lo hi x)) * foldSign (lo i) (hi i) (x i) by
              funext x
              ring]
      calc
        eLpNorm (fun x => (fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) -
            gi i (Fold lo hi x)) * foldSign (lo i) (hi i) (x i)) p.exponent
            (volume.restrict (Box3 lo hi))
            ≤ Cd * eLpNorm (fun y => fderiv ℝ (wn n) y (basisVec i) - gi i y)
              p.exponent (volume.restrict (Box lo hi)) :=
              eLpNorm_foldComp_mul_foldSign_le_finiteLp p
                ((((hw_smooth n).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 (wn n)).continuous_fderiv
                  (by simp)).clm_apply continuous_const |>.measurable.sub (hgi_meas i)) lo hi hlt i
        _ = Cd * eLpNorm (fun x => (A n).grad x i - u.grad x i) p.exponent
              (volume.restrict (Box lo hi)) := by
              congr 1
              refine eLpNorm_congr_ae ?_
              filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hgi_ae i]
                with x hxU hgix
              rw [hfderiv_eq n x hxU, ← hφ_grad n x i, ← hgix]
    have hrhs : Tendsto
        (fun n => Cd * eLpNorm (fun x => (A n).grad x i - u.grad x i) p.exponent
          (volume.restrict (Box lo hi))) atTop (nhds 0) := by
      have hmul := ENNReal.Tendsto.const_mul
        (tendsto_eLpNorm_grad_convexApproxSmoothW1p hU p u hball hr i)
        (Or.inr hCd_lt.ne)
      simpa using hmul
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun n => zero_le) hbound
  exact
    { Eu :=
        { toFun := fun x => g (Fold lo hi x)
          grad := fun x i => gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)
          memLp := hEu_mem
          gradMemLp := hEu_grad_mem
          hasWeakGradient := HasWeakGradientOn.of_tendsto_eLpNorm_finiteLp p
            hEu_mem hEu_grad_mem hEn_mem hDEn_mem hweak htend_u htend_Du }
      toFun_ae := by
        filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hg_ae] with x hxU hgx
        have hfold : Fold lo hi x = x :=
          Fold_of_mem fun k => ⟨(Set.mem_univ_pi.1 hxU k).1.le,
            (Set.mem_univ_pi.1 hxU k).2.le⟩
        show g (Fold lo hi x) = u.toFun x
        rw [hfold, hgx]
      grad_ae := fun i => by
        filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hgi_ae i]
          with x hxU hgix
        have hxk := Set.mem_univ_pi.1 hxU i
        have hfold : Fold lo hi x = x :=
          Fold_of_mem fun k => ⟨(Set.mem_univ_pi.1 hxU k).1.le,
            (Set.mem_univ_pi.1 hxU k).2.le⟩
        have hsign : foldSign (lo i) (hi i) (x i) = 1 := by
          unfold foldSign
          rw [if_neg (not_lt.mpr hxk.1.le), if_neg (not_lt.mpr hxk.2.le)]
        show gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i) = u.grad x i
        rw [hfold, hsign, mul_one, hgix]
      eLpNorm_le := le_of_eq (by
        rw [eLpNorm_foldComp_finiteLp p hg_meas lo hi hlt, ← eLpNorm_congr_ae hg_ae])
      grad_eLpNorm_le := fun i => by
        calc
          eLpNorm (fun x => gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
              p.exponent (volume.restrict (Box3 lo hi))
              ≤ ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal) *
                eLpNorm (gi i) p.exponent (volume.restrict (Box lo hi)) :=
                eLpNorm_foldComp_mul_foldSign_le_finiteLp p (hgi_meas i) lo hi hlt i
          _ = ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal) *
                eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box lo hi)) := by
                congr 1
                rw [← eLpNorm_congr_ae (hgi_ae i)] }

end

end Homogenization
