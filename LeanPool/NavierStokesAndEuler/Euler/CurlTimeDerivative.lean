/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Local mixed-derivative commutation for the ordinary spatial curl. -/

@[expose] public section

noncomputable section

open Set Filter EulerSmoothLimit EulerMeanBoundary EulerMeanCutoffCurl
open scoped ContDiff Topology

namespace Euler.ComparatorBridge

/-- The ordinary derivative of a spatial slice is the spatial restriction of
its joint derivative. -/
theorem fderiv_spatial_slice {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ u (t, x)) :
    fderiv ℝ (fun y => u (t, y)) x =
      (fderiv ℝ u (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have h := hu.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  rw [show (fun y => u (t, y)) = u ∘ (fun y => (t, y)) from rfl, h.fderiv]
  congr 1

/-- The ordinary derivative of a time slice is the time direction of the
joint derivative. -/
theorem deriv_time_slice {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ u (t, x)) :
    deriv (fun r => u (r, x)) t = fderiv ℝ u (t, x) (1, 0) := by
  have h := hu.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simpa only [Function.comp_def, id_eq] using h.deriv

/-- Mixed differentiation commutes using only local joint `C²` regularity. -/
theorem spatial_fderiv_hasDerivAt {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ 2 u (t, x)) :
    HasDerivAt (fun r => fderiv ℝ (fun y => u (r, y)) x)
      (fderiv ℝ (fun y => deriv (fun r => u (r, y)) t) x) t := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) (t, x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : ∀ᶠ z in 𝓝 (t, x), DifferentiableAt ℝ u z := by
    filter_upwards [(hu.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num)]
      with z hz
    exact hz.differentiableAt (by norm_num)
  have htime := hdu.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hmatrix := htime.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ Space))
  have hspatial := hdu.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have hvelocity := hspatial.clm_apply (hasFDerivAt_const (1, (0 : Space)) x)
  have heq : (fun y => deriv (fun r => u (r, y)) t) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u (t, y) (1, 0)) := by
    filter_upwards [((continuous_const.prodMk continuous_id).tendsto x).eventually hnear]
      with y hy
    exact deriv_time_slice hy
  have hvelocity' := hvelocity.congr_of_eventuallyEq heq
  have hderiv : fderiv ℝ (fun y => deriv (fun r => u (r, y)) t) x =
      ((fderiv ℝ (fderiv ℝ u) (t, x)) (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space) := by
    rw [hvelocity'.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    simpa using hu.isSymmSndFDerivAt (by norm_num) (0, v) (1, 0)
  rw [hderiv]
  have hmatrix' : HasDerivAt (fun r => (fderiv ℝ u (r, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space))
      (((fderiv ℝ (fderiv ℝ u) (t, x)) (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) t := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_zero, add_zero] using hmatrix
  apply hmatrix'.congr_of_eventuallyEq
  filter_upwards [((continuous_id.prodMk continuous_const).tendsto t).eventually hnear]
    with r hr
  exact fderiv_spatial_slice hr

/-- The derivative in time is differentiable in space under local `C²`
regularity. -/
theorem time_deriv_differentiableAt {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ 2 u (t, x)) :
    DifferentiableAt ℝ (fun y => deriv (fun r => u (r, y)) t) x := by
  have hswap : ContDiffAt ℝ 2 (fun z : Space × ℝ => u (z.2, z.1)) (x, t) :=
    hu.comp (x, t) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hf : ContDiffAt ℝ 1 (fun y => fderiv ℝ (fun r => u (r, y)) t) x :=
    hswap.fderiv contDiffAt_const (by norm_num)
  exact (hf.clm_apply contDiffAt_const).differentiableAt (by norm_num)

/-- The continuous linear coordinate antisymmetrization defining curl. -/
def curlMatrixCLM : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (show (Space →L[ℝ] Space) →ₗ[ℝ] Space from
    { toFun := curlMatrix
      map_add' := curlMatrix_add
      map_smul' := curlMatrix_smul }).toContinuousLinearMap

@[simp] theorem curlMatrixCLM_apply (A : Space →L[ℝ] Space) :
    curlMatrixCLM A = curlMatrix A := rfl

/-- Spatial curl commutes with ordinary time differentiation at each point
of local joint `C²` regularity. -/
theorem vectorCurl_hasDerivAt {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ 2 u (t, x)) :
    HasDerivAt (fun r => vectorCurl (fun y => u (r, y)) x)
      (vectorCurl (fun y => deriv (fun r => u (r, y)) t) x) t := by
  have hc := curlMatrixCLM.hasFDerivAt.comp_hasDerivAt t
    (spatial_fderiv_hasDerivAt hu)
  rw [vectorCurl_eq_matrix _ x (time_deriv_differentiableAt hu)]
  apply hc.congr_of_eventuallyEq
  have hnear : ∀ᶠ z in 𝓝 (t, x), DifferentiableAt ℝ u z := by
    filter_upwards [(hu.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num)]
      with z hz
    exact hz.differentiableAt (by norm_num)
  filter_upwards [((continuous_id.prodMk continuous_const).tendsto t).eventually hnear]
    with r hr
  exact vectorCurl_eq_matrix _ x (hr.comp x (differentiableAt_const r |>.prodMk
      differentiableAt_id))

/-- Joint spatial curl retains local joint smoothness. -/
theorem joint_vectorCurl_contDiffAt {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ ∞ u (t, x)) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => vectorCurl (fun y => u (z.1, y)) z.2)
      (t, x) := by
  have hd : ContDiffAt ℝ ∞ (fun z => (fderiv ℝ u z).comp
      (ContinuousLinearMap.inr ℝ ℝ Space)) (t, x) :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const
  have hc := curlMatrixCLM.contDiff.contDiffAt.comp (t, x) hd
  apply hc.congr_of_eventuallyEq
  have hnear : ∀ᶠ z in 𝓝 (t, x), DifferentiableAt ℝ u z := by
    filter_upwards [(hu.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)]
      with z hz
    exact hz.differentiableAt (by norm_num)
  filter_upwards [hnear] with z hz
  have hspace : DifferentiableAt ℝ (fun y => u (z.1, y)) z.2 := by
    simpa only [Function.comp_def, id_eq] using
      hz.comp z.2 (differentiableAt_const z.1 |>.prodMk differentiableAt_id)
  rw [vectorCurl_eq_matrix _ z.2 hspace, fderiv_spatial_slice hz]
  rfl

/-- Joint differentiation along a spacetime direction splits into the curl
of the time derivative and spatial transport of the curl. -/
theorem joint_vectorCurl_fderiv_apply {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ ∞ u (t, x)) (a : Space) :
    fderiv ℝ (fun z : ℝ × Space => vectorCurl (fun y => u (z.1, y)) z.2)
      (t, x) (1, a) =
      vectorCurl (fun y => deriv (fun r => u (r, y)) t) x +
        fderiv ℝ (vectorCurl (fun y => u (t, y))) x a := by
  let w : ℝ × Space → Space := fun z => vectorCurl (fun y => u (z.1, y)) z.2
  have hw : DifferentiableAt ℝ w (t, x) :=
    (joint_vectorCurl_contDiffAt hu).differentiableAt (by simp)
  have ht : fderiv ℝ w (t, x) (1, 0) =
      vectorCurl (fun y => deriv (fun r => u (r, y)) t) x :=
    (deriv_time_slice hw).symm.trans
      (vectorCurl_hasDerivAt (hu.of_le (by simp))).deriv
  have hx := congrArg (fun L : Space →L[ℝ] Space => L a) (fderiv_spatial_slice hw)
  change fderiv ℝ w (t, x) (1, a) = _
  rw [show ((1 : ℝ), a) = (1, (0 : Space)) + (0, a) by simp, map_add, ht]
  congr 1
  exact hx.symm

/-- Spatial differentiation preserves joint smoothness on an arbitrary time
set, including its boundary. The spatial domain is the entire Euclidean space. -/
theorem joint_spatial_fderiv_contDiffOn {u : ℝ × Space → Space} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun y => u (z.1, y)) z.2)
      (S ×ˢ (univ : Set Space)) := by
  intro z hz
  have hf : ContDiffWithinAt ℝ ∞
      (fun q : (ℝ × Space) × Space => u (q.1.1, q.2))
      ((S ×ˢ (univ : Set Space)) ×ˢ (univ : Set Space)) (z, z.2) := by
    apply (hu z hz).comp (z, z.2)
      (contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd)
    intro q hq
    exact ⟨hq.1.1, mem_univ _⟩
  have hf' := ContDiffWithinAt.fderivWithin
    (𝕜 := ℝ) (n := ∞) (m := ∞)
    (f := fun (z : ℝ × Space) (y : Space) => u (z.1, y))
    (s := S ×ˢ (univ : Set Space)) (t := (univ : Set Space))
    (g := fun z : ℝ × Space => z.2)
    hf contDiffWithinAt_snd uniqueDiffOn_univ (by simp) hz
    (by intro z hz; exact mem_univ _)
  simpa only [fderivWithin_univ] using hf'

/-- Spatial curl preserves joint smoothness on a time set, including its
boundary, because spatial differentiation is always on the full space. -/
theorem joint_vectorCurl_contDiffOn {u : ℝ × Space → Space} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => vectorCurl (fun y => u (z.1, y)) z.2)
      (S ×ˢ (univ : Set Space)) := by
  apply (curlMatrixCLM.contDiff.comp_contDiffOn (joint_spatial_fderiv_contDiffOn hu)).congr
  intro z hz
  have hspace : ContDiff ℝ ∞ (fun y => u (z.1, y)) :=
    hu.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun y => ⟨hz.1, mem_univ y⟩)
  exact vectorCurl_eq_matrix _ z.2 (hspace.differentiable (by simp) z.2)

end Euler.ComparatorBridge
