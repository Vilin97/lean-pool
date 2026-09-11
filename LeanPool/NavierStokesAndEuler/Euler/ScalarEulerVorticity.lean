/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
import LeanPool.NavierStokesAndEuler.Euler.CurlTimeDerivative
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
import LeanPool.NavierStokesAndEuler.Euler.MeanScalarProductDerivatives
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities

/-! The ordinary vorticity equation of a Comparator solution follows from
its scalar-pressure, unforced Euler equation. -/

section

/-! The ordinary curl identity for the Euler convection term on ℝ³. -/

@[expose] public section

noncomputable section

namespace EulerComparatorCurlTransport

open InnerProductSpace EulerSmoothLimit EulerVectorCalculus EulerMeanCutoffCurl
  EulerMeanHarmonic EulerMeanVectorIdentities EulerMeanBoundary
open scoped ContDiff

theorem fderiv_apply_coordinate_sum (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (x v : Space) (i : Fin 3) :
    (fderiv ℝ f x v) i =
      ∑ j : Fin 3, v j * partialDerivative (fun y => f y i) j x := by
  rw [← fderiv_coordinate f x (hf.differentiable (by simp)).differentiableAt i v]
  have hre : ∑ j : Fin 3, v j • (EuclideanSpace.single j 1 : Space) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  calc
    _ = fderiv ℝ (fun y => f y i) x
        (∑ j : Fin 3, v j • EuclideanSpace.single j 1) :=
      congrArg (fderiv ℝ (fun y => f y i) x) hre.symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, partialDerivative]

/-- Curl of the material convection term, including the compressible correction. -/
theorem vectorCurl_convection (u : Space → Space) (hu : ContDiff ℝ ∞ u) (x : Space) :
    vectorCurl (fun y => fderiv ℝ u y (u y)) x =
      fderiv ℝ (vectorCurl u) x (u x) - fderiv ℝ u x (vectorCurl u x) +
        divergence u x • vectorCurl u x := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun y => u y i) := (contDiff_piLp 2).mp hu i
  have hp (i j : Fin 3) : ContDiff ℝ ∞ (partialDerivative (fun y => u y i) j) :=
    contDiff_partialDerivative _ (hc i) j
  have hconv (i : Fin 3) :
      (fun y => (fderiv ℝ u y (u y)) i) =
        fun y => ∑ j : Fin 3, u y j * partialDerivative (fun z => u z i) j y := by
    funext y
    exact fderiv_apply_coordinate_sum u hu y (u y) i
  have hconvpart (i k : Fin 3) :
      partialDerivative (fun y => (fderiv ℝ u y (u y)) i) k x =
        ∑ j : Fin 3,
          (partialDerivative (fun y => u y i) j x *
            partialDerivative (fun y => u y j) k x +
          u x j * partialDerivative (partialDerivative (fun y => u y i) j) k x) := by
    rw [hconv i, partialDerivative_sum _ (fun j => (hc j).mul (hp i j))]
    apply Finset.sum_congr rfl
    intro j _
    exact EulerMeanHarmonic.partialDerivative_mul
      ((hc j).differentiable (by simp)).differentiableAt
      ((hp i j).differentiable (by simp)).differentiableAt k
  have hcurlpart (i k : Fin 3) :
      partialDerivative (fun y => vectorCurl u y i) k x =
        partialDerivative (partialDerivative (fun y => u y (i+2)) (i+1)) k x -
        partialDerivative (partialDerivative (fun y => u y (i+1)) (i+2)) k x := by
    simp only [vectorCurl, curl_apply]
    exact EulerMeanVectorIdentities.partialDerivative_sub _ _ (hp _ _) (hp _ _) k x
  have hcomm01 (a : Fin 3) :
      partialDerivative (partialDerivative (fun y => u y a) 0) 1 x =
        partialDerivative (partialDerivative (fun y => u y a) 1) 0 x :=
    partialDerivative_comm _ ((hc a).of_le (by simp)) 0 1 x
  have hcomm02 (a : Fin 3) :
      partialDerivative (partialDerivative (fun y => u y a) 0) 2 x =
        partialDerivative (partialDerivative (fun y => u y a) 2) 0 x :=
    partialDerivative_comm _ ((hc a).of_le (by simp)) 0 2 x
  have hcomm12 (a : Fin 3) :
      partialDerivative (partialDerivative (fun y => u y a) 1) 2 x =
        partialDerivative (partialDerivative (fun y => u y a) 2) 1 x :=
    partialDerivative_comm _ ((hc a).of_le (by simp)) 1 2 x
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [fderiv_apply_coordinate_sum (vectorCurl u) (vectorCurl_smooth u hu) x (u x) i,
    fderiv_apply_coordinate_sum u hu x (vectorCurl u x) i]
  simp only [hcurlpart, divergence_coordinate_sum u hu]
  conv_lhs => simp only [vectorCurl, curl_apply]
  rw [hconvpart, hconvpart]
  simp only [vectorCurl, curl_apply]
  fin_cases i <;>
    norm_num [Fin.sum_univ_three, Fin.add_def] <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    simp only [hcomm01, hcomm02, hcomm12] <;> ring!

/-- The form of curl transport used for incompressible Euler. -/
theorem vectorCurl_convection_of_divergence_zero (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (x : Space) (hdiv : divergence u x = 0) :
    vectorCurl (fun y => fderiv ℝ u y (u y)) x =
      fderiv ℝ (vectorCurl u) x (u x) - fderiv ℝ u x (vectorCurl u x) := by
  simpa only [hdiv, zero_smul, add_zero] using vectorCurl_convection u hu x

/-- Ordinary gradients have zero ordinary curl. -/
theorem vectorCurl_gradient_zero (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (x : Space) :
    vectorCurl (gradient p) x = 0 := by
  ext i
  simp only [vectorCurl, curl_apply, gradient_coordinate, PiLp.zero_apply]
  exact sub_eq_zero.mpr (partialDerivative_comm p (hp.of_le (by simp)) (i+2) (i+1) x)

theorem vectorCurl_neg (f : Space → Space) (hf : Differentiable ℝ f) :
    vectorCurl (-f) = -vectorCurl f := by
  simpa only [neg_one_smul] using vectorCurl_smul (-1) f hf

theorem vectorCurl_sub (f g : Space → Space)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    vectorCurl (f-g) = vectorCurl f - vectorCurl g := by
  rw [sub_eq_add_neg, vectorCurl_add f (-g) hf hg.neg, vectorCurl_neg g hg,
    sub_eq_add_neg]

/-- Taking curl removes pressure and gives the Euler vorticity right-hand side. -/
theorem vectorCurl_euler_rhs (u : Space → Space) (p : Space → ℝ)
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ p) (x : Space)
    (hdiv : divergence u x = 0) :
    vectorCurl (fun y => -fderiv ℝ u y (u y) - gradient p y) x =
      fderiv ℝ u x (vectorCurl u x) - fderiv ℝ (vectorCurl u) x (u x) := by
  have hc : Differentiable ℝ (fun y => fderiv ℝ u y (u y)) :=
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply hu).differentiable (by simp)
  have hpg : Differentiable ℝ (gradient p) :=
    (EulerMeanSolenoidal.contDiff_gradient hp).differentiable (by simp)
  change vectorCurl (-(fun y => fderiv ℝ u y (u y)) - gradient p) x = _
  rw [vectorCurl_sub _ _ hc.neg hpg, vectorCurl_neg _ hc]
  simp only [Pi.sub_apply, Pi.neg_apply, vectorCurl_gradient_zero p hp x,
    vectorCurl_convection_of_divergence_zero u hu x hdiv, sub_zero, neg_sub]

end EulerComparatorCurlTransport

end
end

end

section

/-!
# Vorticity support along ordinary particle trajectories

The ODE lemma only needs a bound on the coefficient along one compact
trajectory. It does not assume a spatially uniform bound on the velocity or
its derivatives. The transport theorem below uses an ordinary differential
equation for vorticity, not a prescribed support condition.
-/

@[expose] public section

noncomputable section

open Set InnerProductSpace
open scoped Topology

namespace Euler.ComparatorBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniqueness of the zero solution of a continuous linear ODE, allowing only
interior derivatives and continuity at the two endpoints. -/
theorem linearODE_eq_zero (w : ℝ → E) (B : ℝ → E →L[ℝ] E) (T : ℝ)
    (hw : ContinuousOn w (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt w (B t (w t)) t)
    (hzero : w 0 = 0) (t : ℝ) (ht : t ∈ Icc 0 T) : w t = 0 := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn hB).isBounded.exists_norm_le
  let q : ℝ → ℝ := fun r => Real.exp (-(2 * K) * r) * ‖w r‖ ^ 2
  have hq : ContinuousOn q (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul (hw.norm.pow 2)
  have hqd (r : ℝ) (hr : r ∈ Ioo 0 T) :
      HasDerivAt q
        (Real.exp (-(2 * K) * r) *
          (2 * ⟪w r, B r (w r)⟫_ℝ - 2 * K * ‖w r‖ ^ 2)) r := by
    have h := (((hasDerivAt_id r).const_mul (-(2 * K))).exp).mul (hd r hr).norm_sq
    convert! h using 1
    simp only [id_eq]
    ring
  have hanti : AntitoneOn q (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hq
    · intro r hr
      exact (hqd r (by simpa only [interior_Icc] using hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : r ∈ Ioo 0 T := by simpa only [interior_Icc] using hr
      rw [(hqd r hr').deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hnorm : ‖B r (w r)‖ ≤ K * ‖w r‖ :=
        ((B r).le_opNorm (w r)).trans
          (mul_le_mul_of_nonneg_right (hK _ (mem_image_of_mem B ⟨hr'.1.le, hr'.2.le⟩))
            (norm_nonneg _))
      have hi := (real_inner_le_norm (w r) (B r (w r))).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
      nlinarith
  have hqt : q t ≤ 0 := by
    have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
    simpa only [q, hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      hanti hz ht ht.1
  have hsq : ‖w t‖ ^ 2 ≤ 0 := by
    exact nonpos_of_mul_nonpos_right hqt (Real.exp_pos _)
  have hn : ‖w t‖ = 0 := by nlinarith [norm_nonneg (w t)]
  exact norm_eq_zero.mp hn

/-- A field satisfying the stretching equation along a genuine trajectory
stays zero on that trajectory if it is initially zero. Coefficient
boundedness follows from continuity on the compact time interval. -/
theorem transport_eq_zero_along_trajectory
    (ω u : ℝ × E → E) (X : ℝ → E) (T : ℝ)
    (hω : ContinuousOn ω (Icc 0 T ×ˢ (univ : Set E)))
    (hX : ContinuousOn X (Icc 0 T))
    (hB : ContinuousOn (fun r => fderiv ℝ (fun x => u (r, x)) (X r)) (Icc 0 T))
    (hωdiff : ∀ r ∈ Ioo 0 T, DifferentiableAt ℝ ω (r, X r))
    (hmaterial : ∀ r ∈ Ioo 0 T,
      fderiv ℝ ω (r, X r) (1, u (r, X r)) =
        fderiv ℝ (fun x => u (r, x)) (X r) (ω (r, X r)))
    (hXderiv : ∀ r ∈ Ioo 0 T, HasDerivAt X (u (r, X r)) r)
    (hzero : ω (0, X 0) = 0) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ω (t, X t) = 0 := by
  apply linearODE_eq_zero (fun r => ω (r, X r))
    (fun r => fderiv ℝ (fun x => u (r, x)) (X r)) T
  · exact hω.comp (continuousOn_id.prodMk hX) (fun r hr => ⟨hr, mem_univ _⟩)
  · exact hB
  · intro r hr
    have h := (hωdiff r hr).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hXderiv r hr))
    simpa only [Function.comp_def, id_eq, hmaterial r hr] using h
  · exact hzero
  · exact ht

omit [InnerProductSpace ℝ E] in
/-- Compact initial support remains in its compact image whenever zero
initial values are propagated along every trajectory and the flow has a
right inverse at the specified time. -/
theorem tsupport_subset_flow_image
    (ω : ℝ → E → E) (X : ℝ → E → E) (Y : E → E) (t : ℝ)
    (hc : HasCompactSupport (ω 0)) (hX : Continuous (X t))
    (hXY : ∀ x, X t (Y x) = x)
    (hzero : ∀ a, ω 0 a = 0 → ω t (X t a) = 0) :
    tsupport (ω t) ⊆ X t '' tsupport (ω 0) := by
  apply closure_minimal _ (hc.image hX).isClosed
  intro x hx
  by_contra hnot
  have hz : ω 0 (Y x) = 0 := by
    by_contra hnz
    exact hnot ⟨Y x, subset_tsupport _ hnz, hXY x⟩
  exact hx (by simpa only [hXY x] using hzero (Y x) hz)

omit [InnerProductSpace ℝ E] in
/-- In particular each time slice has compact support. -/
theorem hasCompactSupport_of_flow_image
    (ω : ℝ → E → E) (X : ℝ → E → E) (Y : E → E) (t : ℝ)
    (hc : HasCompactSupport (ω 0)) (hX : Continuous (X t))
    (hXY : ∀ x, X t (Y x) = x)
    (hzero : ∀ a, ω 0 a = 0 → ω t (X t a) = 0) :
    HasCompactSupport (ω t) :=
  (hc.image hX).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_subset_flow_image ω X Y t hc hX hXY hzero)

end Euler.ComparatorBridge

end
end

end

@[expose] public section

noncomputable section

open Set InnerProductSpace EulerSmoothLimit EulerMeanCutoffCurl
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- The reference's joint smoothness in time-first coordinates. -/
theorem velocity_joint_contDiffAt (t : ℝ) (ht : 0 < t) (x : Space) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => v z.2 z.1) (t, x) := by
  have hc : ContDiffAt ℝ ∞ (Function.uncurry v) (x, t) :=
    h.velocity_smooth.contDiffAt (prod_mem_nhds Filter.univ_mem (Ici_mem_nhds ht))
  exact hc.comp (t, x) (contDiffAt_snd.prodMk contDiffAt_fst)

/-- The actual time derivative of vorticity, obtained by taking curl of the
scalar-pressure Euler equation and commuting the ordinary derivatives. -/
theorem vorticity_hasDerivAt (t : ℝ) (ht : 0 < t) (x : Space) :
    HasDerivAt (fun r => vectorCurl (v · r) x)
      (fderiv ℝ (v · t) x (vectorCurl (v · t) x) -
        fderiv ℝ (vectorCurl (v · t)) x (v x t)) t := by
  have hc := ComparatorBridge.vectorCurl_hasDerivAt
    ((h.velocity_joint_contDiffAt t ht x).of_le (by simp))
  have heq : (fun y => deriv (v y ·) t) =
      (fun y => -fderiv ℝ (v · t) y (v y t) - gradient (p · t) y) := by
    funext y
    exact (h.pointwise_euler y t ht).deriv
  have hdiv : EulerSmoothLimit.divergence (v · t) x = 0 := h.div_free x t ht.le
  rw [heq, EulerComparatorCurlTransport.vectorCurl_euler_rhs (v · t) (p · t)
    (h.velocity_contDiff t ht.le) (h.pressure_contDiff t ht.le) x hdiv] at hc
  exact hc

/-- The full spacetime derivative of ordinary curl satisfies the vorticity
stretching law in the material direction `(1,v)`. -/
theorem vorticity_material_derivative (t : ℝ) (ht : 0 < t) (x : Space) :
    fderiv ℝ (fun z : ℝ × Space => vectorCurl (v · z.1) z.2)
      (t, x) (1, v x t) = fderiv ℝ (v · t) x (vectorCurl (v · t) x) := by
  rw [ComparatorBridge.joint_vectorCurl_fderiv_apply
    (h.velocity_joint_contDiffAt t ht x)]
  have hcurl : vectorCurl (fun y => deriv (v y ·) t) x =
      fderiv ℝ (v · t) x (vectorCurl (v · t) x) -
        fderiv ℝ (vectorCurl (v · t)) x (v x t) := by
    exact (ComparatorBridge.vectorCurl_hasDerivAt
      ((h.velocity_joint_contDiffAt t ht x).of_le (by simp))).unique
      (h.vorticity_hasDerivAt t ht x)
  rw [hcurl]
  abel

/-- Joint smoothness in time-first coordinates, including the initial time. -/
theorem velocity_joint_contDiffOn :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.2 z.1)
      (Ici 0 ×ˢ (univ : Set Space)) :=
  h.velocity_smooth.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (fun _z hz => ⟨mem_univ _, hz.1⟩)

/-- Ordinary spatial derivatives remain jointly continuous at time zero. -/
theorem velocity_spatial_fderiv_continuousOn :
    ContinuousOn (fun z : ℝ × Space => fderiv ℝ (v · z.1) z.2)
      (Ici 0 ×ˢ (univ : Set Space)) :=
  (ComparatorBridge.joint_spatial_fderiv_contDiffOn h.velocity_joint_contDiffOn).continuousOn

/-- Vorticity is jointly continuous through the initial time. -/
theorem vorticity_continuousOn :
    ContinuousOn (fun z : ℝ × Space => vectorCurl (v · z.1) z.2)
      (Ici 0 ×ˢ (univ : Set Space)) :=
  (ComparatorBridge.joint_vectorCurl_contDiffOn h.velocity_joint_contDiffOn).continuousOn

/-- Zero vorticity is preserved on any genuine particle trajectory that
exists on the whole compact time interval. -/
theorem vorticity_eq_zero_along_trajectory
    (X : ℝ → Space) (T : ℝ) (hX : ContinuousOn X (Icc 0 T))
    (hXd : ∀ r ∈ Ioo 0 T, HasDerivAt X (v (X r) r) r)
    (hz : vectorCurl (v · 0) (X 0) = 0) (t : ℝ) (ht : t ∈ Icc 0 T) :
    vectorCurl (v · t) (X t) = 0 := by
  apply ComparatorBridge.transport_eq_zero_along_trajectory
    (fun z : ℝ × Space => vectorCurl (v · z.1) z.2)
    (fun z : ℝ × Space => v z.2 z.1) X T
  · exact h.vorticity_continuousOn.mono
      (by intro z hz; exact ⟨hz.1.1, hz.2⟩)
  · exact hX
  · exact h.velocity_spatial_fderiv_continuousOn.comp (continuousOn_id.prodMk hX)
      (fun r hr => ⟨hr.1, mem_univ _⟩)
  · intro r hr
    exact (ComparatorBridge.joint_vectorCurl_contDiffAt
      (h.velocity_joint_contDiffAt r hr.1 (X r))).differentiableAt (by simp)
  · intro r hr
    exact h.vorticity_material_derivative r hr.1 (X r)
  · exact hXd
  · exact hz
  · exact ht

/-- Vorticity support is contained in the image of its initial support under
any complete continuous particle flow with a right inverse at the target time.
The support propagation itself follows from the reference Euler equation. -/
theorem vorticity_tsupport_subset_flow_image
    (X : ℝ → Space → Space) (Y : Space → Space) (T t : ℝ)
    (ht : t ∈ Icc 0 T)
    (hX : ∀ a, ContinuousOn (fun r => X r a) (Icc 0 T))
    (hXd : ∀ a r, r ∈ Ioo 0 T → HasDerivAt (fun s => X s a) (v (X r a) r) r)
    (hX0 : ∀ a, X 0 a = a) (hXt : Continuous (X t))
    (hXY : ∀ x, X t (Y x) = x)
    (hc : HasCompactSupport (vectorCurl u₀)) :
    tsupport (vectorCurl (v · t)) ⊆ X t '' tsupport (vectorCurl u₀) := by
  have he : (v · 0) = u₀ := funext h.initial_condition
  have hcomp : HasCompactSupport (vectorCurl (v · 0)) := by simpa only [he] using hc
  have hs := ComparatorBridge.tsupport_subset_flow_image
    (fun r => vectorCurl (v · r)) X Y t hcomp hXt hXY
    (fun a ha => h.vorticity_eq_zero_along_trajectory (fun r => X r a) T
      (hX a) (hXd a) (by simpa only [hX0 a] using ha) t ht)
  simpa only [he] using hs

/-- Compact initial vorticity therefore stays compactly supported under a
complete particle flow; no global bounds on spatial derivatives are assumed. -/
theorem vorticity_hasCompactSupport_of_flow
    (X : ℝ → Space → Space) (Y : Space → Space) (T t : ℝ)
    (ht : t ∈ Icc 0 T)
    (hX : ∀ a, ContinuousOn (fun r => X r a) (Icc 0 T))
    (hXd : ∀ a r, r ∈ Ioo 0 T → HasDerivAt (fun s => X s a) (v (X r a) r) r)
    (hX0 : ∀ a, X 0 a = a) (hXt : Continuous (X t))
    (hXY : ∀ x, X t (Y x) = x)
    (hc : HasCompactSupport (vectorCurl u₀)) :
    HasCompactSupport (vectorCurl (v · t)) :=
  (hc.image hXt).of_isClosed_subset (isClosed_tsupport _)
    (h.vorticity_tsupport_subset_flow_image X Y T t ht hX hXd hX0 hXt hXY hc)

/-- On a compact time interval all vorticity supports lie in one compact set:
the image of the compact initial support swept out by the particle flow. -/
theorem vorticity_uniformCompactSupport_of_flow
    (X Y : ℝ → Space → Space) (T : ℝ)
    (hX : ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ (univ : Set Space)))
    (hXd : ∀ a r, r ∈ Ioo 0 T → HasDerivAt (fun s => X s a) (v (X r a) r) r)
    (hX0 : ∀ a, X 0 a = a)
    (hXY : ∀ t ∈ Icc 0 T, ∀ x, X t (Y t x) = x)
    (hc : HasCompactSupport (vectorCurl u₀)) :
    ∃ K : Set Space, IsCompact K ∧
      ∀ t ∈ Icc 0 T, tsupport (vectorCurl (v · t)) ⊆ K := by
  refine ⟨Function.uncurry X '' (Icc 0 T ×ˢ tsupport (vectorCurl u₀)),
    (isCompact_Icc.prod hc).image_of_continuousOn
      (hX.mono (by intro z hz; exact ⟨hz.1, mem_univ _⟩)), ?_⟩
  intro t ht x hx
  have htcont : ∀ a, ContinuousOn (fun r => X r a) (Icc 0 T) := by
    intro a
    exact hX.comp (continuousOn_id.prodMk continuousOn_const)
      (fun r hr => ⟨hr, mem_univ _⟩)
  have hxcont : Continuous (X t) :=
    hX.comp_continuous (continuous_const.prodMk continuous_id)
      (fun a => ⟨ht, mem_univ a⟩)
  obtain ⟨a, ha, hax⟩ := h.vorticity_tsupport_subset_flow_image
    X (Y t) T t ht htcont hXd hX0 hxcont (hXY t ht) hc hx
  exact ⟨(t, a), ⟨ht, ha⟩, hax⟩

end Euler.EulerExistenceAndSmoothnessR3
