/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
public import LeanPool.NavierStokesAndEuler.Euler.CurlTimeDerivative
public import LeanPool.NavierStokesAndEuler.Euler.CurlTransportAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.VorticityTransport

@[expose] public section

/-! The ordinary vorticity equation of a Comparator solution follows from
its scalar-pressure, unforced Euler equation. -/

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
