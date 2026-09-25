/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Topology of parabolic space-time

The parabolic metric of `CKN.Foundation.Parabolic.Basic` is obtained by pulling back the
product metric of `L²(ℝ³) × ℝ` (the time factor being snowflaked) along `parabolicMap`.
This file identifies the resulting topology with the product topology of the spatial
variable and time.  It is the bridge that lets openness and closure of the paper's
space-time carriers be read off from the corresponding statements on `Vec3 × ℝ`: in
particular the space-time set `def:sws`, whose carrier is `Ω × I`, is open for open `Ω`
and `I`, and the interior and closure of a parabolic cylinder are computed from the
Euclidean ball and the intervals `Ioo` and `Icc`.
-/

@[expose] public section

open scoped Topology
open Set Metric


noncomputable section

namespace CKN.Foundation.Parabolic

/-- The topology on `ParabolicPoint` is the one induced by `parabolicMap`, i.e. the
pullback of the product topology on `L²(ℝ³) × ℝ`. -/
theorem isInducing_parabolicMap : Topology.IsInducing parabolicMap :=
  Topology.IsInducing.induced parabolicMap

/-- The spatial coordinate is continuous for the parabolic topology: the first factor of
`parabolicMap` is `WithLp.toLp 2`, which is continuous for the `L²` product topology. -/
theorem continuous_fst_parabolicPoint : Continuous (fun p : ParabolicPoint => p.1) := by
  have h : Continuous (fun p : ParabolicPoint => (parabolicMap p).1.ofLp) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
      (continuous_fst.comp isInducing_parabolicMap.continuous)
  have hfun : (fun p : ParabolicPoint => (parabolicMap p).1.ofLp) = (fun p => p.1) := by
    funext p
    exact WithLp.ofLp_toLp 2 p.1
  rwa [hfun] at h

/-- The time coordinate is continuous for the parabolic topology: the second factor of
`parabolicMap` is the snowflaking equivalence, which carries the same topology as `ℝ`. -/
theorem continuous_snd_parabolicPoint : Continuous (fun p : ParabolicPoint => p.2) := by
  have h : Continuous (fun p : ParabolicPoint =>
      Metric.Snowflaking.ofSnowflaking (parabolicMap p).2) :=
    Metric.Snowflaking.continuous_ofSnowflaking.comp
      (continuous_snd.comp isInducing_parabolicMap.continuous)
  have hfun : (fun p : ParabolicPoint =>
      Metric.Snowflaking.ofSnowflaking (parabolicMap p).2) = (fun p => p.2) := by
    funext p
    exact Metric.Snowflaking.ofSnowflaking_toSnowflaking p.2
  rwa [hfun] at h

/-- `parabolicMap`, read on the product `Vec3 × ℝ` with its product topology, is
continuous: both `WithLp.toLp 2` and the snowflaking equivalence are. -/
theorem continuous_parabolicMap_prod :
    Continuous (fun q : Vec3 × ℝ => parabolicMap q) := by
  have h1 : Continuous (fun q : Vec3 × ℝ => WithLp.toLp 2 q.1) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp continuous_fst
  have h2 : Continuous (fun q : Vec3 × ℝ =>
      (Metric.Snowflaking.toSnowflaking q.2 : SnowTime)) :=
    Metric.Snowflaking.continuous_toSnowflaking.comp continuous_snd
  exact h1.prodMk h2

/-- The identity map from the parabolic space-time to `Vec3 × ℝ` with the product
topology is continuous. -/
theorem continuous_parabolicPoint_to_prod :
    Continuous (fun p : ParabolicPoint => (p.1, p.2)) :=
  continuous_fst_parabolicPoint.prodMk continuous_snd_parabolicPoint

/-- The identity map from `Vec3 × ℝ` with the product topology to the parabolic
space-time is continuous; equivalently, the product topology is finer than the parabolic
topology. -/
theorem continuous_prod_to_parabolicPoint :
    Continuous (show Vec3 × ℝ → ParabolicPoint from fun q => (q.1, q.2)) := by
  rw [isInducing_parabolicMap.continuous_iff]
  change Continuous (fun q : Vec3 × ℝ => parabolicMap q)
  exact continuous_parabolicMap_prod

/-- The identity, viewed as a homeomorphism from the parabolic space-time to `Vec3 × ℝ`
with the product topology.  This is the topology bridge: set-theoretic operations on
space-time sets may be performed on the product instead. -/
def parabolicHomeomorph : ParabolicPoint ≃ₜ Vec3 × ℝ where
  toFun := fun p => (p.1, p.2)
  invFun := fun q => ((q.1, q.2) : ParabolicPoint)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_parabolicPoint_to_prod
  continuous_invFun := continuous_prod_to_parabolicPoint

@[simp] theorem parabolicHomeomorph_apply (p : ParabolicPoint) :
    parabolicHomeomorph p = (p.1, p.2) := rfl

@[simp] theorem parabolicHomeomorph_symm_apply (q : Vec3 × ℝ) :
    parabolicHomeomorph.symm q = ((q.1, q.2) : ParabolicPoint) := rfl

/-- The topology bridge, as a statement about preimages: the homeomorphism is the
identity on points, so preimages of product sets are the sets themselves. -/
@[simp] theorem parabolicHomeomorph_preimage (s : Set (Vec3 × ℝ)) :
    parabolicHomeomorph ⁻¹' s = s := by
  ext p
  rfl

/-- The instance topology on `ParabolicPoint` equals the product topology on
`Vec3 × ℝ` transported along the identity. -/
theorem topologicalSpace_eq_induced_prod :
    (inferInstance : TopologicalSpace ParabolicPoint) =
      TopologicalSpace.induced (fun p : ParabolicPoint => (p.1, p.2))
        instTopologicalSpaceProd := by
  change (inferInstance : TopologicalSpace ParabolicPoint) =
    TopologicalSpace.induced (⇑parabolicHomeomorph) instTopologicalSpaceProd
  exact parabolicHomeomorph.isInducing.eq_induced

/-- The identification of `Vec3` (with its product-of-coordinates topology) with
`L²(ℝ³)`, under which `vec3EuclideanNorm` is the `L²` norm. -/
def vec3Homeomorph : Vec3 ≃ₜ L2Vec3 :=
  (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm

@[simp] theorem vec3Homeomorph_apply (v : Vec3) :
    vec3Homeomorph v = WithLp.toLp 2 v := rfl

/-- Under the identification of `Vec3` with `L²(ℝ³)`, the Euclidean ball `vec3Ball` is a
metric ball, hence open. -/
theorem isOpen_vec3Ball (x : Vec3) (r : ℝ) : IsOpen (vec3Ball x r) := by
  have h : vec3Ball x r = vec3Homeomorph ⁻¹' Metric.ball (vec3Homeomorph x) r := by
    ext y
    simp only [mem_preimage, mem_vec3Ball, mem_ball, vec3Homeomorph_apply, dist_eq_norm]
    rw [← WithLp.toLp_sub, ← vec3EuclideanNorm_eq_l2 (y - x)]
  rw [h]
  exact Metric.isOpen_ball.preimage vec3Homeomorph.continuous

/-- The closure of the Euclidean open ball of positive radius is the corresponding
closed set `{y | vec3EuclideanNorm (y - x) ≤ r}`. -/
theorem closure_vec3Ball {x : Vec3} {r : ℝ} (hr : 0 < r) :
    closure (vec3Ball x r) = {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} := by
  have h : vec3Ball x r = vec3Homeomorph ⁻¹' Metric.ball (vec3Homeomorph x) r := by
    ext y
    simp only [mem_preimage, mem_vec3Ball, mem_ball, vec3Homeomorph_apply, dist_eq_norm]
    rw [← WithLp.toLp_sub, ← vec3EuclideanNorm_eq_l2 (y - x)]
  rw [h, ← vec3Homeomorph.preimage_closure, closure_ball _ hr.ne']
  ext y
  simp only [mem_preimage, mem_closedBall, vec3Homeomorph_apply, dist_eq_norm]
  rw [← WithLp.toLp_sub, ← vec3EuclideanNorm_eq_l2 (y - x)]
  rfl

/-- The space-time carrier `def:sws` is open when both `Ω` and `I` are open. -/
theorem isOpen_spaceTimeSet (Ω : Set Vec3) (I : Set ℝ) (hΩ : IsOpen Ω) (hI : IsOpen I) :
    IsOpen (CKN.spaceTimeSet Ω I) := by
  rw [show CKN.spaceTimeSet Ω I = parabolicHomeomorph ⁻¹' (Ω ×ˢ I) by
    rw [CKN.spaceTimeSet, parabolicHomeomorph_preimage]]
  exact (parabolicHomeomorph.isOpen_preimage).mpr (hΩ.prod hI)

/-- The interior of a parabolic cylinder is the product of the Euclidean open ball and
the open time interval: `Ioc` is not open, so its interior is `Ioo`. -/
theorem interior_parabolicCylinder (x : Vec3) (t r : ℝ) :
    interior (parabolicCylinder x t r) = vec3Ball x r ×ˢ Ioo (t - r ^ 2) t := by
  rw [show parabolicCylinder x t r =
      parabolicHomeomorph ⁻¹' (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t) by
    rw [parabolicCylinder, parabolicHomeomorph_preimage],
    ← parabolicHomeomorph.preimage_interior]
  rw [interior_prod_eq, (isOpen_vec3Ball x r).interior_eq, interior_Ioc,
    parabolicHomeomorph_preimage]

/-- The closure of a parabolic cylinder of positive radius is the product of the
Euclidean closed ball and the closed time interval. -/
theorem closure_parabolicCylinder {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    closure (parabolicCylinder x t r) =
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} ×ˢ Icc (t - r ^ 2) t := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hlt : t - r ^ 2 < t := by linarith only [hr2]
  rw [show parabolicCylinder x t r =
      parabolicHomeomorph ⁻¹' (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t) by
    rw [parabolicCylinder, parabolicHomeomorph_preimage],
    ← parabolicHomeomorph.preimage_closure]
  rw [closure_prod_eq, closure_vec3Ball hr, closure_Ioc hlt.ne,
    parabolicHomeomorph_preimage]

/-- Every parabolic cylinder is contained in its closure. -/
theorem parabolicCylinder_subset_closure (x : Vec3) (t r : ℝ) :
    parabolicCylinder x t r ⊆ closure (parabolicCylinder x t r) :=
  subset_closure

/-- Closures of parabolic cylinders are monotone in the radius. -/
theorem closure_parabolicCylinder_mono {x : Vec3} {t r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (hr : r₁ ≤ r₂) :
    closure (parabolicCylinder x t r₁) ⊆ closure (parabolicCylinder x t r₂) :=
  closure_mono (parabolicCylinder_mono hr₁ hr)

end CKN.Foundation.Parabolic
