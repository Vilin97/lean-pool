/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/


import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# A copy of a metric space with metric given by `d x y = dist x y ^ α`

Given a (pseudo) (extended) metric space `X` and a number `0 < α < 1`,
one can consider the metric given by `d x y = (dist x y) ^ α`.
In this file we define `WithRPowDist X α hα₀ hα₁` to be a one-field structure wrapper around `X`
with metric given by this formula.

One of the reasons to introduce this definition is the following.
In the proof of his version of the Morse-Sard theorem,
Moreira [Moreira2001] studies maps of two variables that are Lipschitz continuous in one variable,
but satisfy a stronger assumption `‖f (a, y) - f (a, b)‖ = O(‖y - b‖ ^ α)`
along the second variable, as long as `(a, b)` is one of the "interesting" points.

If we want to apply Vitali family in this context, we need to cover the set by products
`closedBall a (R ^ α) ×ˢ closedBall b R` so that both components make a similar contribution
to `‖f (x, y) - f (a, b)‖`. These sets aren't balls in the original metric
(or even subsets of balls that occupy at least a fixed fraction of the volume,
as we require in our version of Vitali theorem).

However, if we change the metric on the first component to the one introduced in this file,
then these sets become balls, and we can apply Vitali theorem.

## References
* [Carlos Gustavo T. de A. Moreira, _Hausdorff measures and the Morse-Sard theorem_]
  [Moreira2001]
-/


open scoped ENNReal NNReal Filter Uniformity Topology
open Function

noncomputable section

/-- A copy of a type with metric given by `dist x y = (dist x.val y.val) ^ α`.

This is defined as a one-field structure. -/
@[ext]
structure WithRPowDist (X : Type*) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) where
  /-- The value wrapped in `x : WithRPowDist X α hα₀ hα₁`. -/
  val : X

namespace WithRPowDist

variable {X : Type*} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1}

/-- The natural equivalence between `WithRPowDist X α hr₀ hr₁` and `X`. -/
@[simps -fullyApplied apply symm_apply]
def equiv (X : Type*) (α : ℝ) (hr₀ : 0 < α) (hr₁ : α ≤ 1) : WithRPowDist X α hr₀ hr₁ ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem val_comp_mk : (val : WithRPowDist X α hα₀ hα₁ → X) ∘ mk = id := rfl

@[simp]
theorem mk_comp_val : (mk : X → WithRPowDist X α hα₀ hα₁) ∘ val = id := rfl

theorem image_mk_eq_preimage (s : Set X) :
    (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = val ⁻¹' s :=
  (equiv X α hα₀ hα₁).symm.image_eq_preimage_symm _

theorem image_val_eq_preimage (s : Set (WithRPowDist X α hα₀ hα₁)) :
    val '' s = mk ⁻¹' s :=
  (equiv X α hα₀ hα₁).image_eq_preimage_symm _

@[simp]
theorem image_mk_image_val (s : Set (WithRPowDist X α hα₀ hα₁)) :
    mk '' (val '' s) = s :=
  (equiv X α hα₀ hα₁).symm_image_image _

@[simp]
theorem image_val_image_mk (s : Set X) : val '' (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = s :=
  (equiv X α hα₀ hα₁).image_symm_image _

theorem surjective_val : Surjective (val : WithRPowDist X α hα₀ hα₁ → X) :=
  equiv _ _ _ _ |>.surjective

theorem surjective_mk : Surjective (mk :  X → WithRPowDist X α hα₀ hα₁) :=
  equiv _ _ _ _ |>.symm |>.surjective

theorem injective_mk : Injective (mk : X → WithRPowDist X α hα₀ hα₁) := by simp [Injective]

/-!
### Topological space structure

The topology on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/

section TopologicalSpace

variable [TopologicalSpace X]

/-- The topological space structure on `WithRPowDist X α _ _` is induced from the original space. -/
instance : TopologicalSpace (WithRPowDist X α hα₀ hα₁) := .induced WithRPowDist.val ‹_›

@[fun_prop]
theorem continuous_val : Continuous (val : WithRPowDist X α hα₀ hα₁ → X) :=
  continuous_induced_dom

@[fun_prop]
theorem continuous_mk : Continuous (mk : X → WithRPowDist X α hα₀ hα₁) :=
  continuous_induced_rng.2 continuous_id

/-- The natural homeomorphism between `WithRPowDist X α hα₀ hα₁` and `X`. -/
@[simps! -fullyApplied toEquiv apply symm_apply]
def homeomorph : WithRPowDist X α hα₀ hα₁ ≃ₜ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁

/-!
We copy some instances from the underlying space `X` to `WithRPowDist X α hα₀ hα₁`.
In the future, we can add more of them, if needed,
or even copy all the topology-related classes, if we get a tactic to do it automatically.
-/

instance [T0Space X] : T0Space (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.symm.t0Space

instance [T2Space X] : T2Space (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.symm.t2Space

instance [SecondCountableTopology X] : SecondCountableTopology (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.secondCountableTopology

end TopologicalSpace

/-!
### Bornology

The bornology on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/

section Bornology

variable [Bornology X]

instance : Bornology (WithRPowDist X α hα₀ hα₁) := .induced val

open Bornology

@[simp]
theorem _root_.WithRPowDist.isBounded_image_val_iff {s : Set (WithRPowDist X α hα₀ hα₁)} :
    IsBounded (val '' s) ↔ IsBounded s :=
  isBounded_induced.symm

@[simp]
theorem _root_.WithRPowDist.isBounded_preimage_mk_iff {s : Set (WithRPowDist X α hα₀ hα₁)} :
    IsBounded (mk ⁻¹' s) ↔ IsBounded s := by rw [← image_val_eq_preimage, isBounded_image_val_iff]

@[simp]
theorem _root_.WithRPowDist.isBounded_image_mk_iff {s : Set X} :
    IsBounded (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← isBounded_image_val_iff, image_val_image_mk]

@[simp]
theorem _root_.WithRPowDist.isBounded_preimage_val_iff {s : Set X} :
    IsBounded (val ⁻¹' s : Set (WithRPowDist X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← image_mk_eq_preimage, isBounded_image_mk_iff]

end Bornology

/-!
### Uniform space structure

The uniform space structure on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/

section UniformSpace

variable [UniformSpace X]

instance : UniformSpace (WithRPowDist X α hα₀ hα₁) :=
  UniformSpace.comap WithRPowDist.val ‹_›

theorem _root_.WithRPowDist.uniformContinuous_val :
    UniformContinuous (val : WithRPowDist X α hα₀ hα₁ → X) :=
  uniformContinuous_comap

theorem _root_.WithRPowDist.uniformContinuous_mk :
    UniformContinuous (mk : X → WithRPowDist X α hα₀ hα₁) :=
  uniformContinuous_comap' uniformContinuous_id

/-- The natural uniform equivalence between `WithRPowDist X α hα₀ hα₁` and `X`. -/
@[simps! toEquiv apply symm_apply]
def _root_.WithRPowDist.uniformEquiv : WithRPowDist X α hα₀ hα₁ ≃ᵤ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁
  uniformContinuous_toFun := uniformContinuous_val
  uniformContinuous_invFun := uniformContinuous_mk

end UniformSpace

/-!
### Extended distance and a (pseudo) extended metric space structure

Th extended distance on `WithRPowDist X α hα₀ hα₁`
is given by `edist x y = (edist x.val y.val) ^ α`.

If the original space is a (pseudo) extended metric space, then so is `WithRPowDist X α hα₀ hα₁`.
-/

section EDist

variable [EDist X]

instance : EDist (WithRPowDist X α hα₀ hα₁) where
  edist x y := edist x.val y.val ^ α

theorem _root_.WithRPowDist.edist_def (x y : WithRPowDist X α hα₀ hα₁) :
    edist x y = edist x.val y.val ^ α := rfl

@[simp]
theorem _root_.WithRPowDist.edist_mk_mk (x y : X) :
    edist (mk x : WithRPowDist X α hα₀ hα₁) (mk y) = edist x y ^ α :=
  rfl

@[simp]
theorem _root_.WithRPowDist.edist_val_val (x y : WithRPowDist X α hα₀ hα₁) :
    edist x.val y.val = edist x y ^ α⁻¹ := by rw [edist_def, ENNReal.rpow_rpow_inv hα₀.ne']

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

open Metric

instance : PseudoEMetricSpace (WithRPowDist X α hα₀ hα₁) where
  edist_self x := by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.val y.val z.val, ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ ↦ by positivity) fun ε hε ↦
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]

@[simp]
theorem _root_.WithRPowDist.preimage_val_emetricBall (x : X) (r : ℝ≥0∞) :
    val ⁻¹' eball x r = eball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]

@[simp]
theorem _root_.WithRPowDist.image_mk_emetricBall (x : X) (r : ℝ≥0∞) :
    mk '' eball x r = eball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_emetricBall]

@[simp]
theorem _root_.WithRPowDist.preimage_mk_emetricBall
    (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    mk ⁻¹' eball x d = eball x.val (d ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_emetricBall, Set.image_preimage_eq _ surjective_mk, ENNReal.rpow_inv_rpow hα₀.ne']

@[simp]
theorem _root_.WithRPowDist.image_val_emetricBall
    (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    val '' eball x d = eball x.val (d ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_emetricBall]

@[simp]
theorem _root_.WithRPowDist.preimage_val_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    val ⁻¹' closedEBall x r = closedEBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]

@[simp]
theorem _root_.WithRPowDist.image_mk_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    mk '' closedEBall x r = closedEBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_emetricClosedBall]

@[simp]
theorem _root_.WithRPowDist.preimage_mk_emetricClosedBall
    (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    mk ⁻¹' closedEBall x d = closedEBall x.val (d ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_emetricClosedBall, Set.image_preimage_eq _ surjective_mk,
    ENNReal.rpow_inv_rpow hα₀.ne']

@[simp]
theorem _root_.WithRPowDist.image_val_emetricClosedBall
    (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    val '' closedEBall x d = closedEBall x.val (d ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_emetricClosedBall]

@[simp]
theorem _root_.WithRPowDist.ediam_image_val (s : Set (WithRPowDist X α hα₀ hα₁)) :
    ediam (val '' s) = ediam s ^ α⁻¹ := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp [ediam_le_iff, ENNReal.rpow_inv_le_iff hα₀]

@[simp]
theorem _root_.WithRPowDist.ediam_preimage_mk (s : Set (WithRPowDist X α hα₀ hα₁)) :
    ediam (mk ⁻¹' s) = ediam s ^ α⁻¹ := by rw [← image_val_eq_preimage, ediam_image_val]

@[simp]
theorem _root_.WithRPowDist.ediam_preimage_val (s : Set X) :
    ediam (val ⁻¹' s : Set (WithRPowDist X α hα₀ hα₁)) = ediam s ^ α := by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (ediam _), ← ediam_preimage_mk,
    ← Set.preimage_comp, val_comp_mk, Set.preimage_id]

@[simp]
theorem _root_.WithRPowDist.ediam_image_mk (s : Set X) :
    ediam (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = ediam s ^ α := by
  simp [image_mk_eq_preimage]

end PseudoEMetricSpace

instance [EMetricSpace X] : EMetricSpace (WithRPowDist X α hα₀ hα₁) :=
  .ofT0PseudoEMetricSpace _

/-!
### Distance and a (pseudo) metric space structure

Th extended distance on `WithRPowDist X α hα₀ hα₁`
is given by `dist x y = (dist x.val y.val) ^ α`.

If the original space is a (pseudo) metric space, then so is `WithRPowDist X α hα₀ hα₁`.
-/

instance [Dist X] : Dist (WithRPowDist X α hα₀ hα₁) where
  dist x y := dist x.val y.val ^ α

@[simp]
theorem _root_.WithRPowDist.dist_mk_mk [Dist X] (x y : X) :
    dist (mk x : WithRPowDist X α hα₀ hα₁) (mk y) = dist x y ^ α :=
  rfl

section PseudoMetricSpace

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace (WithRPowDist X α hα₀ hα₁) :=
  letI aux : PseudoMetricSpace (WithRPowDist X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by rintro ⟨x⟩ ⟨y⟩; rw [dist_mk_mk]; positivity)
      (by
        rintro ⟨x⟩ ⟨y⟩
        rw [edist_mk_mk, dist_mk_mk, ← ENNReal.ofReal_rpow_of_nonneg, ← edist_dist] <;> positivity)
  aux.replaceBornology fun s ↦ by
    rw [← isBounded_preimage_mk_iff, Metric.isBounded_iff, Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [dist_mk_mk, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_mk_mk, Real.rpow_rpow_inv (by positivity) hα₀.ne']

open Metric

@[simp]
theorem _root_.WithRPowDist.dist_val_val (x y : WithRPowDist X α hα₀ hα₁) :
    dist x.val y.val = dist x y ^ α⁻¹ := by
  cases x; cases y
  rw [dist_mk_mk, Real.rpow_rpow_inv dist_nonneg hα₀.ne']

@[simp]
theorem _root_.WithRPowDist.preimage_val_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    val ⁻¹' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]

@[simp]
theorem _root_.WithRPowDist.image_mk_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    mk '' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_ball x hr]

@[simp]
theorem _root_.WithRPowDist.preimage_mk_ball
    (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    mk ⁻¹' ball x r = ball x.val (r ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_ball _ (by positivity), Set.image_preimage_eq _ surjective_mk,
    Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
theorem _root_.WithRPowDist.image_val_ball
    (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    val '' ball x r = ball x.val (r ^ α⁻¹) := by rw [image_val_eq_preimage, preimage_mk_ball _ hr]

@[simp]
theorem _root_.WithRPowDist.preimage_val_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    val ⁻¹' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]

@[simp]
theorem _root_.WithRPowDist.image_mk_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    mk '' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_closedBall x hr]

@[simp]
theorem _root_.WithRPowDist.preimage_mk_closedBall
    (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    mk ⁻¹' closedBall x r = closedBall x.val (r ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_closedBall _ (by positivity), Set.image_preimage_eq _ surjective_mk,
    Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
theorem _root_.WithRPowDist.image_val_closedBall
    (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    val '' closedBall x r = closedBall x.val (r ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_closedBall _ hr]

end PseudoMetricSpace

instance [MetricSpace X] : MetricSpace (WithRPowDist X α hα₀ hα₁) :=
  .ofT0PseudoMetricSpace _

end WithRPowDist
