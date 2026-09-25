/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Basic
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.AreaVector
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.EqualAreaRelation
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.WeightBounds
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.WeightBox
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.ClosedGraph

/-!
# `NRR.EMP.VariableBody.NormalizedWeightContinuity` — continuity of the selected weight

For a fixed planar parent body `K`, a lower area bound `A`, and a compact metric parameter space `X`
carrying a continuous site family `sites : SiteFamily X n`, the canonical normalized equal-area
weight varies continuously with both the subbody `C : BodySpace K A` and the parameter `x : X`.

The argument is purely topological, derived from the closed normalized equal-area relation
(`isClosed_normalizedWeightGraph`), uniqueness (`normalizedWeight_unique`), and the uniform
coordinate bound (`normalizedWeight_abs_le`); it does not use any pre-existing normalized-weight
continuity core.

* `normalizedWeightBox` — the selected weight, valued in the compact weight box.
* `isClosed_graph_normalizedWeightBox` — its graph is closed.
* `continuous_normalizedWeightBox` — the boxed selection is continuous.
* `continuous_normalizedWeight_compactFamily` — continuity into the ordinary weight space.
* `continuous_normalizedWeight_compactFamily_apply` — coordinate continuity.
* `areaVec_normalizedWeight_eq_target` — the selected area vector is the constant target vector.
* `continuous_areaVec_normalizedWeight_compactFamily` — continuity of the selected area vector.
-/

@[expose] public section

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR.EMP.VariableBody

variable {X : Type*} [MetricSpace X] [CompactSpace X] {n : ℕ}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

/-- The **boxed selected weight**: the canonical normalized equal-area weight, packaged with its
uniform coordinate bound as an element of the compact weight box. -/
noncomputable def normalizedWeightBox
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) :
    WeightBox n (weightBound K sites) :=
  ⟨normalizedWeight hA hn z.1 (sites z.2), by
    intro i
    exact normalizedWeight_abs_le
      (K := K) (A := A) (n := n)
      sites hA hn z.1 z.2 i⟩

@[simp] theorem normalizedWeightBox_coe
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) :
    (normalizedWeightBox sites hA hn z : Fin n → ℝ)
      = normalizedWeight hA hn z.1 (sites z.2) :=
  rfl

/-- **The graph of the boxed selected weight is closed.** The pullback of the closed normalized
equal-area relation along the continuous coordinate inclusion `WeightBox → (Fin n → ℝ)` is a closed
relation that contains the graph (`normalizedWeight_isEqualArea`, `normalizedWeight_normalized`) and
selects uniquely (`normalizedWeight_unique`); apply the uniqueness closed-graph criterion. -/
theorem isClosed_graph_normalizedWeightBox
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n) :
    IsClosed {
      z : (BodySpace K A × X) × WeightBox n (weightBound K sites) |
        z.2 = normalizedWeightBox sites hA hn z.1
    } := by
  set M := weightBound K sites with hM
  refine isClosed_graph_of_isClosed_relation_of_unique
    (R := {z : (BodySpace K A × X) × WeightBox n M |
      ((z.1, (z.2 : Fin n → ℝ)) ∈ NormalizedWeightGraph (K := K) (A := A) sites hA)})
    ?_ (normalizedWeightBox sites hA hn) ?_ ?_
  · -- Closedness: preimage of the closed graph under a continuous map.
    have hmap : Continuous fun z : (BodySpace K A × X) × WeightBox n M =>
        (z.1, (z.2 : Fin n → ℝ)) :=
      continuous_fst.prodMk ((WeightBox.valContinuous n M).continuous.comp continuous_snd)
    exact (isClosed_normalizedWeightGraph sites hA).preimage hmap
  · -- The selected weight satisfies the normalized equal-area relation.
    intro d
    refine ⟨normalizedWeight_isEqualArea hA hn d.1 (sites d.2),
      normalizedWeight_normalized hA hn d.1 (sites d.2)⟩
  · -- Any bounded weight satisfying the relation equals the selected weight.
    intro d wb hwb
    apply WeightBox.ext
    exact normalizedWeight_unique hA hn d.1 (sites d.2) hwb

/-- **Continuity of the boxed selected weight.** The domain `BodySpace K A × X` is compact
Hausdorff, the weight box is compact Hausdorff, and the graph is closed, so the compact closed-graph
criterion gives continuity. -/
theorem continuous_normalizedWeightBox
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n) :
    Continuous (normalizedWeightBox (K := K) sites hA hn) :=
  continuous_of_isClosed_graph_of_compact
    (normalizedWeightBox (K := K) sites hA hn)
    (isClosed_graph_normalizedWeightBox sites hA hn)

/-- **Continuity of the selected weight into the ordinary weight space.** Compose the boxed
continuity with the continuous coordinate inclusion. -/
theorem continuous_normalizedWeight_compactFamily
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n) :
    Continuous fun z : BodySpace K A × X =>
      normalizedWeight hA hn z.1 (sites z.2) :=
  (WeightBox.valContinuous n (weightBound K sites)).continuous.comp
    (continuous_normalizedWeightBox sites hA hn)

/-- **Coordinate continuity of the selected weight.** Each coordinate of the selected weight is
continuous, by composing the vector continuity with the coordinate projection. -/
theorem continuous_normalizedWeight_compactFamily_apply
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (i : Fin n) :
    Continuous fun z : BodySpace K A × X =>
      normalizedWeight hA hn z.1 (sites z.2) i :=
  (continuous_apply i).comp (continuous_normalizedWeight_compactFamily sites hA hn)

omit [CompactSpace X] in
/-- **The selected area vector is the constant target vector.** The equal-area property of the
selected weight says every cell of the partition realizes the average area `targetArea z.1 n`. -/
theorem areaVec_normalizedWeight_eq_target
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) :
    areaVec hA z.1 (sites z.2)
      (normalizedWeight hA hn z.1 (sites z.2)) =
        fun _ => targetArea z.1 n := by
  funext i
  exact (isEqualAreaWeight_iff_areaVec hA z.1 (sites z.2)
    (normalizedWeight hA hn z.1 (sites z.2))).mp
    (normalizedWeight_isEqualArea hA hn z.1 (sites z.2)) i

omit [CompactSpace X] in
/-- **Continuity of the selected area vector.** By the constant-target identity, the selected area
vector equals the continuous map `z ↦ fun _ => targetArea z.1 n`. -/
theorem continuous_areaVec_normalizedWeight_compactFamily
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n) :
    Continuous fun z : BodySpace K A × X =>
      areaVec hA z.1 (sites z.2)
        (normalizedWeight hA hn z.1 (sites z.2)) := by
  have hfun :
      (fun z : BodySpace K A × X =>
          areaVec hA z.1 (sites z.2) (normalizedWeight hA hn z.1 (sites z.2)))
        = fun z : BodySpace K A × X => fun _ : Fin n => targetArea z.1 n := by
    funext z
    exact areaVec_normalizedWeight_eq_target sites hA hn z
  rw [hfun]
  exact continuous_pi (fun _ => continuous_targetArea.comp continuous_fst)

end NRR.EMP.VariableBody
