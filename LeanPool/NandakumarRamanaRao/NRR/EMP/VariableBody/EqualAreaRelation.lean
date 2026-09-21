/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.AreaVector

/-!
# `NRR.EMP.VariableBody.EqualAreaRelation` — closedness of the equal-area relation

Using the joint continuity of the area vector, the relation "the weight `w` is an equal-area weight
for the sites `s` inside the variable body `C`" is a finite intersection of zero sets and hence
closed, and adding the normalization `∑ i, w i = 0` keeps it closed. Composing with a continuous
site family yields the closed normalized-weight graph over any topological parameter space.

* `isClosed_isEqualAreaWeight` — the equal-area relation is closed.
* `isClosed_isNormalizedEqualAreaWeight` — the normalized equal-area relation is closed.
* `NormalizedWeightGraph`, `isClosed_normalizedWeightGraph` — the closed graph over a continuous
  site family.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR.EMP.VariableBody

variable {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}

/-- The variable-body equal-area predicate is exactly the fixed-body predicate of `EMP` applied to
the solid body of `C`. -/
theorem isEqualAreaWeight_iff_emp
    (hA : 0 < A) (C : BodySpace K A) (s : Config n) (w : Fin n → ℝ) :
    IsEqualAreaWeight hA C s w ↔ EMP.IsEqualAreaWeight (solidBody hA C) s.pts w :=
  Iff.rfl

/-- The equal-area predicate as a componentwise equality of the area vector with the target area. -/
theorem isEqualAreaWeight_iff_areaVec
    (hA : 0 < A) (C : BodySpace K A) (s : Config n) (w : Fin n → ℝ) :
    IsEqualAreaWeight hA C s w ↔ ∀ i, areaVec hA C s w i = targetArea C n :=
  Iff.rfl

/-- The normalization predicate as vanishing of the weight sum. -/
theorem weightNormalized_iff_sum
    (w : Fin n → ℝ) :
    EMP.WeightNormalized w ↔ ∑ i, w i = 0 :=
  Iff.rfl

/-- **The equal-area relation is closed.** The set of triples `(C, s, w)` for which `w` is an
equal-area weight for `s` in `C` is closed, being the finite intersection over the sites of the zero
sets of the continuous functions `areaVec hA C s w i - targetArea C n`. -/
theorem isClosed_isEqualAreaWeight
    (hA : 0 < A) :
    IsClosed {
      z : BodySpace K A × Config n × (Fin n → ℝ) |
        IsEqualAreaWeight hA z.1 z.2.1 z.2.2
    } := by
  have hset :
      {z : BodySpace K A × Config n × (Fin n → ℝ) |
          IsEqualAreaWeight hA z.1 z.2.1 z.2.2}
        = ⋂ i, {z | areaVec hA z.1 z.2.1 z.2.2 i = targetArea z.1 n} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact isEqualAreaWeight_iff_areaVec hA z.1 z.2.1 z.2.2
  rw [hset]
  refine isClosed_iInter (fun i => ?_)
  exact isClosed_eq
    ((continuous_apply i).comp (continuous_areaVec hA))
    (continuous_targetArea.comp continuous_fst)

/-- **The normalized equal-area relation is closed.** Intersect the closed equal-area relation with
the closed normalization locus `∑ i, w i = 0`. -/
theorem isClosed_isNormalizedEqualAreaWeight
    (hA : 0 < A) :
    IsClosed {
      z : BodySpace K A × Config n × (Fin n → ℝ) |
        IsNormalizedEqualAreaWeight hA z.1 z.2.1 z.2.2
    } := by
  have hset :
      {z : BodySpace K A × Config n × (Fin n → ℝ) |
          IsNormalizedEqualAreaWeight hA z.1 z.2.1 z.2.2}
        = {z | IsEqualAreaWeight hA z.1 z.2.1 z.2.2}
            ∩ {z | EMP.WeightNormalized z.2.2} := by
    ext z; exact Iff.rfl
  rw [hset]
  refine (isClosed_isEqualAreaWeight hA).inter ?_
  have hsum :
      Continuous fun z : BodySpace K A × Config n × (Fin n → ℝ) => ∑ i, z.2.2 i :=
    continuous_finsetSum _
      (fun i _ => (continuous_apply i).comp (continuous_snd.comp continuous_snd))
  exact isClosed_eq hsum continuous_const

/-- The **normalized-weight graph** over a topological parameter space `X` carrying a continuous
site family `sites : C(X, Config n)`: the set of pairs `((C, x), w)` for which `w` is a normalized
equal-area weight for the sites `sites x` inside the variable body `C`. -/
def NormalizedWeightGraph
    {X : Type*} [TopologicalSpace X]
    (sites : C(X, Config n)) (hA : 0 < A) :
    Set ((BodySpace K A × X) × (Fin n → ℝ)) :=
  {z | IsNormalizedEqualAreaWeight hA z.1.1 (sites z.1.2) z.2}

/-- **The normalized-weight graph is closed.** It is the preimage of the closed normalized
equal-area relation under the continuous reparameterization `((C, x), w) ↦ (C, sites x, w)`. -/
theorem isClosed_normalizedWeightGraph
    {X : Type*} [TopologicalSpace X]
    (sites : C(X, Config n)) (hA : 0 < A) :
    IsClosed (NormalizedWeightGraph (K := K) (A := A) sites hA) := by
  have hmap :
      Continuous fun z : (BodySpace K A × X) × (Fin n → ℝ) =>
        ((z.1.1, sites z.1.2, z.2) : BodySpace K A × Config n × (Fin n → ℝ)) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((sites.continuous.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  exact (isClosed_isNormalizedEqualAreaWeight hA).preimage hmap

end NRR.EMP.VariableBody
