/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Operations
public import LeanPool.NandakumarRamanaRao.NRR.Multivalued.PhaseInterfaces

/-!
# `NRR.Multivalued.ChildEvaluation` — nice multivalued functions on continuous children

This module combines the continuous variable power-partition children on the lower-area
convex-body hyperspace with an arbitrary nice multivalued function `φ` on that hyperspace.

For a parameter `z = ((C, x), t)` with base body `C`, site parameter `x`, and signed-interval
coordinate `t`, and for a site index `i`, the child evaluation `φ.childEval` evaluates `φ` at the
canonical child `child sites hA hn (C, x) i` and the interval coordinate `t`. The child depends
continuously on `(C, x)` and the interval coordinate is continuous, so each coordinate evaluation
is continuous; the whole vector of coordinate evaluations is continuous by `continuous_pi`.

The simultaneous-zero set collects the parameters at which `φ` vanishes on every child at once. It
is a finite intersection of coordinate zero sets, hence closed, and membership is exactly the
vanishing of every child evaluation coordinate.

The output is kept in `Fin n → ℝ`; no projection to a zero-sum representation is performed here,
and no common zero, equivariance, or obstruction result is assumed.
-/

@[expose] public section

open NRR.Geometry

namespace NRR

namespace NiceMV

variable {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The **child evaluation** of a nice multivalued function `φ` at parameter `z = ((C, x), t)` and
site index `i`: evaluate `φ` at the canonical child `child sites hA hn (C, x) i` and the signed
interval coordinate `t`. -/
noncomputable def childEval
    (sites : EMP.VariableBody.SiteFamily X n)
    (hA : 0 < A) (hn : 0 < n)
    (φ : NiceMV (BodySpace K (A / (n : ℝ))))
    (z : (BodySpace K A × X) × SignedInterval)
    (i : Fin n) : ℝ :=
  φ.eval
    (EMP.VariableBody.child sites hA hn z.1 i)
    z.2

variable (sites : EMP.VariableBody.SiteFamily X n)
variable (hA : 0 < A) (hn : 0 < n)
variable (φ : NiceMV (BodySpace K (A / (n : ℝ))))

/-- **Continuity of a child evaluation coordinate.** The child depends continuously on `(C, x)` via
`EMP.VariableBody.continuous_child`, the interval coordinate is continuous, and `φ.continuous_eval`
composes the two. -/
theorem continuous_childEval
    (i : Fin n) :
    Continuous fun z : (BodySpace K A × X) × SignedInterval =>
      φ.childEval sites hA hn z i :=
  φ.continuous_eval.comp
    (((EMP.VariableBody.continuous_child sites hA hn i).comp continuous_fst).prodMk
      continuous_snd)

/-- **Continuity of the child evaluation vector.** The whole finite family of coordinate
evaluations depends continuously on the parameter, by `continuous_pi`. -/
theorem continuous_childEvalVec :
    Continuous fun z : (BodySpace K A × X) × SignedInterval =>
      fun i : Fin n => φ.childEval sites hA hn z i :=
  continuous_pi (fun i => φ.continuous_childEval sites hA hn i)

/-- The **simultaneous child-zero set**: the parameters at which `φ` vanishes on every child at
once. -/
def allChildrenZeroSet
    (sites : EMP.VariableBody.SiteFamily X n)
    (hA : 0 < A) (hn : 0 < n)
    (φ : NiceMV (BodySpace K (A / (n : ℝ)))) :
    Set ((BodySpace K A × X) × SignedInterval) :=
  {z | ∀ i, φ.Zero
    (EMP.VariableBody.child sites hA hn z.1 i) z.2}

omit [CompactSpace X] in
/-- **Membership in the simultaneous child-zero set** is exactly the vanishing of every child
evaluation coordinate. -/
theorem mem_allChildrenZeroSet_iff
    (z : (BodySpace K A × X) × SignedInterval) :
    z ∈ φ.allChildrenZeroSet sites hA hn ↔
      ∀ i, φ.childEval sites hA hn z i = 0 :=
  Iff.rfl

/-- **Closedness of the simultaneous child-zero set.** It is the finite intersection over `i` of
the coordinate zero sets, each closed as the zero set of a continuous coordinate evaluation. -/
theorem isClosed_allChildrenZeroSet :
    IsClosed (φ.allChildrenZeroSet sites hA hn) := by
  have : φ.allChildrenZeroSet sites hA hn =
      ⋂ i : Fin n, {z | φ.childEval sites hA hn z i = 0} := by
    ext z
    simp only [allChildrenZeroSet, Set.mem_ofPred_eq, Set.mem_iInter, zero_iff, childEval]
  rw [this]
  exact isClosed_iInter fun i =>
    isClosed_eq (φ.continuous_childEval sites hA hn i) continuous_const

end NiceMV

end NRR
