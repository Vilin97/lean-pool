/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
/-!
# Functoriality of topological abelianization under equivalence

A continuous multiplicative equivalence carries the closure of the
commutator subgroup onto the corresponding closure.  It therefore descends
to a continuous multiplicative equivalence of topological abelianizations.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

universe u v

variable {G : Type u} {H : Type v}
  [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

private theorem topologicalCommutatorClosure_le_comap
    (e : G ≃ₜ* H) :
    (commutator G).topologicalClosure ≤
      (commutator H).topologicalClosure.comap
        e.toMulEquiv.toMonoidHom := by
  apply Subgroup.topologicalClosure_minimal
  · intro x hx
    change e x ∈ (commutator H).topologicalClosure
    apply Subgroup.le_topologicalClosure
    have hmap :
        (commutator G).map e.toMulEquiv.toMonoidHom =
          commutator H := by
      rw [map_commutator_eq]
      have hrange : e.toMulEquiv.toMonoidHom.range = ⊤ :=
        MonoidHom.range_eq_top.mpr e.surjective
      rw [hrange]
      rfl
    rw [← hmap]
    exact Subgroup.mem_map_of_mem e.toMulEquiv.toMonoidHom hx
  · exact (Subgroup.isClosed_topologicalClosure _).preimage e.continuous

/-- Descend a continuous group equivalence to the topological abelianizations. -/
def topologicalAbelianizationMap (e : G ≃ₜ* H) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
  QuotientGroup.map
    (commutator G).topologicalClosure
    (commutator H).topologicalClosure
    e.toMulEquiv.toMonoidHom
    (by exact topologicalCommutatorClosure_le_comap e)

@[simp]
private theorem topologicalAbelianizationMap_mk
    (e : G ≃ₜ* H) (x : G) :
    topologicalAbelianizationMap e (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

private theorem topologicalAbelianizationMap_continuous
    (e : G ≃ₜ* H) :
    Continuous (topologicalAbelianizationMap e) := by
  apply (QuotientGroup.isQuotientMap_mk
    (commutator G).topologicalClosure).continuous_iff.2
  change Continuous (QuotientGroup.mk ∘ e.toHomeomorph)
  exact QuotientGroup.continuous_mk.comp e.continuous

/-- The multiplicative equivalence induced on topological abelianizations. -/
def topologicalAbelianizationMulEquiv (e : G ≃ₜ* H) :
    TopologicalAbelianization G ≃* TopologicalAbelianization H where
  toFun := topologicalAbelianizationMap e
  invFun := topologicalAbelianizationMap e.symm
  left_inv q := by
    refine q.inductionOn' ?_
    intro x
    simp
  right_inv q := by
    refine q.inductionOn' ?_
    intro x
    simp
  map_mul' x y := map_mul (topologicalAbelianizationMap e) x y

/-- A continuous multiplicative equivalence induces the canonical
continuous multiplicative equivalence of topological abelianizations. -/
noncomputable def topologicalAbelianizationCongr (e : G ≃ₜ* H) :
    TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H :=
  { topologicalAbelianizationMulEquiv e with
    continuous_toFun := by exact topologicalAbelianizationMap_continuous e
    continuous_invFun := by exact topologicalAbelianizationMap_continuous e.symm }

/-- States the theorem `topologicalAbelianizationCongr_mk`. -/
@[simp]
theorem topologicalAbelianizationCongr_mk
    (e : G ≃ₜ* H) (x : G) :
    topologicalAbelianizationCongr e (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

end LocalClassFieldTheory
