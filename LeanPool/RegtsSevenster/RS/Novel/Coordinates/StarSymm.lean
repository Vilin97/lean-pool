/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapPerm

/-!
# Symmetry of the vertex star

All legs of a vertex star meet the same vertex, so any boundary
permutation is absorbed: the star class is symmetric.  This is
the S_d-invariance that makes the vertex coordinates well
defined on multiset data.
-/

@[expose] public section

namespace RS

/-- The vertex star absorbs any boundary relabelling. -/
noncomputable def vertexStarRelabelEquiv (d : ℕ)
    (σ : Fin d ≃ Fin d) :
    ((vertexStar d).relabel σ).Equiv (vertexStar d) where
  flagEquiv := _root_.Equiv.sumCongr σ σ
  vertexEquiv := _root_.Equiv.refl Unit
  attach_comm := fun g => by
    rcases g with i | i <;> rfl
  pairing_comm := fun g => by
    rcases g with i | i <;> rfl
  circles_eq := rfl

variable {R : ℕ} (f : EdgeRankParameter R)

/-- **S_d-invariance of the vertex star class**: composing with
any permutation bundle map is absorbed. -/
theorem vertexStarClass_perm (d : ℕ) (σ : Fin d ≃ Fin d) :
    HomSpace.comp f 0 d d (vertexStarClass f d)
        (bundleMapClass f σ) = vertexStarClass f d := by
  rw [show vertexStarClass f d = HomSpace.ofFragment f.val
      ((vertexStar d).relabel (finCongr
        (by omega : d = 0 + d))) from rfl,
    comp_bundleMapClass]
  refine HomSpace.ofFragment_congr f ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  refine (Fragment.Equiv.relabelEq _ (show
      (finCongr (by omega : d = 0 + d)).trans
        (finSumFinEquiv.symm.trans
          ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin 0))
            σ).trans finSumFinEquiv)) =
      σ.trans (finCongr (by omega : d = 0 + d)) from
    sort_transport_eq σ)).trans ?_
  refine ((Fragment.Equiv.relabelTrans _ _ _).symm).trans ?_
  exact Fragment.Equiv.relabelCongr
    (vertexStarRelabelEquiv d σ) _

end RS
