/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SortFactor

/-!
# The class-level star factorization

Transporting the fragment-level star factorization to Hom
classes: the star-union class of a closed fragment is the circle
power times the iterated vertex-star tensor class composed with
the bundle map of the sort.
-/

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- **Free circles are a scalar on classes**, at any arity. -/
theorem ofFragment_addCircles {t : ℕ} (Y : Fragment (Fin t))
    (c : ℕ) :
    HomSpace.ofFragment f.val (addCircles Y c) =
      circleVal f ^ c • HomSpace.ofFragment f.val Y :=
  ((ofFragment_relabel_unitcast f (s := t) (t := 0)
      (addCircles Y c)).symm.trans
    ((HomSpace.ofFragment_congr f
      (addCirclesTensor (s := t) (t := 0) Y c).symm).trans
      (ofFragment_tensor_circles f (s := t) (t := 0) Y c))).trans
    (congrArg (fun z => circleVal f ^ c • z)
      (ofFragment_relabel_unitcast f (s := t) (t := 0) Y))

/-- Composing with a bundle-map class relabels the fragment along
the outgoing transport. -/
theorem comp_bundleMapClass {s n m : ℕ} (e : Fin n ≃ Fin m)
    (X : Fragment (Fin (s + n))) :
    HomSpace.comp f s n m (HomSpace.ofFragment f.val X)
        (bundleMapClass f e) =
      HomSpace.ofFragment f.val (X.relabel
        (finSumFinEquiv.symm.trans
          ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin s)) e).trans
            finSumFinEquiv))) := by
  rw [bundleMapClass, HomSpace.comp_ofFragment]
  exact HomSpace.ofFragment_congr f (composeBundleMap e X)

/-- At source arity zero the outgoing transport is the map
itself, up to padding casts. -/
theorem sort_transport_eq {N M : ℕ} (σ : Fin N ≃ Fin M) :
    ((finCongr (by omega : N = 0 + N)).trans
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin 0)) σ).trans
          finSumFinEquiv)) : Fin N ≃ Fin (0 + M)) =
    σ.trans (finCongr (by omega : M = 0 + M)) := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  change (finSumFinEquiv ((_root_.Equiv.sumCongr
      (_root_.Equiv.refl (Fin 0)) σ)
    (finSumFinEquiv.symm (finCongr
      (by omega : N = 0 + N) x)))).val = _
  rw [show (finCongr (by omega : N = 0 + N) x :
        Fin (0 + N)) = Fin.natAdd 0 x from
      Fin.ext (show x.val = 0 + x.val by omega),
    finSumFinEquiv_symm_apply_natAdd]
  change 0 + (σ x).val = (σ x).val
  omega

/-- **The class-level star factorization**: the star-union class
is the circle power times the iterated vertex-star tensor class,
composed with the bundle map of the sort. -/
theorem starClass_factor (W : ClosedFragment) :
    starClass f W = circleVal f ^ W.circles •
      HomSpace.comp f 0 ((degList (starAssignEnum W)).sum)
        (edgeCount W + edgeCount W)
        (HomSpace.ofFragment f.val
          ((starTensor (degList (starAssignEnum W))).relabel
            (finCongr (by omega :
              (degList (starAssignEnum W)).sum =
                0 + (degList (starAssignEnum W)).sum))))
        (bundleMapClass f
          (sortEquiv (starAssignEnum W)).symm) := by
  rw [comp_bundleMapClass,
    HomSpace.ofFragment_congr f
      (Fragment.Equiv.relabelTrans
        (starTensor (degList (starAssignEnum W))) _ _),
    show (finCongr (by omega :
        (degList (starAssignEnum W)).sum =
          0 + (degList (starAssignEnum W)).sum)).trans
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin 0))
          (sortEquiv (starAssignEnum W)).symm).trans
          finSumFinEquiv)) =
      (sortEquiv (starAssignEnum W)).symm.trans
        (finCongr (by omega : edgeCount W + edgeCount W =
          0 + (edgeCount W + edgeCount W))) from
      sort_transport_eq _]
  rw [starClass,
    HomSpace.ofFragment_congr f
      ((Fragment.Equiv.relabelCongr (starUnionFactor W)
        (finCongr (by omega : edgeCount W + edgeCount W =
          0 + (edgeCount W + edgeCount W)))).trans
        (Fragment.Equiv.relabelTrans _ _ _))]
  exact ofFragment_addCircles f
    ((starTensor (degList (starAssignEnum W))).relabel
      ((sortEquiv (starAssignEnum W)).symm.trans
        (finCongr (by omega : edgeCount W + edgeCount W =
          0 + (edgeCount W + edgeCount W)))))
    W.circles

end RS
