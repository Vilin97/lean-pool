/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinTrace
import LeanPool.RegtsSevenster.RS.Novel.Envelope.CycleNormal
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTraceCyclic
import LeanPool.RegtsSevenster.RS.Novel.Skein.BraidedInstance

/-!
# The skein Frobenius identity

The bridge from permutation classes to bundle-map classes, and the
one consequence the trace calculus needs: the class of a block-sum
permutation is the tensor of the two block classes.

Both are fragment computations.  A permutation fragment relabels
the strand bundle by the permutation on the outgoing labels, which
is exactly a bundle map; and conjugating a block sum by
`finSumFinEquiv` is the tensor of the blocks.  The trace
factorization these feed is `BlockFactor.lean`, and the Frobenius
identity itself `BlockAssembly.lean`.
-/

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### Bridge: permutation classes are bundle-map classes -/

/-- `permHighEquiv σ = outMapEquiv σ`: both fix the first `t`
labels and permute the last `t` labels by `σ`. -/
private theorem permHighEquiv_eq_outMapEquiv {t : ℕ}
    (σ : Equiv.Perm (Fin t)) :
    permHighEquiv σ = outMapEquiv σ := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  by_cases hx : x.val < t
  · -- Low label: both are the identity
    have h1 : (permHighEquiv σ x).val = x.val := by
      show (if h : x.val < t then x else _).val = x.val
      rw [dif_pos hx]
    have h2 : (outMapEquiv σ x).val = x.val := by
      rw [show x = Fin.castAdd t ⟨x.val, hx⟩ from Fin.ext rfl,
        outMapEquiv_castAdd]
    exact h1.trans h2.symm
  · -- High label: both apply σ
    have hxt := x.isLt
    have h1 : (permHighEquiv σ x).val =
        t + (σ ⟨x.val - t, by omega⟩).val := by
      show (if h : x.val < t then x else _).val = _
      rw [dif_neg hx]
    have hxeq : x = Fin.natAdd t ⟨x.val - t, by omega⟩ :=
      Fin.ext (by show x.val = t + (x.val - t); omega)
    have h2 : (outMapEquiv σ x).val =
        t + (σ ⟨x.val - t, by omega⟩).val := by
      conv_lhs => rw [hxeq]
      rw [outMapEquiv_natAdd]; rfl
    exact h1.trans h2.symm

/-- **Bridge lemma**: `permClass f n σ = bundleMapClass f σ`. -/
theorem permClass_eq_bundleMapClass (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    permClass f n σ = bundleMapClass f σ := by
  show HomSpace.ofFragment f.val (permFragment σ) =
    HomSpace.ofFragment f.val (bundleMap σ)
  exact HomSpace.ofFragment_congr f
    ((permFragmentRelabelBundle σ).trans
      (Fragment.Equiv.relabelEq (strandBundle n)
        (permHighEquiv_eq_outMapEquiv σ)))

/-! ### The tensor of block classes -/

/-- `finSumFinEquiv.permCongr (sumCongr σ τ) = tensorMapEquiv σ τ`:
both conjugate the block-sum permutation by `finSumFinEquiv`. -/
private theorem permCongr_sumCongr_eq_tensorMapEquiv
    {a b : ℕ} (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    finSumFinEquiv.permCongr (Equiv.sumCongr σ τ) =
      tensorMapEquiv σ τ := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  show (finSumFinEquiv ((Equiv.sumCongr σ τ)
    (finSumFinEquiv.symm x))).val =
    (tensorMapEquiv σ τ x).val
  unfold tensorMapEquiv
  rfl

/-- The permutation class of a block-sum permutation is the tensor
of the block classes. -/
theorem permClass_sumCongr (a b : ℕ) (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) :
    permClass f (a + b)
      (finSumFinEquiv.permCongr (Equiv.sumCongr σ τ)) =
    (MonoidalCategoryStruct.tensorHom
        (X₁ := SkeinObj.mk a) (Y₁ := SkeinObj.mk a)
        (X₂ := SkeinObj.mk b) (Y₂ := SkeinObj.mk b)
        (permClass f a σ) (permClass f b τ) :
      End (SkeinObj.mk (a + b))) := by
  rw [permClass_eq_bundleMapClass,
    permCongr_sumCongr_eq_tensorMapEquiv]
  show bundleMapClass f (tensorMapEquiv σ τ) =
    HomSpace.tensor f a a b b (permClass f a σ) (permClass f b τ)
  rw [permClass_eq_bundleMapClass, permClass_eq_bundleMapClass]
  exact (bundleMapClass_tensor f σ τ).symm

end RS
