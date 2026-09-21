/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapExpansion

/-!
# The peel step in model form

The cap value successor law transported to the model: the peel
rotation splits as a same-arity permutation followed by an arity
cast (`CapPerm`), and the cap value at `m + 1` is the split cap
value of the permuted-and-cast vector.  The colour action of the
permutation is the only remaining ingredient of the closed form.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped TensorProduct

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

/-- The peel arity identity, pinned. -/
theorem capPeelArity (m : ℕ) :
    (m + 1) + (m + 1) = (m + m) + 2 := by omega

/-- **The split cap value**: the smaller cap tensored with one
evaluation, on a transported vector. -/
noncomputable def splitCapVal (m : ℕ)
    (w : (superPow (stdSuperPair k ℓ) ((m + m) + 2)).even) : ℂ :=
  letI := P.braided
  omegaFun f P (HomSpace.tensor f (m + m) 0 2 0
      (bundleCapClass f m) (evClass f))
    (((stdToOmega f P e ((m + m) + 2)) :
      SuperVect.Hom _ _).evenMap w)

/-- The split cap value is additive over finite sums. -/
theorem splitCapVal_sum {ι : Type*} (m : ℕ) (s : Finset ι)
    (g : ι → (superPow (stdSuperPair k ℓ) ((m + m) + 2)).even) :
    splitCapVal f P e m (∑ i ∈ s, g i) =
      ∑ i ∈ s, splitCapVal f P e m (g i) := by
  unfold splitCapVal
  rw [map_sum, map_sum]

/-- The split cap value is homogeneous. -/
theorem splitCapVal_smul (m : ℕ) (r : ℂ)
    (w : (superPow (stdSuperPair k ℓ) ((m + m) + 2)).even) :
    splitCapVal f P e m (r • w) =
      r * splitCapVal f P e m w := by
  unfold splitCapVal
  rw [map_smul, map_smul, smul_eq_mul]

/-- **The split cap value in coordinates.** -/
theorem splitCapVal_expansion (m : ℕ)
    (w : (superPow (stdSuperPair k ℓ) ((m + m) + 2)).even) :
    splitCapVal f P e m w =
      ∑ c : {c : MixedColouring k ℓ ((m + m) + 2) // c.IsEven},
        coordOf w c.val *
          splitCapVal f P e m (evenBasisVec c) := by
  conv_lhs => rw [coord_expansion w]
  rw [splitCapVal_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [splitCapVal_smul]
  rw [show coordOf w c.val =
      (colourPowerEquiv k ℓ ((m + m) + 2)).evenEquiv w c from by
    unfold coordOf
    rw [dif_pos c.prop]]
  rfl

/-- The split cap value on merges: `CapSplit` restated. -/
theorem splitCapVal_merge (m : ℕ)
    (x : (superPow (stdSuperPair k ℓ) (m + m)).even)
    (y : (superPow (stdSuperPair k ℓ) 2).even) :
    letI := P.braided
    splitCapVal f P e m
        (((powMerge (stdSuperPair k ℓ) (m + m) 2) :
          SuperVect.Hom _ _).evenMap (evenPair x y)) =
      capVal f P e m x *
        omegaFun f P (evClass f)
          (((stdToOmega f P e 2) :
            SuperVect.Hom _ _).evenMap y) :=
  omegaFun_capTensor_merge f P e m x y

-- Raised budget: the merge of an odd pair is pushed through the
-- split cap on every graded block.
/-- **The split cap value vanishes on odd merges.** -/
theorem splitCapVal_oddMerge (m : ℕ)
    (x : (superPow (stdSuperPair k ℓ) (m + m)).odd)
    (y : (superPow (stdSuperPair k ℓ) 2).odd) :
    splitCapVal f P e m
        (((powMerge (stdSuperPair k ℓ) (m + m) 2) :
          SuperVect.Hom _ _).evenMap
          (((0 : (superPow (stdSuperPair k ℓ) (m + m)).even ⊗[ℂ]
              (superPow (stdSuperPair k ℓ) 2).even),
            x ⊗ₜ[ℂ] y) :
            (SuperVect.tensorObj
              (superPow (stdSuperPair k ℓ) (m + m))
              (superPow (stdSuperPair k ℓ) 2)).even)) = 0 := by
  letI := P.braided
  have hmerge := congrArg (fun z :
      (superPow (stdSuperPair k ℓ) (m + m) ⊗
        superPow (stdSuperPair k ℓ) 2 ⟶
        P.ω.obj (SkeinObj.mk ((m + m) + 2))) =>
    (z : SuperVect.Hom _ _).evenMap
      (((0 : (superPow (stdSuperPair k ℓ) (m + m)).even ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) 2).even),
        x ⊗ₜ[ℂ] y) :
        (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) (m + m))
          (superPow (stdSuperPair k ℓ) 2)).even))
    (stdToOmega_merge f P e (m + m) 2)
  refine Eq.trans (congrArg (omegaFun f P
    (HomSpace.tensor f (m + m) 0 2 0
      (bundleCapClass f m) (evClass f))) hmerge.symm) ?_
  show omegaFun f P (HomSpace.tensor f (m + m) 0 2 0
      (bundleCapClass f m) (evClass f))
    (((μ P.ω (SkeinObj.mk (m + m)) (SkeinObj.mk 2)) :
      SuperVect.Hom _ _).evenMap
      (((stdToOmega f P e (m + m) ⊗ₘ stdToOmega f P e 2) :
        SuperVect.Hom _ _).evenMap
        (((0 : (superPow (stdSuperPair k ℓ) (m + m)).even ⊗[ℂ]
            (superPow (stdSuperPair k ℓ) 2).even),
          x ⊗ₜ[ℂ] y) :
          (SuperVect.tensorObj
            (superPow (stdSuperPair k ℓ) (m + m))
            (superPow (stdSuperPair k ℓ) 2)).even))) = 0
  rw [show ((stdToOmega f P e (m + m) ⊗ₘ stdToOmega f P e 2) :
      SuperVect.Hom _ _).evenMap
      (((0 : (superPow (stdSuperPair k ℓ) (m + m)).even ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) 2).even),
        x ⊗ₜ[ℂ] y) :
        (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) (m + m))
          (superPow (stdSuperPair k ℓ) 2)).even) =
    oddPair
      ((stdToOmega f P e (m + m) :
        SuperVect.Hom _ _).oddMap x)
      ((stdToOmega f P e 2 :
        SuperVect.Hom _ _).oddMap y) from
    tensorHom_oddPair _ _ _ _]
  exact omegaFun_tensor_oddPair f P
    (bundleCapClass f m) (evClass f) _ _

-- Raised budget: peeling one cap rewrites the transport along a
-- permutation and an arity cast at once.
/-- **The cap value successor law in model form.** -/
theorem capVal_succ (m : ℕ)
    (v : (superPow (stdSuperPair k ℓ) ((m + 1) + (m + 1))).even) :
    capVal f P e (m + 1) v =
      splitCapVal f P e m
        (((modelPermMap (capPeelPerm m) ≫
            eqToHom (congrArg (superPow (stdSuperPair k ℓ))
              (capPeelArity m))) :
          SuperVect.Hom _ _).evenMap v) := by
  letI := P.braided
  have hchain : stdToOmega f P e ((m + 1) + (m + 1)) ≫
      P.ω.map (bundleMapClass f (capPeelRotation m)) =
    (modelPermMap (capPeelPerm m) ≫
        eqToHom (congrArg (superPow (stdSuperPair k ℓ))
          (capPeelArity m))) ≫
      stdToOmega f P e ((m + m) + 2) := by
    have hmap : P.ω.map (bundleMapClass f (capPeelRotation m)) =
        P.ω.map ((bundleMapClass f ((capPeelPerm m) :
            Fin ((m + 1) + (m + 1)) ≃
              Fin ((m + 1) + (m + 1))) :
          (SkeinObj.mk ((m + 1) + (m + 1)) : SkeinObj f) ⟶
            SkeinObj.mk ((m + 1) + (m + 1))) ≫
          bundleMapClass f (finCongr (capPeelArity m))) :=
      congrArg P.ω.map (bmc_capPeel_split f m)
    rw [hmap, P.ω.map_comp, ← Category.assoc,
      stdToOmega_bmc_perm_all f P e ((m + 1) + (m + 1))
        (capPeelPerm m),
      Category.assoc,
      stdToOmega_bmc_cast f P e (capPeelArity m),
      ← Category.assoc]
  refine Eq.trans (omegaFun_cap_succ f P m
    (((stdToOmega f P e ((m + 1) + (m + 1))) :
      SuperVect.Hom _ _).evenMap v)) ?_
  have hval := congrArg (fun z :
      (superPow (stdSuperPair k ℓ) ((m + 1) + (m + 1)) ⟶
        P.ω.obj (SkeinObj.mk ((m + m) + 2))) =>
    (z : SuperVect.Hom _ _).evenMap v) hchain
  exact congrArg (omegaFun f P
    (HomSpace.tensor f (m + m) 0 2 0
      (bundleCapClass f m) (evClass f))) hval

end RS
