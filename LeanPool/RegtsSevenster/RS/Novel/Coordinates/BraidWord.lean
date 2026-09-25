/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.AdjSwapBmc

/-!
# Bundle-map permutations through the model transport

Composing the adjacent-swap collapse with the transport
intertwining along an adjacent-transposition word: the image of
any permutation bundle map conjugates through `stdToOmega` into
the corresponding word of model braidings.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The adjacent transposition is the adjacent swap. -/
theorem adjTrans_eq_adjSwap {n : ℕ} (i : Fin n) :
    (adjTrans i : Fin (n + 1) ≃ Fin (n + 1)) =
      adjSwapEquiv (n + 1) i.val (by omega) := by
  unfold adjTrans adjSwapEquiv
  rw [show Fin.castSucc i = (⟨i.val, by omega⟩ : Fin (n + 1))
      from Fin.ext rfl,
    show Fin.succ i = (⟨i.val + 1, by omega⟩ : Fin (n + 1))
      from Fin.ext rfl]

/-- The model-side braiding word. -/
noncomputable def powBraidWord (V : SuperVect) {n : ℕ} :
    List (Fin n) → (superPow V (n + 1) ⟶ superPow V (n + 1))
  | [] => 𝟙 _
  | i :: w => powBraidWord V w ≫
      powBraid V (n + 1) i.val (by omega)

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

/-- **The word intertwining**: the image of the word's product
bundle map conjugates into the model braiding word. -/
theorem stdToOmega_bmc_word {n : ℕ} (w : List (Fin n)) :
    letI := P.braided
    stdToOmega f P e (n + 1) ≫ P.ω.map (bundleMapClass f
        (((w.map adjTrans).prod : _root_.Equiv.Perm
          (Fin (n + 1))) : Fin (n + 1) ≃ Fin (n + 1))) =
      powBraidWord (stdSuperPair k ℓ) w ≫
        stdToOmega f P e (n + 1) := by
  let := P.braided
  induction w with
  | nil =>
    rw [List.map_nil, List.prod_nil]
    have hone : bundleMapClass f
        (((1 : _root_.Equiv.Perm (Fin (n + 1))) :
          Fin (n + 1) ≃ Fin (n + 1))) =
        𝟙 (SkeinObj.mk (n + 1) : SkeinObj f) := by
      rw [show ((1 : _root_.Equiv.Perm (Fin (n + 1))) :
          Fin (n + 1) ≃ Fin (n + 1)) =
        _root_.Equiv.refl (Fin (n + 1)) from rfl]
      exact bundleMapClass_refl f (n + 1)
    rw [hone]
    have hmapid : P.ω.map (𝟙 (SkeinObj.mk (n + 1) :
        SkeinObj f)) = 𝟙 (P.ω.obj (SkeinObj.mk (n + 1))) :=
      P.ω.map_id _
    rw [hmapid]
    change stdToOmega f P e (n + 1) ≫ 𝟙 _ =
      𝟙 _ ≫ stdToOmega f P e (n + 1)
    rw [Category.comp_id, Category.id_comp]
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons]
    have hmul : ((adjTrans i * (w.map adjTrans).prod :
        _root_.Equiv.Perm (Fin (n + 1))) :
        Fin (n + 1) ≃ Fin (n + 1)) =
        (((w.map adjTrans).prod : _root_.Equiv.Perm
          (Fin (n + 1))) : Fin (n + 1) ≃ Fin (n + 1)).trans
          (adjTrans i) := rfl
    rw [hmul]
    have hbmc : bundleMapClass f
        ((((w.map adjTrans).prod : _root_.Equiv.Perm
          (Fin (n + 1))) : Fin (n + 1) ≃ Fin (n + 1)).trans
          (adjTrans i)) =
        HomSpace.comp f (n + 1) (n + 1) (n + 1)
          (bundleMapClass f (((w.map adjTrans).prod :
            _root_.Equiv.Perm (Fin (n + 1))) :
            Fin (n + 1) ≃ Fin (n + 1)))
          (bundleMapClass f (adjTrans i)) :=
      (bundleMapClass_comp f _ _).symm
    rw [hbmc]
    have hmapcomp : P.ω.map (HomSpace.comp f (n + 1) (n + 1)
        (n + 1)
        (bundleMapClass f (((w.map adjTrans).prod :
          _root_.Equiv.Perm (Fin (n + 1))) :
          Fin (n + 1) ≃ Fin (n + 1)))
        (bundleMapClass f (adjTrans i))) =
        P.ω.map (bundleMapClass f (((w.map adjTrans).prod :
          _root_.Equiv.Perm (Fin (n + 1))) :
          Fin (n + 1) ≃ Fin (n + 1))) ≫
        P.ω.map (bundleMapClass f (adjTrans i)) :=
      P.ω.map_comp _ _
    rw [hmapcomp]
    have hswap : bundleMapClass f (adjTrans i) =
        skeinPowBraid f (n + 1) i.val (by omega) := by
      rw [adjTrans_eq_adjSwap]
      exact (skeinPowBraid_bmc f (n + 1) i.val (by omega)).symm
    rw [hswap]
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (fun z => z ≫ P.ω.map
      (skeinPowBraid f (n + 1) i.val (by omega))) ih).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z =>
      powBraidWord (stdSuperPair k ℓ) w ≫ z)
      (stdToOmega_powBraid f P e (n + 1) i.val
        (by omega))).trans ?_
    exact (Category.assoc _ _ _).symm

/-- **The permutation intertwining**: any permutation bundle map
conjugates into the model braiding word of its
adjacent-transposition word. -/
theorem stdToOmega_bmc_perm {n : ℕ}
    (σ : _root_.Equiv.Perm (Fin (n + 1))) :
    letI := P.braided
    stdToOmega f P e (n + 1) ≫ P.ω.map (bundleMapClass f
        (σ : Fin (n + 1) ≃ Fin (n + 1))) =
      powBraidWord (stdSuperPair k ℓ) (adjWord σ) ≫
        stdToOmega f P e (n + 1) := by
  let := P.braided
  have h := stdToOmega_bmc_word f P e (adjWord σ)
  rw [adjWord_spec σ] at h
  exact h

end RS
