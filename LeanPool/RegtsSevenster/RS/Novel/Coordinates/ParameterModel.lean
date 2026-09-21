/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SortPerm

/-!
# The parameter value over the model

Threading the transports through the factored parameter value: the
argument of the cap functional becomes a model-side vector — the
assembled star vector acted on by the sort's model permutation word
and the degree-sum cast — pushed forward once.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- The model action of a permutation: trivial at arity zero,
the braiding word of the adjacent-transposition word above. -/
noncomputable def modelPermMap :
    {n : ℕ} → (σ : _root_.Equiv.Perm (Fin n)) →
      (superPow (stdSuperPair k ℓ) n ⟶ superPow (stdSuperPair k ℓ) n)
  | 0, _ => 𝟙 _
  | _ + 1, σ => powBraidWord (stdSuperPair k ℓ) (adjWord σ)

/-- The permutation intertwining at every arity. -/
theorem stdToOmega_bmc_perm_all :
    ∀ (n : ℕ) (σ : _root_.Equiv.Perm (Fin n)),
      letI := P.braided
      stdToOmega f P e n ≫ P.ω.map (bundleMapClass f
          (σ : Fin n ≃ Fin n)) =
        modelPermMap σ ≫ stdToOmega f P e n
  | 0, σ => by
    letI := P.braided
    rw [show (σ : Fin 0 ≃ Fin 0) =
        _root_.Equiv.refl (Fin 0) from
      Subsingleton.elim _ _]
    rw [show bundleMapClass f (_root_.Equiv.refl (Fin 0)) =
        𝟙 (SkeinObj.mk 0 : SkeinObj f) from
      bundleMapClass_refl f 0]
    rw [show P.ω.map (𝟙 (SkeinObj.mk 0 : SkeinObj f)) =
        𝟙 (P.ω.obj (SkeinObj.mk 0)) from P.ω.map_id _]
    show stdToOmega f P e 0 ≫ 𝟙 _ =
      𝟙 _ ≫ stdToOmega f P e 0
    rw [Category.comp_id, Category.id_comp]
  | n + 1, σ => stdToOmega_bmc_perm f P e σ

-- Raised budget: the parameter is rewritten over the model, so the
-- star vector, the sort word and the degree-sum recast all unfold
-- in one term.
/-- **The parameter value over the model**: the cap functional
evaluated on the transported model vector — the assembled star
vector, permuted by the sort word and recast along the degree
sum. -/
theorem parameter_model (W : ClosedFragment)
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _) :
    letI := P.braided
    f.val W = circleVal f ^ W.circles *
      omegaFun f P (bundleCapClass f (edgeCount W))
        (((stdToOmega f P e (edgeCount W + edgeCount W)) :
          SuperVect.Hom _ _).evenMap
          (((eqToHom (congrArg (superPow (stdSuperPair k ℓ))
              (degList_sum (starAssignEnum W))) :
            superPow (stdSuperPair k ℓ)
              ((degList (starAssignEnum W)).sum) ⟶
            superPow (stdSuperPair k ℓ)
              (edgeCount W + edgeCount W)) :
            SuperVect.Hom _ _).evenMap
            (((modelPermMap (sortSplitPerm W)) :
              SuperVect.Hom _ _).evenMap
              (modelStarVec f P e'
                (degList (starAssignEnum W)))))) := by
  letI := P.braided
  rw [parameter_star_factor f P W]
  refine congrArg (fun z => circleVal f ^ W.circles *
    omegaFun f P (bundleCapClass f (edgeCount W)) z) ?_
  -- Replace the assembled vector by its model form.
  rw [show omegaStarVec f P (degList (starAssignEnum W)) =
      ((stdToOmega f P e
        ((degList (starAssignEnum W)).sum)) :
        SuperVect.Hom _ _).evenMap
        (modelStarVec f P e' (degList (starAssignEnum W)))
      from (stdToOmega_modelStarVec f P e e' hee' _).symm]
  -- Split the sort bundle map.
  have hsplit := (congrArg (fun z :
      ((SkeinObj.mk ((degList (starAssignEnum W)).sum) :
        SkeinObj f) ⟶
        SkeinObj.mk (edgeCount W + edgeCount W)) =>
    P.ω.map z) (bmc_sort_split f W)).trans
    (P.ω.map_comp
      (bundleMapClass f ((sortSplitPerm W) :
        Fin ((degList (starAssignEnum W)).sum) ≃
          Fin ((degList (starAssignEnum W)).sum)))
      (bundleMapClass f (finCongr
        (degList_sum (starAssignEnum W)))))
  refine Eq.trans (congrArg (fun z :
      (P.ω.obj (SkeinObj.mk
        ((degList (starAssignEnum W)).sum)) ⟶
        P.ω.obj (SkeinObj.mk
          (edgeCount W + edgeCount W))) =>
    (z : SuperVect.Hom _ _).evenMap
      ((stdToOmega f P e
        ((degList (starAssignEnum W)).sum) :
        SuperVect.Hom _ _).evenMap
        (modelStarVec f P e'
          (degList (starAssignEnum W))))) hsplit) ?_
  -- Swap the permutation across the transport.
  have hperm := congrArg (fun z :
      (superPow (stdSuperPair k ℓ)
        ((degList (starAssignEnum W)).sum) ⟶
        P.ω.obj (SkeinObj.mk
          ((degList (starAssignEnum W)).sum))) =>
    (z : SuperVect.Hom _ _).evenMap
      (modelStarVec f P e' (degList (starAssignEnum W))))
    (stdToOmega_bmc_perm_all f P e
      ((degList (starAssignEnum W)).sum) (sortSplitPerm W))
  -- Swap the cast across the transport.
  have hcast := congrArg (fun z :
      (superPow (stdSuperPair k ℓ)
        ((degList (starAssignEnum W)).sum) ⟶
        P.ω.obj (SkeinObj.mk
          (edgeCount W + edgeCount W))) =>
    (z : SuperVect.Hom _ _).evenMap
      (((modelPermMap (sortSplitPerm W)) :
        SuperVect.Hom _ _).evenMap
        (modelStarVec f P e'
          (degList (starAssignEnum W)))))
    (stdToOmega_bmc_cast f P e
      (degList_sum (starAssignEnum W)))
  refine Eq.trans (congrArg (fun y =>
    ((P.ω.map (bundleMapClass f (finCongr
        (degList_sum (starAssignEnum W)))) :
      P.ω.obj (SkeinObj.mk
        ((degList (starAssignEnum W)).sum)) ⟶
      P.ω.obj (SkeinObj.mk
        (edgeCount W + edgeCount W))) :
      SuperVect.Hom _ _).evenMap y) hperm) ?_
  exact hcast

end RS
