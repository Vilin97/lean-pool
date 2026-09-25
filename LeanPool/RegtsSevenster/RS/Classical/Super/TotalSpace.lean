/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Super.SuperVect

/-!
# Total spaces of super vector spaces

Forgetting the grading gives the product of the even and odd
components. Morphisms act componentwise, giving an algebra map on
endomorphisms.
-/

@[expose] public section

namespace RS

open CategoryTheory

noncomputable section

/-- The total space of a super vector space. -/
abbrev Tot (V : SuperVect) : Type := V.even × V.odd

/-- The total linear map of a morphism of super vector spaces. -/
def tot {V W : SuperVect} (f : V ⟶ W) : Tot V →ₗ[ℂ] Tot W :=
  LinearMap.prodMap (SuperVect.Hom.evenMap f) (SuperVect.Hom.oddMap f)

/-- The total map of the identity. -/
@[simp]
theorem tot_id (V : SuperVect) : tot (𝟙 V) = LinearMap.id := by
  ext v <;> rfl

/-- The total map of a composite. -/
theorem tot_comp {V W X : SuperVect} (f : V ⟶ W) (g : W ⟶ X) :
    tot (f ≫ g) = (tot g).comp (tot f) := by
  ext v <;> rfl

/-- The total map is additive in the morphism. -/
theorem tot_add {V W : SuperVect} (f g : V ⟶ W) :
    tot (f + g) = tot f + tot g := by
  refine LinearMap.ext fun x => ?_
  change ((f + g).evenMap x.1, (f + g).oddMap x.2) = _
  rw [SuperVect.add_evenMap, SuperVect.add_oddMap]
  rfl

/-- The total map is homogeneous in the morphism. -/
theorem tot_smul {V W : SuperVect} (c : ℂ) (f : V ⟶ W) :
    tot (c • f) = c • tot f := by
  refine LinearMap.ext fun x => ?_
  change ((c • f).evenMap x.1, (c • f).oddMap x.2) = _
  rw [SuperVect.smul_evenMap, SuperVect.smul_oddMap]
  rfl

/-- The total map of a zero morphism. -/
@[simp]
theorem tot_zero (V W : SuperVect) : tot (0 : V ⟶ W) = 0 := by
  ext v <;> rfl

/-- Forgetting the grading preserves the endomorphism algebra. -/
def totAlgHom (V : SuperVect) : End V →ₐ[ℂ] Module.End ℂ (Tot V) where
  toFun := tot
  map_one' := tot_id V
  map_mul' f g := tot_comp g f
  map_zero' := tot_zero V V
  map_add' := tot_add
  commutes' c := by
    change tot (c • 𝟙 V) = c • LinearMap.id
    rw [tot_smul, tot_id]

/-- A super isomorphism induces a linear equivalence of total spaces. -/
def totIso {V W : SuperVect} (e : V ≅ W) : Tot V ≃ₗ[ℂ] Tot W where
  __ := tot e.hom
  invFun := tot e.inv
  left_inv v := by
    have h := LinearMap.congr_fun
      ((tot_comp e.hom e.inv).symm.trans
        (by rw [e.hom_inv_id, tot_id])) v
    exact h
  right_inv w := by
    have h := LinearMap.congr_fun
      ((tot_comp e.inv e.hom).symm.trans
        (by rw [e.inv_hom_id, tot_id])) w
    exact h

end

end RS
