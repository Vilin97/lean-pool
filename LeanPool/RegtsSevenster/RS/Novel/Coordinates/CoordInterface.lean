/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaTransport

/-!
# The coordinate interface

A morphism `⟨0⟩ ⟶ ⟨d⟩` of the skein category has an image vector
in the fibre of `⟨d⟩` (evaluate the unit-conjugated image at
`1`), and a morphism `⟨d⟩ ⟶ ⟨0⟩` has an image functional.  The
scalar of a composite is the functional applied to the vector —
definitionally.  Specialised to the star composite this expresses
the parameter value as a pairing in the fibre, ready for the
standard-model coordinates.
-/

namespace RS

open CategoryTheory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))

/-- The image vector of a `⟨0⟩ ⟶ ⟨d⟩` morphism. -/
noncomputable def omegaVec {d : ℕ}
    (p : (SkeinObj.mk 0 : SkeinObj f) ⟶ SkeinObj.mk d) :
    (P.ω.obj (SkeinObj.mk d)).even :=
  letI := P.braided
  ((ε P.ω ≫ P.ω.map p : SuperVect.tensorUnit ⟶
    P.ω.obj (SkeinObj.mk d)) :
    SuperVect.Hom _ _).evenMap 1

/-- The image functional of a `⟨d⟩ ⟶ ⟨0⟩` morphism. -/
noncomputable def omegaFun {d : ℕ}
    (q : (SkeinObj.mk d : SkeinObj f) ⟶ SkeinObj.mk 0) :
    (P.ω.obj (SkeinObj.mk d)).even →ₗ[ℂ] ℂ :=
  letI := P.braided
  ((P.ω.map q ≫ η P.ω : P.ω.obj (SkeinObj.mk d) ⟶
    SuperVect.tensorUnit) : SuperVect.Hom _ _).evenMap

/-- **The pairing split**: the scalar of a composite is the
functional applied to the vector. -/
theorem omega_pairing {d : ℕ}
    (p : (SkeinObj.mk 0 : SkeinObj f) ⟶ SkeinObj.mk d)
    (q : (SkeinObj.mk d : SkeinObj f) ⟶ SkeinObj.mk 0) :
    letI := P.braided
    ((ε P.ω ≫ (P.ω.map p ≫ P.ω.map q) ≫ η P.ω :
      SuperVect.tensorUnit ⟶ SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap 1 =
    omegaFun f P q (omegaVec f P p) := rfl

/-- **The parameter value as a fibre pairing.** -/
theorem star_pairing (W : ClosedFragment) :
    omegaFun f P (bundleCapClass f (edgeCount W))
      (omegaVec f P (starClass f W)) = f.val W := by
  letI := P.braided
  rw [← omega_pairing]
  exact omega_star_scalar f P W

/-- The single-vertex star with `d` legs: one internal vertex,
`d` pendant edges. -/
def vertexStar (d : ℕ) : Fragment (Fin d) where
  Flag := Fin d ⊕ Fin d
  Vertex := Unit
  attach := fun g => match g with
    | Sum.inl _ => Sum.inl ()
    | Sum.inr i => Sum.inr i
  pairing := fun g => match g with
    | Sum.inl i => Sum.inr i
    | Sum.inr i => Sum.inl i
  pairing_invol := fun g => by rcases g with i | i <;> rfl
  pairing_ne := fun g => by rcases g with i | i <;> simp
  boundaryFlag := Sum.inr
  attach_boundaryFlag := fun _ => rfl
  eq_boundaryFlag := fun ℓ g h => by
    rcases g with i | i
    · exact absurd h (by simp)
    · exact congrArg Sum.inr (Sum.inr.inj h)
  circles := 0

/-- The degree-`d` vertex functional data: the image vector of
the vertex star read as a `(0, d)`-morphism. -/
noncomputable def starVec (d : ℕ) :
    (P.ω.obj (SkeinObj.mk d)).even :=
  omegaVec f P (HomSpace.ofFragment f.val
    ((vertexStar d).relabel (finCongr (by omega : d = 0 + d))))

end RS
