/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.StarCompClass
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinLinear
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DeligneBridge
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ExactPairingInstance

/-!
# Transporting the star identity through the fibre functor

Applying a Deligne package's fibre functor to the categorical
star identity: the images of the star-union and bundle classes
compose to the parameter value times the identity of the image
of the unit object.
-/

@[expose] public section

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The empty class is the identity of the unit object. -/
theorem empty_class_eq_id :
    HomSpace.ofFragment f.val emptyClosedFragment =
      𝟙 (SkeinObj.mk 0 : SkeinObj f) :=
  HomSpace.ofFragment_congr f strandBundleZeroEmpty.symm

variable (P : DelignePackage (SkeinObj f))

/-- **The transported star identity**: the fibre functor sends
the star composite to the parameter value times the identity. -/
theorem omega_star (W : ClosedFragment) :
    P.ω.map (X := SkeinObj.mk 0) (Y := SkeinObj.mk
        (edgeCount W + edgeCount W)) (starClass f W) ≫
      P.ω.map (bundleCapClass f (edgeCount W)) =
    f.val W • 𝟙 (P.ω.obj (SkeinObj.mk 0)) := by
  let := P.linear
  rw [← Functor.map_comp]
  rw [show (starClass f W ≫ bundleCapClass f (edgeCount W) :
      (SkeinObj.mk 0 : SkeinObj f) ⟶ SkeinObj.mk 0) =
    HomSpace.comp f 0 (edgeCount W + edgeCount W) 0
      (starClass f W) (bundleCapClass f (edgeCount W))
    from rfl]
  rw [star_comp_class, empty_class_eq_id]
  exact (P.linear.map_smul _ _).trans
    (by rw [CategoryTheory.Functor.map_id])

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- **The transported star identity, as a scalar**: conjugating
by the unit structure maps and evaluating the even part at `1`
recovers the parameter value. -/
theorem omega_star_scalar (W : ClosedFragment) :
    letI := P.braided
    ((ε P.ω ≫ (P.ω.map (X := SkeinObj.mk 0) (Y := SkeinObj.mk
        (edgeCount W + edgeCount W)) (starClass f W) ≫
      P.ω.map (bundleCapClass f (edgeCount W))) ≫
      η P.ω : SuperVect.tensorUnit ⟶ SuperVect.tensorUnit)
      : SuperVect.Hom SuperVect.tensorUnit
        SuperVect.tensorUnit).evenMap 1 = f.val W := by
  let := P.braided
  rw [omega_star f P W]
  rw [CategoryTheory.Linear.smul_comp,
    CategoryTheory.Linear.comp_smul]
  have h1 : (𝟙 (P.ω.obj (SkeinObj.mk 0)) ≫ η P.ω) = η P.ω :=
    CategoryTheory.Category.id_comp _
  rw [h1]
  have h2 : (ε P.ω ≫ η P.ω : SuperVect.tensorUnit ⟶
      SuperVect.tensorUnit) = 𝟙 _ :=
    Functor.Monoidal.ε_η P.ω
  rw [h2]
  change f.val W * 1 = f.val W
  ring

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- **The standard model of the skein category**: any Deligne
package yields dimensions `k, ℓ` and an isomorphism of the strand
image with the standard super vector space carrying the
evaluation to the standard form and the coevaluation to the
standard copairing. -/
theorem skein_std_model :
    letI := P.braided
    ∃ (k ℓ : ℕ)
      (e : SuperVect.Hom (stdSuperPair k ℓ)
        (P.ω.obj (SkeinObj.mk 1)))
      (e' : SuperVect.Hom (P.ω.obj (SkeinObj.mk 1))
        (stdSuperPair k ℓ)),
      SuperVect.Hom.comp e' e =
        SuperVect.Hom.id (stdSuperPair k ℓ) ∧
      SuperVect.Hom.comp e e' =
        SuperVect.Hom.id (P.ω.obj (SkeinObj.mk 1)) ∧
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ ∧
      SuperVect.Hom.comp (SuperVect.tensorHom e' e')
        (ε P.ω ≫ P.ω.map (η_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫
          δ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) =
        stdCopair k ℓ := by
  let := P.braided
  exact braided_std_model P.ω (SkeinObj.mk 1)
    (strand_ev_symmetry f)

end RS
