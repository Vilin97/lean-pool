/-
Copyright (c) 2026 Ivan Kobe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Kobe
-/

import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Comma

import LeanPool.FactorizationSystems.Basic
import LeanPool.FactorizationSystems.Orthogonality

/-!
# LeanPool.FactorizationSystems.OrthogonalComplements
-/

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]


/- The right orthogonal complement of a class of morphisms W in a category C -/
/-- Imported FactorizationSystems declaration. -/
def rightOrthogonalComplement : (W : MorphismProperty C) → MorphismProperty C := by
  intro W _ _ f
  exact ∀ ⦃A B : C ⦄ (g : A ⟶ B) (p : W g) , (homOrthogonal g f)

/- The left orthogonal complement of a class of morphisms W in a category C-/
/-- Imported FactorizationSystems declaration. -/
def leftOrthogonalComplement : (W : MorphismProperty C) → MorphismProperty C := by
  intro W _ _ f
  exact ∀ ⦃A B : C⦄ (g : A ⟶ B) (p : W g) , (homOrthogonal f g)

namespace Arrow

/- We haven't found this in the library, so we first show that the forgetfull functor
dom : [I,C] ⥤ C preserves limits. -/

/- A cone over f : J ⥤ Arrow C determines a cone over f ⋙ leftFunc -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def sourceConeArrowCone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (Cf : Limits.Cone f) :
  Limits.Cone (f ⋙ leftFunc) := {
    pt := leftFunc.obj Cf.pt
    π := {
      app := fun i => leftFunc.map (Cf.π.app i)
      naturality := by
        intro i j α
        have naturality' := Cf.π.naturality α
        change (((Functor.const J).obj Cf.pt).map α ≫ Cf.π.app j).left =
          (Cf.π.app i ≫ f.map α).left
        exact congrArg (fun h : Cf.pt ⟶ f.obj j => h.left) naturality'
    }
  }

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def coneSourceTrivConeArrow {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C)
  (s : Limits.Cone (f ⋙ leftFunc)) : Limits.Cone f := {
    pt := Arrow.mk (𝟙 s.pt)
    π := {
      app := fun i =>
        Arrow.homMk (s.π.app i) (s.π.app i ≫ (f.obj i).hom) (by
          change s.π.app i ≫ (f.obj i).hom = 𝟙 s.pt ≫ s.π.app i ≫ (f.obj i).hom
          rw [Category.id_comp]
          rfl)
      naturality := fun i j α => by
        have naturality' := s.π.naturality α
        apply Arrow.hom_ext
        · simp only [Arrow.comp_left, Arrow.homMk_left, Functor.const_obj_map,
            Functor.comp_map, leftFunc_map] at naturality' ⊢
          exact naturality'
        · have hnat : s.π.app j = s.π.app i ≫ (f.map α).left :=
            (Category.id_comp (s.π.app j)).symm.trans naturality'
          simp only [Arrow.comp_right, Arrow.homMk_right, Functor.const_obj_map,
            Arrow.id_right]
          change 𝟙 s.pt ≫ s.π.app j ≫ (f.obj j).hom
            = (s.π.app i ≫ (f.obj i).hom) ≫ Hom.right (f.map α)
          rw [Category.id_comp, hnat]
          exact (Category.assoc _ _ _).trans
            ((congrArg (s.π.app i ≫ ·) (f.map α).w).trans
              (Category.assoc _ _ _).symm)}
        }

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def mapTrivMapArrowSource (f : Arrow C) (X : C) (m : X ⟶ f.left) : Arrow.mk (𝟙 X) ⟶ f := by
  exact Arrow.homMk m (m ≫ f.hom) (by
    change m ≫ f.hom = 𝟙 X ≫ m ≫ f.hom
    simp)

/- The domain functor dom : [I,C] ⥤ C preserves limits -/
/-- Imported FactorizationSystems declaration. -/
def sourceLimitConeArrowLimitCone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C)
  (Cf : Limits.LimitCone f) : Limits.LimitCone (f ⋙ leftFunc) :=
  {
    cone := sourceConeArrowCone f Cf.cone
    isLimit := {
      lift := fun s => leftFunc.map (Cf.isLimit.lift (coneSourceTrivConeArrow f s))
      fac := fun s j => by
        have fac' := Cf.isLimit.fac (coneSourceTrivConeArrow f s) j
        change
          (Cf.isLimit.lift (coneSourceTrivConeArrow f s) ≫ Cf.cone.π.app j).left =
            ((coneSourceTrivConeArrow f s).π.app j).left
        exact congrArg (fun h : Arrow.mk (𝟙 s.pt) ⟶ f.obj j => h.left) fac'
      uniq := fun s m p => by
        let m_triv := mapTrivMapArrowSource Cf.cone.pt s.pt m
        let p' : ∀ (j : J), m_triv ≫ Cf.cone.π.app j = (coneSourceTrivConeArrow f s).π.app j :=
          fun j => by
            ext
            · aesop_cat
            · have hcomm :
                  (m ≫ Cf.cone.pt.hom) ≫ (Cf.cone.π.app j).right =
                    (m ≫ (Cf.cone.π.app j).left) ≫ (f.obj j).hom := by
                rw [Category.assoc, Category.assoc]
                exact congrArg (m ≫ ·) (Cf.cone.π.app j).w.symm
              have hp :
                  (m ≫ (Cf.cone.π.app j).left) ≫ (f.obj j).hom =
                    s.π.app j ≫ (f.obj j).hom :=
                congrArg (· ≫ (f.obj j).hom) (p j)
              change (m_triv ≫ Cf.cone.π.app j).right = s.π.app j ≫ (f.obj j).hom
              simp only [Arrow.comp_right]
              exact hcomm.trans hp
        have uniq' := Cf.isLimit.uniq (coneSourceTrivConeArrow f s) m_triv p'
        exact congrArg (fun h : Arrow.mk (𝟙 s.pt) ⟶ Cf.cone.pt => h.left) uniq'
    }
  }

/- If the category C has a terminal object, then the functor cod : [I,C] ⥤ C is continuous as well-/

/- A cone over f : J ⥤ Arrow C determines a cone over f ⋙ rightFunc -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def targetConeArrowCone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (Cf : Limits.Cone f) :
  Limits.Cone (f ⋙ rightFunc) := {
    pt := rightFunc.obj Cf.pt
    π := {
      app := fun i => rightFunc.map (Cf.π.app i)
      naturality := by
        intro i j α
        have naturality' := Cf.π.naturality α
        change (((Functor.const J).obj Cf.pt).map α ≫ Cf.π.app j).right =
          (Cf.π.app i ≫ f.map α).right
        exact congrArg (fun h : Cf.pt ⟶ f.obj j => h.right) naturality'
    }
  }

/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def coneTargetTrivConeArrow {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C]
  (f : J ⥤ Arrow C) (s : Limits.Cone (f ⋙ rightFunc)) : Limits.Cone f := {
    pt := Arrow.mk (Limits.initial.to s.pt)
    π := {
      app := fun i =>
        Arrow.homMk (Limits.initial.to (leftFunc.obj (f.obj i))) (s.π.app i)
          (by apply Limits.initial.hom_ext)
      naturality := fun j i α => by
        ext
        · apply Limits.initial.hom_ext
        · have nat := s.π.naturality α
          aesop_cat}
  }

/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def mapTrivMapArrowTarget [CategoryTheory.Limits.HasInitial C]
  (f : Arrow C) (B : C) (m : B ⟶ f.right) : (Arrow.mk (Limits.initial.to B)) ⟶ f := by
  exact Arrow.homMk (Limits.initial.to f.left) m (by apply Limits.initial.hom_ext)

/- If C has an initial object, then the codomain functor cod : [I,C] ⥤ C preserves limits -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def targetLimitConeArrowLimitCone {J : Type u} [Category.{v} J]
  [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C) (Cf : Limits.LimitCone f) :
  Limits.LimitCone (f ⋙ rightFunc) := {
    cone := targetConeArrowCone f Cf.cone
    isLimit := {
      lift := fun s => rightFunc.map (Cf.isLimit.lift (coneTargetTrivConeArrow f s))
      fac := fun s j => by
        have fac' := Cf.isLimit.fac (coneTargetTrivConeArrow f s) j
        change
          (Cf.isLimit.lift (coneTargetTrivConeArrow f s) ≫ Cf.cone.π.app j).right =
            ((coneTargetTrivConeArrow f s).π.app j).right
        exact congrArg (fun h : Arrow.mk (Limits.initial.to s.pt) ⟶ f.obj j => h.right) fac'
      uniq := fun s m p => by
        let p' : ∀ (j : J), Cf.cone.pt.mapTrivMapArrowTarget s.pt m ≫ Cf.cone.π.app j =
          (coneTargetTrivConeArrow f s).π.app j := fun j => by
            ext
            · apply Limits.initial.hom_ext
            · aesop_cat
        have uniq' := Cf.isLimit.uniq (coneTargetTrivConeArrow f s)
            (mapTrivMapArrowTarget Cf.cone.pt s.pt m) p'
        calc
          m = (mapTrivMapArrowTarget Cf.cone.pt s.pt m).right := by rfl
          _ = (Cf.isLimit.lift (coneTargetTrivConeArrow f s)).right := by
            exact congrArg (fun h : Arrow.mk (Limits.initial.to s.pt) ⟶ Cf.cone.pt => h.right)
              uniq'}
  }

/- We now proceed to prove that the right orthogonal complement of a class of morphisms is closed
  under limits. -/

/- Given a functor f : J ⥤ Arrow C together with a choice of a limit s : X ⟶ Y, a map m : A ⟶ B
and a commuting square

      A ---------> X
      |            |
    m |            |s       (*)
      |            |
      v            v
      B ---------> Y,

we obtain for every object i : J a commuting square

      A -------> dom(fi)
      |            |
    m |            |fi
      |            |
      v            v
      B -------> cod(fi).                          -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def squareCompletionIsClosedUnderLimitsROrtComplement
  {A B : C} {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f) (m : A ⟶ B)
  (sq_lim : squareCompletion m s.cone.pt.hom) :
  (i : J) → squareCompletion m (f.obj i).hom := fun i => {
    top := sq_lim.top ≫ (s.cone.π.app i).left
    bot := sq_lim.bot ≫ (s.cone.π.app i).right
    comm := by
      rw [reassoc_of% sq_lim.comm, Category.assoc]
      exact congrArg (sq_lim.top ≫ ·) (s.cone.π.app i).w.symm
  }

/- Given a square (*) as above, we construct a cone over (U ∘ f) with apex B. -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def coneLimitIsClosedUnderLimitsROrtComplement (W : MorphismProperty C) {A B : C}
  {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : squareCompletion m s.cone.pt.hom)
  (p : ∀ i : J , (rightOrthogonalComplement W) (f.obj i).hom) : Limits.Cone (f ⋙ leftFunc) := {
    pt := B
    π := {
      app := fun i => by
        let m_ort_fi : orthogonal m (f.obj i).hom := homOrthogonalImpliesOrthogonal ((p i) m Wm)
        let sq_i := squareCompletionIsClosedUnderLimitsROrtComplement f s m sq_lim i
        exact (m_ort_fi.diagonal sq_i).map
      naturality := fun i j α => by
        let m_ort_fi : orthogonal m (f.obj i).hom := homOrthogonalImpliesOrthogonal ((p i) m Wm)
        let sq_i := squareCompletionIsClosedUnderLimitsROrtComplement f s m sq_lim i
        let m_ort_fj : orthogonal m (f.obj j).hom := homOrthogonalImpliesOrthogonal ((p j) m Wm)
        let sq_j := squareCompletionIsClosedUnderLimitsROrtComplement f s m sq_lim j
        simp only [Functor.comp_map, leftFunc_map]
        have nat_eq : s.cone.π.app i ≫ f.map α = s.cone.π.app j := s.cone.w α
        let d : diagonalFiller sq_j := {
          map := (m_ort_fj.diagonal sq_j).map
          comm_top := (m_ort_fj.diagonal sq_j).comm_top
          comm_bot := (m_ort_fj.diagonal sq_j).comm_bot}
        let d' : diagonalFiller sq_j := {
          map := (m_ort_fi.diagonal sq_i).map ≫ (f.map α).left
          comm_top := by calc
            m ≫ (m_ort_fi.diagonal sq_i).map ≫ (f.map α).left =
              (sq_lim.top ≫ (s.cone.π.app i).left) ≫ (f.map α).left :=
              by rw [reassoc_of% (m_ort_fi.diagonal sq_i).comm_top]
            _ = sq_lim.top ≫ ((s.cone.π.app i).left ≫ (f.map α).left) := by simp
            _ = sq_lim.top ≫ (s.cone.π.app j).left := by
              calc
                sq_lim.top ≫ (leftFunc.map (s.cone.π.app i) ≫ leftFunc.map (f.map α)) =
                  sq_lim.top ≫ leftFunc.map (s.cone.π.app i ≫ f.map α) := by
                    exact congrArg (fun h => sq_lim.top ≫ h)
                      (leftFunc.map_comp (s.cone.π.app i) (f.map α)).symm
                _ = sq_lim.top ≫ leftFunc.map (s.cone.π.app j) := by
                  exact congrArg (fun h : s.cone.pt ⟶ f.obj j => sq_lim.top ≫ leftFunc.map h)
                    nat_eq
            _ = sq_j.top := by rfl
          comm_bot := by calc
            ((m_ort_fi.diagonal sq_i).map ≫ (f.map α).left) ≫ (f.obj j).hom =
              ((m_ort_fi.diagonal sq_i).map ≫ (f.obj i).hom) ≫ (f.map α).right := by simp
            _ = (sq_lim.bot ≫ (s.cone.π.app i).right) ≫ (f.map α).right :=
              by rw [(m_ort_fi.diagonal sq_i).comm_bot]
            _ = sq_lim.bot ≫ ((s.cone.π.app i).right ≫ (f.map α).right) := by simp
            _ = sq_lim.bot ≫ (s.cone.π.app j).right := by
              calc
                sq_lim.bot ≫ (rightFunc.map (s.cone.π.app i) ≫ rightFunc.map (f.map α)) =
                  sq_lim.bot ≫ rightFunc.map (s.cone.π.app i ≫ f.map α) := by
                    exact congrArg (fun h => sq_lim.bot ≫ h)
                      (rightFunc.map_comp (s.cone.π.app i) (f.map α)).symm
                _ = sq_lim.bot ≫ rightFunc.map (s.cone.π.app j) := by
                  exact congrArg (fun h : s.cone.pt ⟶ f.obj j => sq_lim.bot ≫ rightFunc.map h)
                    nat_eq
            _ = sq_j.bot := by rfl}
        have hunique : d.map = d'.map := (m_ort_fj.diagonal_unique sq_j) d d'
        calc
          ((Functor.const J).obj B).map α ≫ d.map = d.map :=
            Category.id_comp d.map
          _ = d'.map := hunique}
  }

/- By the universal property of the limit cone, the cone from the previous construction gives rise
  to a morphism B → X. -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def diagonalMapLimitIsClosedUnderLimitsROrtComplement (W : MorphismProperty C) {A B : C}
  {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : squareCompletion m s.cone.pt.hom)
  (p : ∀ i : J , (rightOrthogonalComplement W) (f.obj i).hom) : B ⟶ s.cone.pt.left := by
  let this_is_what_we_want :=
    ( sourceLimitConeArrowLimitCone f s).isLimit.lift
      ( coneLimitIsClosedUnderLimitsROrtComplement W f s m Wm sq_lim p)
  let do_the_magic : B ⟶ s.cone.pt.left := by aesop_cat
  exact do_the_magic

/- The diagonal constructed in the previous lemma makes the upper triangle commute -/
lemma diagonal_comm_top_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : squareCompletion m s.cone.pt.hom)
  (p : ∀ i : J , (rightOrthogonalComplement W) (f.obj i).hom) :
  m ≫ (diagonalMapLimitIsClosedUnderLimitsROrtComplement W f s m Wm sq_lim p) = sq_lim.top
  := by
  apply Limits.IsLimit.hom_ext (sourceLimitConeArrowLimitCone f s).isLimit
  intro i
  let m_ort_fi : orthogonal m (f.obj i).hom := homOrthogonalImpliesOrthogonal ((p i) m Wm)
  let sq_i := squareCompletionIsClosedUnderLimitsROrtComplement f s m sq_lim i
  let d := diagonalMapLimitIsClosedUnderLimitsROrtComplement W f s m Wm sq_lim p
  let di := (m_ort_fi.diagonal sq_i).map
  have hd : d ≫ (sourceLimitConeArrowLimitCone f s).cone.π.app i = di :=
    (sourceLimitConeArrowLimitCone f s).isLimit.fac
      (coneLimitIsClosedUnderLimitsROrtComplement W f s m Wm sq_lim p) i
  exact calc
    (m ≫ d) ≫ (sourceLimitConeArrowLimitCone f s).cone.π.app i =
        m ≫ (d ≫ (sourceLimitConeArrowLimitCone f s).cone.π.app i) :=
      Category.assoc m d ((sourceLimitConeArrowLimitCone f s).cone.π.app i)
    _ = sq_lim.top ≫ (sourceLimitConeArrowLimitCone f s).cone.π.app i := by
      rw [hd]
      exact (m_ort_fi.diagonal sq_i).comm_top

/- The bottom triangle commutes as well -/
lemma diagonal_comm_bot_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m) (sq_lim : squareCompletion m s.cone.pt.hom)
  (p : ∀ i : J , (rightOrthogonalComplement W) (f.obj i).hom) :
  (diagonalMapLimitIsClosedUnderLimitsROrtComplement W f s m Wm sq_lim p) ≫ s.cone.pt.hom
    = sq_lim.bot := by
  apply Limits.IsLimit.hom_ext (targetLimitConeArrowLimitCone f s).isLimit
  intro i
  let m_ort_fi : orthogonal m (f.obj i).hom := homOrthogonalImpliesOrthogonal ((p i) m Wm)
  let sq_i := squareCompletionIsClosedUnderLimitsROrtComplement f s m sq_lim i
  let d := diagonalMapLimitIsClosedUnderLimitsROrtComplement W f s m Wm sq_lim p
  let di := (m_ort_fi.diagonal sq_i).map
  have hd : d ≫ (sourceLimitConeArrowLimitCone f s).cone.π.app i = di :=
    (sourceLimitConeArrowLimitCone f s).isLimit.fac
      (coneLimitIsClosedUnderLimitsROrtComplement W f s m Wm sq_lim p) i
  change (d ≫ s.cone.pt.hom) ≫ (targetLimitConeArrowLimitCone f s).cone.π.app i =
    sq_lim.bot ≫ (targetLimitConeArrowLimitCone f s).cone.π.app i
  have hleft :
      (d ≫ s.cone.pt.hom) ≫ (targetLimitConeArrowLimitCone f s).cone.π.app i =
        d ≫ ((s.cone.π.app i).left ≫ (f.obj i).hom) := by
    rw [Category.assoc]
    exact congrArg (d ≫ ·) (s.cone.π.app i).w.symm
  rw [hleft]
  change d ≫ ((sourceLimitConeArrowLimitCone f s).cone.π.app i ≫ (f.obj i).hom) =
    sq_lim.bot ≫ (targetLimitConeArrowLimitCone f s).cone.π.app i
  rw [← Category.assoc, hd]
  exact (m_ort_fi.diagonal sq_i).comm_bot

/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonalFillerLimitIsClosedUnderLimitsROrtComplement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m) (sq_lim : squareCompletion m s.cone.pt.hom)
  (p : ∀ i : J , (rightOrthogonalComplement W) (f.obj i).hom) : diagonalFiller sq_lim := {
    map := diagonalMapLimitIsClosedUnderLimitsROrtComplement W f s m Wm sq_lim p
    comm_top := diagonal_comm_top_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
    comm_bot := diagonal_comm_bot_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
  }

/- Uniqueness of lifts -/

/- If f: J ⥤ Arrow C is a functor with limit cone λᵢ : lim f ⇒ fᵢ, and d is a diagonal filler
of the square
        a
  A ----------> dom(lim f)
  |               |
 m|               |lim f
  |               |
  V               V
  B ----------> cod(lim f),
        b
then for every object i of J, dom(λᵢ) ∘ d is a diagonal filler of the square
      dom(λᵢ)∘a
  A ----------> dom(fᵢ)
  |               |
 m|               |fᵢ
  |               |
  V               V
  B ----------> cod(fᵢ).
      cod(λᵢ)∘b                         -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def diagonalPostcompIsDiagonal {J : Type u}
  [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  {A B : C} (m : A ⟶ B) (S : squareCompletion m s.cone.pt.hom) (d : diagonalFiller S) (i : J) :
  diagonalFiller (squareCompletionIsClosedUnderLimitsROrtComplement f s m S i) := {
    map := d.map ≫ (s.cone.π.app i).left
    comm_top := by rw [reassoc_of% d.comm_top]
    comm_bot := by
      calc
        (d.map ≫ (s.cone.π.app i).left) ≫ (f.obj i).hom =
            d.map ≫ ((s.cone.π.app i).left ≫ (f.obj i).hom) := by simp
        _ = d.map ≫ (s.cone.pt.hom ≫ (s.cone.π.app i).right) := by
          exact congrArg (d.map ≫ ·) (s.cone.π.app i).w
        _ = S.bot ≫ (s.cone.π.app i).right := by rw [reassoc_of% d.comm_bot]
  }

lemma diagonal_unique_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m)
  (p : ∀ i : J , (rightOrthogonalComplement W) (f.obj i).hom)
  (sq_lim : squareCompletion m s.cone.pt.hom) (d d' : diagonalFiller sq_lim) :
  d.map = d'.map := by
  apply Limits.IsLimit.hom_ext (sourceLimitConeArrowLimitCone f s).isLimit
  intro i
  let D := diagonalPostcompIsDiagonal f s m sq_lim d i
  let D' := diagonalPostcompIsDiagonal f s m sq_lim d' i
  have m_ort_fi : orthogonal m (f.obj i).hom := homOrthogonalImpliesOrthogonal ((p i) m Wm)
  exact m_ort_fi.diagonal_unique
    (squareCompletionIsClosedUnderLimitsROrtComplement f s m sq_lim i) D D'

/- Putting everything together -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def isClosedUnderLimitsROrtComplement (W : MorphismProperty C) {A B : C} {J : Type u}
  [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (p : ∀ i : J , (rightOrthogonalComplement W) (f.obj i).hom) :
  orthogonal m s.cone.pt.hom := {
    diagonal := fun S =>
      diagonalFillerLimitIsClosedUnderLimitsROrtComplement W f s m Wm S p
    diagonal_unique := fun S d d' =>
      diagonal_unique_limit_is_closed_under_limits_r_ort_complement W f s m Wm p S d d'
  }

/- We now proceed to show that the right orthogonal complement is closed under composition -/
lemma is_closed_under_comp_r_ort_complement (W : MorphismProperty C) {X Y Z : C} (r : X ⟶ Y)
  (hr : (rightOrthogonalComplement W) r) (r' : Y ⟶ Z) (hr' : (rightOrthogonalComplement W) r') :
  (rightOrthogonalComplement W) (r ≫ r') := by
  intro A B l hl
  apply orthogonal_implies_hom_orthogonal
  exact {
    diagonal := fun S => by
      let a := S.top
      let b := S.bot
      let S' : l □ r' := {
        top := a ≫ r
        bot := b
        comm := by have comm' := S.comm; aesop_cat}
      let d := (homOrthogonalImpliesOrthogonal (hr' l hl)).diagonal S'
      let S'' : l □ r := {
        top := a
        bot := d.map
        comm := d.comm_top}
      let d' := (homOrthogonalImpliesOrthogonal (hr l hl)).diagonal S''
      exact {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by rw [reassoc_of% d'.comm_bot, d.comm_bot]}
    diagonal_unique := fun S d d' => by
      let a := S.top
      let b := S.bot
      let S' : l □ r' := {
        top := a ≫ r
        bot := b
        comm := by have comm' := S.comm; aesop_cat}
      let D : diagonalFiller S' := {
        map := d.map ≫ r
        comm_top := by rw [reassoc_of% d.comm_top]
        comm_bot := by have comm_bot' := d.comm_bot; aesop_cat}
      let D' : diagonalFiller S' := {
        map := d'.map ≫ r
        comm_top := by rw [reassoc_of% d'.comm_top]
        comm_bot := by have comm_bot' := d'.comm_bot; aesop_cat}
      let eq : d.map ≫ r = d'.map ≫ r :=
        (homOrthogonalImpliesOrthogonal (hr' l hl)).diagonal_unique S' D D'
      let S'' : l □ r := {
        top := a
        bot := d.map ≫ r
        comm := by rw [reassoc_of% d.comm_top]}
      let Δ : diagonalFiller S'' := {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by aesop_cat}
      let Δ' : diagonalFiller S'' := {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by aesop_cat}
      exact (homOrthogonalImpliesOrthogonal (hr l hl)).diagonal_unique S'' Δ Δ'}

/- The left orthogonal complement of any class of morphisms is closed under composition as well -/
lemma is_closed_under_comp_l_ort_complement (W : MorphismProperty C) {D E F : C} (l : D ⟶ E)
  (hl : (leftOrthogonalComplement W) l) (l' : E ⟶ F) (hl' : (leftOrthogonalComplement W) l') :
  (leftOrthogonalComplement W) (l ≫ l') := by
  intro X Y r hr
  apply orthogonal_implies_hom_orthogonal
  exact {
    diagonal := fun S => by
      let a := S.top
      let b := S.bot
      let S' : l □ r := {
        top := a
        bot := l' ≫ b
        comm := by have comm' := S.comm; aesop_cat}
      let d := (homOrthogonalImpliesOrthogonal (hl r hr)).diagonal S'
      let S'' : l' □ r := {
        top := d.map
        bot := b
        comm := Eq.symm d.comm_bot}
      let d' := (homOrthogonalImpliesOrthogonal (hl' r hr)).diagonal S''
      exact {
        map := d'.map
        comm_top := by have ct := d.comm_top; have ct' := d'.comm_top; aesop_cat
        comm_bot := d'.comm_bot }
    diagonal_unique := fun S d d' => by
      let a := S.top
      let b := S.bot
      let S' : l □ r := {
        top := a
        bot := l' ≫ b
        comm := by have comm' := S.comm; aesop_cat}
      let D : diagonalFiller S' := {
        map := l' ≫ d.map
        comm_top := by have ct := d.comm_top; aesop_cat
        comm_bot := by have cb := d.comm_bot; aesop_cat }
      let D' : diagonalFiller S' := {
        map := l' ≫ d'.map
        comm_top := by have ct' := d'.comm_top; aesop_cat
        comm_bot := by have cb' := d'.comm_bot; aesop_cat }
      let eq : l' ≫ d.map = l' ≫ d'.map :=
        (homOrthogonalImpliesOrthogonal (hl r hr)).diagonal_unique S' D D'
      let S'' : l' □ r := {
        top := l' ≫ d.map
        bot := b
        comm := by rw [Category.assoc, d.comm_bot] }
      let Δ : diagonalFiller S'' := {
        map := d.map
        comm_top := by rfl
        comm_bot := d.comm_bot }
      let Δ' : diagonalFiller S'' := {
        map := d'.map
        comm_top := Eq.symm eq
        comm_bot := d'.comm_bot}
      exact (homOrthogonalImpliesOrthogonal (hl' r hr)).diagonal_unique S'' Δ Δ' }

/- The right orthogonal complement of any class of morphism has the left cancellation property. -/
lemma left_cancellation_r_ort_complement (W : MorphismProperty C) {X Y Z : C} (r : X ⟶ Y)
  (r' : Y ⟶ Z) (hr' : (rightOrthogonalComplement W) r')
  (hr'r : (rightOrthogonalComplement W) (r ≫ r')) : (rightOrthogonalComplement W) r := by
  intro A B l hl
  apply orthogonal_implies_hom_orthogonal
  exact {
    diagonal := fun S => by
      let a := S.top
      let b := S.bot
      let S' : l □ r ≫ r' := {
        top := a
        bot := b ≫ r'
        comm := by rw [reassoc_of% S.comm]}
      let d := (homOrthogonalImpliesOrthogonal (hr'r l hl)).diagonal S'
      exact {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by
          let S'' : l □ r' := {
            top := a ≫ r
            bot := b ≫ r'
            comm := by have comm' := S'.comm; aesop_cat}
          let D : diagonalFiller S'' := {
            map := d.map ≫ r
            comm_top := by rw [reassoc_of% d.comm_top]
            comm_bot := by have comm_bot' := d.comm_bot; aesop_cat}
          let D' : diagonalFiller S'' := {
            map := S.bot
            comm_top := S.comm
            comm_bot := by rfl}
          exact (homOrthogonalImpliesOrthogonal (hr' l hl)).diagonal_unique S'' D D'}
    diagonal_unique := fun S d d' => by
      let a := S.top
      let b := S.bot
      let S' : l □ r ≫ r' := {
        top := a
        bot := b ≫ r'
        comm := by rw [reassoc_of% S.comm]}
      let Δ : diagonalFiller S' := {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by rw [reassoc_of% d.comm_bot]}
      let Δ' : diagonalFiller S' := {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by rw [reassoc_of% d'.comm_bot]}
      exact (homOrthogonalImpliesOrthogonal (hr'r l hl)).diagonal_unique S' Δ Δ'
  }

/- Moreover, the right orthogonal complement of any class of morphisms is closed under base change-/
lemma base_change_r_ort_complement [Limits.HasPullbacks C] (W : MorphismProperty C) {Y X' Y' : C}
  (r' : X' ⟶ Y') (hr' : (rightOrthogonalComplement W) r') (f : Y ⟶ Y') :
  (rightOrthogonalComplement W) (Limits.pullback.snd r' f) := by
  intro A B l hl
  apply orthogonal_implies_hom_orthogonal
  let r := Limits.pullback.snd r' f
  exact {
    diagonal := fun S => by
      let a := S.top
      let b := S.bot
      let S' : l □ r' := {
        top := a ≫ Limits.pullback.fst r' f
        bot := b ≫ f
        comm := by calc
          l ≫ b ≫ f = (l ≫ b) ≫ f := by simp
          _ = a ≫ r ≫ f := by rw [S.comm]; aesop_cat
          _ = a ≫ Limits.pullback.fst r' f ≫ r' := by rw [Limits.pullback.condition]
          _ = (a ≫ Limits.pullback.fst r' f) ≫ r' := by simp}
      let d := (homOrthogonalImpliesOrthogonal (hr' l hl)).diagonal S'
      let comm' : d.map ≫ r' =  b ≫ f := by have comm_bot' := d.comm_bot; aesop_cat
      exact {
        map := Limits.pullback.lift d.map b comm'
        comm_top := by
          apply Limits.pullback.hom_ext
          · rw [Category.assoc, Limits.pullback.lift_fst, d.comm_top]
          · rw [Category.assoc, Limits.pullback.lift_snd, S.comm]
        comm_bot := by apply Limits.pullback.lift_snd}
    diagonal_unique := fun S d d' => by
      apply Limits.pullback.hom_ext
      · let a := S.top
        let b := S.bot
        let S' : l □ r' := {
          top := a ≫ Limits.pullback.fst r' f
          bot := b ≫ f
          comm := by calc
            l ≫ b ≫ f = (l ≫ b) ≫ f := by simp
            _ = a ≫ r ≫ f := by rw [S.comm]; aesop_cat
            _ = a ≫ Limits.pullback.fst r' f ≫ r' := by rw [Limits.pullback.condition]
            _ = (a ≫ Limits.pullback.fst r' f) ≫ r' := by simp}
        let D : diagonalFiller S' := {
          map := d.map ≫ Limits.pullback.fst r' f
          comm_top := by rw [reassoc_of% d.comm_top]
          comm_bot := by
            rw [Category.assoc, Limits.pullback.condition, reassoc_of% d.comm_bot]}
        let D' : diagonalFiller S' := {
          map := d'.map ≫ Limits.pullback.fst r' f
          comm_top := by rw [reassoc_of% d'.comm_top]
          comm_bot := by
            rw [Category.assoc, Limits.pullback.condition, reassoc_of% d'.comm_bot]}
        exact (homOrthogonalImpliesOrthogonal (hr' l hl)).diagonal_unique S' D D'
      · rw [d.comm_bot, ← d'.comm_bot]}

/- The left orthogonal complement of any class of maps contains isomorphisms -/
lemma contains_isos_left_ort_complement (R : MorphismProperty C) :
  containsIsos (leftOrthogonalComplement R) := by
  intro A B f X Y g Rg
  apply orthogonal_implies_hom_orthogonal
  exact {
    diagonal := fun S => by exact {
      map := f.inv ≫ S.top
      comm_top := by have c := f.hom_inv_id; aesop_cat
      comm_bot := by
        rw [Category.assoc, ← S.comm]
        simp }
    diagonal_unique := fun S d d' => by
      have h := d.comm_top.trans d'.comm_top.symm
      simpa using congrArg (f.inv ≫ ·) h }

/- The right orthogonal complement of any class of maps contains isomorphisms -/
lemma contains_isos_right_ort_complement (L : MorphismProperty C) :
  containsIsos (rightOrthogonalComplement L) := by
    intro X Y g A B f Lf
    apply orthogonal_implies_hom_orthogonal
    exact {
      diagonal := fun S => by
        exact {
          map := S.bot ≫ g.inv
          comm_top := by
            rw [← Category.assoc, S.comm]
            simp
          comm_bot := by have c := g.inv_hom_id; aesop_cat
        }
      diagonal_unique := fun S d d' => by
        have h := d.comm_bot.trans d'.comm_bot.symm
        simpa using congrArg (· ≫ g.inv) h }

end Arrow

end CategoryTheory
