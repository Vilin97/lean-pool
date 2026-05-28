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

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]


/- The right orthogonal complement of a class of morphisms W in a category C -/
/-- Imported FactorizationSystems declaration. -/
def right_orthogonal_complement : (W : MorphismProperty C) → MorphismProperty C := by
  intro W _ _ f
  exact ∀ ⦃A B : C ⦄ (g : A ⟶ B) (p : W g) , (hom_orthogonal g f)

/- The left orthogonal complement of a class of morphisms W in a category C-/
/-- Imported FactorizationSystems declaration. -/
def left_orthogonal_complement : (W : MorphismProperty C) → MorphismProperty C := by
  intro W _ _ f
  exact ∀ ⦃A B : C⦄ (g : A ⟶ B) (p : W g) , (hom_orthogonal f g)

namespace Arrow

/- We haven't found this in the library, so we first show that the forgetfull functor
dom : [I,C] ⥤ C preserves limits. -/

/- A cone over f : J ⥤ Arrow C determines a cone over f ⋙ leftFunc -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def source_cone_arrow_cone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (Cf : Limits.Cone f) :
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
def cone_source_triv_cone_arrow {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C)
  (s : Limits.Cone (f ⋙ leftFunc)) : Limits.Cone f := {
    pt := Arrow.mk (𝟙 s.pt)
    π := {
      app := fun i =>
        Arrow.homMk (s.π.app i) (s.π.app i ≫ (f.obj i).hom) (by aesop_cat)
      naturality := fun i j α => by
        have naturality' := s.π.naturality α
        ext
        · aesop_cat
        · aesop_cat}
        }

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def map_triv_map_arrow_source (f : Arrow C) (X : C) (m : X ⟶ f.left) : Arrow.mk (𝟙 X) ⟶ f := by
  exact Arrow.homMk m (m ≫ f.hom) (by aesop_cat)

/- The domain functor dom : [I,C] ⥤ C preserves limits -/
/-- Imported FactorizationSystems declaration. -/
def source_limit_cone_arrow_limit_cone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C)
  (Cf : Limits.LimitCone f) : Limits.LimitCone (f ⋙ leftFunc) :=
  {
    cone := source_cone_arrow_cone f Cf.cone
    isLimit := {
      lift := fun s => leftFunc.map (Cf.isLimit.lift (cone_source_triv_cone_arrow f s))
      fac := fun s j => by
        have fac' := Cf.isLimit.fac (cone_source_triv_cone_arrow f s) j
        change
          (Cf.isLimit.lift (cone_source_triv_cone_arrow f s) ≫ Cf.cone.π.app j).left =
            ((cone_source_triv_cone_arrow f s).π.app j).left
        exact congrArg (fun h : Arrow.mk (𝟙 s.pt) ⟶ f.obj j => h.left) fac'
      uniq := fun s m p => by
        let m_triv := map_triv_map_arrow_source Cf.cone.pt s.pt m
        let p' : ∀ (j : J), m_triv ≫ Cf.cone.π.app j = (cone_source_triv_cone_arrow f s).π.app j :=
          fun j => by
            ext
            · aesop_cat
            · simpa [m_triv, map_triv_map_arrow_source, source_cone_arrow_cone,
                cone_source_triv_cone_arrow] using
                congrArg (fun h => h ≫ (f.obj j).hom) (p j)
        have uniq' := Cf.isLimit.uniq (cone_source_triv_cone_arrow f s) m_triv p'
        calc
          m = m_triv.left := by rfl
          _ = (Cf.isLimit.lift (cone_source_triv_cone_arrow f s)).left := by
            exact congrArg (fun h : Arrow.mk (𝟙 s.pt) ⟶ Cf.cone.pt => h.left) uniq'
    }
  }

/- If the category C has a terminal object, then the functor cod : [I,C] ⥤ C is continuous as well-/

/- A cone over f : J ⥤ Arrow C determines a cone over f ⋙ rightFunc -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def target_cone_arrow_cone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (Cf : Limits.Cone f) :
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
def cone_target_triv_cone_arrow {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C]
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
def map_triv_map_arrow_target [CategoryTheory.Limits.HasInitial C]
  (f : Arrow C) (B : C) (m : B ⟶ f.right) : (Arrow.mk (Limits.initial.to B)) ⟶ f := by
  exact Arrow.homMk (Limits.initial.to f.left) m (by apply Limits.initial.hom_ext)

/- If C has an initial object, then the codomain functor cod : [I,C] ⥤ C preserves limits -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def target_limit_cone_arrow_limit_cone {J : Type u} [Category.{v} J]
  [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C) (Cf : Limits.LimitCone f) :
  Limits.LimitCone (f ⋙ rightFunc) := {
    cone := target_cone_arrow_cone f Cf.cone
    isLimit := {
      lift := fun s => rightFunc.map (Cf.isLimit.lift (cone_target_triv_cone_arrow f s))
      fac := fun s j => by
        have fac' := Cf.isLimit.fac (cone_target_triv_cone_arrow f s) j
        change
          (Cf.isLimit.lift (cone_target_triv_cone_arrow f s) ≫ Cf.cone.π.app j).right =
            ((cone_target_triv_cone_arrow f s).π.app j).right
        exact congrArg (fun h : Arrow.mk (Limits.initial.to s.pt) ⟶ f.obj j => h.right) fac'
      uniq := fun s m p => by
        let p' : ∀ (j : J), Cf.cone.pt.map_triv_map_arrow_target s.pt m ≫ Cf.cone.π.app j =
          (cone_target_triv_cone_arrow f s).π.app j := fun j => by
            ext
            · aesop_cat
            · aesop_cat
        have uniq' := Cf.isLimit.uniq (cone_target_triv_cone_arrow f s)
            (map_triv_map_arrow_target Cf.cone.pt s.pt m) p'
        calc
          m = (map_triv_map_arrow_target Cf.cone.pt s.pt m).right := by rfl
          _ = (Cf.isLimit.lift (cone_target_triv_cone_arrow f s)).right := by
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
def square_completion_is_closed_under_limits_r_ort_complement
  {A B : C} {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f) (m : A ⟶ B)
  (sq_lim : square_completion m s.cone.pt.hom) :
  (i : J) → square_completion m (f.obj i).hom := fun i => {
    top := sq_lim.top ≫ (s.cone.π.app i).left
    bot := sq_lim.bot ≫ (s.cone.π.app i).right
    comm := by calc
      m ≫ sq_lim.bot ≫ (s.cone.π.app i).right = (m ≫ sq_lim.bot) ≫ (s.cone.π.app i).right
        := by simp
    _ =  (sq_lim.top ≫ s.cone.pt.hom) ≫ (s.cone.π.app i).right := by rw [sq_lim.comm]
    _ = (sq_lim.top ≫ (s.cone.π.app i).left) ≫ (f.obj i).hom := by aesop_cat
  }

/- Given a square (*) as above, we construct a cone over (U ∘ f) with apex B. -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def cone_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C) {A B : C}
  {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) : Limits.Cone (f ⋙ leftFunc) := {
    pt := B
    π := {
      app := fun i => by
        let m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
        let sq_i := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i
        exact (m_ort_fi.diagonal sq_i).map
      naturality := fun i j α => by
        let m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
        let sq_i := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i
        let m_ort_fj : orthogonal m (f.obj j).hom := hom_orthogonal_implies_orthogonal ((p j) m Wm)
        let sq_j := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim j
        simp only [Functor.const_obj_obj, Functor.comp_obj, leftFunc_obj, Functor.const_obj_map,
          Category.id_comp, Functor.comp_map, leftFunc_map]
        let d : diagonal_filler sq_j := {
          map := (m_ort_fj.diagonal sq_j).map
          comm_top := (m_ort_fj.diagonal sq_j).comm_top
          comm_bot := (m_ort_fj.diagonal sq_j).comm_bot}
        let d' : diagonal_filler sq_j := {
          map := (m_ort_fi.diagonal sq_i).map ≫ (f.map α).left
          comm_top := by calc
            m ≫ (m_ort_fi.diagonal sq_i).map ≫ (f.map α).left =
              (m ≫ (m_ort_fi.diagonal sq_i).map) ≫ (f.map α).left := by simp
            _ = (sq_lim.top ≫ (s.cone.π.app i).left) ≫ (f.map α).left :=
              by rw [(m_ort_fi.diagonal sq_i).comm_top]
            _ = sq_lim.top ≫ ((s.cone.π.app i).left ≫ (f.map α).left) := by simp
            _ = sq_lim.top ≫ (s.cone.π.app j).left := by
              have naturality := s.cone.π.naturality α
              have naturality' : s.cone.π.app i ≫ f.map α = s.cone.π.app j := by aesop_cat
              calc
                sq_lim.top ≫ (leftFunc.map (s.cone.π.app i) ≫ leftFunc.map (f.map α)) =
                  sq_lim.top ≫ leftFunc.map (s.cone.π.app i ≫ f.map α) := by
                    exact congrArg (fun h => sq_lim.top ≫ h)
                      (leftFunc.map_comp (s.cone.π.app i) (f.map α)).symm
                _ = sq_lim.top ≫ leftFunc.map (s.cone.π.app j) := by
                  exact congrArg (fun h : s.cone.pt ⟶ f.obj j => sq_lim.top ≫ leftFunc.map h)
                    naturality'
            _ = sq_j.top := by rfl
          comm_bot := by calc
            ((m_ort_fi.diagonal sq_i).map ≫ (f.map α).left) ≫ (f.obj j).hom =
              ((m_ort_fi.diagonal sq_i).map ≫ (f.obj i).hom) ≫ (f.map α).right := by simp
            _ = (sq_lim.bot ≫ (s.cone.π.app i).right) ≫ (f.map α).right :=
              by rw [(m_ort_fi.diagonal sq_i).comm_bot]
            _ = sq_lim.bot ≫ ((s.cone.π.app i).right ≫ (f.map α).right) := by simp
            _ = sq_lim.bot ≫ (s.cone.π.app j).right := by
              have naturality := s.cone.π.naturality α
              have naturality' : s.cone.π.app i ≫ f.map α = s.cone.π.app j := by aesop_cat
              calc
                sq_lim.bot ≫ (rightFunc.map (s.cone.π.app i) ≫ rightFunc.map (f.map α)) =
                  sq_lim.bot ≫ rightFunc.map (s.cone.π.app i ≫ f.map α) := by
                    exact congrArg (fun h => sq_lim.bot ≫ h)
                      (rightFunc.map_comp (s.cone.π.app i) (f.map α)).symm
                _ = sq_lim.bot ≫ rightFunc.map (s.cone.π.app j) := by
                  exact congrArg (fun h : s.cone.pt ⟶ f.obj j => sq_lim.bot ≫ rightFunc.map h)
                    naturality'
            _ = sq_j.bot := by rfl}
        apply (m_ort_fj.diagonal_unique sq_j) d d'}
  }

/- By the universal property of the limit cone, the cone from the previous construction gives rise
  to a morphism B → X. -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def diagonal_map_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C) {A B : C}
  {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) : B ⟶ s.cone.pt.left := by
  let this_is_what_we_want :=
    ( source_limit_cone_arrow_limit_cone f s).isLimit.lift
      ( cone_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p)
  let do_the_magic : B ⟶ s.cone.pt.left := by aesop_cat
  exact do_the_magic

/- The diagonal constructed in the previous lemma makes the upper triangle commute -/
lemma diagonal_comm_top_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) :
  m ≫ (diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p) = sq_lim.top
  := by
  apply Limits.IsLimit.hom_ext (source_limit_cone_arrow_limit_cone f s).isLimit
  intro i
  let m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
  let sq_i := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i
  let d := diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
  let di := (m_ort_fi.diagonal sq_i).map
  have hd : d ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i = di :=
    (source_limit_cone_arrow_limit_cone f s).isLimit.fac
      (cone_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p) i
  exact calc
    (m ≫ d) ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i =
        m ≫ (d ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i) :=
      Category.assoc m d ((source_limit_cone_arrow_limit_cone f s).cone.π.app i)
    _ = sq_lim.top ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i := by
      rw [hd]
      exact (m_ort_fi.diagonal sq_i).comm_top

/- The bottom triangle commutes as well -/
lemma diagonal_comm_bot_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) :
  (diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p) ≫ s.cone.pt.hom
    = sq_lim.bot := by
  apply Limits.IsLimit.hom_ext (target_limit_cone_arrow_limit_cone f s).isLimit
  intro i
  let m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
  let sq_i := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i
  let d := diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
  let di := (m_ort_fi.diagonal sq_i).map
  have hd : d ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i = di :=
    (source_limit_cone_arrow_limit_cone f s).isLimit.fac
      (cone_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p) i
  change (d ≫ s.cone.pt.hom) ≫ (target_limit_cone_arrow_limit_cone f s).cone.π.app i =
    sq_lim.bot ≫ (target_limit_cone_arrow_limit_cone f s).cone.π.app i
  have hleft :
      (d ≫ s.cone.pt.hom) ≫ (target_limit_cone_arrow_limit_cone f s).cone.π.app i =
        d ≫ ((s.cone.π.app i).left ≫ (f.obj i).hom) := by
    aesop_cat
  rw [hleft]
  change d ≫ ((source_limit_cone_arrow_limit_cone f s).cone.π.app i ≫ (f.obj i).hom) =
    sq_lim.bot ≫ (target_limit_cone_arrow_limit_cone f s).cone.π.app i
  rw [← Category.assoc, hd]
  exact (m_ort_fi.diagonal sq_i).comm_bot

/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonal_filler_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) : diagonal_filler sq_lim := {
    map := diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
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
def diagonal_postcomp_is_diagonal {J : Type u}
  [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  {A B : C} (m : A ⟶ B) (S : square_completion m s.cone.pt.hom) (d : diagonal_filler S) (i : J) :
  diagonal_filler (square_completion_is_closed_under_limits_r_ort_complement f s m S i) := {
    map := d.map ≫ (s.cone.π.app i).left
    comm_top := by
      calc
        m ≫ d.map ≫ (s.cone.π.app i).left = (m ≫ d.map) ≫ (s.cone.π.app i).left := by
          simp
        _ = S.top ≫ (s.cone.π.app i).left := by rw [d.comm_top]
        _ = (square_completion_is_closed_under_limits_r_ort_complement f s m S i).top := by
          rfl
    comm_bot := by
      calc
        (d.map ≫ (s.cone.π.app i).left) ≫ (f.obj i).hom =
            d.map ≫ ((s.cone.π.app i).left ≫ (f.obj i).hom) := by
          simp
        _ = d.map ≫ (s.cone.pt.hom ≫ (s.cone.π.app i).right) := by
          aesop_cat
        _ = (d.map ≫ s.cone.pt.hom) ≫ (s.cone.π.app i).right := by
          simp
        _ = S.bot ≫ (s.cone.π.app i).right := by rw [d.comm_bot]
        _ = (square_completion_is_closed_under_limits_r_ort_complement f s m S i).bot := by
          rfl
  }

lemma diagonal_unique_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom)
  (sq_lim : square_completion m s.cone.pt.hom) (d d' : diagonal_filler sq_lim) :
  d.map = d'.map := by
  apply Limits.IsLimit.hom_ext (source_limit_cone_arrow_limit_cone f s).isLimit
  intro i
  let D := diagonal_postcomp_is_diagonal f s m sq_lim d i
  let D' := diagonal_postcomp_is_diagonal f s m sq_lim d' i
  have m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
  exact m_ort_fi.diagonal_unique
    (square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i) D D'

/- Putting everything together -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def is_closed_under_limits_r_ort_complement (W : MorphismProperty C) {A B : C} {J : Type u}
  [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) :
  orthogonal m s.cone.pt.hom := {
    diagonal := fun S =>
      diagonal_filler_limit_is_closed_under_limits_r_ort_complement W f s m Wm S p
    diagonal_unique := fun S d d' =>
      diagonal_unique_limit_is_closed_under_limits_r_ort_complement W f s m Wm p S d d'
  }

/- We now proceed to show that the right orthogonal complement is closed under composition -/
lemma is_closed_under_comp_r_ort_complement (W : MorphismProperty C) {X Y Z : C} (r : X ⟶ Y)
  (hr : (right_orthogonal_complement W) r) (r' : Y ⟶ Z) (hr' : (right_orthogonal_complement W) r') :
  (right_orthogonal_complement W) (r ≫ r') := by
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
      let d := (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal S'
      let S'' : l □ r := {
        top := a
        bot := d.map
        comm := d.comm_top}
      let d' := (hom_orthogonal_implies_orthogonal (hr l hl)).diagonal S''
      exact {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by
          let comm_bot' := d'.comm_bot
          let comm_bot'' := d.comm_bot
          calc
            d'.map ≫ r ≫ r' = (d'.map ≫ r) ≫ r' := by simp
            _ = d.map ≫ r' := by rw [comm_bot']
            _ = b := comm_bot''}
    diagonal_unique := fun S d d' => by
      let a := S.top
      let b := S.bot
      let S' : l □ r' := {
        top := a ≫ r
        bot := b
        comm := by have comm' := S.comm; aesop_cat}
      let D : diagonal_filler S' := {
        map := d.map ≫ r
        comm_top := by calc
          l ≫ d.map ≫ r = S.top ≫ r := by rw [←d.comm_top]; simp
          _ = a ≫ r := by rfl
        comm_bot := by have comm_bot' := d.comm_bot; aesop_cat}
      let D' : diagonal_filler S' := {
        map := d'.map ≫ r
        comm_top := by calc
          l ≫ d'.map ≫ r = S.top ≫ r := by rw [←d'.comm_top]; simp
          _ = a ≫ r := by rfl
        comm_bot := by have comm_bot' := d'.comm_bot; aesop_cat}
      let eq : d.map ≫ r = d'.map ≫ r :=
        (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal_unique S' D D'
      let S'' : l □ r := {
        top := a
        bot := d.map ≫ r
        comm := by calc
          l ≫ d.map ≫ r = (l ≫ d.map) ≫ r := by simp
          _ = S'.top := by rw [d.comm_top]
          _ = a ≫ r := by rfl}
      let Δ : diagonal_filler S'' := {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by aesop_cat}
      let Δ' : diagonal_filler S'' := {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by aesop_cat}
      exact (hom_orthogonal_implies_orthogonal (hr l hl)).diagonal_unique S'' Δ Δ'}

/- The left orthogonal complement of any class of morphisms is closed under composition as well -/
lemma is_closed_under_comp_l_ort_complement (W : MorphismProperty C) {D E F : C} (l : D ⟶ E)
  (hl : (left_orthogonal_complement W) l) (l' : E ⟶ F) (hl' : (left_orthogonal_complement W) l') :
  (left_orthogonal_complement W) (l ≫ l') := by
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
      let d := (hom_orthogonal_implies_orthogonal (hl r hr)).diagonal S'
      let S'' : l' □ r := {
        top := d.map
        bot := b
        comm := Eq.symm d.comm_bot}
      let d' := (hom_orthogonal_implies_orthogonal (hl' r hr)).diagonal S''
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
      let D : diagonal_filler S' := {
        map := l' ≫ d.map
        comm_top := by have ct := d.comm_top; aesop_cat
        comm_bot := by have cb := d.comm_bot; aesop_cat }
      let D' : diagonal_filler S' := {
        map := l' ≫ d'.map
        comm_top := by have ct' := d'.comm_top; aesop_cat
        comm_bot := by have cb' := d'.comm_bot; aesop_cat }
      let eq : l' ≫ d.map = l' ≫ d'.map :=
        (hom_orthogonal_implies_orthogonal (hl r hr)).diagonal_unique S' D D'
      let S'' : l' □ r := {
        top := l' ≫ d.map
        bot := b
        comm := by calc
          l' ≫ b = l' ≫ d.map ≫ r := by rw [d.comm_bot]
          _ = (l' ≫ d.map) ≫ r := by simp }
      let Δ : diagonal_filler S'' := {
        map := d.map
        comm_top := by rfl
        comm_bot := d.comm_bot }
      let Δ' : diagonal_filler S'' := {
        map := d'.map
        comm_top := Eq.symm eq
        comm_bot := d'.comm_bot}
      exact (hom_orthogonal_implies_orthogonal (hl' r hr)).diagonal_unique S'' Δ Δ' }

/- The right orthogonal complement of any class of morphism has the left cancellation property. -/
lemma left_cancellation_r_ort_complement (W : MorphismProperty C) {X Y Z : C} (r : X ⟶ Y)
  (r' : Y ⟶ Z) (hr' : (right_orthogonal_complement W) r')
  (hr'r : (right_orthogonal_complement W) (r ≫ r')) : (right_orthogonal_complement W) r := by
  intro A B l hl
  apply orthogonal_implies_hom_orthogonal
  exact {
    diagonal := fun S => by
      let a := S.top
      let b := S.bot
      let S' : l □ r ≫ r' := {
        top := a
        bot := b ≫ r'
        comm := by calc
          l ≫ b ≫ r' = (l ≫ b) ≫ r' := by simp
          _ = (a ≫ r) ≫ r' := by rw [S.comm]
          _ = a ≫ r ≫ r' := by simp}
      let d := (hom_orthogonal_implies_orthogonal (hr'r l hl)).diagonal S'
      exact {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by
          let S'' : l □ r' := {
            top := a ≫ r
            bot := b ≫ r'
            comm := by have comm' := S'.comm; aesop_cat}
          let D : diagonal_filler S'' := {
            map := d.map ≫ r
            comm_top := by calc
              l ≫ d.map ≫ r = (l ≫ d.map) ≫ r := by simp
              _ = S'.top ≫ r := by rw [d.comm_top]
              _ = S''.top := by rfl
            comm_bot := by have comm_bot' := d.comm_bot; aesop_cat}
          let D' : diagonal_filler S'' := {
            map := S.bot
            comm_top := S.comm
            comm_bot := by rfl}
          exact (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal_unique S'' D D'}
    diagonal_unique := fun S d d' => by
      let a := S.top
      let b := S.bot
      let S' : l □ r ≫ r' := {
        top := a
        bot := b ≫ r'
        comm := by calc
          l ≫ b ≫ r' = (l ≫ b) ≫ r' := by simp
          _ = (a ≫ r) ≫ r' := by rw [S.comm]
          _ = a ≫ r ≫ r' := by simp}
      let Δ : diagonal_filler S' := {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by calc
          d.map ≫ r ≫ r' = (d.map ≫ r) ≫ r' := by simp
          _ = b ≫ r' := by rw [d.comm_bot]}
      let Δ' : diagonal_filler S' := {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by calc
          d'.map ≫ r ≫ r' = (d'.map ≫ r) ≫ r' := by simp
          _ = b ≫ r' := by rw [d'.comm_bot]}
      exact (hom_orthogonal_implies_orthogonal (hr'r l hl)).diagonal_unique S' Δ Δ'
  }

/- Moreover, the right orthogonal complement of any class of morphisms is closed under base change-/
lemma base_change_r_ort_complement [Limits.HasPullbacks C] (W : MorphismProperty C) {Y X' Y' : C}
  (r' : X' ⟶ Y') (hr' : (right_orthogonal_complement W) r') (f : Y ⟶ Y') :
  (right_orthogonal_complement W) (Limits.pullback.snd r' f) := by
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
      let d := (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal S'
      let comm' : d.map ≫ r' =  b ≫ f := by have comm_bot' := d.comm_bot; aesop_cat
      exact {
        map := Limits.pullback.lift d.map b comm'
        comm_top := by
          apply Limits.pullback.hom_ext
          · calc
            (l ≫ Limits.pullback.lift d.map b comm') ≫ Limits.pullback.fst r' f =
              l ≫ (Limits.pullback.lift d.map b comm' ≫ Limits.pullback.fst r' f) := by simp
            _ = l ≫ d.map := by rw [Limits.pullback.lift_fst]
            _ = a ≫ Limits.pullback.fst r' f := d.comm_top
          · calc
            (l ≫ Limits.pullback.lift d.map b comm') ≫ Limits.pullback.snd r' f =
              l ≫ (Limits.pullback.lift d.map b comm' ≫ Limits.pullback.snd r' f) := by simp
            _ = l ≫ b := by rw [Limits.pullback.lift_snd]
            _ = a ≫ r := S.comm
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
        let D : diagonal_filler S' := {
          map := d.map ≫ Limits.pullback.fst r' f
          comm_top := by calc
            l ≫ d.map ≫ Limits.pullback.fst r' f = (l ≫ d.map) ≫ Limits.pullback.fst r' f :=
              by simp
            _ = a ≫ Limits.pullback.fst r' f := by rw [d.comm_top]
          comm_bot := by calc
            (d.map ≫ Limits.pullback.fst r' f) ≫ r' = d.map ≫ (Limits.pullback.fst r' f ≫ r') :=
              by simp
            _ = d.map ≫ (r ≫ f) := by rw [Limits.pullback.condition]
            _ = (d.map ≫ r) ≫ f := by simp
            _ = b ≫ f := by rw [d.comm_bot]}
        let D' : diagonal_filler S' := {
          map := d'.map ≫ Limits.pullback.fst r' f
          comm_top := by calc
            l ≫ d'.map ≫ Limits.pullback.fst r' f = (l ≫ d'.map) ≫ Limits.pullback.fst r' f :=
              by simp
            _ = a ≫ Limits.pullback.fst r' f := by rw [d'.comm_top]
          comm_bot := by calc
            (d'.map ≫ Limits.pullback.fst r' f) ≫ r' = d'.map ≫ (Limits.pullback.fst r' f ≫ r')
              := by simp
            _ = d'.map ≫ (r ≫ f) := by rw [Limits.pullback.condition]
            _ = (d'.map ≫ r) ≫ f := by simp
            _ = b ≫ f := by rw [d'.comm_bot]}
        exact (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal_unique S' D D'
      · calc
        d.map ≫ Limits.pullback.snd r' f = S.bot := d.comm_bot
        _ = d'.map ≫ Limits.pullback.snd r' f := by rw [←d'.comm_bot]}

/- The left orthogonal complement of any class of maps contains isomorphisms -/
lemma contains_isos_left_ort_complement (R : MorphismProperty C) :
  contains_isos (left_orthogonal_complement R) := by
  intro A B f X Y g Rg
  apply orthogonal_implies_hom_orthogonal
  exact {
    diagonal := fun S => by exact {
      map := f.inv ≫ S.top
      comm_top := by have c := f.hom_inv_id; aesop_cat
      comm_bot := by calc
        (f.inv ≫ S.top) ≫ g = f.inv ≫ S.top ≫ g := by simp
        _ = f.inv ≫ f.hom ≫ S.bot := by rw [ S.comm ]
        _ = (f.inv ≫ f.hom) ≫ S.bot := by simp
        _ = S.bot := by rw [ f.inv_hom_id ]; simp }
    diagonal_unique := fun S d d' => by calc
      d.map = f.inv ≫ f.hom ≫ d.map := by have c := f.inv_hom_id; aesop_cat
    _ = f.inv ≫ S.top := by rw [ d.comm_top ]
    _ = f.inv ≫ f.hom ≫ d'.map := by rw [ d'.comm_top ]
    _ = d'.map := by have c := f.inv_hom_id; aesop_cat }

/- The right orthogonal complement of any class of maps contains isomorphisms -/
lemma contains_isos_right_ort_complement (L : MorphismProperty C) :
  contains_isos (right_orthogonal_complement L) := by
    intro X Y g A B f Lf
    apply orthogonal_implies_hom_orthogonal
    exact {
      diagonal := fun S => by
        exact {
          map := S.bot ≫ g.inv
          comm_top := by calc
            f ≫ S.bot ≫ g.inv = (f ≫ S.bot) ≫ g.inv := by simp
            _ = (S.top ≫ g.hom) ≫ g.inv := by rw [ S.comm ]
            _ = S.top := by have c := g.hom_inv_id; aesop_cat
          comm_bot := by have c := g.inv_hom_id; aesop_cat
        }
      diagonal_unique := fun S d d' => by calc
        d.map = (d.map ≫ g.hom) ≫ g.inv := by have c := g.hom_inv_id; aesop_cat
        _ = S.bot ≫ g.inv := by rw [ d.comm_bot ]
        _ = (d'.map ≫ g.hom) ≫ g.inv := by rw [ d'.comm_bot ]
        _ = d'.map := by have c := g.hom_inv_id; aesop_cat }

end Arrow

end CategoryTheory
