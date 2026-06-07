/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren
import LeanPool.LeanSubst.Subst

namespace LeanSubst
  universe u

  class Substitutive {T : Type} [RenMap T] [SubstMap T T] (R : T -> T -> Prop) where
    subst {t s} (σ : Subst T) : R t s -> R (t[σ]) (s[σ])

  class HasTriangle {T : Type u} (R : T -> T -> Prop) where
    complete : T -> T
    triangle {t s} : R t s -> R s (complete t)

  section
    variable {T : Type}

    inductive ActionRed (R : T -> T -> Prop) : Subst.Action T -> Subst.Action T -> Prop where
    | su {x y} : R x y -> ActionRed R (.su x) (.su y)
    | re {x} : ActionRed R (.re x) (.re x)

    inductive Star (R : T -> T -> Prop) : T -> T -> Prop where
    | refl {t} : Star R t t
    | step {x y z} : Star R x y -> R y z -> Star R x z

    inductive Plus (R : T -> T -> Prop) : T -> T -> Prop where
    | start {t s} : R t s -> Plus R t s
    | step {x y z} : Plus R x y -> R y z -> Plus R x z

    inductive Conv (R : T -> T -> Prop) : T -> T -> Prop where
    | refl {x} : Conv R x x
    | forward {x y z} : Conv R x z -> R x y -> Conv R y z
    | backward {x y z} : Conv R y z -> R x y -> Conv R x z

    class HasConfluence (R : T -> T -> Prop) where
      confluence {s t1 t2} : Star R s t1 -> Star R s t2 -> ∃ t, Star R t1 t ∧ Star R t2 t

    variable {R R1 R2 : T -> T -> Prop}

    namespace Star
      theorem trans {x y z} : Star R x y -> Star R y z -> Star R x z := by
        intro r1 r2; induction r2 generalizing x
        case _ => apply r1
        case _ a b _ r2 ih => apply Star.step (ih r1) r2

      theorem promote {x y} (Rprm : ∀ {x y}, R1 x y -> R2 x y) :
        Star R1 x y -> Star R2 x y
      := by
        intro r; induction r
        case _ => constructor
        case _ _ r ih => constructor; apply ih; apply Rprm r

      theorem stepr {x y z} : R x y -> Star R y z -> Star R x z := by
        intro h r; induction r generalizing x
        case _ => apply Star.step Star.refl h
        case _ r1 r2 ih =>
          replace ih := ih h
          apply Star.step ih r2

      theorem destruct {x z} : Star R x z -> (∃ y, R x y ∧ Star R y z) ∨ x = z := by
        intro h; induction h
        case _ => apply Or.inr rfl
        case _ u v r1 r2 ih =>
          cases ih
          case _ ih =>
            cases ih; case _ w ih =>
            apply Or.inl; apply Exists.intro w
            apply And.intro ih.1
            apply Star.step ih.2 r2
          case _ ih =>
            subst ih; apply Or.inl
            apply Exists.intro v; apply And.intro r2 Star.refl

      theorem congr3_1 {t1 t1'} t2 t3 (f : T -> T -> T -> T) :
        (∀ {t1 t2 t3 t1'}, R t1 t1' -> R (f t1 t2 t3) (f t1' t2 t3)) ->
        Star R t1 t1' ->
        Star R (f t1 t2 t3) (f t1' t2 t3)
      := by
        intro fh h2
        induction h2
        case _ => apply refl
        case _ h4 ih =>
          have h5 := @fh _ t2 t3 _ h4
          apply trans ih (Star.step Star.refl h5)

      theorem congr3_2 {t2 t2'} t1 t3 (f : T -> T -> T -> T) :
        (∀ {t1 t2 t3 t2'}, R t2 t2' -> R (f t1 t2 t3) (f t1 t2' t3)) ->
        Star R t2 t2' ->
        Star R (f t1 t2 t3) (f t1 t2' t3)
      := by
        intro fh h2
        induction h2
        case _ => apply refl
        case _ h4 ih =>
          have h5 := @fh t1 _ t3 _ h4
          apply trans ih (Star.step Star.refl h5)

      theorem congr3_3 {t3 t3'} t1 t2 (f : T -> T -> T -> T) :
        (∀ {t1 t2 t3 t3'}, R t3 t3' -> R (f t1 t2 t3) (f t1 t2 t3')) ->
        Star R t3 t3' ->
        Star R (f t1 t2 t3) (f t1 t2 t3')
      := by
        intro fh h2
        induction h2
        case _ => apply refl
        case _ h4 ih =>
          have h5 := @fh t1 t2 _ _ h4
          apply trans ih (Star.step Star.refl h5)

      theorem congr3 {t1 t1' t2 t2' t3 t3'} (f : T -> T -> T -> T) :
        (∀ {t1 t2 t3 t1'}, R t1 t1' -> R (f t1 t2 t3) (f t1' t2 t3)) ->
        (∀ {t1 t2 t3 t2'}, R t2 t2' -> R (f t1 t2 t3) (f t1 t2' t3)) ->
        (∀ {t1 t2 t3 t3'}, R t3 t3' -> R (f t1 t2 t3) (f t1 t2 t3')) ->
        Star R t1 t1' -> Star R t2 t2' -> Star R t3 t3' ->
        Star R (f t1 t2 t3) (f t1' t2' t3')
      := by
        intro f1 f2 f3 h1 h2 h3
        have r1 := congr3_1 t2 t3 f f1 h1
        have r2 := congr3_2 t1' t3 f f2 h2
        have r3 := congr3_3 t1' t2' f f3 h3
        apply trans r1; apply trans r2; apply trans r3; apply refl

      theorem congr2_1 {t1 t1'} t2 (f : T -> T -> T) :
        (∀ {t1 t2 t1'}, R t1 t1' -> R (f t1 t2) (f t1' t2)) ->
        Star R t1 t1' ->
        Star R (f t1 t2) (f t1' t2)
      := by
        intro fh h
        apply congr3_1 t2 t2 (λ t1 t2 _t3 => f t1 t2)
        intro t1 t2 _t3 t1' h; apply fh h
        exact h

      theorem congr2_2 {t2 t2'} t1 (f : T -> T -> T) :
        (∀ {t1 t2 t2'}, R t2 t2' -> R (f t1 t2) (f t1 t2')) ->
        Star R t2 t2' ->
        Star R (f t1 t2) (f t1 t2')
      := by
        intro fh h
        apply congr3_2 t1 t1 (λ t1 t2 _t3 => f t1 t2)
        intro t1 t2 _t3 t1' h; apply fh h
        exact h

      theorem congr2 {t1 t1' t2 t2'} (f : T -> T -> T) :
        (∀ {t1 t2 t1'}, R t1 t1' -> R (f t1 t2) (f t1' t2)) ->
        (∀ {t1 t2 t2'}, R t2 t2' -> R (f t1 t2) (f t1 t2')) ->
        Star R t1 t1' -> Star R t2 t2' ->
        Star R (f t1 t2) (f t1' t2')
      := by
        intro f1 f2 h1 h2
        have r1 := congr2_1 t2 f f1 h1
        have r2 := congr2_2 t1' f f2 h2
        apply trans r1; apply trans r2; apply refl

      theorem congr1 {t1 t1'} (f : T -> T) :
        (∀ {t1 t1'}, R t1 t1' -> R (f t1) (f t1')) ->
        Star R t1 t1' ->
        Star R (f t1) (f t1')
      := by
        intro fh h
        apply congr2_1 t1 (λ t1 _t2 => f t1)
        intro t1 _t2 t1' h; apply fh h
        exact h

      variable [HasTriangle R]

      theorem strip {s t1 t2} : R s t1 -> Star R s t2 -> ∃ t, Star R t1 t ∧ R t2 t := by
        intro h1 h2
        induction h2 generalizing t1
        case _ t' => exists t1; apply And.intro; apply Star.refl; apply h1
        case _ x y z _r1 r2 ih =>
          replace ih := ih h1
          cases ih
          case _ w ih =>
            replace r2 := HasTriangle.triangle r2
            have lem := HasTriangle.triangle ih.2
            replace lem := Star.step ih.1 lem
            exists (HasTriangle.complete R y)

      theorem confluence {s t1 t2} : Star R s t1 -> Star R s t2 -> ∃ t, Star R t1 t ∧ Star R t2 t := by
        intro h1 h2
        induction h1 generalizing t2
        case _ z =>
          exists t2; apply And.intro
          apply h2; apply Star.refl
        case _ s y t1 _r1 r2 ih =>
          replace ih := ih h2
          cases ih; case _ w ih =>
            have lem := strip r2 ih.1
            cases lem; case _ q lem =>
              exists q; apply And.intro
              apply lem.1; apply Star.step ih.2 lem.2

      variable [RenMap T] [SubstMap T T] [Substitutive R]

      omit [HasTriangle R] in
      theorem subst {x y} (σ : Subst T) : Star R x y -> Star R x[σ] y[σ] := by
        intro r; induction r
        case _ => apply Star.refl
        case _ r1 r2 ih =>
          replace r2 := Substitutive.subst σ r2
          apply Star.step ih r2
    end Star

    instance HasConfluence_from_HasTriangle {T : Type} {R : T -> T -> Prop} [HasTriangle R] : HasConfluence R where
      confluence := Star.confluence

    namespace Plus
      theorem destruct {x z} : Plus R x z -> ∃ y, R x y ∧ Star R y z := by
        intro r; induction r
        case _ b r =>
          exists b; apply And.intro r Star.refl
        case _ r1 r2 ih =>
          cases ih; case _ u ih =>
            exists u; apply And.intro ih.1
            apply Star.step ih.2 r2

      theorem stepr {x y z} : R x y -> Plus R y z -> Plus R x z := by
        intro r1 r2
        induction r2 generalizing x
        case _ r2 => apply Plus.step (Plus.start r1) r2
        case _ r3 r4 ih => apply Plus.step (ih r1) r4

      theorem stepr_from_star {x y z} : R x y -> Star R y z -> Plus R x z := by
        intro r1 r2
        induction r2 generalizing x
        case _ => apply Plus.start; apply r1
        case _ r3 r4 ih => apply Plus.step (ih r1) r4
    end Plus

    namespace Conv
      theorem forward_right {x y z} : Conv R x y -> R y z -> Conv R x z := by
        intro h r; induction h generalizing z
        case _ => apply backward refl r
        case _ r2 ih => apply forward (ih r) r2
        case _ r2 ih => apply backward (ih r) r2

      theorem backward_right {x y z} : Conv R x y -> R z y -> Conv R x z := by
        intro h r; induction h generalizing z
        case _ => apply forward refl r
        case _ r2 ih => apply forward (ih r) r2
        case _ r2 ih => apply backward (ih r) r2

      theorem sym {x y} : Conv R x y -> Conv R y x := by
        intro h; induction h
        case _ => constructor
        case _ r ih => apply forward_right ih r
        case _ r ih => apply backward_right ih r

      theorem star_forward {x y z} : Conv R x z -> Star R x y -> Conv R y z := by
        intro cv r
        induction r; simp [*]
        case _ r1 r2 ih => apply forward ih r2

      theorem star_backward {x y z} : Conv R y z -> Star R x y -> Conv R x z := by
        intro cv r
        induction r; simp [*]
        case _ r1 r2 ih =>
          apply ih
          apply backward cv r2

      theorem star_forward_right {x y z} : Conv R x y -> Star R y z -> Conv R x z := by
        intro cv r
        induction r; simp [*]
        case _ r1 r2 ih => apply forward_right ih r2

      theorem star_backward_right {x y z} : Conv R x y -> Star R z y -> Conv R x z := by
        intro cv r
        induction r; simp [*]
        case _ r1 r2 ih =>
          apply ih
          apply backward_right cv r2

      theorem star_equiv {x y} [HasConfluence R] : Conv R x y <-> (∃ t, Star R x t ∧ Star R y t) := by
        apply Iff.intro
        case _ =>
          intro cv
          induction cv
          case _ t =>
            exists t
            apply And.intro Star.refl Star.refl
          case _ a b c cv r ih =>
            cases ih; case _ t ih =>
            have lem := HasConfluence.confluence (Star.step Star.refl r) ih.1
            cases lem; case _ z lem =>
            have lem2 := Star.trans ih.2 lem.2
            exists z; apply And.intro lem.1 lem2
          case _ a b c cv r ih =>
            cases ih; case _ t ih =>
            have lem := Star.stepr r ih.1
            exists t; simp [*]
        case _ =>
          intro h
          cases h; case _ t h =>
          apply star_backward _ h.1
          apply star_backward_right _ h.2
          apply refl

      theorem trans {x y z} [HasConfluence R] : Conv R x y -> Conv R y z -> Conv R x z := by
        intro h1 h2
        replace h1 := star_equiv.1 h1
        replace h2 := star_equiv.1 h2
        cases h1; case _ t1 h1 =>
        cases h2; case _ t2 h2 =>
        have lem := HasConfluence.confluence h1.2 h2.1
        cases lem; case _ w lem =>
        replace h1 := Star.trans h1.1 lem.1
        replace h2 := Star.trans h2.2 lem.2
        apply star_backward _ h1
        apply star_backward_right _ h2
        apply refl
    end Conv
  end

  section
    variable {T : Type u} (R : T -> T -> Prop) {t t' : T}

    @[simp]
    def FunctionalTerm (t : T) :=
      ∀ {x y}, R t x -> R t y -> x = y

    class Functional where
      functional : ∀ {t}, FunctionalTerm R t
  end

end LeanSubst
