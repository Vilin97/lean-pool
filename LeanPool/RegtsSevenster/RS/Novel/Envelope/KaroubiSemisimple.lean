/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.KaroubiTrace
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SemisimpleAll
import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockFactorialTrace

/-!
# Semisimplicity of Karoubi endomorphism algebras

The endomorphism algebra of any object of the Karoubi envelope of
the skein category is a corner `e·End(n)·e`, and the trace
criterion restricts: corner-nilpotents are ambient-nilpotents, and
cyclicity moves the idempotent across products, so ambient
nondegeneracy restricts to the corner.
-/

namespace RS

open CategoryTheory CategoryTheory.Idempotents

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### The endomorphism algebras of Karoubi objects -/

variable (X : Karoubi (SkeinObj f))

/-- Endomorphisms of a Karoubi object form a ring. -/
noncomputable instance karoubiEndRing : Ring (End X) :=
  inferInstance

/-- And a ℂ-algebra — the corner `e·End(n)·e`. -/
noncomputable instance karoubiEndAlgebra : Algebra ℂ (End X) :=
  inferInstance

/-- Finite-dimensional, as a subspace of the ambient skein
endomorphisms. -/
noncomputable instance karoubiEndFinite :
    FiniteDimensional ℂ (End X) :=
  FiniteDimensional.of_injective
    (show End X →ₗ[ℂ] skeinEnd f X.X.arity from
      karoubiHomLinearMap X X)
    (fun _ _ h => Karoubi.Hom.ext h)

/-- The corner trace criterion, given nilpotent-trace vanishing
in the ambient strand algebra. -/
theorem karoubiEnd_isSemisimpleRing_of_nilpotent_trace
    (hnil : ∀ g : skeinEnd f X.X.arity,
      IsNilpotent g → skeinTrace f X.X.arity g = 0) :
    IsSemisimpleRing (End X) := by
  haveI : FiniteDimensional ℂ (End X.X) :=
    inferInstanceAs (FiniteDimensional ℂ (skeinEnd f X.X.arity))
  exact karoubiEnd_isSemisimpleRing_of_trace X
    (HomSpace.traceMap f.val X.X.arity) hnil
    (HomSpace.traceMap_comp_comm f)
    (end_eq_zero_of_traces_vanish f X.X)

/-- **Semisimplicity of Karoubi endomorphism algebras**, by the
factorial trace obstruction. -/
theorem karoubiEnd_isSemisimpleRing :
    IsSemisimpleRing (End X) :=
  karoubiEnd_isSemisimpleRing_of_nilpotent_trace f X
    (fun _ hg =>
      skeinTrace_eq_zero_of_isNilpotent_factorial f X.X.arity hg)

/-- The mainline Karoubi semisimplicity theorem, with the
factorial proof method explicit in its name. -/
theorem karoubiEnd_isSemisimpleRing_factorial :
    IsSemisimpleRing (End X) := karoubiEnd_isSemisimpleRing f X

/-! ### Mixed-Hom nondegeneracy in the Karoubi envelope -/

/-- A Karoubi morphism all of whose composite traces against
reverse morphisms vanish is zero: the separation engine for the
simples. -/
theorem karoubiHom_eq_zero_of_traces_vanish
    {X Y : Karoubi (SkeinObj f)} (a : X ⟶ Y)
    (ha : ∀ b : Y ⟶ X,
      HomSpace.traceMap f.val X.X.arity (a.f ≫ b.f) = 0) :
    a = 0 := by
  apply Karoubi.hom_ext
  show a.f = 0
  apply hom_eq_zero_of_traces_vanish' f X.X Y.X a.f
  intro b
  have hb : Y.p ≫ (Y.p ≫ b ≫ X.p) ≫ X.p =
      Y.p ≫ b ≫ X.p := by
    rw [show Y.p ≫ (Y.p ≫ b ≫ X.p) ≫ X.p =
      (Y.p ≫ Y.p) ≫ b ≫ (X.p ≫ X.p) from by
        simp only [Category.assoc]]
    rw [Y.idem, X.idem]
  have key := ha (⟨Y.p ≫ b ≫ X.p, hb⟩ : Y ⟶ X)
  have hred : a.f ≫ (Y.p ≫ b ≫ X.p) =
      (a.f ≫ b) ≫ X.p := by
    rw [show a.f ≫ (Y.p ≫ b ≫ X.p) =
      (a.f ≫ Y.p) ≫ b ≫ X.p from by
        simp only [Category.assoc]]
    rw [Karoubi.comp_p]
    simp only [Category.assoc]
  have hcyc := HomSpace.traceMap_comp_comm f
    (t := X.X.arity) (u := X.X.arity)
    (a.f ≫ b) X.p
  have hfin : HomSpace.traceMap f.val X.X.arity
      (X.p ≫ (a.f ≫ b)) =
      HomSpace.traceMap f.val X.X.arity (a.f ≫ b) := by
    rw [show X.p ≫ (a.f ≫ b) = (X.p ≫ a.f) ≫ b from by
      simp only [Category.assoc]]
    rw [Karoubi.p_comp]
  calc HomSpace.traceMap f.val X.X.arity (a.f ≫ b)
      = HomSpace.traceMap f.val X.X.arity
          (X.p ≫ (a.f ≫ b)) := hfin.symm
    _ = HomSpace.traceMap f.val X.X.arity
          ((a.f ≫ b) ≫ X.p) := hcyc.symm
    _ = HomSpace.traceMap f.val X.X.arity
          (a.f ≫ (Y.p ≫ b ≫ X.p)) := by rw [hred]
    _ = 0 := key

end RS
