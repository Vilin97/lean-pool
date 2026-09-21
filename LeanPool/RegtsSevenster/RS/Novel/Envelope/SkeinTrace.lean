/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinTower
import LeanPool.RegtsSevenster.RS.Novel.Skein.MonoidalInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseUnion
import LeanPool.RegtsSevenster.RS.Novel.Skein.ScalarFunctional

/-!
# The skein trace

The trace of an `n`-strand endomorphism -- its closure against
the strand bundle -- and the one fact the trace calculus needs of
it: closing a tensor product multiplies the two closures, proved
by bilinear induction down to single fragments.
-/

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The trace of an `n`-strand endomorphism: the closure against
the strand bundle. -/
noncomputable def skeinTrace (n : ℕ) (g : skeinEnd f n) : ℂ :=
  HomSpace.traceMap f.val n g

/-- **The trace of a tensor product is the product of traces.** -/
theorem skeinTrace_tensorHom {a b : ℕ}
    (u : skeinEnd f a) (v : skeinEnd f b) :
    skeinTrace f (a + b)
      (show skeinEnd f (a + b) from
        MonoidalCategoryStruct.tensorHom u v) =
    skeinTrace f a u * skeinTrace f b v := by
  -- Reduce to HomSpace operations
  show HomSpace.traceMap f.val (a + b)
    (HomSpace.tensor f a a b b u v) =
    HomSpace.traceMap f.val a u * HomSpace.traceMap f.val b v
  -- Lift u, v to free-module representatives
  obtain ⟨xu, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨xv, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  -- At the free module level
  show traceFunctional f.val (a + b) (tensorFinsupp a a b b xu xv) =
    traceFunctional f.val a xu * traceFunctional f.val b xv
  -- Helper: traceFunctional on a scaled single fragment
  have htr : ∀ (n : ℕ) (H : Fragment (Fin (n + n))) (e : ℂ),
      traceFunctional f.val n (Finsupp.single H e) =
        e * fragTrace f.val H := by
    intro n H e
    rw [show (Finsupp.single H e : Fragment (Fin (n + n)) →₀ ℂ) =
        e • Finsupp.single H 1 by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, traceFunctional_single, smul_eq_mul]
  -- Bilinear induction on xu
  induction xu using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, zero_mul]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply]
    rw [h₁, h₂, add_mul]
  | single F c =>
    induction xv using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add]
      rw [h₁, h₂, mul_add]
    | single G d =>
      rw [tensorFinsupp_single, htr, htr, htr, fragTrace_tensor]
      ring

/-- The trace of the empty identity is one. -/
theorem skeinTrace_zero_one :
    skeinTrace f 0 (1 : skeinEnd f 0) = 1 :=
  (traceMap_zero_ofFragment f (strandBundle 0)).trans
    ((f.iso_invariant _ _ strandBundleZeroEmpty).trans
      f.val_empty)

end RS
