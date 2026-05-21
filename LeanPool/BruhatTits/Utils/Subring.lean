/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.Tactic

open Module

variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [Ring R]
variable {A : Subring R}

@[simp]
lemma Subtype.val_comp_single (i : ι) (a : A) :
    Subtype.val ∘ Pi.single i a = Pi.single i a := by
  ext j
  by_cases h : i = j
  all_goals aesop

omit [DecidableEq ι]
@[simp]
lemma Subtype.val_comp_add (v w : ι → A) :
    Subtype.val ∘ (v + w) = Subtype.val ∘ v + Subtype.val ∘ w := by
  ext j
  simp

@[simp]
lemma Subtype.val_comp_smul (a : A) (v : ι → A) :
    Subtype.val ∘ (a • v) = a • Subtype.val ∘ v := by
  ext j
  simp
  rfl

section

variable {K : Type*} [Field K]
variable {R : Subring K} [IsFractionRing R K]

lemma Module.Basis.linearIndependent_of_submodule {κ : Type*} {M : Submodule R (ι → K)}
    (b : Basis κ R M) :
    LinearIndependent K (fun i ↦ (b i).val) := by
  rw [← LinearIndependent.iff_fractionRing (R := R), linearIndependent_iff']
  intro s g hs
  simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
  exact linearIndependent_iff'.mp b.linearIndependent s g hs

end
