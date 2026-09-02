/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Constant germs and the residue field

This file packages the constant inclusion, identifies the residue field with
`ℂ`, and supplies the zero-dimensional base case used by Rückert induction.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- Embed a complex number as a constant holomorphic germ. -/
def constantGermHom (n : ℕ) : ℂ →+* HolomorphicGerm n where
  toFun c := HolomorphicGerm.ofFunction (fun _ ↦ c) analyticAt_const
  map_zero' := by
    apply Subtype.ext
    rfl
  map_one' := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    rfl

@[simp]
theorem evalAtOrigin_constantGerm (n : ℕ) (c : ℂ) :
    evalAtOriginHom n (constantGermHom n c) = c :=
  rfl

/-- Evaluation at the origin is onto, with the constant-germ map as a section. -/
theorem evalAtOrigin_surjective (n : ℕ) :
    Function.Surjective (evalAtOriginHom n) := by
  intro c
  exact ⟨constantGermHom n c, by simp⟩

/-- The maximal ideal is the kernel of evaluation at the origin. -/
theorem holomorphicGerm_maximalIdeal_eq_ker (n : ℕ) :
    IsLocalRing.maximalIdeal (HolomorphicGerm n) =
      RingHom.ker (evalAtOriginHom n) := by
  simpa [RingHom.ker] using holomorphicGerm_maximalIdeal n

/-- The residue field of the holomorphic local ring is canonically `ℂ`. -/
def holomorphicGermResidueFieldEquiv (n : ℕ) :
    (HolomorphicGerm n ⧸ IsLocalRing.maximalIdeal (HolomorphicGerm n)) ≃+* ℂ :=
  (Ideal.quotEquivOfEq (holomorphicGerm_maximalIdeal_eq_ker n)).trans
    (RingHom.quotientKerEquivOfSurjective (evalAtOrigin_surjective n))

@[simp]
theorem holomorphicGerm_residueFieldEquiv_mk (n : ℕ) (f : HolomorphicGerm n) :
    holomorphicGermResidueFieldEquiv n
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolomorphicGerm n)) f) =
        evalAtOrigin f := by
  simp [holomorphicGermResidueFieldEquiv]

/-- In complex dimension zero, evaluation is injective. -/
theorem evalAtOrigin_injective_zero :
    Function.Injective (evalAtOriginHom 0) := by
  intro φ ψ h
  obtain ⟨f, hf, hφ⟩ := φ.property
  obtain ⟨g, hg, hψ⟩ := ψ.property
  have hfg0 : f 0 = g 0 := by
    change Filter.Germ.value (φ : FunctionGerm 0) =
      Filter.Germ.value (ψ : FunctionGerm 0) at h
    rw [← hφ, ← hψ] at h
    simpa using h
  apply Subtype.ext
  rw [← hφ, ← hψ]
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro x
  have hx : x = (0 : ComplexEuclidean 0) := Subsingleton.elim _ _
  subst x
  exact hfg0

/-- The zero-dimensional holomorphic germ ring is canonically `ℂ`. -/
def holomorphicGermZeroEquiv : HolomorphicGerm 0 ≃+* ℂ :=
  RingEquiv.ofBijective (evalAtOriginHom 0)
    ⟨evalAtOrigin_injective_zero, evalAtOrigin_surjective 0⟩

@[simp]
theorem holomorphicGermZeroEquiv_apply (f : HolomorphicGerm 0) :
    holomorphicGermZeroEquiv f = evalAtOrigin f :=
  rfl

/-- The zero-dimensional case of Rückert's basis theorem. -/
theorem holomorphicGerm_isNoetherian_zero :
    IsNoetherianRing (HolomorphicGerm 0) :=
  isNoetherianRing_of_ringEquiv ℂ holomorphicGermZeroEquiv.symm

end

end LocalComplexGeometry
