/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.Positivity.Finset

/-!
# Kernel of the Evaluation Map on Adic Completions

For a Noetherian local ring (R, M) and n : N, an element of the
M-adic completion that maps to zero under the canonical projection
to R/M^n must lie in the n-th power of the extended maximal ideal.
This follows from the kernel description for evaluation on a
finitely generated adic completion.
-/

@[expose] public section

open scoped Pointwise
open AdicCompletion

variable {R : Type*} [CommRing R]

/-! ### R ⧸ I^n is I-adically complete -/

lemma smul_eq_zero_of_quotient (I : Ideal R) (n : ℕ)
    (x : R ⧸ (I ^ n • ⊤ : Submodule R R))
    (hx : x ∈ I ^ n • (⊤ : Submodule R (R ⧸ (I ^ n • ⊤ : Submodule R R)))) :
    x = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    induction y using Quotient.inductionOn' with
    | h a =>
      change Submodule.Quotient.mk (r • a) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    rw [hx, hy, add_zero]

instance quotientIsHausdorff (I : Ideal R) (n : ℕ) :
    IsHausdorff I (R ⧸ (I ^ n • ⊤ : Submodule R R)) where
  haus' x hx := smul_eq_zero_of_quotient I n x (by
    have := hx n
    rwa [SModEq.sub_mem, sub_zero] at this)

instance quotientIsPrecomplete (I : Ideal R) (n : ℕ) :
    IsPrecomplete I (R ⧸ (I ^ n • ⊤ : Submodule R R)) where
  prec' f hf := ⟨f n, fun k => by
    rw [SModEq.sub_mem]
    by_cases hkn : k ≤ n
    · exact SModEq.sub_mem.mp (hf hkn)
    · have h0 := smul_eq_zero_of_quotient I n _ (SModEq.sub_mem.mp (hf (le_of_not_ge hkn)))
      rw [← sub_eq_zero.mp h0, sub_self]
      exact Submodule.zero_mem _⟩

instance quotientAdicComplete (I : Ideal R) (n : ℕ) :
    IsAdicComplete I (R ⧸ (I ^ n • ⊤ : Submodule R R)) :=
  IsAdicComplete.mk

/-! ### Key lemma: evalₐ I n x = 0 → x ∈ I^n • ⊤ -/

/-- If evalₐ I n x = 0, then x ∈ I^n • ⊤ (as R-submodule of R̂).
This is the backward half of ker(evalₐ I n) = (Ideal.map f I)^n. -/
lemma ker_evalₐ_le_smul_top (I : Ideal R) [IsNoetherianRing R] (n : ℕ)
    (x : AdicCompletion I R)
    (hx : evalₐ I n x = 0) :
    x ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
  rw [pow_smul_top_eq_ker_eval (M := R) I.fg_of_isNoetherianRing,
    LinearMap.mem_ker, ← factor_evalₐ_eq_eval I x (by simp), hx, _root_.map_zero]

/-! ### Main theorem: kernel of evalₐ is contained in the power of the extended maximal ideal -/

/-- If an element `x` of the `𝔪`-adic completion of a Noetherian local ring `(R, 𝔪)` satisfies
`evalₐ 𝔪 n x = 0`, then `x ∈ (𝔪̂)^n` where `𝔪̂ = Ideal.map (algebraMap R R̂) 𝔪`. -/
theorem mem_map_pow_of_evalₐ_eq_zero
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (hx : AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n x = 0) :
    x ∈ (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
      (IsLocalRing.maximalIdeal R)) ^ n := by
  rw [← Ideal.map_pow]
  simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using
    ker_evalₐ_le_smul_top (IsLocalRing.maximalIdeal R) n x hx
