/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Finite-field coordinates for minimal representations

An injective affine chart has an affine left inverse on the whole ambient
vector space. Its retraction identity extends from the support to its affine
span. Integer affine generation also implies affine generation modulo `p`.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ

/-- An affine retraction that is a left inverse when the original affine map is injective. -/
noncomputable def affineLeftInverse {k : Type*} [Field k] {m n : ℕ}
    (A : (Fin m → k) →ᵃ[k] (Fin n → k)) : (Fin n → k) →ᵃ[k] (Fin m → k) :=
  A.linear.leftInverse.toAffineMap.comp
    (AffineMap.id k _ - AffineMap.const k _ (A 0))

theorem affineLeftInverse_apply {k : Type*} [Field k] {m n : ℕ}
    (A : (Fin m → k) →ᵃ[k] (Fin n → k)) (hA : Function.Injective A)
    (q : Fin m → k) : affineLeftInverse A (A q) = q := by
  change A.linear.leftInverse (A q - A 0) = q
  have hlin : A q - A 0 = A.linear q := by
    simpa using (A.linearMap_vsub q 0).symm
  rw [hlin]
  exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr
    (A.linear_injective_iff.mpr hA)) q

theorem affineLeftInverse_retract {k : Type*} [Field k] {m n : ℕ}
    (A : (Fin m → k) →ᵃ[k] (Fin n → k)) (hA : Function.Injective A)
    {q : Fin n → k} (hq : q ∈ Set.range A) : A (affineLeftInverse A q) = q := by
  obtain ⟨z, rfl⟩ := hq
  rw [affineLeftInverse_apply A hA]

/-- Retraction through the chart is the identity on the entire affine span
once it is the identity on the support. -/
theorem affineLeftInverse_retract_affineSpan {k : Type*} [Field k] {l m n : ℕ}
    (A : (Fin m → k) →ᵃ[k] (Fin n → k)) (hA : Function.Injective A)
    (φ : (Fin l → k) →ᵃ[k] (Fin n → k)) (S : Set (Fin l → k))
    (hS : ∀ v ∈ S, φ v ∈ Set.range A) {v : Fin l → k}
    (hv : v ∈ affineSpan k S) : A (affineLeftInverse A (φ v)) = φ v :=
  AffineMap.eqOn_affineSpan
    (f := A.comp ((affineLeftInverse A).comp φ)) (g := φ)
    (fun v hv ↦ affineLeftInverse_retract A hA (hS v hv)) hv

theorem surjOn_affineSpan_of_image_span_eq_top {k : Type*} [Field k] {m n : ℕ}
    (φ : (Fin m → k) →ᵃ[k] (Fin n → k)) (S : Set (Fin m → k))
    (hS : affineSpan k (φ '' S) = ⊤) :
    Set.SurjOn φ (affineSpan k S : Set (Fin m → k)) Set.univ := by
  intro q _
  have hq : q ∈ affineSpan k (φ '' S) := by rw [hS]; trivial
  rw [← AffineSubspace.map_span] at hq
  exact hq

/-- Integer affine generators generate the full finite-field affine space
after reduction modulo a prime. -/
theorem FlagDecomposition.AffineIntSpans.affineSpan_mod_eq_top {p n : ℕ}
    [Fact p.Prime]
    {S : Finset (IntCoord n)} (hS : FlagDecomposition.AffineIntSpans S) :
    affineSpan (ZMod p) (IntCoord.mod p '' (S : Set (IntCoord n))) = ⊤ := by
  classical
  apply top_unique
  intro a _
  obtain ⟨c, hcS, hsum, hcoord⟩ := hS (FpCoord.centeredLift a)
  have hsum' : (∑ z ∈ c.support, (c z : ZMod p)) = 1 := by
    have hc := congrArg (fun z : ℤ ↦ (z : ZMod p)) hsum
    simpa only [Int.cast_sum, Int.cast_one] using hc
  have hcomb := affineCombination_mem_affineSpan_image
    (s := c.support) (s' := (S : Set (IntCoord n))) hsum'
    (fun _ hz hn ↦ (hn (hcS hz)).elim) (IntCoord.mod p)
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum'] at hcomb
  have heq : (∑ z ∈ c.support, (c z : ZMod p) • z.mod p) = a := by
    have hmod := congrArg (IntCoord.mod p) hcoord
    rw [FpCoord.mod_centeredLift] at hmod
    convert hmod using 1
    ext i
    simp [IntCoord.mod, Finset.sum_apply, Int.cast_sum, Int.cast_mul]
  rwa [heq] at hcomb

end EGZ
