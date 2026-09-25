/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.ScalarExtensionPoints


/-!
# Poisson closure after scalar extension

This file transports bracket closure through coefficient extension.  Its main
result uses the Gabber-shaped involutivity hypothesis `{J,J} ⊆ J`, rather than
the much stronger project predicate `IsPoisson J = {J,R} ⊆ J`.  A second result
transports that stronger predicate by extracting stability under every
coordinate derivation.  No claim is made that taking a radical after base
change preserves bracket closure.
-/

@[expose] public section

namespace Stafford38.Characteristic.PostScalarExtensionPoisson

open Stafford38.Characteristic
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.CoisotropicTranslation

noncomputable section

universe u v

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]
variable {n : ℕ}

/-- The Gabber-shaped bracket condition: both bracket entries lie in the
ideal.  This is weaker than the project predicate `IsPoisson`. -/
def IsInvolutive (J : Ideal (SymbolRing k n)) : Prop :=
  ∀ f ∈ J, ∀ g ∈ J, poissonBracket f g ∈ J

/-- Coefficient extension commutes with the canonical Poisson bracket. -/
theorem poissonBracket_scalarPolynomialMap
    (f g : SymbolRing k n) :
    poissonBracket
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n) f)
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n) g) =
      scalarPolynomialMap (k := k) (K := K) (PhaseVar n)
        (poissonBracket f g) := by
  simp [poissonBracket, scalarPolynomialMap, MvPolynomial.pderiv_map]

theorem poissonBracket_add_left (f₁ f₂ g : SymbolRing k n) :
    poissonBracket (f₁ + f₂) g =
      poissonBracket f₁ g + poissonBracket f₂ g := by
  simp [poissonBracket, add_mul, Finset.sum_add_distrib]
  ring

theorem poissonBracket_add_right (f g₁ g₂ : SymbolRing k n) :
    poissonBracket f (g₁ + g₂) =
      poissonBracket f g₁ + poissonBracket f g₂ := by
  simp [poissonBracket, mul_add, Finset.sum_add_distrib]
  ring

theorem poissonBracket_mul_left (a f g : SymbolRing k n) :
    poissonBracket (a * f) g =
      a * poissonBracket f g + f * poissonBracket a g := by
  simp only [poissonBracket, MvPolynomial.pderiv_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem poissonBracket_mul_right (f a g : SymbolRing k n) :
    poissonBracket f (a * g) =
      a * poissonBracket f g + g * poissonBracket f a := by
  simp only [poissonBracket, MvPolynomial.pderiv_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Gabber-shaped involutivity is preserved by arbitrary field-valued
coefficient extension. -/
theorem isInvolutive_map_scalarPolynomialMap
    (J : Ideal (SymbolRing k n)) (hJ : IsInvolutive J) :
    IsInvolutive
      (J.map (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))) := by
  let I := J.map (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))
  intro f hf
  change f ∈ J.map
    (scalarPolynomialMap (k := k) (K := K) (PhaseVar n)) at hf
  rw [Ideal.map] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨f₀, hf₀, rfl⟩
      intro g hg
      change g ∈ J.map
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n)) at hg
      rw [Ideal.map] at hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
          rcases hg with ⟨g₀, hg₀, rfl⟩
          rw [poissonBracket_scalarPolynomialMap]
          exact Ideal.mem_map_of_mem _ (hJ f₀ hf₀ g₀ hg₀)
      | zero => simp [poissonBracket]
      | add g₁ g₂ _ _ hg₁ hg₂ =>
          rw [poissonBracket_add_right]
          exact I.add_mem hg₁ hg₂
      | smul a g hgm hg =>
          rw [smul_eq_mul, poissonBracket_mul_right]
          exact I.add_mem (I.mul_mem_left _ hg) (I.mul_mem_right _ hgm)
  | zero =>
      intro g hg
      simp [poissonBracket]
  | add f₁ f₂ _ _ hf₁ hf₂ =>
      intro g hg
      rw [poissonBracket_add_left]
      exact I.add_mem (hf₁ g hg) (hf₂ g hg)
  | smul a f hfm hf =>
      intro g hg
      rw [smul_eq_mul, poissonBracket_mul_left]
      exact I.add_mem (I.mul_mem_left _ (hf g hg)) (I.mul_mem_right _ hfm)

/-- Scalar extension of Gabber-shaped involutivity gives exactly the
base-relative condition consumed by the conormal proof. -/
theorem isBaseRelativePoisson_map_of_isInvolutive
    (J : Ideal (SymbolRing k n)) (hJ : IsInvolutive J) :
    BaseRelativePoisson.IsBaseRelativePoisson
      (J.map (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))) := by
  intro f hf g hg
  exact isInvolutive_map_scalarPolynomialMap J hJ (baseLift f) hf g hg

/-- A Poisson ideal is stable under each phase-space partial derivative. -/
theorem pderiv_mem_of_isPoisson
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J)
    {f : SymbolRing k n} (hf : f ∈ J) (i : PhaseVar n) :
    MvPolynomial.pderiv i f ∈ J := by
  rcases i with i | i
  · have h := hJ f hf (MvPolynomial.X (Sum.inr i))
    simpa [poissonBracket, Pi.single_apply] using h
  · have h := hJ f hf (MvPolynomial.X (Sum.inl i))
    have hn : -MvPolynomial.pderiv (Sum.inr i) f ∈ J := by
      simpa [poissonBracket, Pi.single_apply] using h
    simpa using J.neg_mem hn

/-- Every coordinate derivation preserves the ideal generated after scalar
extension from a Poisson ideal. -/
theorem pderiv_mem_map_scalarPolynomialMap
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J)
    {f : SymbolRing K n}
    (hf : f ∈ J.map
      (scalarPolynomialMap (k := k) (K := K) (PhaseVar n)))
    (i : PhaseVar n) :
    MvPolynomial.pderiv i f ∈ J.map
      (scalarPolynomialMap (k := k) (K := K) (PhaseVar n)) := by
  rw [Ideal.map] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨g, hg, rfl⟩
      change MvPolynomial.pderiv i
          (MvPolynomial.map (algebraMap k K) g) ∈ _
      rw [MvPolynomial.pderiv_map]
      exact Ideal.mem_map_of_mem _ (pderiv_mem_of_isPoisson J hJ hg i)
  | zero => simp
  | add f g _ _ hf hg =>
      simpa using (J.map
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).add_mem hf hg
  | smul a f hfm hf =>
      rw [smul_eq_mul, MvPolynomial.pderiv_mul]
      exact (J.map
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).add_mem
          ((J.map
            (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).mul_mem_left _ hfm)
          ((J.map
            (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).mul_mem_left _ hf)

/-- Full Poisson closure is preserved by arbitrary field-valued coefficient
extension.  The target is the actual extended ideal `map`, not its radical. -/
theorem isPoisson_map_scalarPolynomialMap
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J) :
    IsPoisson
      (J.map (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))) := by
  intro f hf g
  apply (J.map
    (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).sum_mem
  intro i hi
  apply (J.map
    (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).sub_mem
  · exact (J.map
      (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).mul_mem_right _
        (pderiv_mem_map_scalarPolynomialMap J hJ hf (Sum.inl i))
  · exact (J.map
      (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).mul_mem_right _
        (pderiv_mem_map_scalarPolynomialMap J hJ hf (Sum.inr i))

/-- The transported full Poisson theorem supplies the exact base-relative
fragment used by the conormal argument. -/
theorem isBaseRelativePoisson_map_scalarPolynomialMap
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J) :
    BaseRelativePoisson.IsBaseRelativePoisson
      (J.map (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))) :=
  BaseRelativePoisson.IsPoisson.isBaseRelativePoisson _
    (isPoisson_map_scalarPolynomialMap J hJ)


end

end Stafford38.Characteristic.PostScalarExtensionPoisson
