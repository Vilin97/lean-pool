/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.ScalarPermTrace
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPermCast
import LeanPool.RegtsSevenster.RS.Novel.Envelope.ScalarTrace
import LeanPool.RegtsSevenster.RS.Novel.Envelope.TraceZetaSharp

/-!
# The Frobenius tower of an object

The tensor powers of a single object in a rigid symmetric ℂ-linear
category, with the symmetric-group action permuting the factors and
the categorical trace, form a Frobenius tower.  Everything the tower
asks for has been assembled: the representations are `permAlg`,
vanishing propagates by `permAlg_compat`, the traces are
`scalarTrace`, the tensor-power maps are `powHom`, and the Frobenius
identity comes from the cycle-type formula for the trace of a
permutation against a tensor power.
-/

namespace RS

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

variable {A : Type u}

/-! ## The Frobenius identity -/

/-- **The Frobenius trace identity** for the tensor powers of an
object: the trace of a Young idempotent against a tensor power is
the block dimension times the Schur specialization of the power
traces.  Expanding the idempotent turns the left side into a
character-weighted sum of permutation traces, and the cycle-type
formula turns each of those into the cycle product the classical
Frobenius formula sums. -/
theorem frobenius_powHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) (X : A)
    (P : SchurPackage.{v}) (μ : YoungDiagram) (g : End X) :
    scalarTrace hu (tensorPow A X μ.card)
        (permAlg X μ.card (P.e μ) * powHom X g μ.card) =
      (P.dim μ : ℂ) *
        diagramSchur μ (fun m => scalarTrace hu X (g ^ m)) := by
  classical
  set t : ℕ → ℂ := fun m => scalarTrace hu X (g ^ m) with ht
  have hexp : permAlg X μ.card (P.e μ) * powHom X g μ.card =
      ((P.dim μ : ℂ) / (μ.card.factorial : ℂ)) •
        ∑ π : Equiv.Perm (Fin μ.card), P.char μ π •
          (permAlg X μ.card (MonoidAlgebra.single π (1 : ℂ)) *
            powHom X g μ.card) := by
    rw [SchurPackage.e_def, charIdempotent, map_smul, map_sum,
      smul_mul_assoc, Finset.sum_mul]
    refine congrArg _ (Finset.sum_congr rfl fun π _ => ?_)
    rw [map_smul, smul_mul_assoc]
    rfl
  have hterm : ∀ π : Equiv.Perm (Fin μ.card),
      scalarTrace hu (tensorPow A X μ.card)
          (P.char μ π •
            (permAlg X μ.card (MonoidAlgebra.single π (1 : ℂ)) *
              powHom X g μ.card)) =
        P.char μ π * ((π.cycleType.map t).prod *
          t 1 ^ (μ.card - π.cycleType.sum)) := by
    intro π
    have hmor : permAlg X μ.card (MonoidAlgebra.single π (1 : ℂ)) *
        powHom X g μ.card =
        powHom X g μ.card ≫ permMor X μ.card π := by
      rw [permAlg_single]
      rfl
    rw [hmor, map_smul, smul_eq_mul]
    refine congrArg (P.char μ π * ·) ?_
    rw [scalarTrace_comp_comm, scalarTrace_permMor_powHom,
      prod_fullCycleType]
  rw [hexp, map_smul, smul_eq_mul, map_sum,
    Finset.sum_congr rfl fun π _ => hterm π, div_eq_mul_inv,
    mul_assoc]
  exact congrArg ((P.dim μ : ℂ) * ·) (P.frobenius μ t)

/-! ## The tower -/

/-- **The Frobenius tower of an object**: the tensor powers of `X`,
with the symmetric-group action permuting the factors, the tensor
powers of an endomorphism, and the categorical trace read as a
complex number. -/
noncomputable def objectFrobeniusTower
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) (X : A)
    (P : SchurPackage.{v}) (A₀ : ℝ)
    (hb : ∀ n, ((Module.finrank ℂ (End (tensorPow A X n)) : ℕ) : ℝ) ≤
      A₀ ^ n) :
    FrobeniusTower P (fun n => End (tensorPow A X n)) A₀ (End X) where
  rep := permAlg X
  compat h x hx := permAlg_compat X h x hx
  bound := hb
  traceA := scalarTrace hu X
  trace n := scalarTrace hu (tensorPow A X n)
  pow n g := powHom X g n
  frobenius μ g := frobenius_powHom hu X P μ g

/-! ## The theorems of the appendix, for an object -/

open scoped Polynomial PowerSeries

/-- **The nilpotent-trace theorem for an object**: in a rigid
symmetric ℂ-linear category with scalar unit endomorphisms, if the
tensor powers of `X` have finite-dimensional endomorphism algebras
of exponentially bounded dimension, then every nilpotent
endomorphism of `X` has vanishing categorical trace. -/
theorem scalarTrace_eq_zero_of_isNilpotent
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A)
    (X : A) [∀ n, Module.Finite ℂ (End (tensorPow A X n))]
    (A₀ : ℝ)
    (hb : ∀ n, ((Module.finrank ℂ (End (tensorPow A X n)) : ℕ) : ℝ) ≤
      A₀ ^ n) {g : End X} (hg : IsNilpotent g) :
    scalarTrace hu X g = 0 :=
  (objectFrobeniusTower hu X schurPackage.{v} A₀
    hb).traceA_eq_zero_of_isNilpotent hg

/-- **The trace-zeta theorem for an object** (the accompanying
paper, Corollary A.2): for an object whose tensor powers have
endomorphism dimensions bounded by `A₀ ^ n`, and for every integer
`s > 2e√A₀`, the trace zeta function of every endomorphism is `P/Q`
with `P` and `Q` coprime, of constant term `1`, and of degree at
most `s − 1`. -/
theorem traceZeta_rational_of_object
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A)
    (X : A) [∀ n, Module.Finite ℂ (End (tensorPow A X n))]
    (A₀ : ℝ)
    (hb : ∀ n, ((Module.finrank ℂ (End (tensorPow A X n)) : ℕ) : ℝ) ≤
      A₀ ^ n) (g : End X) {s : ℕ}
    (hs : 2 * Real.exp 1 * Real.sqrt A₀ < s) :
    ∃ Pp Qp : Polynomial ℂ,
      Pp.coeff 0 = 1 ∧ Qp.coeff 0 = 1 ∧
      Pp.natDegree ≤ s - 1 ∧ Qp.natDegree ≤ s - 1 ∧
      IsCoprime Pp Qp ∧
      traceZeta (fun m => scalarTrace hu X (g ^ m)) * ↑Qp =
        (↑Pp : PowerSeries ℂ) := by
  exact (objectFrobeniusTower hu X schurPackage.{v} A₀
    hb).traceZeta_rational_sharp g hs

/-- **The reduced super-spectrum form of Corollary A.2 for an object**: for
every integer `s > 2e√A₀` the power traces are a difference of power
sums of two disjoint multisets of nonzero complex numbers, each of
size at most `s − 1`. -/
theorem traceZeta_superSpectrum_of_object
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A)
    (X : A) [∀ n, Module.Finite ℂ (End (tensorPow A X n))]
    (A₀ : ℝ)
    (hb : ∀ n, ((Module.finrank ℂ (End (tensorPow A X n)) : ℕ) : ℝ) ≤
      A₀ ^ n) (g : End X) {s : ℕ}
    (hs : 2 * Real.exp 1 * Real.sqrt A₀ < s) :
    ∃ alpha beta : Multiset ℂ,
      alpha.card ≤ s - 1 ∧ beta.card ≤ s - 1 ∧
      (∀ x ∈ alpha, x ≠ 0) ∧ (∀ x ∈ beta, x ≠ 0) ∧
      (∀ x ∈ alpha, x ∉ beta) ∧
      ∀ m : ℕ, 1 ≤ m →
        scalarTrace hu X (g ^ m) =
          (alpha.map (· ^ m)).sum - (beta.map (· ^ m)).sum := by
  exact (objectFrobeniusTower hu X schurPackage.{v} A₀
    hb).traceZeta_superSpectrum_sharp g hs

end RS
