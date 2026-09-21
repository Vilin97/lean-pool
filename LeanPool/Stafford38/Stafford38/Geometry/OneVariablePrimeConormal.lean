/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ConstantCoordinateConormal
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# One-variable prime components and the conormal axis

The completed boundary chart is unavailable in one affine variable, but no
boundary argument is needed there.  A prime component of the affine line
whose zero set avoids the origin is nonzero.  Transporting it to the ordinary
polynomial ring makes it a nonzero prime in a PID, hence a maximal ideal.
Over an algebraically closed field it is therefore the ideal of one point
`c != 0`, and in particular contains `X - c`.

The final theorem feeds this component equation into the existing
constant-coordinate consumer and produces the exact Laurent conormal axis.
No projective chart, completion, Gabber input, or filtered cancellation is
used here.
-/

namespace Stafford38.Geometry.OneVariablePrimeConormal

open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ConstantCoordinateConormal
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

/-- The standard identification of a one-variable multivariate polynomial
ring with the ordinary polynomial ring. -/
private def finOnePolynomialEquiv (k : Type u) [Field k] :
    MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
  (MvPolynomial.renameEquiv k (Equiv.equivPUnit.{1, 1} (Fin 1))).trans
    (MvPolynomial.pUnitAlgEquiv.{u, 0} k)

/-- A prime component of the affine line whose entire zero set avoids the
origin is maximal.  Algebraic closedness is not needed for this PID step. -/
theorem primeComponent_isMaximal_of_axis_avoidance
    {k : Type u} [Field k]
    (P : Ideal (MvPolynomial (Fin 1) k)) [P.IsPrime]
    (havoid : ∀ y : Fin 1 → k,
      (∀ f ∈ P, MvPolynomial.eval y f = 0) → y 0 ≠ 0) :
    P.IsMaximal := by
  have hPne : P ≠ ⊥ := by
    intro hP
    have hzero : ∀ f ∈ P,
        MvPolynomial.eval (fun _ : Fin 1 ↦ (0 : k)) f = 0 := by
      intro f hf
      have hf0 : f = 0 := by
        rw [hP] at hf
        simpa using hf
      rw [hf0]
      simp
    exact (havoid (fun _ ↦ 0) hzero) rfl
  let e := finOnePolynomialEquiv k
  let Q : Ideal (Polynomial k) := Ideal.map e P
  letI : Q.IsPrime := by
    dsimp [Q]
    infer_instance
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hPne
    apply (Ideal.map_eq_bot_iff_of_injective e.injective).mp
    exact hQ
  have hQmax : Q.IsMaximal := IsPrime.to_maximal_ideal hQne
  exact (Ideal.isMaximal_map_iff_of_bijective e e.bijective).mp hQmax

/-- Componentwise one-variable production: axis avoidance forces the prime
component to be the ideal of a nonzero point and supplies its linear
coordinate equation. -/
theorem exists_coordinate_sub_constant_mem_of_prime_axis_avoidance
    {k : Type u} [Field k] [IsAlgClosed k]
    (P : Ideal (MvPolynomial (Fin 1) k)) [P.IsPrime]
    (havoid : ∀ y : Fin 1 → k,
      (∀ f ∈ P, MvPolynomial.eval y f = 0) → y 0 ≠ 0) :
    ∃ (c : k) (y : Fin 1 → k),
      c ≠ 0 ∧ y 0 = c ∧
      P = MvPolynomial.vanishingIdeal k {y} ∧
      MvPolynomial.X (0 : Fin 1) - MvPolynomial.C c ∈ P := by
  have hmax := primeComponent_isMaximal_of_axis_avoidance P havoid
  obtain ⟨y, hPy⟩ :=
    MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hmax
  let c : k := y 0
  have hy : ∀ f ∈ P, MvPolynomial.eval y f = 0 := by
    intro f hf
    rw [hPy] at hf
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff y f).mp hf
  have hc : c ≠ 0 := havoid y hy
  have hcoordinate :
      MvPolynomial.X (0 : Fin 1) - MvPolynomial.C c ∈ P := by
    rw [hPy, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp [c]
  exact ⟨c, y, hc, rfl, hPy, hcoordinate⟩

/-- Ambient-to-component form.  If `P` is a prime component above `I`, then
avoidance of the coordinate origin by `V(I)` also holds on `V(P)`, so the
linear equation is produced in the component ideal `P`. -/
theorem exists_coordinate_sub_constant_mem_of_primeComponent
    {k : Type u} [Field k] [IsAlgClosed k]
    (I P : Ideal (MvPolynomial (Fin 1) k)) [P.IsPrime]
    (hIP : I ≤ P)
    (havoid : ∀ y : Fin 1 → k,
      (∀ f ∈ I, MvPolynomial.eval y f = 0) → y 0 ≠ 0) :
    ∃ (c : k) (y : Fin 1 → k),
      c ≠ 0 ∧ y 0 = c ∧
      P = MvPolynomial.vanishingIdeal k {y} ∧
      MvPolynomial.X (0 : Fin 1) - MvPolynomial.C c ∈ P := by
  apply exists_coordinate_sub_constant_mem_of_prime_axis_avoidance P
  intro y hyP
  apply havoid y
  intro f hf
  exact hyP f (hIP hf)

/-- Direct rank-one replacement for the impossible boundary-chart branch.
The fibre residue is the unique pure coordinate axis. -/
theorem exists_laurentConormalAxis_of_prime_axis_avoidance
    {k : Type u} [Field k] [IsAlgClosed k]
    (P : Ideal (MvPolynomial (Fin 1) k)) [P.IsPrime]
    (havoid : ∀ y : Fin 1 → k,
      (∀ f ∈ P, MvPolynomial.eval y f = 0) → y 0 ≠ 0) :
    ∃ (yL : Fin 1 → LaurentSeries k)
      (xi : Fin 1 → PowerSeries k),
      Sum.elim yL
          (fun j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi j)) ∈
        equationConormalLocus
          (P.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin 1))) ∧
      residueColumn xi = (fun _ : Fin 1 ↦ 1) := by
  obtain ⟨c, y, _hc, _hyc, hPy, hcoordinate⟩ :=
    exists_coordinate_sub_constant_mem_of_prime_axis_avoidance P havoid
  have hy : ∀ f ∈ P, MvPolynomial.eval y f = 0 := by
    intro f hf
    rw [hPy] at hf
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff y f).mp hf
  obtain ⟨yL, xi, hphase, hresidue⟩ :=
    exists_laurentConormalAxis_of_coordinate_sub_constant_mem
      P y hy (0 : Fin 1) c hcoordinate
  refine ⟨yL, xi, hphase, ?_⟩
  rw [hresidue]
  funext j
  fin_cases j
  simp


end

end Stafford38.Geometry.OneVariablePrimeConormal
