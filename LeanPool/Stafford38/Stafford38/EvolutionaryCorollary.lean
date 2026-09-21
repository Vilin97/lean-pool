/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.EvolutionaryCertificate
import LeanPool.Stafford38.Stafford38.EulerRootSeparation
import LeanPool.Stafford38.Stafford38.Weyl.IteratedEquivalence

/-!
# Evolutionary Stafford corollary

This file combines the algebraic certificate with Euler-root separation. It
contains only the unconditional ring-theoretic corollary needed by the paper.
-/

namespace Stafford38.Evolution

open scoped TensorProduct
open Stafford38.WeylIteratedEquivalence

variable {D : Type*} [Ring D] {x p : D}

/-- For a Weyl pair and a finite polynomial potential whose coefficients
commute separately with both generators, the two displayed right multiples
give a Stafford certificate with fixed left source `x ^ r`. -/
theorem evolution_stafford (k : Type*) [Field k] [CharZero k] [Algebra k D]
    (hw : p * x = x * p + 1) {r : ℕ} (hr : 0 < r) (terms : List (D × ℕ))
    (hx : ∀ t ∈ terms, t.1 * x = x * t.1)
    (hp : ∀ t ∈ terms, t.1 * p = p * t.1) :
    ∃ R S : D, (p ^ r - potentialSum x terms) * R
        + x ^ r * (p ^ r - potentialSum x terms) * S = 1 := by
  obtain ⟨α, β, hαβ⟩ := exists_bezout (k := k) (D := D) hr terms
  exact evolution_stafford_certificate hw r terms hx hp α β hαβ

/-- Exact paper-facing form. No commutativity among the coefficients is
assumed: each displayed coefficient need only commute with `x` and `p`. -/
theorem evolutionaryCorollary (k : Type*) [Field k] [CharZero k] [Algebra k D]
    (hw : p * x = x * p + 1) {r : ℕ} (hr : 0 < r) (terms : List (D × ℕ))
    (hx : ∀ t ∈ terms, t.1 * x = x * t.1)
    (hp : ∀ t ∈ terms, t.1 * p = p * t.1)
    {d : D} (hd : d = p ^ r - potentialSum x terms) :
    ∃ R S : D, 1 = d * R + x ^ r * d * S := by
  obtain ⟨R, S, h⟩ := evolution_stafford k hw hr terms hx hp
  exact ⟨R, S, by simpa [hd] using h.symm⟩

section TensorProduct

variable (k B : Type*) [Field k] [CharZero k] [Ring B] [Algebra k B]

local notation "W₁" => PresentedWeyl k 1
local notation "Dᵣ" => B ⊗[k] W₁
local notation "ιB" => (Algebra.TensorProduct.includeLeft : B →ₐ[k] Dᵣ)
local notation "ιW" => (Algebra.TensorProduct.includeRight : W₁ →ₐ[k] Dᵣ)

/-- The evolutionary certificate in the literal tensor algebra
`B ⊗[k] A₁(k)`. This asserts no identification with a geometric ring of
differential operators. -/
theorem tensorEvolutionaryCorollary {r : ℕ} (hr : 0 < r)
    (terms : List (B × ℕ)) {d : Dᵣ}
    (hd : d = ιW (presentedMomentum k 0) ^ r -
      potentialSum (ιW (presentedCoordinate k 0))
        (terms.map fun t => (ιB t.1, t.2))) :
    ∃ R S : Dᵣ, 1 = d * R + ιW (presentedCoordinate k 0) ^ r * d * S := by
  let lifted : List (Dᵣ × ℕ) := terms.map fun t => (ιB t.1, t.2)
  have hcomm : ∀ (b : B) (w : W₁), ιB b * ιW w = ιW w * ιB b := by
    intro b w
    simp [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
  have hx : ∀ t ∈ lifted,
      t.1 * ιW (presentedCoordinate k 0) =
        ιW (presentedCoordinate k 0) * t.1 := by
    rintro t ht
    rcases List.mem_map.mp ht with ⟨⟨b, n⟩, _, rfl⟩
    exact hcomm b (presentedCoordinate k 0)
  have hp : ∀ t ∈ lifted,
      t.1 * ιW (presentedMomentum k 0) =
        ιW (presentedMomentum k 0) * t.1 := by
    rintro t ht
    rcases List.mem_map.mp ht with ⟨⟨b, n⟩, _, rfl⟩
    exact hcomm b (presentedMomentum k 0)
  have hw : ιW (presentedMomentum k 0) * ιW (presentedCoordinate k 0) =
      ιW (presentedCoordinate k 0) * ιW (presentedMomentum k 0) + 1 := by
    calc
      _ = ιW (presentedMomentum k 0 * presentedCoordinate k 0) :=
        (map_mul ιW _ _).symm
      _ = ιW (presentedCoordinate k 0 * presentedMomentum k 0 + 1) :=
        congrArg ιW (presentedMomentum_mul_coordinate k 0)
      _ = _ := by rw [map_add, map_mul, map_one]
  exact evolutionaryCorollary
    (D := Dᵣ) (x := ιW (presentedCoordinate k 0))
    (p := ιW (presentedMomentum k 0)) k hw hr lifted hx hp hd

end TensorProduct

end Stafford38.Evolution
