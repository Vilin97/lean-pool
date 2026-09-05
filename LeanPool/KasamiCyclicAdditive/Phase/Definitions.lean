/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Phase.CharacterSums

/-!
# Objects of the phase-to-root-count identity

Throughout, `K` is a finite field (in the application `K = GF(2^n)`), `ψ` is a
primitive additive character of `K` with values in `ℂ` (in the application
`ψ x = (-1)^(Tr x)`), and `D` is an exponent inverse to `m` modulo `N = #Kˣ`.
-/

open Finset

namespace KasamiCyclicAdditive.Phase

section Defs

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- `U = μ₃(K)`, the group of cube roots of unity of `K`, as a finset. -/
def cubeRootsOne : Finset K := {u : K | u ^ 3 = 1}

/-- `c = |μ₃(K)|`. -/
def mu3Card : ℕ := (cubeRootsOne K).card

end Defs

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- `Φ(x) = ∑_{u ∈ U} ψ(u x^D)`. -/
noncomputable def phi (ψ : AddChar K ℂ) (D : ℕ) (x : K) : ℂ := ∑ u ∈ cubeRootsOne K, ψ (u * x ^ D)

/-- The additive Fourier transform `Φ̂(z) = ∑_{t ∈ K} Φ(t) ψ(z t)`. -/
noncomputable def phiHat (ψ : AddChar K ℂ) (D : ℕ) (z : K) : ℂ := ∑ t : K, phi ψ D t * ψ (z * t)

/-- `W_{u,v} = ∑_{x,y ∈ K} ψ(u x^D + v (A x + B y)^D + y^D)`. -/
noncomputable def weilSum (ψ : AddChar K ℂ) (D : ℕ) (A B u v : K) : ℂ :=
  ∑ x : K, ∑ y : K, ψ (u * x ^ D + v * (A * x + B * y) ^ D + y ^ D)

/-- `R_{u,v}(A,B) = #{t ∈ K : u t^D + v (A t + B)^D = 1}`. -/
def rootCount (D : ℕ) (A B u v : K) : ℕ := #{t : K | u * t ^ D + v * (A * t + B) ^ D = 1}

/-- `Z(ρ) = ∑_{λ ∈ G} S(λ) S(ρ λ) S(σ λ)`. -/
noncomputable def phaseTripleSum (S : K → ℂ) (rho sigma : K) : ℂ :=
  ∑ lam : Kˣ, S (lam : K) * S (rho * (lam : K)) * S (sigma * (lam : K))

/-- The all-character Walsh formula
`2 S(a) = (Q/N) ∑_χ [G(χ^e)/G(χ^3)] χ(a)` for every `a ∈ Kˣ`, stated as a
property of `S` rather than assumed. -/
def WalshCharacterFormula (ψ : AddChar K ℂ) (e : ℕ) (S : K → ℂ) : Prop :=
  ∀ a : Kˣ, 2 * S (a : K) =
    (Fintype.card K : ℂ) / (Fintype.card Kˣ : ℂ) *
      ∑ χ : MulChar K ℂ, gaussSum (χ ^ e) ψ / gaussSum (χ ^ 3) ψ * χ (a : K)

end KasamiCyclicAdditive.Phase
