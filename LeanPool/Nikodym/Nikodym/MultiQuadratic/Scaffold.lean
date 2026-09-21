/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Construction.Scaffold
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Norm
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Legendre

/-!
# Scaffold instance for the multiquadratic order

Blueprint node K06 of `docs/nikodym_construction_lean_blueprint.md`.

Under the standing hypotheses of K01 (`hr1`, `hsq`, `hcop`) and a choice of square roots
`sⱼ² = rⱼ` in a prime-cardinality field `F` (L02), the monomial basis, sign embeddings and
reduction map form a `Nikodym.Scaffold` with `K₀ = ∏ⱼ rⱼ` and `K₁ = 1`. The basis bound is
monotone in `K₀`, so the same data is a scaffold with the larger constant `∏ⱼ ℓⱼ ℓ'ⱼ` whenever
`rⱼ ∣ ℓⱼ ℓ'ⱼ`.
-/

namespace Nikodym

open Finset

/-- Blueprint K06: the basis bound is monotone in `K₀`. Only `basis_bound` mentions `K₀`. -/
theorem Scaffold.mono_K₀ {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F]
    [Fintype F] {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ K₀' : ℝ}
    (h : Scaffold b σ φ K₀ K₁) (hle : K₀ ≤ K₀') : Scaffold b σ φ K₀' K₁ where
  card_eq := h.card_eq
  basis_bound := fun i k ↦ (h.basis_bound i k).trans hle
  coord_bound := h.coord_bound
  trace_int := h.trace_int
  small_ker := h.small_ker

end Nikodym

namespace Nikodym.MultiQuad

noncomputable section

open Finset

variable {m : ℕ} {r : Fin m → ℕ}

/-- Blueprint K06: the number of sign embeddings is `2 ^ m`. -/
theorem rank_eq : Fintype.card (Fin m → ℤˣ) = 2 ^ m := by
  rw [Fintype.card_fun, Fintype.card_units_int, Fintype.card_fin]

/-- Blueprint K06: the monomials, sign embeddings and reduction map form a scaffold with
`K₀ = ∏ⱼ rⱼ` and `K₁ = 1`. -/
theorem scaffold (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k))
    {F : Type*} [Field F] [Fintype F] (hp : (Fintype.card F).Prime)
    (s : Fin m → F) (hs : ∀ j, s j ^ 2 = (r j : F)) :
    Nikodym.Scaffold (monoBasis hr1 hsq hcop) (fun ε : Fin m → ℤˣ ↦ emb r ε) (reduce r s hs)
      (∏ j, (r j : ℝ)) 1 where
  card_eq := by
    rw [rank_eq, Fintype.card_finset, Fintype.card_fin]
  basis_bound := fun ε S ↦ by
    rw [monoBasis_apply]
    exact abs_emb_mono_le hr1 ε S
  coord_bound := fun x T hx S ↦ by
    rw [one_mul]
    exact abs_repr_le hr1 hsq hcop hx S
  trace_int := exists_int_sum_emb hr1 hsq hcop
  small_ker := fun x hx hsmall ↦
    eq_zero_of_map_eq_zero hr1 hsq hcop hp (reduce r s hs) hx hsmall

/-- Blueprint K06: if `rⱼ ∣ ℓⱼ ℓ'ⱼ` for all `j`, the same data is a scaffold with the uniform
constant `K₀ = ∏ⱼ ℓⱼ ℓ'ⱼ`. -/
theorem scaffold_of_dvd (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k))
    {F : Type*} [Field F] [Fintype F] (hp : (Fintype.card F).Prime)
    (s : Fin m → F) (hs : ∀ j, s j ^ 2 = (r j : F))
    (ℓ ℓ' : Fin m → ℕ) (hdvd : ∀ j, r j ∣ ℓ j * ℓ' j) (hℓ : ∀ j, 0 < ℓ j * ℓ' j) :
    Nikodym.Scaffold (monoBasis hr1 hsq hcop) (fun ε : Fin m → ℤˣ ↦ emb r ε) (reduce r s hs)
      (∏ j, ((ℓ j * ℓ' j : ℕ) : ℝ)) 1 := by
  refine Nikodym.Scaffold.mono_K₀ (scaffold hr1 hsq hcop hp s hs) ?_
  refine prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _) fun j _ ↦ ?_
  exact_mod_cast Nat.le_of_dvd (hℓ j) (hdvd j)

end

end Nikodym.MultiQuad

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
