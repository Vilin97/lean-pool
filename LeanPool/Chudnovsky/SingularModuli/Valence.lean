/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.JFunction
import LeanPool.Chudnovsky.Fourier
import LeanPool.Chudnovsky.DivisionValues
import Mathlib.NumberTheory.Modular
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Complex.OpenMapping
import LeanPool.Chudnovsky.Estimates

/-!
# Valence theory of the `j`-function (Phase C, Track 2, §4.3)

This file develops the *valence theory* of the modular `j`-invariant that the Rationality
track (`Rationality.lean`, statement 2 of `SingularModuli.lean`) consumes: **injectivity
mod `Γ`** and **surjectivity**. See `Playground/Pi/PhaseC-PLAN.md`, §4.2 (the three-prime
argument, input `(C3)`) and §4.3 (this sub-plan). The Isabelle/AFP "Complex Lattices,
Elliptic Functions, and the Modular Group" development is the design blueprint (§1).

## What is proved here (sorry-free)

* **Fundamental-domain reduction** `exists_smul_mem_fd_j`: every `τ` is `SL(2,ℤ)`-equivalent
  to a point of the closed fundamental domain `𝒟`, with equal `j`-value (a thin wrapper of
  Mathlib's `ModularGroup.exists_smul_mem_fd` and `j_smul`).
* **Lattice reformulation** `j_eq_iff_J`, `j_eq_iff_periodPair_J`: `j τ₁ = j τ₂` iff Klein's
  invariants of the lattices `L_{τ₁}`, `L_{τ₂}` agree (via `Fourier.J_eq_J_Lτ`).
* **The weighted-projective identity** `E₄E₆_proj_eq_of_j_eq` / `g₂g₃_proj_eq_of_j_eq`:
  `j τ₁ = j τ₂ ⇒ E₄(τ₁)³·E₆(τ₂)² = E₄(τ₂)³·E₆(τ₁)²`, equivalently
  `g₂(L₁)³·g₃(L₂)² = g₂(L₂)³·g₃(L₁)²` — the `(g₂³ : g₃²)` proportionality of §4.3.
* **Lattice-rigidity step 1** `exists_units_smul_g₂_g₃`: for two lattices with `L₁.J = L₂.J`
  (and nonzero discriminants) there is a homothety `a : ℂˣ` with
  `g₂(a·L₂) = g₂(L₁)` and `g₃(a·L₂) = g₃(L₁)`. This is the "there is `λ ∈ ℂˣ` with
  `g₂(λ L_{τ′}) = g₂(L_τ)`, `g₃(λ L_{τ′}) = g₃(L_τ)`" of §4.3, done in full (the 4th/6th-root
  bookkeeping). It reduces injectivity to the lattice-recovery core (see TODO below).
* **Gated injectivity** `j_injective_mod_Γ_of_lattice_core`: injectivity mod `Γ` follows from
  the isolated lattice-recovery core (equal `(g₂,g₃)` of homothetic lattices ⇒ the base points
  are `Γ`-equivalent).
* **The lattice-recovery core**, discharged in full (see the section "The lattice-recovery
  core, discharged"): `PeriodPair.weierstrassP_eventuallyEq_of_g₂_g₃` (equal `(g₂,g₃)` ⇒ equal
  `℘` near `0`, via the Eisenstein-coefficient recursion extracted from the ODE
  `℘'' = 6℘² − g₂/2` of `DivisionValues.lean`),
  `PeriodPair.lattice_eq_of_weierstrassP_eventuallyEq` (identity theorem + pole-set
  comparison ⇒ equal lattices), `exists_sl2_of_lattice_eq` (equal lattices ⇒ `Γ`-related base
  points), combined in `lattice_recovery_core`.
* **Injectivity mod `Γ`, unconditional** `j_injective_mod_Γ`:
  `j τ₁ = j τ₂ → ∃ γ : SL(2,ℤ), τ₂ = γ • τ₁`.
* **Surjectivity, unconditional** `j_surjective`: `Function.Surjective (j : ℍ → ℂ)`. Proved by
  the open-and-closed argument of §4.3 (`isOpen_range_j` via the open mapping theorem for the
  nonconstant holomorphic `j`, `isClosed_range_j` via the cusp estimate + compactness of a
  truncation of the fundamental domain, assembled with `IsClopen.eq_univ` on the preconnected
  `ℂ`). See the "Surjectivity" section.

Both halves of the §4.3 valence theory (`j_injective_mod_Γ` and `j_surjective`) are now
`sorry`-free.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries
open scoped Real Manifold MatrixGroups Modular Topology

/-! ## Fundamental-domain reduction -/

/-- Every `τ : ℍ` is `SL(2,ℤ)`-equivalent to a point of the closed fundamental domain `𝒟`,
and `j` is constant along this move. Wrapper of `ModularGroup.exists_smul_mem_fd` and
`j_smul`; used by the surjectivity argument (move a would-be limit point into `𝒟`). -/
theorem exists_smul_mem_fd_j (τ : ℍ) :
    ∃ γ : SL(2, ℤ), γ • τ ∈ ModularGroup.fd ∧ j (γ • τ) = j τ := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  exact ⟨γ, hγ, j_smul γ τ⟩

/-! ## Lattice reformulation of `j`-equality -/

/-- `j τ₁ = j τ₂ ↔ J τ₁ = J τ₂` (the factor `1728` is a unit). -/
theorem j_eq_iff_J (τ₁ τ₂ : ℍ) : j τ₁ = j τ₂ ↔ J τ₁ = J τ₂ := by
  rw [j_def, j_def]
  constructor
  · exact fun h ↦ mul_left_cancel₀ (by norm_num : (1728 : ℂ) ≠ 0) h
  · exact fun h ↦ by rw [h]

/-- `j τ₁ = j τ₂` iff Klein's absolute invariants of the lattices `L_{τ₁}`, `L_{τ₂}` agree.
This is the entry point for the lattice-rigidity route to injectivity (§4.3). -/
theorem j_eq_iff_periodPair_J (τ₁ τ₂ : ℍ) : j τ₁ = j τ₂ ↔ (Lτ τ₁).J = (Lτ τ₂).J := by
  rw [j_eq_iff_J, J_eq_J_Lτ, J_eq_J_Lτ]

/-! ## The weighted-projective `(g₂³ : g₃²)` identity -/

/-- `j τ₁ = j τ₂ ⇒ E₄(τ₁)³·E₆(τ₂)² = E₄(τ₂)³·E₆(τ₁)²`. Cross-multiplying `J τ₁ = J τ₂`
kills the `E₄³·E₄³` terms and leaves the weighted-projective equality of §4.3. -/
theorem E₄E₆_proj_eq_of_j_eq {τ₁ τ₂ : ℍ} (h : j τ₁ = j τ₂) :
    E₄ τ₁ ^ 3 * E₆ τ₂ ^ 2 = E₄ τ₂ ^ 3 * E₆ τ₁ ^ 2 := by
  rw [j_eq_iff_J, J, J,
    div_eq_div_iff (E₄_cube_sub_E₆_sq_ne_zero τ₁) (E₄_cube_sub_E₆_sq_ne_zero τ₂)] at h
  linear_combination -h

/-- The lattice form of `E₄E₆_proj_eq_of_j_eq`: `g₂(L₁)³·g₃(L₂)² = g₂(L₂)³·g₃(L₁)²`. -/
theorem g₂g₃_proj_eq_of_j_eq {τ₁ τ₂ : ℍ} (h : j τ₁ = j τ₂) :
    (Lτ τ₁).g₂ ^ 3 * (Lτ τ₂).g₃ ^ 2 = (Lτ τ₂).g₂ ^ 3 * (Lτ τ₁).g₃ ^ 2 := by
  have hE := E₄E₆_proj_eq_of_j_eq h
  simp only [g₂_Lτ, g₃_Lτ]
  linear_combination
    (4 / 3 * (π : ℂ) ^ 4) ^ 3 * (8 / 27 * (π : ℂ) ^ 6) ^ 2 * hE

/-! ## Lattice rigidity, step 1: matching `g₂` and `g₃` by a homothety

`§4.3`: from `J(L₁) = J(L₂)` there is a scaling `a ∈ ℂˣ` with `g₂(a·L₂) = g₂(L₁)` and
`g₃(a·L₂) = g₃(L₁)`. Proof: `J`-equality gives the projective relation
`g₂(L₁)³ g₃(L₂)² = g₂(L₂)³ g₃(L₁)²`; then a case split on which of `g₂`, `g₃` vanish, with the
4th/6th-root of unity juggling handled by a square/6th/4th root in `ℂ` (`ℂ` algebraically
closed). -/

/-- The auxiliary projective relation extracted from `L₁.J = L₂.J` (both discriminants `≠ 0`):
`g₂(L₁)³·g₃(L₂)² = g₂(L₂)³·g₃(L₁)²`. -/
theorem g₂cube_g₃sq_eq_of_periodPair_J {L₁ L₂ : PeriodPair}
    (hd₁ : L₁.discr ≠ 0) (hd₂ : L₂.discr ≠ 0) (hJ : L₁.J = L₂.J) :
    L₁.g₂ ^ 3 * L₂.g₃ ^ 2 = L₂.g₂ ^ 3 * L₁.g₃ ^ 2 := by
  rw [PeriodPair.J, PeriodPair.J, div_eq_div_iff hd₁ hd₂] at hJ
  simp only [PeriodPair.discr] at hJ
  linear_combination (-1 / 27 : ℂ) * hJ

/-- **Lattice-rigidity step 1** (§4.3). If two lattices have the same Klein invariant (with
nonzero discriminants) then there is a homothety `a : ℂˣ` scaling `L₂` so that its `g₂` and
`g₃` match those of `L₁`. -/
theorem exists_units_smul_g₂_g₃ (L₁ L₂ : PeriodPair)
    (hd₁ : L₁.discr ≠ 0) (hd₂ : L₂.discr ≠ 0) (hJ : L₁.J = L₂.J) :
    ∃ a : ℂˣ, (a • L₂).g₂ = L₁.g₂ ∧ (a • L₂).g₃ = L₁.g₃ := by
  have hR : L₁.g₂ ^ 3 * L₂.g₃ ^ 2 = L₂.g₂ ^ 3 * L₁.g₃ ^ 2 :=
    g₂cube_g₃sq_eq_of_periodPair_J hd₁ hd₂ hJ
  -- Package: from a nonzero `α` with the two inverse-power identities, build the unit.
  suffices h : ∃ α : ℂ, α ≠ 0 ∧ (α ^ 4)⁻¹ * L₂.g₂ = L₁.g₂ ∧ (α ^ 6)⁻¹ * L₂.g₃ = L₁.g₃ by
    obtain ⟨α, hα, h2, h3⟩ := h
    refine ⟨Units.mk0 α hα, ?_, ?_⟩
    · rw [PeriodPair.g₂_smul]; simpa using h2
    · rw [PeriodPair.g₃_smul]; simpa using h3
  by_cases ha2 : L₁.g₂ = 0
  · -- `J₁ = 0`, so `L₂.g₂ = 0`; match the `g₃`'s by a 6th root.
    have ha3 : L₁.g₃ ≠ 0 := fun h ↦ hd₁ (by simp [PeriodPair.discr, ha2, h])
    have hb2 : L₂.g₂ = 0 := by
      have hz : L₂.g₂ ^ 3 * L₁.g₃ ^ 2 = 0 := by rw [← hR, ha2]; ring
      have : L₂.g₂ ^ 3 = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact h
        · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ha3
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hb3 : L₂.g₃ ≠ 0 := fun h ↦ hd₂ (by simp [PeriodPair.discr, hb2, h])
    obtain ⟨α, hα6⟩ := IsAlgClosed.exists_pow_nat_eq (L₂.g₃ / L₁.g₃) (n := 6) (by norm_num)
    have hαne : α ≠ 0 := by
      rintro rfl; rw [zero_pow (by norm_num)] at hα6
      exact (div_ne_zero hb3 ha3) hα6.symm
    refine ⟨α, hαne, ?_, ?_⟩
    · rw [ha2, hb2]; ring
    · rw [hα6, inv_div, div_mul_cancel₀ _ hb3]
  · by_cases ha3 : L₁.g₃ = 0
    · -- `J₁ = 1`, so `L₂.g₃ = 0`; match the `g₂`'s by a 4th root.
      have hb3 : L₂.g₃ = 0 := by
        have hz : L₁.g₂ ^ 3 * L₂.g₃ ^ 2 = 0 := by rw [hR, ha3]; ring
        have : L₂.g₃ ^ 2 = 0 := by
          rcases mul_eq_zero.mp hz with h | h
          · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ha2
          · exact h
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hb2 : L₂.g₂ ≠ 0 := fun h ↦ hd₂ (by simp [PeriodPair.discr, h, hb3])
      obtain ⟨α, hα4⟩ := IsAlgClosed.exists_pow_nat_eq (L₂.g₂ / L₁.g₂) (n := 4) (by norm_num)
      have hαne : α ≠ 0 := by
        rintro rfl; rw [zero_pow (by norm_num)] at hα4
        exact (div_ne_zero hb2 ha2) hα4.symm
      refine ⟨α, hαne, ?_, ?_⟩
      · rw [hα4, inv_div, div_mul_cancel₀ _ hb2]
      · rw [ha3, hb3]; ring
    · -- Generic case: all four of `g₂ᵢ, g₃ᵢ` nonzero.
      have hb2 : L₂.g₂ ≠ 0 := by
        intro h
        have hb3z : L₂.g₃ = 0 := by
          have hz : L₁.g₂ ^ 3 * L₂.g₃ ^ 2 = 0 := by rw [hR, h]; ring
          have : L₂.g₃ ^ 2 = 0 := by
            rcases mul_eq_zero.mp hz with h' | h'
            · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h') ha2
            · exact h'
          exact pow_eq_zero_iff (by norm_num) |>.mp this
        exact hd₂ (by simp [PeriodPair.discr, h, hb3z])
      have hb3 : L₂.g₃ ≠ 0 := by
        intro h
        have hz : L₂.g₂ ^ 3 * L₁.g₃ ^ 2 = 0 := by rw [← hR, h]; ring
        have : L₂.g₂ ^ 3 = 0 := by
          rcases mul_eq_zero.mp hz with h' | h'
          · exact h'
          · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h') ha3
        exact hb2 (pow_eq_zero_iff (by norm_num) |>.mp this)
      -- `u = g₂₂/g₂₁`, `v = g₃₂/g₃₁`, and `u³ = v²`; pick `α` with `α² = v/u`.
      have hcube : (L₂.g₂ / L₁.g₂) ^ 3 = (L₂.g₃ / L₁.g₃) ^ 2 := by
        field_simp
        linear_combination -hR
      obtain ⟨α, hα2⟩ :=
        IsAlgClosed.exists_pow_nat_eq ((L₂.g₃ / L₁.g₃) / (L₂.g₂ / L₁.g₂)) (n := 2) (by norm_num)
      have hu : L₂.g₂ / L₁.g₂ ≠ 0 := div_ne_zero hb2 ha2
      have hv : L₂.g₃ / L₁.g₃ ≠ 0 := div_ne_zero hb3 ha3
      have hαne : α ≠ 0 := by
        rintro rfl; rw [zero_pow (by norm_num)] at hα2
        exact (div_ne_zero hv hu) hα2.symm
      -- `α⁴ = (v/u)² = u`  and  `α⁶ = (v/u)³ = v`.
      have h4 : α ^ 4 = L₂.g₂ / L₁.g₂ := by
        have : α ^ 4 = (α ^ 2) ^ 2 := by ring
        rw [this, hα2, div_pow, ← hcube]
        field_simp
      have h6 : α ^ 6 = L₂.g₃ / L₁.g₃ := by
        have : α ^ 6 = (α ^ 2) ^ 3 := by ring
        rw [this, hα2, div_pow, hcube]
        field_simp
      refine ⟨α, hαne, ?_, ?_⟩
      · rw [h4, inv_div, div_mul_cancel₀ _ hb2]
      · rw [h6, inv_div, div_mul_cancel₀ _ hb3]

/-! ## Injectivity mod `Γ` -/

/-- `(Lτ τ).discr ≠ 0` (the discriminant of the lattice `ℤ + ℤτ` is nonzero). -/
theorem discr_Lτ_ne_zero (τ : ℍ) : (Lτ τ).discr ≠ 0 := by
  rw [discr_Lτ]
  refine mul_ne_zero ?_ (E₄_cube_sub_E₆_sq_ne_zero τ)
  refine div_ne_zero (pow_ne_zero _ ?_) (by norm_num)
  simp [Real.pi_ne_zero]

/-
[DISCHARGED — see the section "The lattice-recovery core, discharged" below, which proves
`lattice_recovery_core` and the unconditional `j_injective_mod_Γ`. The route described here
is the one carried out.]

TODO (§4.3, the lattice-recovery core — the deep, multi-week remainder of injectivity).

The hypothesis `lattice_core` below packages the entire remaining content:
given a homothety `a` with `g₂(a·L_{τ₂}) = g₂(L_{τ₁})` and `g₃(a·L_{τ₂}) = g₃(L_{τ₁})`,
the base points `τ₁, τ₂` are `Γ`-equivalent. Route to discharge it (§4.3):

  1. **Equal `(g₂, g₃)` ⇒ equal `℘`.** The Laurent coefficients of `℘` at `0` are universal
     polynomials in `g₂, g₃` (Mathlib: `PeriodPair.weierstrassPSeries` /
     `coeff_weierstrassPSeries`, the `G`-recursion). Hence `℘_{a·L₂}` and `℘_{L₁}` have equal
     power series at `0`, so agree on a neighbourhood of `0`.
  2. **Agree everywhere ⇒ equal pole sets.** By the identity theorem
     (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) on the connected set
     `ℂ ∖ (lattice₁ ∪ lattice₂)` (complement of two countable sets), `℘_{a·L₂} = ℘_{L₁}`
     wherever both are defined; the pole set of `℘_L` is exactly `L`, so `a·L₂ = L₁` as
     lattices.
  3. **Equal lattice ⇒ `Γ`-related points.** `a·(ℤ + ℤτ₂) = ℤ + ℤτ₁` means the two bases are
     related by `GL(2,ℤ)`; `Im τᵢ > 0` forces `det = 1`, i.e. `τ₂ = γ • τ₁` with
     `γ ∈ SL(2,ℤ)`.

Mathlib assets: `PeriodPair.weierstrassPSeries`, `PeriodPair.weierstrassP`,
`weierstrassP_smul` (project `Lattices.lean`), the identity theorem, and the
`ModularGroup` action API. This is the fiddly half of §4.3 (Isabelle/AFP has the analogue).
-/

/-- **Injectivity mod `Γ`, gated on the lattice-recovery core.** Once the core (equal `(g₂,g₃)`
of homothetic lattices ⇒ base points `Γ`-equivalent — see the `TODO` above for its route) is
available, `j τ₁ = j τ₂` forces `τ₂ = γ • τ₁` for some `γ ∈ SL(2,ℤ)`. The scaling `a` is
produced here in full by `exists_units_smul_g₂_g₃`. -/
theorem j_injective_mod_Γ_of_lattice_core
    (lattice_core : ∀ (σ₁ σ₂ : ℍ) (a : ℂˣ),
      (a • Lτ σ₂).g₂ = (Lτ σ₁).g₂ → (a • Lτ σ₂).g₃ = (Lτ σ₁).g₃ →
        ∃ γ : SL(2, ℤ), σ₂ = γ • σ₁)
    {τ₁ τ₂ : ℍ} (h : j τ₁ = j τ₂) :
    ∃ γ : SL(2, ℤ), τ₂ = γ • τ₁ := by
  have hJ : (Lτ τ₁).J = (Lτ τ₂).J := (j_eq_iff_periodPair_J τ₁ τ₂).mp h
  obtain ⟨a, hg₂, hg₃⟩ :=
    exists_units_smul_g₂_g₃ (Lτ τ₁) (Lτ τ₂) (discr_Lτ_ne_zero τ₁) (discr_Lτ_ne_zero τ₂) hJ
  exact lattice_core τ₁ τ₂ a hg₂ hg₃

/-! ## The lattice-recovery core, discharged

The `TODO` route above is now carried out in full:

1. **Equal `(g₂, g₃)` ⇒ equal `℘` near `0`** (`PeriodPair.weierstrassP_eventuallyEq_of_g₂_g₃`):
   the analytic part `h := ℘ − z⁻²` of `℘` at `0` satisfies (from the project's second-order
   ODE `℘'' = 6℘² − g₂/2`, `PeriodPair.lemwp2str`) the classical Eisenstein-coefficient
   recursion; by strong induction all Taylor coefficients of `h` at `0` are universal
   polynomials in `(g₂, g₃)`, so the two `℘`'s agree on a punctured neighbourhood of `0`.
2. **Equal near `0` ⇒ equal lattices** (`PeriodPair.lattice_eq_of_weierstrassP_eventuallyEq`):
   by the identity theorem on the connected set `ℂ ∖ (L₁ ∪ L₂)` (complement of a countable
   set), `℘₁ = ℘₂` wherever both are defined; a lattice point of `L₁` not in `L₂` would be a
   double pole of `℘₁` (`PeriodPair.order_weierstrassP`) at which `℘₂` is analytic
   (meromorphic order `≥ 0`) — contradiction, since meromorphic order only depends on the
   germ on the punctured neighbourhood.
3. **Equal lattices ⇒ `Γ`-related base points** (`exists_sl2_of_lattice_eq`): the two bases
   `(1, τ₁)` and `(a, a·τ₂)` of the common lattice are related by an integer matrix in each
   direction; the imaginary-part identity `det·Im τ₁ = |a|²·Im τ₂` (and its inverse-homothety
   mirror) forces both determinants positive with product `1`, hence `det = 1`, and the
   Möbius formula gives `τ₂ = γ • τ₁` with `γ ∈ SL(2, ℤ)`.

Combining the three yields `lattice_recovery_core`, and with
`j_injective_mod_Γ_of_lattice_core` the unconditional injectivity `j_injective_mod_Γ`. -/

open Filter Metric
open scoped Topology

namespace PeriodPair

/-- The lattice of a `PeriodPair` is countable (it is an image of `ℤ × ℤ`). -/
lemma lattice_countable (L : PeriodPair) : (↑L.lattice : Set ℂ).Countable := by
  have : Countable L.lattice := Countable.of_equiv (ℤ × ℤ) (L.latticeEquivProd.toEquiv.symm)
  exact Set.countable_coe_iff.mp this

attribute [local fun_prop] AnalyticAt.contDiffAt

/-- `iteratedDeriv` of `z ↦ z² · f z` at `0`: only the `i = 2` Leibniz term survives. -/
lemma iteratedDeriv_sq_mul (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (m : ℕ) :
    iteratedDeriv m (fun z => z ^ 2 * f z) 0
      = ((m : ℂ) * ((m : ℂ) - 1)) * iteratedDeriv (m - 2) f 0 := by
  have hcd2 : ContDiffAt ℂ (m : WithTop ℕ∞) (fun z : ℂ => z ^ 2) 0 := by fun_prop
  rw [iteratedDeriv_fun_mul hcd2 hf.contDiffAt]
  have hstep : ∀ i ∈ Finset.range (m + 1),
      (↑(m.choose i) : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ 2) 0 * iteratedDeriv (m - i) f 0
        = if i = 2 then (↑(m.choose 2) : ℂ) * 2 * iteratedDeriv (m - 2) f 0 else 0 := by
    intro i hi
    simp only [iteratedDeriv_fun_pow_zero]
    by_cases h : i = 2
    · subst h; norm_num
    · simp [h]
  rw [Finset.sum_congr rfl hstep,
      Finset.sum_ite_eq' (Finset.range (m + 1)) 2
        (fun _ => (↑(m.choose 2) : ℂ) * 2 * iteratedDeriv (m - 2) f 0)]
  by_cases hm2 : 2 ∈ Finset.range (m + 1)
  · rw [if_pos hm2, Nat.cast_choose_two]; ring
  · rw [if_neg hm2]
    have hlt : m < 2 := by simpa [Finset.mem_range] using hm2
    interval_cases m <;> simp

/-- `iteratedDeriv (m+2) f = iteratedDeriv m (iteratedDeriv 2 f)`. -/
lemma iteratedDeriv_add_two (m : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv (m + 2) f = iteratedDeriv m (iteratedDeriv 2 f) := by
  have h2f : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2f, show m + 2 = (m + 1) + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_succ']

/-- **Step 1 of the lattice-recovery core**: two period pairs with equal `g₂` and `g₃` have
equal `℘` on a punctured neighbourhood of `0`.

Proof: let `w := ℘₁Except − ℘₂Except` be the difference of the analytic parts at `0`. The
second-order ODE `℘'' = 6℘² − g₂/2` (`PeriodPair.lemwp2str`, from `DivisionValues.lean`)
turns — after the shared `g₂`-terms cancel — into the *linear* relation
`z²·w'' = z²·6·w·(h₁+h₂) + 12·w` near `0`. Taking `m`-th Taylor coefficients at `0` yields
the classical Eisenstein recursion with coefficient `m(m−1) − 12 = (m−4)(m+3)`; strong
induction (with the resonances `m = 0, 1, 4` handled by `g₂ = g₂`, `G₃ = G₅ = 0`, and
`g₃ = g₃`) kills every Taylor coefficient of `w`, so `w ≡ 0` near `0`. -/
theorem weierstrassP_eventuallyEq_of_g₂_g₃ (L₁ L₂ : PeriodPair)
    (h2 : L₁.g₂ = L₂.g₂) (h3 : L₁.g₃ = L₂.g₃) :
    L₁.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] L₂.weierstrassP := by
  -- `℘Except 0 = ℘ − 1/z²`
  have hPexc : ∀ (L : PeriodPair) (t : ℂ),
      L.weierstrassPExcept 0 t = L.weierstrassP t - 1 / t ^ 2 := by
    intro L t
    have h := L.weierstrassPExcept_add (0 : L.lattice) t
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    have h0 : (1 : ℂ) / (0 : ℂ) ^ 2 = 0 := by norm_num
    rw [h0, sub_zero] at h
    linear_combination h
  -- `HasDerivAt` facts, reconstructed from the analyticity lemmas
  have hDP : ∀ {L : PeriodPair} {z : ℂ}, z ∉ L.lattice →
      HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    intro L z hz
    have h := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
    rwa [congrFun L.deriv_weierstrassP z] at h
  have hDP' : ∀ {L : PeriodPair} {z : ℂ}, z ∉ L.lattice →
      HasDerivAt L.derivWeierstrassP (deriv L.derivWeierstrassP z) z := by
    intro L z hz
    exact (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  -- the difference of the analytic parts
  set w : ℂ → ℂ := fun z => L₁.weierstrassPExcept 0 z - L₂.weierstrassPExcept 0 z with hwdef
  have hf₁ : AnalyticAt ℂ (L₁.weierstrassPExcept 0) 0 := L₁.analyticAt_weierstrassPExcept 0
  have hf₂ : AnalyticAt ℂ (L₂.weierstrassPExcept 0) 0 := L₂.analyticAt_weierstrassPExcept 0
  have hw : AnalyticAt ℂ w 0 := by rw [hwdef]; exact hf₁.sub hf₂
  have hf₁₂ : AnalyticAt ℂ (fun z => L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z) 0 :=
    hf₁.add hf₂
  have han2 : AnalyticAt ℂ (iteratedDeriv 2 w) 0 := by
    have he : iteratedDeriv 2 w = deriv (deriv w) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [he]; exact hw.deriv.deriv
  -- `w = ℘₁ − ℘₂` globally
  have hwglobal : w = fun t => L₁.weierstrassP t - L₂.weierstrassP t := by
    rw [hwdef]; funext t; rw [hPexc L₁ t, hPexc L₂ t]; ring
  -- the linearized ODE identity on a punctured neighbourhood of `0`
  have hpt : (fun z => z ^ 2 * iteratedDeriv 2 w z) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => z ^ 2 * (6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z)))
        + 12 * w z) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (L₁.compl_lattice_sdiff_singleton_mem_nhds 0),
      mem_nhdsWithin_of_mem_nhds (L₂.compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz0 hzL1 hzL2
    have hz0' : z ≠ 0 := hz0
    have hzn1 : z ∉ L₁.lattice := by
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not] at hzL1
      exact fun hm => hz0' (hzL1 hm)
    have hzn2 : z ∉ L₂.lattice := by
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not] at hzL2
      exact fun hm => hz0' (hzL2 hm)
    -- second derivative of `w` at `z`, via `lemwp2str`
    have hdw : deriv w =ᶠ[𝓝 z] (fun t => L₁.derivWeierstrassP t - L₂.derivWeierstrassP t) := by
      filter_upwards [L₁.isClosed_lattice.isOpen_compl.mem_nhds hzn1,
                      L₂.isClosed_lattice.isOpen_compl.mem_nhds hzn2] with t ht1 ht2
      have hha : HasDerivAt w (L₁.derivWeierstrassP t - L₂.derivWeierstrassP t) t := by
        rw [hwglobal]; exact (hDP ht1).sub (hDP ht2)
      exact hha.deriv
    have hd2 : iteratedDeriv 2 w z
        = (6 * L₁.weierstrassP z ^ 2 - L₁.g₂ / 2) - (6 * L₂.weierstrassP z ^ 2 - L₂.g₂ / 2) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hdw.deriv_eq]
      have hha2 : HasDerivAt (fun t => L₁.derivWeierstrassP t - L₂.derivWeierstrassP t)
          (deriv L₁.derivWeierstrassP z - deriv L₂.derivWeierstrassP z) z :=
        (hDP' hzn1).sub (hDP' hzn2)
      rw [hha2.deriv, L₁.lemwp2str hzn1, L₂.lemwp2str hzn2]
    rw [hd2, congrFun hwglobal z, hPexc L₁ z, hPexc L₂ z, h2]
    field_simp
    ring
  -- upgrade to a full neighbourhood of `0` (both sides analytic)
  have hLHSan : AnalyticAt ℂ (fun z => z ^ 2 * iteratedDeriv 2 w z) 0 := by
    have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ 2) 0 := by fun_prop
    exact hsq.mul han2
  have hGan : AnalyticAt ℂ
      (fun z => 6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z))) 0 :=
    analyticAt_const.mul (hw.mul hf₁₂)
  have hRHSan : AnalyticAt ℂ
      (fun z => z ^ 2 * (6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z)))
        + 12 * w z) 0 := by
    have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ 2) 0 := by fun_prop
    exact (hsq.mul hGan).add (analyticAt_const.mul hw)
  have hident : (fun z => z ^ 2 * iteratedDeriv 2 w z) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => z ^ 2 * (6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z)))
        + 12 * w z) :=
    (hLHSan.frequently_eq_iff_eventually_eq hRHSan).mp hpt.frequently
  -- Part A: all Taylor coefficients of `w` at `0` vanish (the Eisenstein recursion)
  have hAll : ∀ m, iteratedDeriv m w 0 = 0 := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m IH =>
      rcases eq_or_ne m 0 with rfl | hm0
      · simp [iteratedDeriv_zero, hwdef]
      rcases eq_or_ne m 1 with rfl | hm1
      · rw [hwdef, iteratedDeriv_fun_sub hf₁.contDiffAt hf₂.contDiffAt,
            L₁.iteratedDeriv_weierstrassPExcept_self 0, L₂.iteratedDeriv_weierstrassPExcept_self 0]
        simp [L₁.sumInvPow_zero, L₂.sumInvPow_zero, L₁.G_eq_zero_of_odd 3 (by decide),
          L₂.G_eq_zero_of_odd 3 (by decide)]
      rcases eq_or_ne m 4 with rfl | hm4
      · -- the resonance `m = 4`: uses `g₃ = g₃`
        have hG6 : L₁.G 6 = L₂.G 6 := by
          have e : (140 : ℂ) * L₁.G 6 = 140 * L₂.G 6 := by
            have hh := h3; simp only [PeriodPair.g₃] at hh; exact hh
          exact mul_left_cancel₀ (by norm_num) e
        rw [hwdef, iteratedDeriv_fun_sub hf₁.contDiffAt hf₂.contDiffAt,
            L₁.iteratedDeriv_weierstrassPExcept_self 0, L₂.iteratedDeriv_weierstrassPExcept_self 0,
            L₁.sumInvPow_zero, L₂.sumInvPow_zero]
        norm_num [hG6]
      -- recursion branch: `m ≥ 2`, `m ≠ 4`
      have hm2 : 2 ≤ m := by omega
      have hkey := hident.iteratedDeriv_eq m
      have hLHSval : iteratedDeriv m (fun z => z ^ 2 * iteratedDeriv 2 w z) 0
          = ((m : ℂ) * ((m : ℂ) - 1)) * iteratedDeriv m w 0 := by
        rw [iteratedDeriv_sq_mul (iteratedDeriv 2 w) han2 m]
        have hc : iteratedDeriv (m - 2) (iteratedDeriv 2 w) 0 = iteratedDeriv m w 0 := by
          rw [← iteratedDeriv_add_two (m - 2) w]; congr 1; omega
        rw [hc]
      have hRHSval : iteratedDeriv m
          (fun z => z ^ 2 * (6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z)))
            + 12 * w z) 0
          = ((m : ℂ) * ((m : ℂ) - 1)) * iteratedDeriv (m - 2)
              (fun z => 6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z))) 0
            + 12 * iteratedDeriv m w 0 := by
        have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ 2) 0 := by fun_prop
        have hAan : AnalyticAt ℂ
            (fun z => z ^ 2 *
              (6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z)))) 0 :=
          hsq.mul hGan
        have hBan : AnalyticAt ℂ (fun z => 12 * w z) 0 := analyticAt_const.mul hw
        rw [iteratedDeriv_fun_add hAan.contDiffAt hBan.contDiffAt,
            iteratedDeriv_sq_mul
              (fun z => 6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z))) hGan m,
            iteratedDeriv_const_mul 12 hw.contDiffAt]
      have hGzero : iteratedDeriv (m - 2)
          (fun z => 6 * (w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z))) 0 = 0 := by
        have hwGprod : AnalyticAt ℂ
            (fun z => w z * (L₁.weierstrassPExcept 0 z + L₂.weierstrassPExcept 0 z)) 0 :=
          hw.mul hf₁₂
        rw [iteratedDeriv_const_mul 6 hwGprod.contDiffAt,
            iteratedDeriv_fun_mul hw.contDiffAt hf₁₂.contDiffAt,
            Finset.sum_eq_zero (fun i hi => by
              rw [IH i (by simp only [Finset.mem_range] at hi; omega)]; ring)]
        ring
      rw [hLHSval, hRHSval, hGzero, mul_zero, zero_add] at hkey
      have hcoef : ((m : ℂ) * ((m : ℂ) - 1) - 12) * iteratedDeriv m w 0 = 0 := by
        rw [sub_mul, hkey]; ring
      have hne : ((m : ℂ) * ((m : ℂ) - 1) - 12) ≠ 0 := by
        have hfac : ((m : ℂ) * ((m : ℂ) - 1) - 12) = ((m : ℂ) - 4) * ((m : ℂ) + 3) := by ring
        rw [hfac]
        refine mul_ne_zero (sub_ne_zero.mpr ?_) ?_
        · exact_mod_cast hm4
        · have hc3 : ((m : ℂ) + 3) = ((m + 3 : ℕ) : ℂ) := by push_cast; ring
          rw [hc3]; exact_mod_cast (by omega : m + 3 ≠ 0)
      exact (mul_eq_zero.mp hcoef).resolve_left hne
  -- Part B: `w` vanishes to infinite order, hence identically near `0`
  have htop : analyticOrderAt w 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hw).mpr (fun i _ => hAll i)
  have hworder : ∀ᶠ z in 𝓝 (0 : ℂ), w z = 0 := analyticOrderAt_eq_top.mp htop
  have hwloc : ∀ᶠ z in 𝓝[≠] (0 : ℂ), w z = 0 := hworder.filter_mono nhdsWithin_le_nhds
  filter_upwards [hwloc] with z hz
  have hfe : L₁.weierstrassPExcept 0 z = L₂.weierstrassPExcept 0 z := by
    rw [hwdef] at hz; simpa [sub_eq_zero] using hz
  rw [hPexc L₁ z, hPexc L₂ z] at hfe
  linear_combination hfe

/-- If `℘₁ = ℘₂` off the union of the two lattices, then `L₁ ⊆ L₂`: a point of `L₁ ∖ L₂`
would be a double pole of `℘₁` at which `℘₂` is analytic, contradicting equality of the
meromorphic orders (which only depend on punctured-neighbourhood germs). -/
lemma lattice_subset_of_eqOn (L₁ L₂ : PeriodPair)
    (heqOn : Set.EqOn L₁.weierstrassP L₂.weierstrassP (↑L₁.lattice ∪ ↑L₂.lattice)ᶜ) :
    L₁.lattice ≤ L₂.lattice := by
  rw [← SetLike.coe_subset_coe]
  intro ω hω1
  by_contra hω2
  -- a punctured neighbourhood of `ω` avoids both lattices
  have hApp : (↑L₁.lattice \ {ω})ᶜ ∈ 𝓝 ω := L₁.compl_lattice_sdiff_singleton_mem_nhds ω
  have hBpp : (↑L₂.lattice)ᶜ ∈ 𝓝 ω := (L₂.isClosed_lattice).isOpen_compl.mem_nhds hω2
  have hev2 : L₁.weierstrassP =ᶠ[𝓝[≠] ω] L₂.weierstrassP := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hApp, mem_nhdsWithin_of_mem_nhds hBpp,
      self_mem_nhdsWithin] with z hzA hzB hzne
    apply heqOn
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨?_, hzB⟩
    intro hzL1
    exact hzA ⟨hzL1, fun hh => hzne (by simpa using hh)⟩
  have hord1 : meromorphicOrderAt L₁.weierstrassP ω = -2 := L₁.order_weierstrassP ω hω1
  have hnn : 0 ≤ meromorphicOrderAt L₂.weierstrassP ω :=
    (L₂.analyticOnNhd_weierstrassP ω hω2).meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hev2, hord1] at hnn
  exact absurd hnn (by decide)

/-- **Steps 2–3 of the lattice-recovery core**: if `℘₁ = ℘₂` on a punctured neighbourhood of
`0`, then `L₁ = L₂`. Identity theorem on the connected complement of the two (countable)
lattices, then pole-set comparison. -/
theorem lattice_eq_of_weierstrassP_eventuallyEq (L₁ L₂ : PeriodPair)
    (h : L₁.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] L₂.weierstrassP) :
    L₁.lattice = L₂.lattice := by
  set S : Set ℂ := (↑L₁.lattice ∪ ↑L₂.lattice) with hS
  have hScount : S.Countable := (lattice_countable L₁).union (lattice_countable L₂)
  have hUconn : IsPreconnected Sᶜ :=
    (hScount.isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
  have hUdense : Dense Sᶜ := hScount.dense_compl ℝ
  have ha1 : AnalyticOnNhd ℂ L₁.weierstrassP Sᶜ :=
    (L₁.analyticOnNhd_weierstrassP).mono
      (Set.compl_subset_compl.mpr (Set.subset_union_left))
  have ha2 : AnalyticOnNhd ℂ L₂.weierstrassP Sᶜ :=
    (L₂.analyticOnNhd_weierstrassP).mono
      (Set.compl_subset_compl.mpr (Set.subset_union_right))
  -- a base point where the two `℘`'s agree on a neighbourhood: any point of `Sᶜ` inside the
  -- punctured ball on which `h` holds
  obtain ⟨r, hr, hrsub⟩ := (nhdsWithin_basis_ball (x := (0 : ℂ)) (s := ({0}ᶜ : Set ℂ))).mem_iff.mp h
  set W : Set ℂ := ball (0 : ℂ) r ∩ ({0}ᶜ : Set ℂ) with hW
  have hWopen : IsOpen W := (isOpen_ball).inter (isOpen_compl_singleton)
  have hWne : W.Nonempty := by
    refine ⟨((r/2 : ℝ) : ℂ), ?_, ?_⟩
    · simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]; linarith
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
  obtain ⟨z₀, hz₀W, hz₀U⟩ := hUdense.inter_open_nonempty W hWopen hWne
  have hev : L₁.weierstrassP =ᶠ[𝓝 z₀] L₂.weierstrassP :=
    Filter.eventually_of_mem (hWopen.mem_nhds hz₀W) (fun z hz => hrsub hz)
  have heqOn : Set.EqOn L₁.weierstrassP L₂.weierstrassP Sᶜ :=
    ha1.eqOn_of_preconnected_of_eventuallyEq ha2 hUconn hz₀U hev
  exact le_antisymm (lattice_subset_of_eqOn L₁ L₂ heqOn)
    (lattice_subset_of_eqOn L₂ L₁ (by rw [Set.union_comm]; exact heqOn.symm))

end PeriodPair

open Complex in
/-- Orientation / imaginary-part identity: if `b = m₁ + n₁·s` and `b·t = m₂ + n₂·s`, then
`(m₁n₂ − n₁m₂)·Im s = |b|²·Im t`. Applied twice (to a homothety and its inverse) it forces
the two change-of-basis determinants to be positive with product `1`. -/
lemma orient_eq {b s t : ℂ} {m₁ n₁ m₂ n₂ : ℤ}
    (h1 : b = ↑m₁ + ↑n₁ * s) (h2 : b * t = ↑m₂ + ↑n₂ * s) :
    ((m₁ * n₂ - n₁ * m₂ : ℤ) : ℝ) * s.im = Complex.normSq b * t.im := by
  have e : starRingEnd ℂ b * (b * t) = ↑(Complex.normSq b) * t := by
    rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  have hcb : starRingEnd ℂ b = ↑m₁ + ↑n₁ * starRingEnd ℂ s := by
    rw [h1]; simp
  rw [hcb, h2] at e
  have him := congrArg Complex.im e
  simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.intCast_im,
    Complex.intCast_re, Complex.mul_re, Complex.conj_im, Complex.conj_re,
    Complex.ofReal_im, Complex.ofReal_re] at him
  push_cast
  linarith [him]

/-- **Step 4 of the lattice-recovery core**: if the lattice of `L_{σ₁}` equals the lattice of
the homothety `a • L_{σ₂}`, then `σ₂ = γ • σ₁` for some `γ ∈ SL(2, ℤ)`. The two bases
`(1, σ₁)` and `(a, a·σ₂)` of the common lattice are related by integer matrices in both
directions; `orient_eq` forces both determinants to be `1`, and the Möbius formula finishes. -/
theorem exists_sl2_of_lattice_eq {σ₁ σ₂ : ℍ} {a : ℂˣ}
    (hlat : (Lτ σ₁).lattice = (a • Lτ σ₂).lattice) :
    ∃ γ : SL(2, ℤ), σ₂ = γ • σ₁ := by
  -- Forward direction: `a` and `a·σ₂` lie in `Lτ σ₁`'s lattice
  have ha_mem : (↑a : ℂ) ∈ (Lτ σ₁).lattice := by
    rw [hlat, PeriodPair.mem_smul_lattice_iff]
    exact ⟨1, PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩, by rw [mul_one]⟩
  have hb_mem : (↑a : ℂ) * ↑σ₂ ∈ (Lτ σ₁).lattice := by
    rw [hlat, PeriodPair.mem_smul_lattice_iff]
    exact ⟨↑σ₂, PeriodPair.mem_lattice.mpr ⟨0, 1, by simp⟩, rfl⟩
  obtain ⟨m₁, n₁, hA⟩ := PeriodPair.mem_lattice.mp ha_mem
  obtain ⟨m₂, n₂, hB⟩ := PeriodPair.mem_lattice.mp hb_mem
  simp only [Lτ_ω₁, Lτ_ω₂, mul_one] at hA hB
  have h1 : (↑a : ℂ) = ↑m₁ + ↑n₁ * ↑σ₁ := hA.symm
  have h2 : (↑a : ℂ) * ↑σ₂ = ↑m₂ + ↑n₂ * ↑σ₁ := hB.symm
  -- Reverse lattice equation: `Lτ σ₂ = a⁻¹ • Lτ σ₁` as lattices
  have hlat2 : (Lτ σ₂).lattice = ((a⁻¹) • Lτ σ₁).lattice := by
    ext z
    rw [PeriodPair.mem_smul_lattice_iff]
    constructor
    · intro hz
      refine ⟨(↑a : ℂ) * z, ?_, by rw [← mul_assoc]; simp⟩
      rw [hlat, PeriodPair.mem_smul_lattice_iff]
      exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rw [hlat, PeriodPair.mem_smul_lattice_iff] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      rw [← mul_assoc]
      simpa using hw'
  -- Reverse direction: `a⁻¹` and `a⁻¹·σ₁` lie in `Lτ σ₂`'s lattice
  have ha'_mem : ((a⁻¹ : ℂˣ) : ℂ) ∈ (Lτ σ₂).lattice := by
    rw [hlat2, PeriodPair.mem_smul_lattice_iff]
    exact ⟨1, PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩, by rw [mul_one]⟩
  have hb'_mem : ((a⁻¹ : ℂˣ) : ℂ) * ↑σ₁ ∈ (Lτ σ₂).lattice := by
    rw [hlat2, PeriodPair.mem_smul_lattice_iff]
    exact ⟨↑σ₁, PeriodPair.mem_lattice.mpr ⟨0, 1, by simp⟩, rfl⟩
  obtain ⟨m₁', n₁', hA'⟩ := PeriodPair.mem_lattice.mp ha'_mem
  obtain ⟨m₂', n₂', hB'⟩ := PeriodPair.mem_lattice.mp hb'_mem
  simp only [Lτ_ω₁, Lτ_ω₂, mul_one] at hA' hB'
  have h1' : ((a⁻¹ : ℂˣ) : ℂ) = ↑m₁' + ↑n₁' * ↑σ₂ := hA'.symm
  have h2' : ((a⁻¹ : ℂˣ) : ℂ) * ↑σ₁ = ↑m₂' + ↑n₂' * ↑σ₂ := hB'.symm
  -- imaginary parts
  have hy1 : 0 < (↑σ₁ : ℂ).im := by rw [coe_im]; exact σ₁.im_pos
  have hy2 : 0 < (↑σ₂ : ℂ).im := by rw [coe_im]; exact σ₂.im_pos
  have hna : 0 < Complex.normSq (↑a : ℂ) := Complex.normSq_pos.mpr a.ne_zero
  have hnai : 0 < Complex.normSq ((a⁻¹ : ℂˣ) : ℂ) := Complex.normSq_pos.mpr (a⁻¹).ne_zero
  -- orientation equations
  have eqA := orient_eq h1 h2
  have eqB := orient_eq h1' h2'
  -- positivity of the two determinants
  have hdMpos : 0 < (m₁ * n₂ - n₁ * m₂ : ℤ) := by
    have : (0 : ℝ) < ((m₁ * n₂ - n₁ * m₂ : ℤ) : ℝ) := by nlinarith [eqA, hy1, hy2, hna]
    exact_mod_cast this
  have hdNpos : 0 < (m₁' * n₂' - n₁' * m₂' : ℤ) := by
    have : (0 : ℝ) < ((m₁' * n₂' - n₁' * m₂' : ℤ) : ℝ) := by nlinarith [eqB, hy1, hy2, hnai]
    exact_mod_cast this
  -- product of `normSq`s is `1`
  have hnprod : Complex.normSq (↑a : ℂ) * Complex.normSq ((a⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Complex.normSq_mul]
    simp
  -- product of the determinants is `1`
  have hprodR : (((m₁ * n₂ - n₁ * m₂ : ℤ) : ℝ) * ((m₁' * n₂' - n₁' * m₂' : ℤ) : ℝ))
      * ((↑σ₁ : ℂ).im * (↑σ₂ : ℂ).im) = (↑σ₁ : ℂ).im * (↑σ₂ : ℂ).im := by
    calc (((m₁ * n₂ - n₁ * m₂ : ℤ) : ℝ) * ((m₁' * n₂' - n₁' * m₂' : ℤ) : ℝ))
          * ((↑σ₁ : ℂ).im * (↑σ₂ : ℂ).im)
        = (((m₁ * n₂ - n₁ * m₂ : ℤ) : ℝ) * (↑σ₁ : ℂ).im)
            * (((m₁' * n₂' - n₁' * m₂' : ℤ) : ℝ) * (↑σ₂ : ℂ).im) := by ring
      _ = (Complex.normSq (↑a : ℂ) * (↑σ₂ : ℂ).im)
            * (Complex.normSq ((a⁻¹ : ℂˣ) : ℂ) * (↑σ₁ : ℂ).im) := by rw [eqA, eqB]
      _ = (Complex.normSq (↑a : ℂ) * Complex.normSq ((a⁻¹ : ℂˣ) : ℂ))
            * ((↑σ₁ : ℂ).im * (↑σ₂ : ℂ).im) := by ring
      _ = (↑σ₁ : ℂ).im * (↑σ₂ : ℂ).im := by rw [hnprod]; ring
  have hprod : (m₁ * n₂ - n₁ * m₂ : ℤ) * (m₁' * n₂' - n₁' * m₂' : ℤ) = 1 := by
    have hpos : 0 < (↑σ₁ : ℂ).im * (↑σ₂ : ℂ).im := mul_pos hy1 hy2
    have hR := mul_right_cancel₀ (ne_of_gt hpos) (hprodR.trans (one_mul _).symm)
    exact_mod_cast hR
  -- the Möbius matrix has determinant `1`
  have hdet1 : (m₁ * n₂ - n₁ * m₂ : ℤ) = 1 := by
    have h1 : (1 : ℤ) ≤ m₁ * n₂ - n₁ * m₂ := hdMpos
    have h2 : (1 : ℤ) ≤ m₁' * n₂' - n₁' * m₂' := hdNpos
    exact le_antisymm (by nlinarith [hprod, h1, h2]) h1
  -- build `γ` and check the Möbius formula
  set M : Matrix (Fin 2) (Fin 2) ℤ := !![n₂, m₂; n₁, m₁] with hM
  have hMdet : M.det = 1 := by
    rw [hM, Matrix.det_fin_two_of]; linear_combination hdet1
  refine ⟨⟨M, hMdet⟩, ?_⟩
  rw [← UpperHalfPlane.coe_inj, coe_specialLinearGroup_apply]
  have hden : (↑n₁ : ℂ) * ↑σ₁ + ↑m₁ ≠ 0 := by
    have : (↑n₁ : ℂ) * ↑σ₁ + ↑m₁ = ↑a := by rw [h1]; ring
    rw [this]; exact a.ne_zero
  change (↑σ₂ : ℂ) = _
  simp only [hM, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, algebraMap_int_eq, eq_intCast]
  push_cast
  rw [eq_div_iff hden]
  linear_combination (-(↑σ₂ : ℂ)) * h1 + h2

/-- **The lattice-recovery core** (the hypothesis of `j_injective_mod_Γ_of_lattice_core`,
now a theorem): a homothety matching `g₂` and `g₃` forces the base points to be
`Γ`-equivalent. Chains steps 1–4 above. -/
theorem lattice_recovery_core (σ₁ σ₂ : ℍ) (a : ℂˣ)
    (hg2 : (a • Lτ σ₂).g₂ = (Lτ σ₁).g₂) (hg3 : (a • Lτ σ₂).g₃ = (Lτ σ₁).g₃) :
    ∃ γ : SL(2, ℤ), σ₂ = γ • σ₁ := by
  have hpp := PeriodPair.weierstrassP_eventuallyEq_of_g₂_g₃ (Lτ σ₁) (a • Lτ σ₂) hg2.symm hg3.symm
  have hlat := PeriodPair.lattice_eq_of_weierstrassP_eventuallyEq (Lτ σ₁) (a • Lτ σ₂) hpp
  exact exists_sl2_of_lattice_eq hlat

/-- **Injectivity of `j` mod `Γ`** (§4.3, unconditional): `j τ₁ = j τ₂` forces
`τ₂ = γ • τ₁` for some `γ ∈ SL(2, ℤ)`. -/
theorem j_injective_mod_Γ {τ₁ τ₂ : ℍ} (h : j τ₁ = j τ₂) :
    ∃ γ : SL(2, ℤ), τ₂ = γ • τ₁ :=
  j_injective_mod_Γ_of_lattice_core lattice_recovery_core h

/-! ## Surjectivity (§4.3, unconditional)

`j : ℍ → ℂ` is surjective, proved by the **open-and-closed** argument of §4.3: the image
`j(ℍ) = Set.range j` is nonempty, open and closed in the (pre)connected space `ℂ`, hence all
of `ℂ`.

  * **Open image** (`isOpen_range_j`): `j` is holomorphic (`mdifferentiable_j`) and nonconstant
    (`j_two_values`), so by Mathlib's open mapping theorem `AnalyticOnNhd.is_constant_or_isOpen`
    on the connected open set `{z : ℂ | 0 < z.im}` (transferring `MDifferentiable`
    to `DifferentiableOn (j ∘ ofComplex)` via `UpperHalfPlane.mdifferentiable_iff`), `j(ℍ)` is
    open.
  * **Closed image** (`isClosed_range_j`): if `j τ_n → w`, move each `τ_n` into the closed
    fundamental domain `𝒟` (`exists_smul_mem_fd_j`). The cusp estimate `theonaeherJ_lower`
    (`0.737/‖q‖ < ‖1728·J‖` on `Im τ > 5/4`) bounds `Im τ_n` above (else `‖j τ_n‖ → ∞`) while
    `𝒟` bounds it below (`three_le_four_mul_im_sq_of_mem_fd`), so the `τ_n` lie in a compact
    truncation of `𝒟`; a convergent subsequence (Heine–Borel + `IsCompact.tendsto_subseq`) has
    limit in `ℍ`, and continuity of `j` gives `w = j(limit) ∈ j(ℍ)`.
  * **Clopen ⇒ `ℂ`** (`j_surjective`): `IsClopen.eq_univ` on the preconnected space `ℂ`. -/

/-- Two explicit points of `ℍ` at which `j` takes different values (the nonconstancy witness
for the open mapping theorem). Uses the cusp bracketing `theonaeherJ_lower`/`theonaeherJ_upper`:
at `im = 3` the lower bound `0.737·e^{6π}` exceeds the upper bound `1.321·e^{4π}` at `im = 2`. -/
theorem j_two_values : ∃ τ₁ τ₂ : ℍ, j τ₁ ≠ j τ₂ := by
  set τa : ℍ := UpperHalfPlane.mk ⟨0, 3⟩ (by norm_num) with hτa
  set τb : ℍ := UpperHalfPlane.mk ⟨0, 2⟩ (by norm_num) with hτb
  have hima : τa.im = 3 := rfl
  have himb : τb.im = 2 := rfl
  have hRa : τa ∈ Region := by rw [Region, Set.mem_setOf_eq, hima]; norm_num
  have hRb : τb ∈ Region := by rw [Region, Set.mem_setOf_eq, himb]; norm_num
  refine ⟨τa, τb, ?_⟩
  have hlow := theonaeherJ_lower hRa
  have hup := theonaeherJ_upper hRb
  have hqa_pos := norm_q_pos τa
  have hqb_pos := norm_q_pos τb
  -- key: `1.321/‖q τb‖ ≤ 0.737/‖q τa‖`
  have hkey : (1.321 : ℝ) / ‖q τb‖ ≤ 0.737 / ‖q τa‖ := by
    rw [div_le_div_iff₀ hqb_pos hqa_pos, norm_q, norm_q, hima, himb]
    have e1 : Real.exp (-(2 * π * 3)) = Real.exp (-(2 * π * 2)) * Real.exp (-(2 * π)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h7 : (7 : ℝ) ≤ Real.exp (2 * π) := by
      have hae := Real.add_one_le_exp (2 * π)
      nlinarith [Real.pi_gt_three]
    have hE : Real.exp (-(2 * π)) ≤ 1 / 7 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h7
    have hBpos : 0 < Real.exp (-(2 * π * 2)) := Real.exp_pos _
    rw [e1]
    nlinarith [hE, hBpos, mul_nonneg hBpos.le (sub_nonneg.mpr hE)]
  have hja : ‖(1728 : ℂ) * J τa‖ = ‖j τa‖ := by rw [j_def]
  have hjb : ‖(1728 : ℂ) * J τb‖ = ‖j τb‖ := by rw [j_def]
  rw [hja] at hlow
  rw [hjb] at hup
  have hchain : ‖j τb‖ < ‖j τa‖ := lt_of_lt_of_le hup (le_trans hkey hlow.le)
  intro h
  rw [h] at hchain
  exact lt_irrefl _ hchain

/-- `Set.range j = (j ∘ ofComplex) '' {z : ℂ | 0 < z.im}`, the `ℂ`-picture of the image. -/
theorem range_j_eq_image :
    (j ∘ ofComplex) '' upperHalfPlaneSet = Set.range (j : ℍ → ℂ) := by
  ext c
  constructor
  · rintro ⟨z, _, rfl⟩
    exact ⟨ofComplex z, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨↑τ, τ.2, by rw [Function.comp_apply, ofComplex_apply]⟩

/-- **The image of `j` is open** (open mapping theorem for the nonconstant holomorphic `j`). -/
theorem isOpen_range_j : IsOpen (Set.range (j : ℍ → ℂ)) := by
  have hdiff : DifferentiableOn ℂ (j ∘ ofComplex) upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_j
  have hana : AnalyticOnNhd ℂ (j ∘ ofComplex) upperHalfPlaneSet :=
    hdiff.analyticOnNhd isOpen_upperHalfPlaneSet
  have hpre : IsPreconnected upperHalfPlaneSet :=
    (convex_halfSpace_im_gt 0).isPreconnected
  rcases AnalyticOnNhd.is_constant_or_isOpen hana hpre with hconst | hopenmap
  · exfalso
    obtain ⟨w, hw⟩ := hconst
    obtain ⟨τ₁, τ₂, hne⟩ := j_two_values
    apply hne
    have h1 := hw (τ₁ : ℂ) τ₁.2
    have h2 := hw (τ₂ : ℂ) τ₂.2
    rw [Function.comp_apply, ofComplex_apply] at h1 h2
    rw [h1, h2]
  · have ho := hopenmap upperHalfPlaneSet subset_rfl isOpen_upperHalfPlaneSet
    rwa [range_j_eq_image] at ho

/-- **The image of `j` is closed**: a limit `w` of `j`-values is a `j`-value. Move the
approximating points into `𝒟`, bound their imaginary parts (above by the cusp estimate, below
by `𝒟`), extract a convergent subsequence in a compact truncation of `𝒟`, and use continuity. -/
theorem isClosed_range_j : IsClosed (Set.range (j : ℍ → ℂ)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro y w hy hlim
  -- for each `n`, a point `τ n ∈ 𝒟` with `j (τ n) = y n`
  have hpick : ∀ n, ∃ τ : ℍ, τ ∈ ModularGroup.fd ∧ j τ = y n := by
    intro n
    obtain ⟨σ, hσ⟩ := hy n
    obtain ⟨γ, hγfd, hγj⟩ := exists_smul_mem_fd_j σ
    exact ⟨γ • σ, hγfd, by rw [hγj, hσ]⟩
  choose τ hτfd hτj using hpick
  -- the norms `‖y n‖` are bounded (convergent sequence)
  have hnormlim : Filter.Tendsto (fun n => ‖y n‖) Filter.atTop (𝓝 ‖w‖) := hlim.norm
  obtain ⟨C, hC⟩ := hnormlim.bddAbove_range
  have hnorm_le : ∀ n, ‖y n‖ ≤ C := fun n => hC ⟨n, rfl⟩
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hnorm_le 0)
  set C₁ : ℝ := C + 1 with hC1
  have hC1pos : 0 < C₁ := by positivity
  have h2πpos : (0 : ℝ) < 2 * π := by positivity
  set M : ℝ := max (5 / 4) ((-(Real.log (0.737 / C₁))) / (2 * π)) with hM
  -- upper bound on `Im (τ n)`
  have him_le : ∀ n, (τ n).im ≤ M := by
    intro n
    by_cases hR : 5 / 4 < (τ n).im
    · have hReg : τ n ∈ Region := by rw [Region, Set.mem_setOf_eq]; exact hR
      have hlow := theonaeherJ_lower hReg
      have hjyn : (1728 : ℂ) * J (τ n) = y n := by rw [← j_def]; exact hτj n
      rw [show ‖(1728 : ℂ) * J (τ n)‖ = ‖y n‖ by rw [hjyn]] at hlow
      have hqpos := norm_q_pos (τ n)
      have hlt : 0.737 / ‖q (τ n)‖ < C₁ :=
        lt_of_lt_of_le hlow (le_trans (hnorm_le n) (by linarith))
      rw [div_lt_iff₀ hqpos, norm_q] at hlt
      have hexp : 0.737 / C₁ < Real.exp (-(2 * π * (τ n).im)) := by
        rw [div_lt_iff₀ hC1pos]; linarith
      have hlog : Real.log (0.737 / C₁) < -(2 * π * (τ n).im) := by
        have := Real.log_lt_log (by positivity : (0 : ℝ) < 0.737 / C₁) hexp
        rwa [Real.log_exp] at this
      have himlt : (τ n).im < (-(Real.log (0.737 / C₁))) / (2 * π) := by
        rw [lt_div_iff₀ h2πpos]; nlinarith [hlog]
      exact le_trans himlt.le (le_max_right _ _)
    · exact le_trans (le_of_not_gt hR) (le_max_left _ _)
  -- lower bound on `Im (τ n)` from the fundamental domain
  have him_ge : ∀ n, (3 : ℝ) / 4 ≤ (τ n).im := by
    intro n
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd (hτfd n)
    nlinarith [(τ n).im_pos]
  -- the compact truncation of `𝒟` in `ℂ`
  set Kc : Set ℂ :=
    {z | 1 ≤ Complex.normSq z ∧ |z.re| ≤ 1 / 2 ∧ (3 : ℝ) / 4 ≤ z.im ∧ z.im ≤ M} with hKc
  have hKc_closed : IsClosed Kc := by
    apply IsClosed.inter
    · exact isClosed_le continuous_const Complex.continuous_normSq
    apply IsClosed.inter
    · exact isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
    apply IsClosed.inter
    · exact isClosed_le continuous_const Complex.continuous_im
    · exact isClosed_le Complex.continuous_im continuous_const
  have hKc_bdd : Bornology.IsBounded Kc := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1 / 2 + (3 / 4 + |M|), fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ 1 / 2 := hz.2.1
    have him1 : (3 : ℝ) / 4 ≤ z.im := hz.2.2.1
    have him2 : z.im ≤ M := hz.2.2.2
    have habs : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have himabs : |z.im| ≤ 3 / 4 + |M| := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z.im)]
      nlinarith [le_abs_self M]
    linarith
  have hKc_compact : IsCompact Kc :=
    Metric.isCompact_of_isClosed_isBounded hKc_closed hKc_bdd
  have hmem : ∀ n, (τ n : ℂ) ∈ Kc := by
    intro n
    refine ⟨(hτfd n).1, ?_, ?_, ?_⟩
    · rw [UpperHalfPlane.coe_re]; exact (hτfd n).2
    · rw [UpperHalfPlane.coe_im]; exact him_ge n
    · rw [UpperHalfPlane.coe_im]; exact him_le n
  obtain ⟨a, haKc, φ, hφmono, hφlim⟩ := hKc_compact.tendsto_subseq hmem
  have haim : (0 : ℝ) < a.im := lt_of_lt_of_le (by norm_num) haKc.2.2.1
  set τstar : ℍ := UpperHalfPlane.mk a haim with hτstar
  have hcoe : (τstar : ℂ) = a := rfl
  have htend : Filter.Tendsto (fun k => τ (φ k)) Filter.atTop (𝓝 τstar) := by
    rw [UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff]
    simpa [Function.comp_def, hcoe] using hφlim
  have hjcont : Continuous (j : ℍ → ℂ) := mdifferentiable_j.continuous
  have htendj : Filter.Tendsto (fun k => j (τ (φ k))) Filter.atTop (𝓝 (j τstar)) :=
    (hjcont.tendsto τstar).comp htend
  have htendw : Filter.Tendsto (fun k => j (τ (φ k))) Filter.atTop (𝓝 w) := by
    have heqfun : (fun k => j (τ (φ k))) = fun k => y (φ k) := by
      funext k; exact hτj (φ k)
    rw [heqfun]
    exact hlim.comp hφmono.tendsto_atTop
  have hjw : j τstar = w := tendsto_nhds_unique htendj htendw
  exact ⟨τstar, hjw⟩

/-- **Surjectivity of the modular `j`-function** (§4.3, unconditional): every complex number is
a `j`-value. The image `Set.range j` is nonempty, open (`isOpen_range_j`) and closed
(`isClosed_range_j`) in the preconnected space `ℂ`, hence all of `ℂ`. -/
theorem j_surjective : Function.Surjective (j : ℍ → ℂ) := by
  intro w
  have hcl : IsClopen (Set.range (j : ℍ → ℂ)) := ⟨isClosed_range_j, isOpen_range_j⟩
  have hne : (Set.range (j : ℍ → ℂ)).Nonempty :=
    ⟨j (UpperHalfPlane.mk ⟨0, 1⟩ (by norm_num)), Set.mem_range_self _⟩
  have hall : Set.range (j : ℍ → ℂ) = Set.univ := hcl.eq_univ hne
  have hw : w ∈ Set.range (j : ℍ → ℂ) := hall ▸ Set.mem_univ w
  exact hw

end Chudnovsky
