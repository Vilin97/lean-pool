/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.OrdinalDerivation

/-!
# Degrees of the terms of a truncated expansion

Expanding a monomial by the convolution formula produces terms in which some factors are truncated
and the rest are not. `MvPolynomial.TermDegree wt d k rho` records that `rho` is the degree of such
a term for the monomial `d` with exactly `k` truncated factors: an untruncated `X_i` contributes
`wt i`, a truncated one some smaller ordinal.

This is bookkeeping about the weights alone, with no series in it, and the limit step needs it to
bound the terms with at least two truncated factors.
-/

universe u v

open Finsupp

public section

namespace MvPolynomial

variable {ι : Type u} {R : Type v} [CommRing R] {wt : ι → NatOrdinal}

/-- `TermDegree wt d k ρ`: `ρ` is the degree of a term of the expansion of the monomial `d` by the
convolution formula in which exactly `k` factors are truncated — each untruncated factor `X_i`
contributes `wt i`, each truncated one some `ρ' < wt i`. -/
inductive TermDegree (wt : ι → NatOrdinal) : (ι →₀ ℕ) → ℕ → NatOrdinal → Prop
  | zero : TermDegree wt 0 0 0
  | untrunc {d : ι →₀ ℕ} {k : ℕ} {ρ : NatOrdinal} (i : ι) :
      TermDegree wt d k ρ → TermDegree wt (d + Finsupp.single i 1) k (ρ + wt i)
  | trunc {d : ι →₀ ℕ} {k : ℕ} {ρ ρ' : NatOrdinal} (i : ι) (h : ρ' < wt i) :
      TermDegree wt d k ρ → TermDegree wt (d + Finsupp.single i 1) (k + 1) (ρ + ρ')

/-- Appending untruncated factors. -/
theorem TermDegree.add_right {d d' : ι →₀ ℕ} {k : ℕ} {ρ : NatOrdinal}
    (h : TermDegree wt d k ρ) : TermDegree wt (d + d') k (ρ + Finsupp.weight wt d') := by
  classical
  induction d' using Finsupp.induction with
  | zero => simpa using h
  | single_add a b f haf hb ih =>
    rw [add_comm (Finsupp.single a b) f, ← add_assoc, map_add, ← add_assoc]
    clear haf hb
    induction b with
    | zero => simpa using ih
    | succ b ihb =>
      rw [show Finsupp.single a (b + 1) = Finsupp.single a b + Finsupp.single a 1 from
        Finsupp.single_add a b 1, ← add_assoc, map_add, ← add_assoc,
        Finsupp.weight_single wt a 1, one_smul]
      exact TermDegree.untrunc a ihb

/-- The term of a monomial with no truncated factor has the degree of the monomial. -/
theorem termDegree_weight (wt : ι → NatOrdinal) (d : ι →₀ ℕ) :
    TermDegree wt d 0 (Finsupp.weight wt d) := by
  have := TermDegree.add_right (wt := wt) (d' := d) TermDegree.zero
  rwa [zero_add, zero_add] at this

/-- Appending untruncated factors on the left. -/
theorem TermDegree.add_left {d d' : ι →₀ ℕ} {k : ℕ} {ρ : NatOrdinal}
    (h : TermDegree wt d k ρ) : TermDegree wt (d' + d) k (Finsupp.weight wt d' + ρ) := by
  rw [add_comm d' d, add_comm _ ρ]
  exact h.add_right

/-- A truncated factor `X_i`, appended on the left. -/
theorem TermDegree.trunc_left {d : ι →₀ ℕ} {k : ℕ} {ρ ρ' : NatOrdinal} (i : ι) (h : ρ' < wt i)
    (hd : TermDegree wt d k ρ) : TermDegree wt (Finsupp.single i 1 + d) (k + 1) (ρ' + ρ) := by
  rw [add_comm (Finsupp.single i 1) d, add_comm ρ' ρ]
  exact TermDegree.trunc i h hd

/-- A monomial of a product of two polynomials has a degree that is the natural sum of degrees
of monomials of the factors. -/
theorem exists_add_eq_weight_of_mem_support_mul {P Q : MvPolynomial ι R} {d : ι →₀ ℕ}
    (hd : d ∈ (P * Q).support) :
    ∃ d₁ ∈ P.support, ∃ d₂ ∈ Q.support,
      Finsupp.weight wt d₁ + Finsupp.weight wt d₂ = Finsupp.weight wt d := by
  classical
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp (support_mul P Q hd)
  exact ⟨d₁, hd₁, d₂, hd₂, (map_add _ _ _).symm⟩

/-- Every term of the expansion has degree at most that of the monomial. -/
theorem TermDegree.le_weight {d : ι →₀ ℕ} {k : ℕ} {ρ : NatOrdinal} (h : TermDegree wt d k ρ) :
    ρ ≤ Finsupp.weight wt d := by
  induction h with
  | zero => simp
  | untrunc i _ ih => rw [map_add, Finsupp.weight_single, one_smul]; exact add_le_add_left ih _
  | trunc i hlt _ ih =>
    rw [map_add, Finsupp.weight_single, one_smul]
    exact add_le_add ih hlt.le

/-- A term with a truncated factor: the monomial is `d' · X_i`, the degree at most `deg d' ⊕ ρ'`
with `ρ' < wt i`. -/
theorem TermDegree.exists_single_truncated {d : ι →₀ ℕ} {k : ℕ} {ρ : NatOrdinal}
    (h : TermDegree wt d k ρ) (hk : 1 ≤ k) :
    ∃ (i : ι) (d' : ι →₀ ℕ) (ρ' : NatOrdinal), d = d' + Finsupp.single i 1 ∧ ρ' < wt i ∧
      ρ ≤ Finsupp.weight wt d' + ρ' := by
  induction h with
  | zero => exact absurd hk (by omega)
  | untrunc i _ ih =>
    obtain ⟨i', d', ρ', rfl, hρ', hle⟩ := ih hk
    refine ⟨i', d' + Finsupp.single i 1, ρ', by rw [add_right_comm], hρ', ?_⟩
    rw [map_add, Finsupp.weight_single, one_smul, add_right_comm]
    exact add_le_add_left hle _
  | trunc i hlt hd _ =>
    exact ⟨i, _, _, rfl, hlt, add_le_add_left hd.le_weight _⟩

/-- A term with two truncated factors: the monomial is `d' · X_i · X_j`, the degree at most
`deg d' ⊕ ρ'_i ⊕ ρ'_j` with `ρ'_i < wt i`, `ρ'_j < wt j`. -/
theorem TermDegree.exists_two_truncated {d : ι →₀ ℕ} {k : ℕ} {ρ : NatOrdinal}
    (h : TermDegree wt d k ρ) (hk : 2 ≤ k) :
    ∃ (i j : ι) (d' : ι →₀ ℕ) (ρᵢ ρⱼ : NatOrdinal),
      d = d' + Finsupp.single i 1 + Finsupp.single j 1 ∧ ρᵢ < wt i ∧ ρⱼ < wt j ∧
      ρ ≤ Finsupp.weight wt d' + ρᵢ + ρⱼ := by
  induction h with
  | zero => exact absurd hk (by omega)
  | untrunc i _ ih =>
    obtain ⟨i', j', d', ρᵢ, ρⱼ, rfl, hρᵢ, hρⱼ, hle⟩ := ih hk
    refine ⟨i', j', d' + Finsupp.single i 1, ρᵢ, ρⱼ, by
      rw [add_right_comm, add_right_comm d' (Finsupp.single i' 1)], hρᵢ, hρⱼ, ?_⟩
    rw [map_add, Finsupp.weight_single, one_smul]
    calc _ ≤ Finsupp.weight wt d' + ρᵢ + ρⱼ + wt i := add_le_add_left hle _
      _ = Finsupp.weight wt d' + wt i + ρᵢ + ρⱼ := by abel
  | trunc i hlt hd _ =>
    obtain ⟨i', d', ρ', rfl, hρ', hle⟩ := hd.exists_single_truncated (by omega)
    exact ⟨i', i, d', ρ', _, rfl, hρ', hlt, add_le_add_left hle _⟩

/-- Truncating exactly two factors of a monomial `d' · X_i · X_j`. -/
theorem termDegree_pair (d' : ι →₀ ℕ) {i j : ι} {ρᵢ ρⱼ : NatOrdinal} (hρᵢ : ρᵢ < wt i)
    (hρⱼ : ρⱼ < wt j) :
    TermDegree wt (d' + Finsupp.single i 1 + Finsupp.single j 1) 2
      (Finsupp.weight wt d' + ρᵢ + ρⱼ) :=
  TermDegree.trunc j hρⱼ (TermDegree.trunc i hρᵢ (termDegree_weight wt d'))

/-- A term of the expansion of a monomial by the convolution formula in which at least one factor
is a translated truncation at a cutoff `ζ < 0` has degree below that of the monomial. -/
theorem TermDegree.lt_weight {d : ι →₀ ℕ} {k : ℕ} {ρ : NatOrdinal} (h : TermDegree wt d k ρ)
    (hk : 1 ≤ k) : ρ < Finsupp.weight wt d := by
  obtain ⟨i, d', ρ', rfl, hρ', hle⟩ := h.exists_single_truncated hk
  rw [map_add, Finsupp.weight_single, one_smul]
  exact hle.trans_lt (add_lt_add_right hρ' _)

end MvPolynomial
