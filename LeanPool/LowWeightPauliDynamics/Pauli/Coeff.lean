/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Pauli.Trace
public import LeanPool.LowWeightPauliDynamics.Pauli.Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Pauli coefficient vector, and `‖O‖_{2,normalized} = ‖x‖_{ℓ²}`

This file sets up the coefficient-vector picture in which the proof of
`apd:thm:local_flow_k_local` takes place. An operator `O` on `n` qubits has Pauli coefficients
`x_P = 2^{-n} Tr(P O)`, indexed by the `4^n` Pauli strings of `def:pauli_basis`. Those strings are
orthonormal for the normalized Hilbert–Schmidt inner product `⟨A,B⟩ := 2^{-n} Tr(A† B)`, so the
normalized Schatten 2-norm `‖O‖_{2,normalized}` (the *Pauli 2-norm*) equals the `ℓ²` norm of the
coefficient
vector. The high-weight norm of `apd:eq:def_high_weight_norm` is then the `ℓ²` norm of the
coefficient vector restricted to the classes above a weight threshold.

## Main definitions

* `PauliIndex n`: the signless Pauli classes `(x, z)`, the index set of the expansion.
* `PauliString.cls`, `PauliString.herm`: the class of a Pauli string, and the self-adjoint
  representative of a class.
* `PauliString.wt`: the weight of a class (`def:pauli_weight`).
* `PauliString.coeff`, `PauliString.coeffVec`: the coefficient `x_P`, and the coefficient vector
  as an element of `EuclideanSpace ℂ (PauliIndex n)`.
* `PauliString.pauliNormSq`, `PauliString.pauliNorm`: the Pauli 2-norm, defined entrywise.
* `PauliString.restr`: restriction of a coefficient vector to a set of classes.
* `PauliString.highSet`, `PauliString.highNorm`: the region `{p : w < |p|}` and the high-weight
  norm `‖O_{≥ w+1}‖_{2,normalized}` (`apd:eq:def_high_weight_norm`).

## Main results

* `PauliString.pauliNormSq_eq_trace`: `‖O‖_{2,normalized}² = 2^{-n} Tr(O† O)`.
* `PauliString.sum_norm_coeff_sq`, `PauliString.norm_coeffVec`: Parseval, `‖x‖_{ℓ²} =
‖O‖_{2,normalized}`.
* `PauliString.coeff_toMatrix_herm`: the coefficient vector of a basis Pauli is a unit vector.
* `PauliString.highNorm_le_pauliNorm`, `PauliString.highNorm_eq_zero`,
  `PauliString.highNorm_pos_of_coeff_ne_zero`: the basic facts about the high-weight norm.

## The normalization

The expansion is in the unnormalized strings `{I,X,Y,Z}^{⊗n}`, with the factor `2^{-n}` carried by
the coefficient. They are orthonormal for `⟨·,·⟩` because `Tr(P† P) = 2^n`
(`trace_star_toMatrix_mul_self`), which is why no further constant appears in Parseval.

## The index set, and the phase that has to be chosen

`Pauli/Trace.lean` proves that the trace pairing sees only the `(x, z)` data, so the
phase-extended Pauli group is *not* an orthogonal family. The index set of the expansion therefore
cannot be `PauliString n`; it is the `4^n` **signless classes**
`PauliIndex n := Bits n × Bits n`, and a representative has to be chosen in each. `herm` chooses
the self-adjoint one with phase `(z ⬝ᵥ x).val ∈ {0, 1}`.

Self-adjointness is the only part of the choice that matters downstream:
`isSelfAdjoint_iff_phase` pins the phase's parity and leaves a sign, and `herm_eq_or_eq_neg`
records that a different admissible choice changes `herm p` only by `±1`. Nothing here needs the
finer convention `phase = #{Y-sites} mod 4`, which identifies the representative with the tensor
product of the one-qubit matrices `I, X, Y, Z` with coefficient `+1`; `Pauli/Tensor.lean` makes
that comparison.

**The coefficients are not proved real.** `coeff O p : ℂ`. For a self-adjoint `O` every
coefficient is real, since the representatives are self-adjoint, but that lemma is neither proved
nor needed: the flow argument works verbatim over `ℂ` because the transformation is by *real*
planar rotations, so `Pauli/Flow.lean` never asks. The real coefficient vector of the paper's
proof is therefore mirrored in the operators (self-adjoint representatives), not in the scalars.

## Parseval, without a basis

`sum_norm_coeff_sq` is the identity `‖x‖_{ℓ²}² = ‖O‖_{2,normalized}²`, and it is proved by a
**direct character
sum**, not by exhibiting an orthonormal basis. The reason is economy: the basis route needs linear
independence, a `finrank` count for `Matrix (Bits n) (Bits n) ℂ`, and an `InnerProductSpace`
instance on matrices; the direct route needs `char_sum`, which `Pauli/Trace.lean` already has. In
one line: for a fixed `x`-part, `Tr(P_{x,z} O)` is the `z`-character transform of the shifted
diagonal `b ↦ O_{b, b+x}` (`trace_toMatrix_mul`), and Plancherel for `(ZMod 2)^n` turns the sum
over `z` into `2^n` times the sum of `|O_{b,b+x}|²`. Summing over `x` sweeps every entry of `O`
exactly once.

Parseval alone does not give completeness, `O = ∑_P x_P P`. That is proved in
`Pauli/Truncate.lean`, as `truncOp_univ` and `sum_coeff_smul_toMatrix_herm`, from Parseval and the
reproducing property `coeff_truncOp`: an operator whose coefficients all vanish has
`‖·‖_{2,normalized} = 0`
and hence vanishing entries. Neither a `finrank` count nor an `InnerProductSpace` instance is
needed for it.
-/

@[expose] public section

namespace Lean4LPD

open Finset

/-- Fourth roots of unity have modulus one. -/
@[simp] lemma norm_iPow (k : ZMod 4) : ‖iPow k‖ = 1 := by
  rw [iPow, norm_pow, Complex.norm_I, one_pow]

/-- The **signless Pauli class**: the `(x, z)` data of a Pauli string, with the phase forgotten.
There are `4^n` of them, and they — not the `4·4^n` group elements — index the Pauli basis of
`def:pauli_basis`. -/
abbrev PauliIndex (n : ℕ) := Bits n × Bits n

namespace PauliString

variable {n : ℕ}

/-! ### Classes and their Hermitian representatives -/

/-- The class of a Pauli string. -/
def cls (s : PauliString n) : PauliIndex n := (s.x, s.z)

@[simp] lemma cls_fst (s : PauliString n) : (cls s).1 = s.x := rfl

@[simp] lemma cls_snd (s : PauliString n) : (cls s).2 = s.z := rfl

/-- The **self-adjoint representative** of a class, `i^{z ⬝ᵥ x} X^x Z^z`. Defined, not
characterized: `isSelfAdjoint_iff_phase` admits two phases differing by `2`, and this picks the
one in `{0, 1}`. See `herm_eq_or_eq_neg` for what the other choice would cost. -/
def herm (p : PauliIndex n) : PauliString n := ⟨p.1, p.2, ((p.2 ⬝ᵥ p.1).val : ZMod 4)⟩

@[simp] lemma herm_x (p : PauliIndex n) : (herm p).x = p.1 := rfl

@[simp] lemma herm_z (p : PauliIndex n) : (herm p).z = p.2 := rfl

@[simp] lemma cls_herm (p : PauliIndex n) : cls (herm p) = p := rfl

/-- `herm p` is self-adjoint, so `toMatrix (herm p)` is a Hermitian operator. -/
theorem isSelfAdjoint_herm (p : PauliIndex n) : IsSelfAdjoint (herm p) :=
  isSelfAdjoint_iff_phase.2 rfl

/-- Two self-adjoint Pauli strings on the same class differ by at most a sign: their phases
differ by `0` or `2`. This is the residual freedom `isSelfAdjoint_iff_phase` leaves. -/
theorem phase_sub_of_isSelfAdjoint {s t : PauliString n} (hs : IsSelfAdjoint s)
    (ht : IsSelfAdjoint t) (hx : s.x = t.x) (hz : s.z = t.z) :
    s.phase - t.phase = 0 ∨ s.phase - t.phase = 2 := by
  rw [isSelfAdjoint_iff_phase] at hs ht
  have h : 2 * s.phase = 2 * t.phase := by rw [← hs, ← ht, hx, hz]
  have h2 : 2 * (s.phase - t.phase) = 0 := by rw [mul_sub, h, sub_self]
  revert h2
  generalize s.phase - t.phase = d
  revert d
  decide

/-- Any self-adjoint representative of a class is `± herm`. -/
theorem herm_eq_or_eq_neg {s : PauliString n} (hs : IsSelfAdjoint s) :
    s = herm (cls s) ∨ s = phaseMul 2 (herm (cls s)) := by
  rcases phase_sub_of_isSelfAdjoint hs (isSelfAdjoint_herm (cls s)) rfl rfl with h | h
  · exact Or.inl (ext' rfl rfl (by linear_combination h))
  · refine Or.inr (ext' rfl rfl ?_)
    change s.phase = (herm (cls s)).phase + 2
    linear_combination h

/-! ### The weight of a class -/

/-- The weight sees only the `(x, z)` data. -/
lemma weight_congr {s t : PauliString n} (hx : s.x = t.x) (hz : s.z = t.z) :
    weight s = weight t := by
  have hsite : site s = site t := by funext i; rw [site, site, hx, hz]
  rw [weight, weight, support, support, hsite]

/-- **The weight of a Pauli class**, `def:pauli_weight` transported to the index
set. Well defined because the weight cannot see a phase. -/
def wt (p : PauliIndex n) : ℕ := weight (herm p)

@[simp] lemma wt_cls (s : PauliString n) : wt (cls s) = weight s := weight_congr rfl rfl

/-! ### The coefficient vector -/

/-- **The Pauli coefficient vector** `x_P = 2^{-n} Tr(P O)`, with `P` the
self-adjoint representative of the class `p`. -/
noncomputable def coeff (O : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * (toMatrix (herm p) * O).trace

/-- The squared **Pauli 2-norm** `‖O‖_{2,normalized}² = 2^{-n} Tr(O† O)`, written entrywise as
`2^{-n} ∑_{a,b} |O_{ab}|²`. `pauliNormSq_eq_trace` is the equality with the trace form. -/
noncomputable def pauliNormSq (O : Matrix (Bits n) (Bits n) ℂ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ a : Bits n, ∑ b : Bits n, ‖O a b‖ ^ 2

/-- The **Pauli 2-norm** `‖O‖_{2,normalized}`, the normalized Schatten 2-norm:
`‖O‖_{2,normalized}² = 2^{-n} Tr(O† O)`,
so that every Pauli string has norm one. This is the norm in which the high-weight norm of
`apd:eq:def_high_weight_norm` is measured. -/
noncomputable def pauliNorm (O : Matrix (Bits n) (Bits n) ℂ) : ℝ := Real.sqrt (pauliNormSq O)

lemma pauliNormSq_nonneg (O : Matrix (Bits n) (Bits n) ℂ) : 0 ≤ pauliNormSq O := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_)
  positivity

lemma pauliNorm_nonneg (O : Matrix (Bits n) (Bits n) ℂ) : 0 ≤ pauliNorm O := Real.sqrt_nonneg _

@[simp] lemma pauliNorm_sq (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm O ^ 2 = pauliNormSq O := Real.sq_sqrt (pauliNormSq_nonneg O)

/-- `‖O‖_{2,normalized}² = 2^{-n} Tr(O† O)`: the entrywise definition `pauliNormSq` agrees with
the trace
form of the normalized Schatten 2-norm. -/
theorem pauliNormSq_eq_trace (O : Matrix (Bits n) (Bits n) ℂ) :
    ((pauliNormSq O : ℝ) : ℂ) = ((2 : ℂ) ^ n)⁻¹ * (star O * O).trace := by
  have h : (star O * O).trace = ∑ a : Bits n, ∑ b : Bits n, ((‖O a b‖ : ℝ) : ℂ) ^ 2 := by
    rw [Matrix.trace]
    rw [Finset.sum_comm (s := (univ : Finset (Bits n))) (t := (univ : Finset (Bits n)))
      (f := fun a b => ((‖O a b‖ : ℝ) : ℂ) ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.star_apply, ← Complex.mul_conj' (O b a), RCLike.star_def, mul_comm]
  rw [pauliNormSq, h]
  push_cast
  rw [Finset.mul_sum]

/-! ### The trace against a Pauli, as a character transform -/

/-- **`Tr(s O)` is a character transform of a shifted diagonal of `O`.** The matrix `toMatrix s`
is monomial, so the double sum of the trace collapses to a single one: the `X`-part `s.x` selects
which off-diagonal of `O` is read, and the `Z`-part `s.z` supplies the character. -/
theorem trace_toMatrix_mul (s : PauliString n) (O : Matrix (Bits n) (Bits n) ℂ) :
    (toMatrix s * O).trace
      = iPow s.phase * ∑ b : Bits n, negOnePow (s.z ⬝ᵥ b) * O b (b + s.x) := by
  have hshift : ∀ a : Bits n, a + s.x + s.x = a := fun a => by
    rw [add_assoc, bits_add_self, add_zero]
  have hdiag : ∀ a : Bits n, (toMatrix s * O) a a
      = iPow s.phase * (negOnePow (s.z ⬝ᵥ (a + s.x)) * O (a + s.x) a) := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single (a + s.x)]
    · rw [toMatrix_apply, ite_eq_left (hshift a).symm]
      ring
    · intro b _ hb
      refine mul_eq_zero_of_left (toMatrix_apply_ne s fun hc => hb ?_) _
      rw [hc, hshift b]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.trace, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight s.x) _ _ fun a => ?_
  rw [Matrix.diag_apply, hdiag a, Equiv.coe_addRight, hshift a]

/-! ### Parseval

Plancherel for `(ZMod 2)^n`, then a sweep over the `X`-parts. -/

/-- **Plancherel on one off-diagonal.** For a fixed `X`-part, summing `|Tr(P_{x,z} O)|²` over the
`Z`-part gives `2^n` times the squared `ℓ²` mass of the corresponding off-diagonal of `O`. -/
private lemma sum_sq_char (x : Bits n) (O : Matrix (Bits n) (Bits n) ℂ) :
    ∑ z : Bits n, ‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ ^ 2
      = 2 ^ n * ∑ b : Bits n, ‖O b (b + x)‖ ^ 2 := by
  have key : ∀ z : Bits n, ((‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ : ℝ) : ℂ) ^ 2
      = ∑ b : Bits n, ∑ c : Bits n,
          negOnePow (z ⬝ᵥ (b + c)) * (O b (b + x) * (starRingEnd ℂ) (O c (c + x))) := by
    intro z
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, conj_negOnePow, dotProduct_add, negOnePow_add]
    ring
  have hchar : ∀ b c : Bits n, (∑ z : Bits n, negOnePow (z ⬝ᵥ (b + c)))
      = if b = c then (2 : ℂ) ^ n else 0 := by
    intro b c
    rw [Finset.sum_congr rfl fun z (_ : z ∈ univ) =>
        congrArg negOnePow (dotProduct_comm z (b + c)), char_sum]
    by_cases h : b = c
    · rw [ite_eq_left (by rw [h]; exact bits_add_self c), ite_eq_left h]
    · rw [ite_eq_right fun hc => h (bits_add_eq_zero_iff.1 hc), ite_eq_right h]
  have main : ((∑ z : Bits n, ‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ ^ 2 : ℝ) : ℂ)
      = ((2 ^ n * ∑ b : Bits n, ‖O b (b + x)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    calc ∑ z : Bits n, ((‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ : ℝ) : ℂ) ^ 2
        = ∑ z : Bits n, ∑ b : Bits n, ∑ c : Bits n,
            negOnePow (z ⬝ᵥ (b + c)) * (O b (b + x) * (starRingEnd ℂ) (O c (c + x))) :=
          Finset.sum_congr rfl fun z _ => key z
      _ = ∑ b : Bits n, ∑ c : Bits n, ∑ z : Bits n,
            negOnePow (z ⬝ᵥ (b + c)) * (O b (b + x) * (starRingEnd ℂ) (O c (c + x))) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ b : Bits n, ∑ c : Bits n,
            (if b = c then (2 : ℂ) ^ n else 0)
              * (O b (b + x) * (starRingEnd ℂ) (O c (c + x))) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
            rw [← Finset.sum_mul, hchar b c]
      _ = 2 ^ n * ∑ b : Bits n, ((‖O b (b + x)‖ : ℝ) : ℂ) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_eq_single b]
          · rw [ite_eq_left rfl, ← Complex.mul_conj']
          · intro c _ hc
            rw [ite_eq_right (Ne.symm hc), zero_mul]
          · intro h
            exact absurd (Finset.mem_univ _) h
  exact_mod_cast main

/-- **Parseval: `‖O‖_{2,normalized} = ‖x‖_{ℓ²}`, squared.** This is the identity the proof of
`apd:thm:local_flow_k_local` starts from; it expresses the orthonormality of the Pauli strings for
`⟨A,B⟩ = 2^{-n} Tr(A† B)`.

Proved directly from the character sum rather than through an orthonormal basis, so it does
**not** by itself give the expansion `O = ∑_P x_P P`; that is `sum_coeff_smul_toMatrix_herm` in
`Pauli/Truncate.lean`. -/
theorem sum_norm_coeff_sq (O : Matrix (Bits n) (Bits n) ℂ) :
    ∑ p : PauliIndex n, ‖coeff O p‖ ^ 2 = pauliNormSq O := by
  have hnorm : ∀ p : PauliIndex n,
      ‖coeff O p‖ ^ 2
        = (((2 : ℝ) ^ n)⁻¹) ^ 2 * ‖∑ b : Bits n, negOnePow (p.2 ⬝ᵥ b) * O b (b + p.1)‖ ^ 2 := by
    intro p
    rw [coeff, trace_toMatrix_mul, norm_mul, norm_mul, mul_pow, mul_pow, norm_iPow, one_pow,
      one_mul, herm_x, herm_z]
    congr 2
    rw [norm_inv, norm_pow, Complex.norm_ofNat]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hnorm p, ← Finset.mul_sum,
    Fintype.sum_prod_type]
  have hx : ∀ x : Bits n, (∑ z : Bits n, ‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ ^ 2)
      = 2 ^ n * ∑ b : Bits n, ‖O b (b + x)‖ ^ 2 := fun x => sum_sq_char x O
  rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => hx x, ← Finset.mul_sum, Finset.sum_comm]
  have hswap : ∀ b : Bits n, (∑ x : Bits n, ‖O b (b + x)‖ ^ 2) = ∑ a : Bits n, ‖O b a‖ ^ 2 :=
    fun b => Fintype.sum_equiv (Equiv.addLeft b) _ _ fun x => rfl
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hswap b, pauliNormSq, ← mul_assoc,
    show (((2 : ℝ) ^ n)⁻¹) ^ 2 * 2 ^ n = ((2 : ℝ) ^ n)⁻¹ from by
      have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
      field_simp]

/-- **`‖O‖_{2,normalized} = ‖x‖_{ℓ²}`**, as norms rather than squares. -/
theorem pauliNorm_eq_sqrt_sum (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm O = Real.sqrt (∑ p : PauliIndex n, ‖coeff O p‖ ^ 2) := by
  rw [pauliNorm, sum_norm_coeff_sq]

/-! ### The coefficients of a single Pauli

A guard against a vacuous reading of everything above, and the cheapest consequence of
`Pauli/Trace.lean`'s orthogonality: the coefficient vector of one basis Pauli is the corresponding
unit vector. This is what makes the locality hypothesis of `highNorm_eq_zero` (no coefficient
above a given weight, cf. `def:support`) satisfiable by a concrete observable. -/

/-- **The coefficient vector of a basis Pauli is a unit vector.** -/
theorem coeff_toMatrix_herm (p q : PauliIndex n) :
    coeff (toMatrix (herm q)) p = if p = q then 1 else 0 := by
  rw [coeff, ← star_toMatrix_of_isSelfAdjoint (isSelfAdjoint_herm p), trace_star_toMatrix_mul]
  by_cases h : p = q
  · subst h
    rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl]
    have hone : star (herm p) * herm p = 1 := by rw [star_eq_inv, inv_mul_cancel]
    have h2 : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
    rw [hone, one_phase, iPow_zero, mul_one, inv_mul_cancel₀ h2]
  · rw [ite_eq_right fun hc => h (Prod.ext hc.1 hc.2), ite_eq_right h, mul_zero]

/-- A basis Pauli is `|q|`-local: no class of larger weight carries a coefficient. -/
theorem coeff_toMatrix_herm_eq_zero {p q : PauliIndex n} (h : wt q < wt p) :
    coeff (toMatrix (herm q)) p = 0 := by
  refine (coeff_toMatrix_herm p q).trans (ite_eq_right fun hpq => ?_)
  rw [hpq] at h
  exact absurd h (lt_irrefl _)

/-! ### The coefficient vector as an `ℓ²` vector, and its weight-graded pieces

The proof of `apd:thm:local_flow_k_local` treats the coefficients as an `ℓ²` vector and applies
Minkowski's inequality on that space, so the coefficients are packaged as an element of
`EuclideanSpace ℂ (PauliIndex n)`. That buys the triangle inequality; nothing else here needs the
inner product. -/

/-- **The coefficient vector** `x = (x_P)_P` of an operator, as a vector in `ℓ²(PauliIndex n)`. -/
noncomputable def coeffVec (O : Matrix (Bits n) (Bits n) ℂ) : EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 (coeff O)

@[simp] lemma coeffVec_apply (O : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    (coeffVec O).ofLp p = coeff O p := rfl

/-- **`‖O‖_{2,normalized} = ‖x‖_{ℓ²}`**, as an identity of norms: the Pauli 2-norm of the operator
*is* the
`ℓ²` norm of its coefficient vector. -/
theorem norm_coeffVec (O : Matrix (Bits n) (Bits n) ℂ) : ‖coeffVec O‖ = pauliNorm O := by
  rw [EuclideanSpace.norm_eq, pauliNorm, ← sum_norm_coeff_sq]
  simp only [coeffVec_apply]

/-- Restriction of a coefficient vector to a set of classes `S`, zeroing every other coefficient.
For `S` the high-weight region this is the block `x_R` of the splitting `x = x_R + x_B` used in the
proof of `apd:thm:local_flow_k_local`; for its complement it is the coefficient side of the
truncation `Π_{≤ w}` (see `truncOp` in `Pauli/Truncate.lean`). -/
noncomputable def restr (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 fun p => if p ∈ S then y.ofLp p else 0

@[simp] lemma restr_apply (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n))
    (p : PauliIndex n) : (restr S y).ofLp p = if p ∈ S then y.ofLp p else 0 := rfl

lemma norm_restr_sq (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr S y‖ ^ 2 = ∑ p ∈ S, ‖y.ofLp p‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq,
    Finset.sum_congr rfl fun p (_ : p ∈ univ) =>
      show ‖(restr S y).ofLp p‖ ^ 2 = if p ∈ S then ‖y.ofLp p‖ ^ 2 else 0 from by
        rw [restr_apply]; split <;> simp,
    Finset.sum_ite_mem, Finset.univ_inter]

/-- Dropping classes cannot increase the `ℓ²` mass. -/
lemma norm_restr_le (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr S y‖ ≤ ‖y‖ := by
  have h : ‖restr S y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [norm_restr_sq, EuclideanSpace.norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      fun p _ _ => by positivity
  nlinarith [norm_nonneg (restr S y), norm_nonneg y]

@[simp] lemma restr_univ (y : EuclideanSpace ℂ (PauliIndex n)) : restr univ y = y := by
  ext p
  change (if p ∈ (univ : Finset (PauliIndex n)) then y.ofLp p else 0) = y.ofLp p
  rw [ite_eq_left (Finset.mem_univ p)]

lemma restr_add (S : Finset (PauliIndex n)) (y z : EuclideanSpace ℂ (PauliIndex n)) :
    restr S (y + z) = restr S y + restr S z := by
  ext p
  change (if p ∈ S then y.ofLp p + z.ofLp p else 0)
    = (if p ∈ S then y.ofLp p else 0) + (if p ∈ S then z.ofLp p else 0)
  split <;> simp

/-- `x = x_R + x_B`: a coefficient vector is the sum of its restrictions to a set of classes and
to the complement. -/
lemma restr_add_restr_compl (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    restr S y + restr Sᶜ y = y := by
  ext p
  change (if p ∈ S then y.ofLp p else 0) + (if p ∈ Sᶜ then y.ofLp p else 0) = y.ofLp p
  by_cases h : p ∈ S <;> simp [h, Finset.mem_compl]

/-! ### The high-weight region -/

/-- The high-weight region `R = {p : |p| > w}`: the classes of weight above the threshold `w`. -/
def highSet (n w : ℕ) : Finset (PauliIndex n) := univ.filter fun p => w < wt p

@[simp] lemma mem_highSet {n w : ℕ} {p : PauliIndex n} : p ∈ highSet n w ↔ w < wt p := by
  simp [highSet]

/-- **The high-weight norm** `‖O_{≥ w+1}‖_{2,normalized}` of `apd:eq:def_high_weight_norm`,
at threshold `w`: the `ℓ²` mass of the coefficients on classes of weight `> w`. -/
noncomputable def highNorm (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : ℝ :=
  ‖restr (highSet n w) (coeffVec O)‖

lemma highNorm_nonneg (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : 0 ≤ highNorm w O :=
  norm_nonneg _

/-- The high-weight mass never exceeds the total mass: `‖O_{≥ w+1}‖_{2,normalized} ≤
‖O‖_{2,normalized}` at every
threshold `w`. This is the inequality behind the base case of the induction in
`apd:cor:norm_cumulation_jump`. -/
theorem highNorm_le_pauliNorm (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w O ≤ pauliNorm O := by
  rw [highNorm, ← norm_coeffVec]
  exact norm_restr_le _ _

/-- A `k_o`-local observable has no mass above weight `k_o`: `init` for the ladder. Locality is
read through the coefficient vector (cf. `def:support`): every class carrying a non-zero
coefficient has weight at most `w`. -/
theorem highNorm_eq_zero (w : ℕ) {O : Matrix (Bits n) (Bits n) ℂ}
    (h : ∀ p : PauliIndex n, w < wt p → coeff O p = 0) : highNorm w O = 0 := by
  have hsq : ‖restr (highSet n w) (coeffVec O)‖ ^ 2 = 0 := by
    rw [norm_restr_sq]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [coeffVec_apply, h p (mem_highSet.1 hp), norm_zero]
    norm_num
  exact (pow_eq_zero_iff (n := 2) (by norm_num)).1 hsq

/-- The converse of `highNorm_eq_zero`: a single nonzero coefficient above the cut forces
positive high-weight mass. Used wherever a witness must show the discarded sector is really
occupied rather than merely reachable. -/
theorem highNorm_pos_of_coeff_ne_zero {w : ℕ} {O : Matrix (Bits n) (Bits n) ℂ}
    {p : PauliIndex n} (hp : w < wt p) (h : coeff O p ≠ 0) : 0 < highNorm w O := by
  refine norm_pos_iff.mpr fun hzero => h ?_
  have hz := congrArg (fun v : EuclideanSpace ℂ (PauliIndex n) => v.ofLp p) hzero
  change (if p ∈ highSet n w then coeff O p else 0) = 0 at hz
  rwa [ite_eq_left (mem_highSet.mpr hp)] at hz

end PauliString

end Lean4LPD
