/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import Mathlib.Tactic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.CompactInclusion
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.FourierSynthesis

/-!
# Distribution-Side Sobolev Spaces on the Torus

This file introduces the function/distribution-side formulation of the Sobolev
space scale on the n-torus and recasts the Rellich compactness lemma and the
Sobolev embedding theorem in that form.

## Overview

Let `X_n` denote the ℂ-vector space of trigonometric polynomials on ℝⁿ
(finite ℂ-linear combinations of the Fourier exponentials `{eₘ}_{m ∈ ℤⁿ}`).
Its algebraic dual `X_n^* = Hom_ℂ(X_n, ℂ)` is canonically isomorphic to
`ℂ^{ℤⁿ}` via the Fourier coefficient map `φ ↦ (m ↦ φ(e_{-m}))`.

The Sobolev space `H^s_{2πℤⁿ}(ℝⁿ)` consists of those distributions
`φ ∈ X_n^*` whose Fourier coefficient sequence lies in `ℓ²_(s)(ℤⁿ)`.
Under the canonical isomorphism, the Hilbert space structure is pulled back
from `ℓ²_(s)`.

## Main definitions

* `TrigPoly n` — the space of trigonometric polynomials
* `evalTrigPoly` — evaluation of a trigonometric polynomial at a point
* `TrigPolyDual n` — the algebraic dual `X_n^*`
* `fourierCoeffDistrib` — the Fourier coefficient map `φ ↦ φ̂`
* `seqToDual` — the inverse map `a ↦ φ_a` from sequences to distributions
* `dualEquivSeq` — the canonical isomorphism `X_n^* ≃ₗ[ℂ] ℂ^{ℤⁿ}`
* `MemSobolevDistrib` — membership in `H^s`
* `sobolevNormSqDistrib` — the squared Sobolev norm of a distribution
* `stdFourierCoeff` — the standard Fourier coefficient of a function
* `integrationEmbed` — the integration embedding `ι : C_{2π}(ℝⁿ; ℂ) → X_n^*`

## Main results

* `rellich_compactness_dist` — Rellich compactness for `H^t → H^s` (s < t)
* `stdFourierCoeff_fourierSynthesis` — Fourier coefficient recovery
* `sobolev_embedding_factorization` — `ι(ε(φ)) = φ` in `X_n^*`
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Complex Real NashEmbedding.Sobolev


noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Conjugation of Fourier exponentials -/

/-
The complex conjugate of a Fourier exponential equals the exponential at
the negated frequency: `conj(eₘ(θ)) = e_{-m}(θ)`.
-/
lemma starRingEnd_fourierExp (m : Fin n → ℤ) (θ : Fin n → ℝ) :
    starRingEnd ℂ (fourierExp n m θ) = fourierExp n (-m) θ := by
  unfold fourierExp;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

/-! ## Standard Fourier coefficients -/

/-- The standard Fourier coefficient of a function `f`:
`f̂ₘ = (2π)^{-n} ∫_{[0,2π]^n} f(θ) · e_{-m}(θ) dθ`. -/
def stdFourierCoeff (n : ℕ) (f : (Fin n → ℝ) → ℂ) (m : Fin n → ℤ) : ℂ :=
  (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ *
    ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
      f θ * fourierExp n (-m) θ

/-
**Fourier coefficient recovery.** If `a ∈ ℓ¹(ℤⁿ)`, then the standard
Fourier coefficients of the synthesis `a_check = ∑ aₘ eₘ` recover `a`:
`stdFourierCoeff(a_check)_m = a_m`. This is the key identity `ι ∘ ε = id`.
-/
theorem stdFourierCoeff_fourierSynthesis
    {a : (Fin n → ℤ) → ℂ} (ha : Summable (fun m => ‖a m‖))
    (m : Fin n → ℤ) :
    stdFourierCoeff n (fourierSynthesis n a) m = a m := by
  convert congr_arg ( fun x : ℂ => ( ( 2 * Real.pi ) ^ n : ℂ ) ⁻¹ * x ) ( fourierSynthesis_inner
      ha m ) using 1;
  · simp +decide [ stdFourierCoeff, starRingEnd_fourierExp ];
  · norm_num [ ← mul_assoc, Real.pi_ne_zero ]

/-! ## The space X_n of trigonometric polynomials and its dual -/

/-- `TrigPoly n` is the ℂ-vector space of trigonometric polynomials on ℝⁿ:
finite ℂ-linear combinations of `{eₘ}_{m ∈ ℤⁿ}`. We represent this as the
free ℂ-module `(Fin n → ℤ) →₀ ℂ`, where `Finsupp.single m 1` corresponds
to `eₘ`. -/
abbrev TrigPoly (n : ℕ) := (Fin n → ℤ) →₀ ℂ

/-- Evaluate a trigonometric polynomial `u = ∑ cₘ eₘ` at `θ ∈ ℝⁿ`,
producing `∑ cₘ eₘ(θ)`. -/
def evalTrigPoly (u : TrigPoly n) (θ : Fin n → ℝ) : ℂ :=
  u.sum fun m c => c * fourierExp n m θ

/-- The algebraic dual `X_n^* = Hom_ℂ(X_n, ℂ)`. A distribution on the torus
(in the algebraic sense) is a ℂ-linear functional on trigonometric
polynomials. -/
abbrev TrigPolyDual (n : ℕ) := TrigPoly n →ₗ[ℂ] ℂ

/-- The Fourier coefficient `φ̂ₘ := φ(e_{-m})` of a distribution `φ ∈ X_n^*`.
The sign inversion ensures compatibility with the standard Fourier coefficient
convention for functions via the integration embedding. -/
def fourierCoeffDistrib (φ : TrigPolyDual n) (m : Fin n → ℤ) : ℂ :=
  φ (Finsupp.single (-m) 1)

/-- Reconstruct a distribution from a sequence `a : ℤⁿ → ℂ`. The linear
functional sends the basis element `eₘ` to `a(-m)`, extended by linearity. -/
def seqToDual (n : ℕ) (a : (Fin n → ℤ) → ℂ) : TrigPolyDual n :=
  Finsupp.linearCombination ℂ (fun m => a (-m))

/-- `fourierCoeffDistrib` and `seqToDual` are inverses (forward direction):
`fourierCoeffDistrib (seqToDual a) = a`. -/
lemma fourierCoeffDistrib_seqToDual (a : (Fin n → ℤ) → ℂ) :
    fourierCoeffDistrib (seqToDual n a) = a := by
  ext m
  simp [fourierCoeffDistrib, seqToDual, Finsupp.linearCombination_single]

/-
`fourierCoeffDistrib` and `seqToDual` are inverses (backward direction):
`seqToDual (fourierCoeffDistrib φ) = φ`.
-/
lemma seqToDual_fourierCoeffDistrib (φ : TrigPolyDual n) :
    seqToDual n (fourierCoeffDistrib φ) = φ := by
  -- Use `ext` to reduce the goal to showing equality at each basis element `single m 1`.
  ext u; simp [seqToDual, fourierCoeffDistrib]

/-- The canonical ℂ-linear isomorphism `X_n^* ≃ₗ[ℂ] ℂ^{ℤⁿ}`, sending
`φ` to its Fourier coefficient sequence `m ↦ φ(e_{-m})`.
Every linear functional on `X_n` is determined by its values on the basis
`(eₘ)_{m ∈ ℤⁿ}`, and any choice of values defines a linear functional. -/
def dualEquivSeq (n : ℕ) : TrigPolyDual n ≃ₗ[ℂ] ((Fin n → ℤ) → ℂ) :=
  { toFun := fourierCoeffDistrib
    invFun := seqToDual n
    left_inv := seqToDual_fourierCoeffDistrib
    right_inv := fourierCoeffDistrib_seqToDual
    map_add' := fun φ ψ => by ext m; simp [fourierCoeffDistrib]
    map_smul' := fun c φ => by ext m; simp [fourierCoeffDistrib] }

/-! ## Distribution-side Sobolev spaces -/

/-- A distribution `φ ∈ X_n^*` belongs to `H^s_{2πℤⁿ}(ℝⁿ)` iff its
Fourier coefficient sequence `φ̂` belongs to `ℓ²_(s)(ℤⁿ)`. -/
def MemSobolevDistrib (n : ℕ) (s : ℝ) (φ : TrigPolyDual n) : Prop :=
  MemSobolev n s (fourierCoeffDistrib φ)

/-- The squared Sobolev norm of a distribution, pulled back from `ℓ²_(s)`:
`‖φ‖²_{(s)} = ∑ₘ (1 + |m|²)^s |φ̂ₘ|²`. -/
def sobolevNormSqDistrib (n : ℕ) (s : ℝ) (φ : TrigPolyDual n) : ℝ :=
  sobolevNormSq n s (fourierCoeffDistrib φ)

/-! ## Continuous inclusion -/

/-- For `t ≥ s`, the inclusion `H^t ⊆ H^s` holds. -/
lemma MemSobolevDistrib.mono {s t : ℝ} {φ : TrigPolyDual n}
    (hφ : MemSobolevDistrib n t φ) (hst : s ≤ t) : MemSobolevDistrib n s φ :=
  MemSobolev.mono hφ hst

/-- For `s ≤ t`, `‖φ‖²_{(s)} ≤ ‖φ‖²_{(t)}`. -/
lemma sobolevNormSqDistrib_mono {s t : ℝ} {φ : TrigPolyDual n}
    (hφ : MemSobolevDistrib n t φ) (hst : s ≤ t) :
    sobolevNormSqDistrib n s φ ≤ sobolevNormSqDistrib n t φ :=
  sobolevNormSq_mono hφ hst

/-! ## Rellich compactness lemma (distribution side) -/

/-
**Rellich's compactness lemma (distribution side).** For `s < t`, the
inclusion `H^t → H^s` is compact: any bounded sequence in `H^t` has a
subsequence converging in `H^s`.

The proof factors through the Fourier coefficient isomorphisms:
`H^t ≅ ℓ²_(t) ↪ ℓ²_(s) ≅ H^s`, where the middle map is compact by the
coefficient-side Rellich compactness lemma (`compactInclusion_lp_weighted`).
-/
theorem rellich_compactness_dist {s t : ℝ} (hst : s < t)
    (φseq : ℕ → TrigPolyDual n)
    (hmem : ∀ k, MemSobolevDistrib n t (φseq k))
    (hbdd : ∀ k, sobolevNormSqDistrib n t (φseq k) ≤ 1) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
    ∃ (φ_lim : TrigPolyDual n), MemSobolevDistrib n s φ_lim ∧
      Filter.Tendsto (fun k => sobolevNormSqDistrib n s (φseq (ψ k) - φ_lim))
        Filter.atTop (nhds 0) := by
  obtain ⟨ ψ, hψ ⟩ := compactInclusion_lp_weighted hst ( fun k => fourierCoeffDistrib ( φseq k )
      ) ( fun k => hmem k ) ( fun k => hbdd k );
  obtain ⟨ b, hb₁, hb₂ ⟩ := hψ.2;
  refine ⟨ ψ, hψ.1, seqToDual n b, ?_, ?_ ⟩;
  · convert hb₁ using 1;
    unfold MemSobolevDistrib;
    rw [ fourierCoeffDistrib_seqToDual ];
  · -- By definition of `fourierCoeffDistrib`, we have `fourierCoeffDistrib (φseq (ψ k) -
    -- seqToDual n b) = fourierCoeffDistrib (φseq (ψ k)) - b`.
    have h_fourierCoeffDistrib : ∀ k, fourierCoeffDistrib (φseq (ψ k) - seqToDual n b) = fun m
        => fourierCoeffDistrib (φseq (ψ k)) m - b m := by
      intro k; ext m; simp +decide [ fourierCoeffDistrib, seqToDual ] ;
    unfold sobolevNormSqDistrib; aesop;

/-! ## Integration embedding -/

/-- The integration embedding `ι` sends a function `f : ℝⁿ → ℂ` to the
distribution in `X_n^*` defined by
`ι(f)(u) = (2π)^{-n} ∫_{[0,2π]^n} f(θ) u(θ) dθ`.
We construct this via the canonical identification `X_n^* ≅ ℂ^{ℤⁿ}`:
the Fourier coefficient sequence of `ι(f)` is the standard Fourier
coefficient sequence of `f`. -/
def integrationEmbed (n : ℕ) (f : (Fin n → ℝ) → ℂ) : TrigPolyDual n :=
  seqToDual n (stdFourierCoeff n f)

/-- The Fourier coefficients of the integration embedding are the standard
Fourier coefficients: `(ι(f))^ = f̂`. -/
lemma fourierCoeffDistrib_integrationEmbed (f : (Fin n → ℝ) → ℂ) :
    fourierCoeffDistrib (integrationEmbed n f) = stdFourierCoeff n f :=
  fourierCoeffDistrib_seqToDual _

/-! ## Sobolev embedding theorem (distribution side) -/

/-- **Sobolev embedding: sup-norm bound.** For `2s > n` and `|α| ≤ k`,
the α-th derivative of the Fourier synthesis of `φ̂` satisfies
`sup_θ |∂^α ε(φ)(θ)| ≤ C · ‖φ‖_{(s+k)}`.

This is the distribution-side reformulation of
`fourierSynthesis_supBound`. -/
theorem sobolev_supBound_dist {s : ℝ} {k : ℕ} {α : Fin n → ℕ}
    (hn : 0 < n) (hs : (n : ℝ) < 2 * s) (hα : multiDeg α ≤ k)
    {φ : TrigPolyDual n} (hφ : MemSobolevDistrib n (s + k) φ)
    (θ : Fin n → ℝ) :
    ‖∑' m : Fin n → ℤ, derivCoeff α (fourierCoeffDistrib φ) m *
      fourierExp n m θ‖ ≤
    (∑' m : Fin n → ℤ, weight n (-s) m) ^ (1/2 : ℝ) *
      sobolevNormSqDistrib n (s + k) φ ^ (1/2 : ℝ) :=
  fourierSynthesis_supBound hn hs hα hφ θ

/-- **Sobolev embedding: factorization.** For `2s > n` and `a ∈ ℓ²_(s+k)`,
the Fourier coefficients of the Fourier synthesis recover `a`:
`stdFourierCoeff(a_check) = a`, i.e., `ι(ε(a)) = a` in `X_n^*`. -/
theorem sobolev_embedding_factorization
    {s : ℝ} {k : ℕ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n (s + k) a) (m : Fin n → ℤ) :
    stdFourierCoeff n (fourierSynthesis n a) m = a m :=
  stdFourierCoeff_fourierSynthesis
    (summable_norm_of_memSobolev hn (by linarith) (ha.mono (by linarith))) m

/-
**Sobolev embedding: factorization in X_n^*.** For `2s > n` and
`φ ∈ H^{s+k}`, we have `ι(ε(φ)) = φ` in `X_n^*`, where `ε(φ)` is the
Fourier synthesis of `φ̂` and `ι` is the integration embedding.
-/
theorem sobolev_embedding_factorization_dist
    {s : ℝ} {k : ℕ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {φ : TrigPolyDual n} (hφ : MemSobolevDistrib n (s + k) φ) :
    integrationEmbed n (fourierSynthesis n (fourierCoeffDistrib φ)) = φ := by
  convert seqToDual_fourierCoeffDistrib φ using 1;
  refine LinearMap.ext fun x => ?_;
  convert congr_arg ( fun a => ( Finsupp.linearCombination ℂ ( fun m => a ( -m ) ) ) x ) (
      funext fun m => sobolev_embedding_factorization hn hs hφ m ) using 1
  all_goals rfl

/-- **Sobolev embedding: linearity.** The Fourier synthesis map
`a ↦ a_check` is linear. -/
theorem sobolev_embedding_linear_add
    {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖))
    (hb : Summable (fun m => ‖b m‖))
    (θ : Fin n → ℝ) :
    fourierSynthesis n (a + b) θ =
      fourierSynthesis n a θ + fourierSynthesis n b θ :=
  fourierSynthesis_add ha hb θ

/-- **Sobolev embedding: scalar multiplication.** -/
theorem sobolev_embedding_linear_smul
    {a : (Fin n → ℤ) → ℂ} (c : ℂ)
    (θ : Fin n → ℝ) :
    fourierSynthesis n (c • a) θ = c * fourierSynthesis n a θ :=
  fourierSynthesis_smul c θ

/-- **Sobolev embedding: periodicity.** The Fourier synthesis is `2π`-periodic
in each variable. -/
theorem sobolev_embedding_periodic
    {a : (Fin n → ℤ) → ℂ}
    (θ : Fin n → ℝ) (j : Fin n) :
    fourierSynthesis n a (Function.update θ j (θ j + 2 * π)) =
      fourierSynthesis n a θ :=
  fourierSynthesis_periodic θ j

/-- **Sobolev embedding: injectivity.** If the Fourier synthesis vanishes
identically, then the coefficient sequence is zero. -/
theorem sobolev_embedding_injective
    {a : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖))
    (h : ∀ θ : Fin n → ℝ, fourierSynthesis n a θ = 0) :
    a = 0 :=
  fourierSynthesis_injective ha h

end NashEmbedding.Sobolev

end
