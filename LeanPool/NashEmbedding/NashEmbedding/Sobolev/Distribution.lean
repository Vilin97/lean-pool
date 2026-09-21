/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.CompactInclusion
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.FourierSynthesis

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

/-! ## Orthogonality of Fourier exponentials -/

/-
Orthogonality of Fourier exponentials on `[0, 2π]ⁿ`:
`∫_{[0,2π]^n} eₘ(θ) · conj(e_{m₀}(θ)) dθ = (2π)^n δ_{m,m₀}`.
-/
lemma fourierExp_inner_eq (m m₀ : Fin n → ℤ) :
    ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
      fourierExp n m θ * starRingEnd ℂ (fourierExp n m₀ θ) =
    if m = m₀ then ((2 * π) ^ n : ℝ) else 0 := by
  split_ifs with h;
  · simp +decide only [Algebra.mul_smul_comm, mul_one, fourierExp, ofReal_sum, ofReal_mul,
    ofReal_intCast, ← h, ofReal_pow, ofReal_ofNat];
    norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp ];
    erw [ MeasureTheory.measureReal_def ];
    erw [ Real.volume_Icc_pi ]; norm_num [ mul_comm ];
    rw [ ENNReal.toReal_ofReal ( by positivity ) ]; norm_num;
  · -- Since $m \neq m_0$, there exists $j$ such that $m_j \neq m_{0,j}$.
    obtain ⟨j, hj⟩ : ∃ j : Fin n, m j ≠ m₀ j := by
      exact Function.ne_iff.mp h;
    -- The integral over the product space can be factored into a product of integrals.
    have h_prod : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), Complex.exp
        (Complex.I * ∑ i : Fin n, ((m i - m₀ i) : ℂ) * θ i) = ∏ i : Fin n, ∫ θ : ℝ in Set.Icc 0
        (2 * Real.pi), Complex.exp (Complex.I * ((m i - m₀ i) : ℂ) * θ) := by
      have h_prod : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), Complex.exp
          (Complex.I * ∑ i : Fin n, ((m i - m₀ i) : ℂ) * θ i) = ∫ θ : Fin n → ℝ, (∏ i : Fin n,
          (if 0 ≤ θ i ∧ θ i ≤ 2 * Real.pi then Complex.exp (Complex.I * ((m i - m₀ i) : ℂ) * θ
          i) else 0)) := by
        rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator, Pi.le_def,
            forall_and ];
        congr with x; split_ifs <;> simp_all +decide only [ne_eq, mul_comm, and_self,
          ↓reduceIte, mul_left_comm, not_and, not_forall, not_le, Finset.prod_ite,
          Finset.prod_const, zero_eq_mul, pow_eq_zero_iff', Finset.card_eq_zero,
          Finset.filter_eq_empty_iff, Finset.mem_univ,  not_lt, forall_const, true_and];
        · rw [ ← Complex.exp_sum, Finset.mul_sum _ _ _ ];
        · grind;
      have h_prod : ∀ (f : Fin n → ℝ → ℂ), (∫ θ : Fin n → ℝ, ∏ i : Fin n, f i (θ i)) = ∏ i : Fin
          n, ∫ θ : ℝ, f i θ := by
        exact fun f => MeasureTheory.integral_fin_nat_prod_volume_eq_prod f;
      convert h_prod ( fun i θ => if 0 ≤ θ ∧ θ ≤ 2 * Real.pi then Complex.exp ( Complex.I * ( m
          i - m₀ i ) * θ ) else 0 ) using 1;
      exact Finset.prod_congr rfl fun _ _ => by rw [ ← MeasureTheory.integral_indicator ] <;>
          norm_num [ Set.indicator ];
    -- For $m_j \neq m_{0,j}$, the integral $\int_0^{2\pi} e^{i(m_j - m_{0,j})\theta}
    -- d\theta$ is zero.
    have h_integral_zero : ∀ j : Fin n, m j ≠ m₀ j → ∫ θ : ℝ in Set.Icc 0 (2 * Real.pi),
        Complex.exp (Complex.I * ((m j - m₀ j) : ℂ) * θ) = 0 := by
      intro j hj; rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ←
          intervalIntegral.integral_of_le Real.two_pi_pos.le ];
      have := @integral_exp_mul_complex 0 ( 2 * Real.pi );
      convert this ( show ( I * ( m j - m₀ j : ℂ ) ) ≠ 0 from mul_ne_zero Complex.I_ne_zero <|
          sub_ne_zero_of_ne <| mod_cast hj ) using 1; norm_num;
      exact Eq.symm ( div_eq_zero_iff.mpr <| Or.inl <| sub_eq_zero.mpr <|
          Complex.exp_eq_one_iff.mpr ⟨ m j - m₀ j, by push_cast; ring ⟩ );
    convert h_prod using 1;
    · unfold fourierExp; norm_num [ Complex.exp_add, Complex.exp_neg, mul_sub, sub_mul,
        Finset.sum_sub_distrib ];
      norm_num [ Complex.exp_sub, Complex.exp_neg, Complex.exp_conj ];
      norm_num [ div_eq_mul_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.norm_exp ];
    · rw [ Finset.prod_eq_zero ( Finset.mem_univ j ) ( h_integral_zero j hj ) ]; norm_num

/-! ## Fourier inversion formula -/

/-
**Fourier inversion.** If `a ∈ ℓ¹(ℤⁿ)`, then the inner product of the
Fourier synthesis `a_check(θ) = ∑ aₘ eₘ(θ)` with `conj(e_{m₀}(θ))` over
`[0, 2π]ⁿ` recovers `(2π)ⁿ · a_{m₀}`.
-/
lemma fourierSynthesis_inner
    {a : (Fin n → ℤ) → ℂ} (ha : Summable (fun m => ‖a m‖))
    (m₀ : Fin n → ℤ) :
    ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
      fourierSynthesis n a θ * starRingEnd ℂ (fourierExp n m₀ θ) =
    ((2 * π) ^ n : ℝ) * a m₀ := by
  -- Expand the integral using the definition of `fourierSynthesis`.
  have h_expand : ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • (1 : Fin n → ℝ)),
      fourierSynthesis n a θ * (starRingEnd ℂ) (fourierExp n m₀ θ) = ∑' m : Fin n → ℤ, a m * ∫ θ
      in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • (1 : Fin n → ℝ)), fourierExp n m θ *
      (starRingEnd ℂ) (fourierExp n m₀ θ) := by
    simp +decide only [fourierSynthesis, ← MeasureTheory.integral_const_mul];
    rw [ ← MeasureTheory.integral_tsum ];
    · simp +decide only [← tsum_mul_right, ← mul_assoc];
    · intro m; apply_rules [ Continuous.aestronglyMeasurable, Continuous.mul, continuous_const ];
      · exact Complex.continuous_exp.comp <| Continuous.mul continuous_const <| by continuity;
      · exact Complex.continuous_conj.comp ( Complex.continuous_exp.comp <| by continuity );
    · refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum
          (g := fun m => ENNReal.ofReal (‖a m‖ * (2 * Real.pi) ^ n)) (fun m => ?_)) ?_)
      · refine le_trans (MeasureTheory.lintegral_mono
            (g := fun _ => ENNReal.ofReal ‖a m‖) (fun x => ?_)) ?_
        · rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num [ norm_fourierExp ];
          finiteness;
        · simp +decide only [Algebra.mul_smul_comm, mul_one, ofReal_norm,
          MeasureTheory.lintegral_const, MeasurableSet.univ,
          MeasureTheory.Measure.restrict_apply, Set.univ_inter, volume_Icc_pi, Pi.smul_apply,
          Pi.ofNat_apply, smul_eq_mul,  sub_zero, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, mul_pow, norm_nonneg, ENNReal.ofReal_mul,
          Nat.ofNat_nonneg, pow_nonneg, ENNReal.ofReal_pow, ENNReal.ofReal_ofNat];
          rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_pow ( by positivity ) ];
              ring_nf; norm_num;
      · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num;
        · exact fun m => mul_nonneg ( norm_nonneg _ ) ( pow_nonneg ( by positivity ) _ );
        · exact ha.mul_right _;
  rw [ h_expand, tsum_eq_single m₀ ];
  · rw [ mul_comm, fourierExp_inner_eq ]; norm_num;
  · intro m hm; rw [ fourierExp_inner_eq m m₀ ] ; aesop;

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
