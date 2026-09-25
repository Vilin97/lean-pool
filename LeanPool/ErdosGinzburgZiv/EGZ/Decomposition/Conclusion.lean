/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Initialization
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Completeness

/-!
# Conclusions and the zero-dimensional flag decomposition

This file defines the conclusion of Theorem 4.13 and proves its monotonicity
and zero-dimensional case. The asymptotic dependencies are:

* `δ` and the flag-cardinality bound depend only on `d` and `ε`;
* after the growing function `g` is fixed, the prime threshold and the
  uniform coordinate bound may also depend on `g`;
* none of these constants depends on the prime or the input weight.

The zero-dimensional case is proved by the initial one-node decomposition.
The positive-dimensional existence proof is assembled in `Existence.lean`.
-/

@[expose] public section

namespace EGZ

open scoped BigOperators

/-- The conclusions supplied by the Flag Decomposition Lemma for one prime
and one nonzero input function.

The primality proof installs the `NeZero p` instance required by finite sums
over `ZMod p`.  Keeping that implementation detail inside this predicate
makes the public theorem quantify naturally over primes. -/
def HasFlagDecompositionConclusion {p d : ℕ} (hp : p.Prime)
    (f : FpCoord p d → ℕ) (ε δ : ℝ) (g : ℕ → ℕ)
    (Bcard BK : ℕ) : Prop := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact ∃ (Φ : FlagDecomposition p d f)
      (T K : Φ.flag.Node → ℕ),
    Fintype.card Φ.flag.Node ≤ Bcard ∧
    Antitone K ∧
    (∀ x, 1 ≤ K x ∧ K x ≤ BK) ∧
    Φ.IsKBounded K ∧
    Φ.IsComplete T ε δ ∧
    (∀ x, g (K x) ≤ T x) ∧
    (∀ x,
      δ ^ 3 * (K x : ℝ)⁻¹ ^ d * (natMass f : ℝ) ≤ (Φ.gap x : ℝ)) ∧
    (1 - ε) * (natMass f : ℝ) ≤ (Φ.retainedMass : ℝ)

/-- The final conclusion is monotone in the permitted mass loss. This
justifies the paper's reduction to `ε ≤ 1/2`. -/
theorem HasFlagDecompositionConclusion.mono_epsilon {p d : ℕ} {hp : p.Prime}
    {f : FpCoord p d → ℕ} {ε ε' δ : ℝ} {g : ℕ → ℕ} {Bcard BK : ℕ}
    (h : HasFlagDecompositionConclusion hp f ε δ g Bcard BK) (hε : ε ≤ ε') :
    HasFlagDecompositionConclusion hp f ε' δ g Bcard BK := by
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Φ, T, K, hcard, hanti, hK, hbounded, hcomplete, hg, hgap, hmass⟩ := h
  refine ⟨Φ, T, K, hcard, hanti, hK, hbounded, hcomplete.mono_epsilon hε,
    hg, hgap, ?_⟩
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hε 1)
    (Nat.cast_nonneg _)).trans hmass

/-- A smaller positive scale preserves both completeness and the gap
estimate. This is the final uniform-scale replacement in the paper. -/
theorem HasFlagDecompositionConclusion.mono_delta {p d : ℕ} {hp : p.Prime}
    {f : FpCoord p d → ℕ} {ε δ δ' : ℝ} {g : ℕ → ℕ} {Bcard BK : ℕ}
    (h : HasFlagDecompositionConclusion hp f ε δ g Bcard BK)
    (hδ' : 0 ≤ δ') (hδ : δ' ≤ δ) :
    HasFlagDecompositionConclusion hp f ε δ' g Bcard BK := by
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Φ, T, K, hcard, hanti, hK, hbounded, hcomplete, hg, hgap, hmass⟩ := h
  refine ⟨Φ, T, K, hcard, hanti, hK, hbounded, hcomplete.mono_delta hδ,
    hg, ?_, hmass⟩
  intro x
  apply le_trans _ (hgap x)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ' hδ 3) (by positivity)

/-- Dimension zero needs no refinement: there are no nonconstant affine
functionals, and the unique lifted atom carries the full input mass. -/
theorem hasFlagDecompositionConclusion_dimZero (p : ℕ) (hp : p.Prime)
    (f : FpCoord p 0 → ℕ) (hf : f ≠ 0) (ε : ℝ) (hε : 0 ≤ ε)
    (g : ℕ → ℕ) : HasFlagDecompositionConclusion hp f ε 1 g 1 1 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let Φ := FlagDecomposition.initial f hf
  refine ⟨Φ, fun _ ↦ g 1, fun _ ↦ 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_of_eq (FlagDecomposition.initial_card f hf)
  · exact antitone_const
  · intro x
    exact ⟨le_rfl, le_rfl⟩
  · exact FlagDecomposition.initial_isKBounded f hf _
  · exact FlagDecomposition.initial_isComplete_dimZero f hf _ ε 1
  · intro x
    exact le_rfl
  · intro x
    rw [show Φ.gap x = natMass f from FlagDecomposition.initial_gap f hf x]
    simp
  · rw [show Φ.retainedMass = natMass f from FlagDecomposition.initial_retainedMass f hf]
    have hmass : (0 : ℝ) ≤ natMass f := Nat.cast_nonneg _
    nlinarith

theorem flag_decomposition_lemma_dimZero (ε : ℝ) (hε : 0 < ε) :
    ∃ (δ : ℝ) (Bcard : ℕ), 0 < δ ∧
      ∀ g : ℕ → ℕ, IsGrowing g →
        ∃ (p₀ BK : ℕ), 2 ≤ p₀ ∧ 1 ≤ BK ∧
          ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
            ∀ f : FpCoord p 0 → ℕ, f ≠ 0 →
              HasFlagDecompositionConclusion hp f ε δ g Bcard BK := by
  refine ⟨1, 1, zero_lt_one, ?_⟩
  intro g _
  refine ⟨2, 1, le_rfl, le_rfl, ?_⟩
  intro p hp _ f hf
  exact hasFlagDecompositionConclusion_dimZero p hp f hf ε hε.le g

end EGZ
