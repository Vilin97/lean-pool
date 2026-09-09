/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient

@[expose] public section

/-! The finite sum of nested genuine derivative words is the corresponding longer word sum. -/

noncomputable section

namespace EulerParameterWordGevrey

open Finset
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem sum_wordSum_wordDerivative (directions : ι → P) (f : P → E)
    (hf : ContDiff ℝ ∞ f) (k n : ℕ) (x : P) :
    (∑ w : Fin k → ι, wordSum directions (wordDerivative directions f w) n x) =
      wordSum directions f (k+n) x := by
  induction k generalizing f with
  | zero =>
    have he (w : Fin 0 → ι) : wordDerivative directions f w = f :=
      funext (wordDerivative_zero directions f w)
    simp only [he, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero,
      one_smul, Nat.zero_add]
  | succ k ih =>
    rw [sum_words_snoc]
    have he (i : ι) (w : Fin k → ι) :
        wordDerivative directions f (Fin.snoc w i) =
          wordDerivative directions (directional directions f i) w :=
      funext (wordDerivative_snoc directions f hf w i)
    simp_rw [he, ih _ (directional_contDiff directions f hf _)]
    simpa only [show k+1+n=k+n+1 by omega] using (wordSum_succ directions f hf (k+n) x).symm

end EulerParameterWordGevrey
