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
import LeanPool.NashEmbedding.NashEmbedding.Torus.Main
import LeanPool.NashEmbedding.NashEmbedding.Torus.RealizableMetrics

/-!
# NashTorus witness tests

Statement-level sanity checks for the final theorem

  `nashTorus : 0 < n → IsPosDefSmoothMetric g → IsInjRealizable g`.

The proof is machine-checked; what these tests guard against is
*definitional drift* — the hypothesis or conclusion silently meaning
something weaker than intended.  Each test is either a positive
witness (the hypothesis class is non-empty and non-trivial, the
conclusion is attainable by the expected map) or a negative witness
(the conclusion is not satisfiable by a degenerate map).

Tests are grouped by what they discriminate:
 - N1–N2: `nashTorus` applies to the flat metric and to a genuinely
   $x$-dependent metric `(2 + sin x₀) · I`.
 - N3: `Realizes` is not vacuous — a constant map does not realize
   the flat metric.
 - N4: `IsInjectiveEmbedding` is not vacuous — the zero map fails it.
 - N5: `IsInjectiveMod2Pi` uses the lattice `2πℤⁿ`, not a finer one —
   the doubled circle map `x ↦ (cos 2x, sin 2x)` fails it.
 - N6: the flat metric is realized by the expected explicit map.
-/

open scoped BigOperators ContDiff
open NashEmbedding NashEmbedding.Sobolev Matrix

noncomputable section

namespace NashTorusWitnessTests

/-! ## N1–N2 — the theorem applies to concrete metrics -/

/-- **N1.** The flat metric is injectively realizable, via `nashTorus`. -/
example {n : ℕ} (hn : 0 < n) : IsInjRealizable (flatMetric n) :=
  nashTorus hn flatMetric_isPosDefSmoothMetric

/-- An $x$-dependent conformally flat metric `(2 + sin x₀) · I`. -/
def bumpyMetric (n : ℕ) (hn : 0 < n) : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
  fun x => (2 + Real.sin (x ⟨0, hn⟩)) • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma bumpyMetric_pos {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    0 < 2 + Real.sin (x ⟨0, hn⟩) := by
  have := Real.neg_one_le_sin (x ⟨0, hn⟩)
  linarith

lemma bumpyMetric_isPosDefSmoothMetric {n : ℕ} (hn : 0 < n) :
    IsPosDefSmoothMetric (bumpyMetric n hn) where
  smoothPeriodic := by
    refine ⟨?_, ?_⟩
    · -- smooth: scalar function times a constant matrix
      have hs : ContDiff ℝ ∞ (fun x : Fin n → ℝ => 2 + Real.sin (x ⟨0, hn⟩)) :=
        contDiff_const.add (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ (⟨0, hn⟩ : Fin n)))
      exact hs.smul contDiff_const
    · intro x k
      change (2 + Real.sin ((x + periodicShift n k) ⟨0, hn⟩)) • (1 : Matrix (Fin n) (Fin n) ℝ)
          = (2 + Real.sin (x ⟨0, hn⟩)) • 1
      have h : (x + periodicShift n k) ⟨0, hn⟩
          = x ⟨0, hn⟩ + (k ⟨0, hn⟩ : ℝ) * (2 * Real.pi) := by
        simp [periodicShift, Pi.add_apply]
        ring
      rw [h, Real.sin_add_int_mul_two_pi]
  posDef := fun x => Matrix.PosDef.one.smul (bumpyMetric_pos hn x)

/-- **N2.** `nashTorus` applies to an $x$-dependent metric. -/
example {n : ℕ} (hn : 0 < n) : IsInjRealizable (bumpyMetric n hn) :=
  nashTorus hn (bumpyMetric_isPosDefSmoothMetric hn)

/-! ## N3 — `Realizes` is not vacuous -/

/-- **N3.** A constant map does not realize the flat metric (its partial
    derivatives vanish, so the Gram entries are `0 ≠ 1`). -/
example {n N : ℕ} (hn : 0 < n) (c : Fin N → ℝ) :
    ¬ Realizes (fun _ : Fin n → ℝ => c) (flatMetric n) := by
  intro h
  have := h 0 ⟨0, hn⟩ ⟨0, hn⟩
  simp [NashEmbedding.partialDeriv, flatMetric, fderiv_const_apply] at this

/-! ## N4 — `IsInjectiveEmbedding` is not vacuous -/

/-- **N4.** The zero map is not an injective embedding: its derivative has
    no rank at all. -/
example {n N : ℕ} (hn : 0 < n) :
    ¬ IsInjectiveEmbedding (fun _ : Fin n → ℝ => (0 : Fin N → ℝ)) := by
  intro h
  have hfr := h.fullRank 0
  have := hfr.ne_zero ⟨0, hn⟩
  apply this
  simp [NashEmbedding.partialDeriv, fderiv_const_apply]

/-! ## N5 — the injectivity lattice is `2πℤⁿ` -/

/-- The doubled circle map `x ↦ (cos 2x₀, sin 2x₀)` on `ℝ¹`. -/
def doubledCircle : (Fin 1 → ℝ) → (Fin 2 → ℝ) :=
  fun x => ![Real.cos (2 * x 0), Real.sin (2 * x 0)]

/-- **N5.** `doubledCircle` identifies `0` and `π`, which differ by `π ∉ 2πℤ`,
    so it is *not* injective modulo `2πℤ`.  This discriminates the intended
    lattice `2πℤⁿ` from any coarser one (e.g. `πℤⁿ`). -/
example : ¬ IsInjectiveMod2Pi doubledCircle := by
  intro h
  have heq : doubledCircle 0 = doubledCircle (fun _ => Real.pi) := by
    simp [doubledCircle, Real.cos_two_pi, Real.sin_two_pi]
  obtain ⟨k, hk⟩ := h _ _ heq
  have h0 := congrFun hk 0
  simp [periodicShift] at h0
  -- h0 : -π = 2 * π * k 0
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hk' : (2 : ℝ) * (k 0 : ℝ) = -1 := by
    have := h0
    field_simp at this
    nlinarith [this]
  have : (2 : ℤ) * k 0 = -1 := by exact_mod_cast hk'
  omega

/-! ## N6 — the expected explicit realization -/

/-- **N6.** The flat metric is injectively realized (independently of
    `nashTorus`) by the standard embedding `x ↦ (cos xᵢ, sin xᵢ)ᵢ`. -/
example {n : ℕ} : IsInjRealizable (flatMetric n) := flatTorusEmb_injRealizes

end NashTorusWitnessTests

end
