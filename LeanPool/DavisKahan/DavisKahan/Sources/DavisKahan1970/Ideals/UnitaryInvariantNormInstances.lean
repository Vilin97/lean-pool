/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.NormCorrespondence

/-!
# Concrete witnesses for the Davis--Kahan source norm class

The universal source theorem must quantify over a demonstrably inhabited class.
This file constructs the normalized nuclear norm from the finite-list `l1`
gauge and transports it through the proved equivalence between coherent
symmetric norming functions and `SymmetricNormingFunction`.

The construction is independent of matrix coordinates.  Its finite gauge is
`sum i, |x i|`; zero padding is literal, normalization is immediate, and weak
majorization is the final-prefix inequality.  Consequently this is also a
small end-to-end regression test for the source-norm correspondence.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

noncomputable section

universe u v

/-- The finite `l1` symmetric gauge. -/
def l1Gauge (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, |x i|

namespace L1Gauge

/-- The `l1` gauge of the zero list is `0`. -/
@[simp]
theorem zero (n : ℕ) : l1Gauge n (0 : Fin n → ℝ) = 0 := by
  simp [l1Gauge]

/-- The `l1` gauge is nonnegative. -/
theorem nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ l1Gauge n x :=
  Finset.sum_nonneg fun i _ => abs_nonneg (x i)

/-- The `l1` gauge is definite: it vanishes exactly at the zero list. -/
theorem definite {n : ℕ} (x : Fin n → ℝ) :
    l1Gauge n x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have hi : |x i| ≤ l1Gauge n x := by
      exact Finset.single_le_sum
        (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
    have habs : |x i| = 0 := by
      apply le_antisymm
      · simpa [hx] using hi
      · exact abs_nonneg _
    exact abs_eq_zero.mp habs
  · rintro rfl
    exact zero n

/-- Triangle inequality for the `l1` gauge. -/
theorem add_le {n : ℕ} (x y : Fin n → ℝ) :
    l1Gauge n (x + y) ≤ l1Gauge n x + l1Gauge n y := by
  calc
    l1Gauge n (x + y)
        = ∑ i, |x i + y i| := by
          simp [l1Gauge]
    _ ≤ ∑ i, (|x i| + |y i|) :=
      Finset.sum_le_sum fun i _ => abs_add_le (x i) (y i)
    _ = l1Gauge n x + l1Gauge n y := by
      simp [l1Gauge, Finset.sum_add_distrib]

/-- Absolute homogeneity: scaling a list scales its gauge by the absolute value. -/
theorem smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    l1Gauge n (c • x) = |c| * l1Gauge n x := by
  simp_rw [l1Gauge, Pi.smul_apply, smul_eq_mul, abs_mul]
  exact (Finset.mul_sum _ _ _).symm

/-- The `l1` gauge is invariant under permuting the entries — it is a *symmetric*
norming function. -/
theorem perm {n : ℕ} (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    l1Gauge n (x ∘ π) = l1Gauge n x := by
  simpa [l1Gauge, Function.comp_apply] using
    Equiv.sum_comp π (fun i => |x i|)

/-- The `l1` gauge depends only on the absolute values of the entries. -/
@[simp]
theorem abs {n : ℕ} (x : Fin n → ℝ) :
    l1Gauge n (fun i => |x i|) = l1Gauge n x := by
  simp [l1Gauge]

/-- Padding a list with one extra zero entry leaves the `l1` gauge unchanged.  This is
the coherence condition linking the gauges at successive lengths. -/
theorem zero_pad {n : ℕ} (x : Fin n → ℝ) :
    l1Gauge (n + 1) (zeroPad x) = l1Gauge n x := by
  rw [l1Gauge, Fin.sum_univ_castSucc]
  simp [l1Gauge, zeroPad]

/-- Normalization: the one-entry list `(1)` has gauge `1`. -/
@[simp]
theorem normalized : l1Gauge 1 (fun _ => 1) = 1 := by
  simp [l1Gauge]

/-- The `l1` gauge is monotone under weak majorization of nonnegative lists — for this
gauge the prefix-sum hypothesis at the final index *is* the conclusion. -/
theorem weak_majorization {n : ℕ} {x y : Fin n → ℝ}
    (_hx : Antitone x) (h0x : ∀ i, 0 ≤ x i) (h0y : ∀ i, 0 ≤ y i)
    (hpre : ∀ m : ℕ,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), x i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), y i)) :
    l1Gauge n x ≤ l1Gauge n y := by
  have hall :
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < n) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => i.isLt
  have hfull := hpre n
  rw [hall] at hfull
  simpa [l1Gauge, abs_of_nonneg, h0x, h0y] using hfull

end L1Gauge

/-- The normalized `l1` symmetric norming function from the source definition. -/
noncomputable def nuclearAxiomatic :
    SymmetricNormingFunction.Axiomatic where
  gauge := l1Gauge
  nonneg := L1Gauge.nonneg
  definite := L1Gauge.definite
  add_le := L1Gauge.add_le
  smul := L1Gauge.smul
  perm := L1Gauge.perm
  abs := L1Gauge.abs
  zero_pad := L1Gauge.zero_pad
  normalized := L1Gauge.normalized
  weak_majorization := L1Gauge.weak_majorization

/-- A concrete member of the exact Davis--Kahan norm class: the nuclear norm. -/
noncomputable def nuclearNormingFunction : SymmetricNormingFunction :=
  nuclearAxiomatic.toNormingFunction

/-- The paper norm class is genuinely inhabited. -/
theorem symmetricNormingFunction_nonempty :
    Nonempty SymmetricNormingFunction :=
  ⟨nuclearNormingFunction⟩

/-- The finite gauge of the concrete nuclear witness is exactly the `l1` gauge. -/
theorem nuclearNormingFunction_finiteGauge (n : ℕ) (x : Fin n → ℝ) :
    nuclearNormingFunction.finiteGauge n x = l1Gauge n x :=
  SymmetricNormingFunction.Axiomatic.toNormingFunction_finiteGauge
    nuclearAxiomatic n x

/-- The finite-prefix value of the nuclear witness is the Ky Fan prefix sum. -/
theorem nuclearNormingFunction_prefixGauge
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (n : ℕ) (A : E →L[𝕜] F) :
    nuclearNormingFunction.prefixGauge n A = kyFanApproximationGauge n A := by
  have habs : ∀ i : Fin n,
      |SymmetricNormingFunction.approximationPrefix n A i| =
        SymmetricNormingFunction.approximationPrefix n A i := fun _ =>
    abs_of_nonneg (approximationSingularValue_nonneg _ _)
  rw [SymmetricNormingFunction.prefixGauge,
    nuclearNormingFunction_finiteGauge, l1Gauge,
    Finset.sum_congr rfl fun i _ => habs i,
    SymmetricNormingFunction.sum_approximationPrefix]

end

end ExactSinTheta
end DavisKahan
end TauCeti
