/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.StableRiccatiPair
public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.KyFanOrthonormal

/-!
# Unrestricted sharp Ky Fan `tan 2Theta`

This file performs the finite approximate-family sum and the epsilon limit.
The only nonroutine input is the local spectral-selection theorem from
`DavisKahan.Sources.DavisKahan1970.Ideals.SpectralSelection`; all variational and
approximation-number calls are existing declarations in the repository.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace BigOperators
open DavisKahanExt
open ExactSinTheta

noncomputable section

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]

/-- Uniform version of the stable-pair error for singular values `s ≤ r`. -/
def uniformStablePairError
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (r ε : ℝ) : ℝ :=
  2 * (((‖B.A0‖ + ‖B.A1‖) * ε) +
      2 * r * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) /
    (1 - r ^ 2)

/-- Monotonicity of the explicit error on the contractive interval. -/
theorem stablePairError_le_uniform
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {s r ε : ℝ} (hs0 : 0 ≤ s) (hsr : s ≤ r)
    (hr1 : r < 1) (hε0 : 0 ≤ ε) :
    stablePairError B s ε ≤ uniformStablePairError B r ε := by
  have hr0 : 0 ≤ r := hs0.trans hsr
  have hds : 0 < 1 - s ^ 2 := by nlinarith
  have hdr : 0 < 1 - r ^ 2 := by nlinarith
  unfold stablePairError uniformStablePairError
  apply (div_le_div_iff₀ hds hdr).2
  have hnum :
      ((‖B.A0‖ + ‖B.A1‖) * ε +
          2 * s * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) ≤
        ((‖B.A0‖ + ‖B.A1‖) * ε +
          2 * r * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) := by
    gcongr
  have hnonneg' : 0 ≤
      ((‖B.A0‖ + ‖B.A1‖) * ε +
        2 * r * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) := by positivity
  have hdenmono : 1 - r ^ 2 ≤ 1 - s ^ 2 := by nlinarith
  calc
    2 * ((‖B.A0‖ + ‖B.A1‖) * ε +
          2 * s * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) * (1 - r ^ 2)
        ≤ 2 * ((‖B.A0‖ + ‖B.A1‖) * ε +
          2 * r * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) * (1 - r ^ 2) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnum (by norm_num)) hdr.le
    _ ≤ 2 * ((‖B.A0‖ + ‖B.A1‖) * ε +
          2 * r * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) * (1 - s ^ 2) := by
          exact mul_le_mul_of_nonneg_left hdenmono
            (mul_nonneg (by norm_num) hnonneg')

/-- Ky Fan prefixes are monotone in the prefix length. -/
theorem kyFanApproximationGauge_mono_length
    (K : E1 →L[ℂ] E0) {m k : ℕ} (hmk : m ≤ k) :
    kyFanApproximationGauge m K ≤ kyFanApproximationGauge k K := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  rw [← Finset.sum_range_add_sum_Ico
    (f := fun n => K.approximationNumber n) hmk]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ =>
    K.approximationNumber_nonneg n)

section CompleteSpaces

variable [CompleteSpace E0] [CompleteSpace E1]

/-- Sum the stable scalar estimate over one approximate leading family. -/
theorem selected_doubleAngleTangent_le_kyFan_add_error
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d r ε : ℝ} (hd0 : 0 ≤ d) (_hr0 : 0 ≤ r) (hr1 : r < 1)
    (hε0 : 0 ≤ ε)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hXr : ‖X‖ ≤ r) {k : ℕ}
    (F : TauCeti.DavisKahan.ApproximateLeadingSingularFamily X k ε) :
    d * (∑ i : Fin F.count,
        DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i)) ≤
      2 * kyFanApproximationGauge k B.B01 +
        (F.count : ℝ) * uniformStablePairError B r ε := by
  have hs0 : ∀ i : Fin F.count, 0 ≤ X.approximationNumber i :=
    fun i => X.approximationNumber_nonneg i
  have hsr : ∀ i : Fin F.count, X.approximationNumber i ≤ r :=
    fun i => (X.approximationNumber_le_norm i).trans hXr
  have hs1 : ∀ i : Fin F.count, X.approximationNumber i < 1 :=
    fun i => (hsr i).trans_lt hr1
  have hpoint : ∀ i : Fin F.count,
      d * DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i) ≤
        2 * (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) +
          uniformStablePairError B r ε := by
    intro i
    calc
      d * DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i)
          ≤ 2 * (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) +
              stablePairError B (X.approximationNumber i) ε :=
        stableSingularPair_doubleAngleTangent_le B hd0 (hs0 i) (hs1 i)
          hε0 hA0 hA1 hX (F.norm_right i) (F.norm_left i)
          (F.apply_residual i) (F.adjoint_residual i)
      _ ≤ 2 * (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) +
              uniformStablePairError B r ε := by
        gcongr
        exact stablePairError_le_uniform B (hs0 i) (hsr i) hr1 hε0
  have hsum :
      d * (∑ i : Fin F.count,
          DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i)) ≤
        2 * (∑ i : Fin F.count,
          (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ)) +
          (F.count : ℝ) * uniformStablePairError B r ε := by
    calc
      d * (∑ i : Fin F.count,
          DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i))
          = ∑ i : Fin F.count,
              d * DavisKahan.TanTwoTheta.doubleAngleTangent
                (X.approximationNumber i) := by
              rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin F.count,
            (2 * (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) +
              uniformStablePairError B r ε) := by
              exact Finset.sum_le_sum fun i _ => hpoint i
      _ = 2 * (∑ i : Fin F.count,
            (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ)) +
            (F.count : ℝ) * uniformStablePairError B r ε := by
              rw [Finset.sum_add_distrib, Finset.mul_sum,
                Finset.sum_const, nsmul_eq_mul]
              have hcard :
                  (((Finset.univ : Finset (Fin F.count)).card : ℕ) : ℝ) =
                    (F.count : ℝ) := by
                simp
              rw [hcard]
  have hcoeff :
      (∑ i : Fin F.count,
        (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ)) ≤
        kyFanApproximationGauge F.count B.B01 := by
    apply sum_le_kyFanApproximationGauge_of_orthonormal
      B.B01 F.orthonormal_neg_right F.left_orthonormal
    intro i
    simp
  have hlen := kyFanApproximationGauge_mono_length B.B01 F.count_le
  calc
    d * (∑ i : Fin F.count,
        DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i))
        ≤ 2 * (∑ i : Fin F.count,
          (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ)) +
            (F.count : ℝ) * uniformStablePairError B r ε := hsum
    _ ≤ 2 * kyFanApproximationGauge F.count B.B01 +
          (F.count : ℝ) * uniformStablePairError B r ε := by gcongr
    _ ≤ 2 * kyFanApproximationGauge k B.B01 +
          (F.count : ℝ) * uniformStablePairError B r ε := by gcongr

/-- Error-bound form of the full transformed prefix estimate. -/
theorem transformed_prefix_le_kyFan_add_error
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d r ε : ℝ} (hd0 : 0 ≤ d) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hε0 : 0 ≤ ε)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hXr : ‖X‖ ≤ r) {k : ℕ}
    (F : TauCeti.DavisKahan.ApproximateLeadingSingularFamily X k ε) :
    d * (∑ n ∈ Finset.range k,
        DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber n)) ≤
      2 * kyFanApproximationGauge k B.B01 +
        (F.count : ℝ) * uniformStablePairError B r ε +
        d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) := by
  have hprefix := TauCeti.DavisKahan.sum_doubleAngleTangent_le_selected_add_tail
    X k hε0 hr0 hr1 hXr F
  have hselected := selected_doubleAngleTangent_le_kyFan_add_error
    B hd0 hr0 hr1 hε0 hA0 hA1 hX hXr F
  have hmul := mul_le_mul_of_nonneg_left hprefix hd0
  calc
    d * (∑ n ∈ Finset.range k,
        DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber n))
        ≤ d * ((∑ i : Fin F.count,
              DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i)) +
            (k - F.count) * ((2 / (1 - r ^ 2)) * ε)) := hmul
    _ = d * (∑ i : Fin F.count,
          DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i)) +
        d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) := by
          rw [Nat.cast_sub F.count_le]
          ring
    _ ≤ 2 * kyFanApproximationGauge k B.B01 +
          (F.count : ℝ) * uniformStablePairError B r ε +
        d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) := by gcongr

/-- **Sharp unrestricted approximation-number Ky Fan theorem.** -/
theorem sharp_transformed_prefix
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    d * (∑ n ∈ Finset.range k,
        DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber n)) ≤
      2 * kyFanApproximationGauge k B.B01 := by
  let r : ℝ := (‖X‖ + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hXr : ‖X‖ ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  apply le_of_forall_pos_le_add
  intro η hη
  let C : ℝ :=
    (k : ℝ) * (2 * ((‖B.A0‖ + ‖B.A1‖) + 2 * r * ‖B.B01‖ + ‖B.B01‖) /
      (1 - r ^ 2)) +
      d * (k : ℝ) * (2 / (1 - r ^ 2))
  have hdenr : 0 < 1 - r ^ 2 := by nlinarith
  have hC0 : 0 ≤ C := by
    have hmainCoeff :
        0 ≤ 2 * ((‖B.A0‖ + ‖B.A1‖) +
          2 * r * ‖B.B01‖ + ‖B.B01‖) / (1 - r ^ 2) := by
      exact div_nonneg (by positivity) hdenr.le
    have htailCoeff : 0 ≤ 2 / (1 - r ^ 2) := by
      exact div_nonneg (by norm_num) hdenr.le
    dsimp [C]
    exact add_nonneg
      (mul_nonneg (by positivity) hmainCoeff)
      (mul_nonneg (mul_nonneg hd0 (by positivity)) htailCoeff)
  let ε : ℝ := min 1 (η / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min zero_lt_one (div_pos hη hC1)
  have hε0 : 0 ≤ ε := hεpos.le
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨F⟩ := TauCeti.DavisKahan.exists_approximateLeadingSingularFamily
    X k hεpos
  have hraw := transformed_prefix_le_kyFan_add_error
    B hd0 hr0 hr1 hε0 hA0 hA1 hX hXr F
  have hcountReal : (F.count : ℝ) ≤ (k : ℝ) := by exact_mod_cast F.count_le
  have hsubReal : ((k - F.count : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.sub_le k F.count
  have hεsq : ε ^ 2 ≤ ε := by nlinarith
  have herr :
      (F.count : ℝ) * uniformStablePairError B r ε +
          d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) ≤ η := by
    have hεchoice : ε * (C + 1) ≤ η := by
      have hmin : ε ≤ η / (C + 1) := min_le_right _ _
      calc
        ε * (C + 1) ≤ (η / (C + 1)) * (C + 1) :=
          mul_le_mul_of_nonneg_right hmin hC1.le
        _ = η := by field_simp
    let A : ℝ := ‖B.A0‖ + ‖B.A1‖
    let b : ℝ := ‖B.B01‖
    have hquad : b * ε ^ 2 ≤ b * ε := by
      exact mul_le_mul_of_nonneg_left hεsq (by dsimp [b]; positivity)
    have hnum :
        A * ε + 2 * r * b * ε + b * ε ^ 2 ≤
          (A + 2 * r * b + b) * ε := by
      calc
        A * ε + 2 * r * b * ε + b * ε ^ 2
            ≤ A * ε + 2 * r * b * ε + b * ε := by
              linarith [hquad]
        _ = (A + 2 * r * b + b) * ε := by ring
    have huniform :
        uniformStablePairError B r ε ≤
          (2 * (A + 2 * r * b + b) / (1 - r ^ 2)) * ε := by
      unfold uniformStablePairError
      dsimp [A, b] at hnum ⊢
      calc
        2 * ((‖B.A0‖ + ‖B.A1‖) * ε +
              2 * r * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) /
              (1 - r ^ 2)
            ≤ 2 * (((‖B.A0‖ + ‖B.A1‖) +
              2 * r * ‖B.B01‖ + ‖B.B01‖) * ε) /
              (1 - r ^ 2) := by
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hnum (by norm_num)) hdenr.le
        _ = (2 * ((‖B.A0‖ + ‖B.A1‖) +
              2 * r * ‖B.B01‖ + ‖B.B01‖) /
              (1 - r ^ 2)) * ε := by ring
    have huniform0 : 0 ≤ uniformStablePairError B r ε := by
      unfold uniformStablePairError
      positivity
    have hselectedError :
        (F.count : ℝ) * uniformStablePairError B r ε ≤
          ε * ((k : ℝ) *
            (2 * (A + 2 * r * b + b) / (1 - r ^ 2))) := by
      calc
        (F.count : ℝ) * uniformStablePairError B r ε
            ≤ (k : ℝ) * uniformStablePairError B r ε :=
              mul_le_mul_of_nonneg_right hcountReal huniform0
        _ ≤ (k : ℝ) *
              ((2 * (A + 2 * r * b + b) / (1 - r ^ 2)) * ε) := by
                exact mul_le_mul_of_nonneg_left huniform (by positivity)
        _ = ε * ((k : ℝ) *
              (2 * (A + 2 * r * b + b) / (1 - r ^ 2))) := by ring
    have htailCoeff0 :
        0 ≤ d * ((2 / (1 - r ^ 2)) * ε) := by positivity
    have htailError :
        d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) ≤
          ε * (d * (k : ℝ) * (2 / (1 - r ^ 2))) := by
      calc
        d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε)
            = ((k - F.count : ℕ) : ℝ) *
                (d * ((2 / (1 - r ^ 2)) * ε)) := by ring
        _ ≤ (k : ℝ) * (d * ((2 / (1 - r ^ 2)) * ε)) :=
              mul_le_mul_of_nonneg_right hsubReal htailCoeff0
        _ = ε * (d * (k : ℝ) * (2 / (1 - r ^ 2))) := by ring
    calc
      (F.count : ℝ) * uniformStablePairError B r ε +
          d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε)
          ≤ ε * ((k : ℝ) *
                (2 * (A + 2 * r * b + b) / (1 - r ^ 2))) +
              ε * (d * (k : ℝ) * (2 / (1 - r ^ 2))) :=
            add_le_add hselectedError htailError
      _ = ε * C := by
            dsimp [C, A, b]
            ring
      _ ≤ ε * (C + 1) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hε0
      _ ≤ η := hεchoice
  exact hraw.trans (by linarith)

/-- Sharp Ky Fan theorem for the canonical tangent operator. -/
theorem sharp_doubleAngleTangentOperator_kyFan
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    d * kyFanApproximationGauge k
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
      2 * kyFanApproximationGauge k B.B01 := by
  rw [TauCeti.DavisKahan.kyFanApproximationGauge_doubleAngleTangentOperator]
  exact sharp_transformed_prefix B hd0 hA0 hA1 hX hcontractive k

end CompleteSpaces

end

end DavisKahan
end TauCeti
