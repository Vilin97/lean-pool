/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SharpKyFan
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.StandardFanDominance
-- branch selection: the canonical contractive Riccati solution, and the
-- spectrum-to-form-bound bridge that feeds it the paper's hypotheses
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedCanonicalSolution
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SpectralOrder

/-! # Sharp Ideal -/

open TauCeti.DavisKahan.Angle


/-!
# Sharp standard-ideal `tan 2Theta`

Fan dominance is now applied as a theorem.  For both maximal and minimal
standard completions the clean common statement places the positive scalar
`d/2` on the tangent operator.  The maximal/Fatou specialization is then
unscaled using the repository's existing real-gauge theorem.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open DavisKahanExt
open ExactSinTheta

noncomputable section

universe u

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type u} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The sharp Ky Fan estimate in the orientation needed by Fan dominance. -/
private theorem half_mul_kyFan_le_adjoint
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    (d / 2) * kyFanApproximationGauge k
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
      kyFanApproximationGauge k B.B01.adjoint := by
  have hsharp := sharp_doubleAngleTangentOperator_kyFan
    B hd.le hA0 hA1 hX hcontractive k
  rw [kyFanApproximationGauge_adjoint]
  calc
    (d / 2) * kyFanApproximationGauge k
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) =
        (d * kyFanApproximationGauge k
          (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive)) / 2 := by
      ring
    _ ≤ kyFanApproximationGauge k B.B01 := by
      linarith

/-- Sharp endpoint for every standard symmetric completion, formulated in the
scale-invariant common form. -/
theorem sharp_standardSymmetricIdeal_scaled
    (I : TauCeti.SymmetricIdeal.StandardSymmetricIdeal)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : I.Mem B.B01) :
    I.Mem (((d / 2 : ℝ) : ℂ) •
        TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ∧
      I.gauge (((d / 2 : ℝ) : ℂ) •
          TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
        I.gauge B.B01 := by
  let T : E0 →L[ℂ] E1 :=
    TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive
  let S : E0 →L[ℂ] E1 := (((d / 2 : ℝ) : ℂ) • T)
  have hBadj : I.Mem B.B01.adjoint := I.mem_adjoint hB
  have hscalarNorm : ‖(((d / 2 : ℝ) : ℂ))‖ = d / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ d / 2)]
  have hdom : ∀ k : ℕ,
      kyFanApproximationGauge k S ≤
        kyFanApproximationGauge k B.B01.adjoint := by
    intro k
    simpa only [S, T, kyFanApproximationGauge_smul, hscalarNorm] using
      half_mul_kyFan_le_adjoint B hd hA0 hA1 hX hcontractive k
  have hfan : I.Mem S ∧ I.gauge S ≤ I.gauge B.B01.adjoint :=
    TauCeti.SymmetricIdeal.standard_fanDominance I hBadj hdom
  change I.Mem S ∧ I.gauge S ≤ I.gauge B.B01
  refine ⟨hfan.1, ?_⟩
  calc
    I.gauge S ≤ I.gauge B.B01.adjoint := hfan.2
    _ = I.gauge B.B01 := I.gauge_adjoint B.B01

/-- Maximal/Fatou source-norm endpoint in the paper's conventional scaling. -/
theorem sharp_symmetricNormingFunction
    (N : SymmetricNormingFunction)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : N.Mem B.B01) :
    N.Mem (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ∧
      d * N.gauge
          (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
        2 * N.gauge B.B01 := by
  let T : E0 →L[ℂ] E1 :=
    TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive
  have hBadj : N.Mem B.B01.adjoint :=
    (N.mem_adjoint_iff B.B01).mpr hB
  have hfan : ∀ k : ℕ,
      (d / 2) * kyFanApproximationGauge k T ≤
        kyFanApproximationGauge k B.B01.adjoint := by
    intro k
    exact half_mul_kyFan_le_adjoint B hd hA0 hA1 hX hcontractive k
  have h : N.Mem T ∧ (d / 2) * N.gauge T ≤ N.gauge B.B01.adjoint :=
    N.mul_gauge_le_of_all_mul_kyFan_le
      (A := T) (B := B.B01.adjoint) (c := d / 2)
      (by positivity) hBadj hfan
  change N.Mem T ∧ d * N.gauge T ≤ 2 * N.gauge B.B01
  refine ⟨h.1, ?_⟩
  calc
    d * N.gauge T = 2 * ((d / 2) * N.gauge T) := by ring
    _ ≤ 2 * N.gauge B.B01.adjoint :=
      mul_le_mul_of_nonneg_left h.2 (by norm_num)
    _ = 2 * N.gauge B.B01 := by
      rw [N.gauge_adjoint]

/-- Schatten-`p` maximal ideal endpoint for every `1 ≤ p`. -/
theorem sharp_schattenMaximal
    (p : ℝ) (hp : 1 ≤ p)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : (TauCeti.SymmetricIdeal.lpNormingFunction p hp).Mem B.B01) :
    (TauCeti.SymmetricIdeal.lpNormingFunction p hp).Mem
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ∧
      d * (TauCeti.SymmetricIdeal.lpNormingFunction p hp).gauge
          (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
        2 * (TauCeti.SymmetricIdeal.lpNormingFunction p hp).gauge B.B01 :=
  sharp_symmetricNormingFunction
    (TauCeti.SymmetricIdeal.lpNormingFunction p hp)
    B hd hA0 hA1 hX hcontractive hB

/-- Trace/nuclear specialization. -/
theorem sharp_nuclear
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : nuclearNormingFunction.Mem B.B01) :
    nuclearNormingFunction.Mem
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ∧
      d * nuclearNormingFunction.gauge
          (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
        2 * nuclearNormingFunction.gauge B.B01 :=
  sharp_symmetricNormingFunction nuclearNormingFunction
    B hd hA0 hA1 hX hcontractive hB

/-! ### Branch selection, so the caller supplies no branch

The endpoints above take the contractive Riccati solution `X` as **data**.
Davis and Kahan do not: their Section 8 *selects* it, from spectral separation
plus smallness of the off-diagonal block.  That selection is already in the
default build — `canonicalContractiveRiccatiSolution`, together with its
existence-and-uniqueness theorem — so the two compose, and the composite is the
paper's `tan 2Θ` theorem for an arbitrary unitarily invariant norm in an
arbitrary complex Hilbert space with **no branch supplied by the caller**.

The hypotheses are the printed ones: the wanted block's spectrum sits in
`[left, 0]`, the unwanted block's in `[d, ∞)`, and the coupling is small
relative to the gap.  The form bounds `sharp_symmetricNormingFunction` wants
are read off from those spectral containments by
`SpectralOrder.re_inner_le_of_spectrum_subset_Iic` and its lower
companion; the interval/exterior shape the Riccati selection wants is the same
data reassociated.

The selected `X` is *unique* among contractive solutions — see
`existsUnique_contractive_riccati_solution_of_spectrum_gap` — so the existential
below names one operator, not a class. -/

/-- **Davis--Kahan 1970 `tan 2Θ` for an arbitrary unitarily invariant norm, with
the acute branch selected rather than assumed.**

Spectral separation (`spectrum A₀ ⊆ [left, 0]`, `spectrum A₁ ⊆ [d, ∞)`) together
with smallness of the coupling (`2‖B₀₁‖ < d`) produces a contractive Riccati
solution — unique among contractive solutions — and the bound
`d · N(tan 2Θ) ≤ 2 · N(B₀₁)` for it, in an arbitrary complex Hilbert space and
for every `SymmetricNormingFunction`.

The caller supplies no branch: that is the difference from
`sharp_symmetricNormingFunction`, which takes `X` as data. -/
theorem sharp_symmetricNormingFunction_selectedBranch
    (N : SymmetricNormingFunction)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left d : ℝ} (hd : 0 < d) (hleft : left ≤ 0)
    (hA0spec : spectrum ℝ B.A0 ⊆ Set.Icc left 0)
    (hA1spec : spectrum ℝ B.A1 ⊆ Set.Ici d)
    (hsmall : 2 * ‖B.B01‖ < d)
    (hB : N.Mem B.B01) :
    ∃ (X : E0 →L[ℂ] E1) (hXc : ‖X‖ < 1), SolvesRiccati B X ∧
      N.Mem (TauCeti.DavisKahan.doubleAngleTangentOperator X hXc) ∧
        d * N.gauge (TauCeti.DavisKahan.doubleAngleTangentOperator X hXc) ≤
          2 * N.gauge B.B01 := by
  have hA0sa : IsSelfAdjoint B.A0 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr B.selfAdjoint0
  have hA1sa : IsSelfAdjoint B.A1 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr B.selfAdjoint1
  -- the form bounds the sharp endpoint runs on
  have hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0 := by
    intro z
    have h := SpectralOrder.re_inner_le_of_spectrum_subset_Iic B.A0
      hA0sa (c := 0) (fun r hr => (hA0spec hr).2) z
    simpa using h
  have hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ :=
    SpectralOrder.le_re_inner_of_spectrum_subset_Ici B.A1 hA1sa hA1spec
  -- the interval/exterior shape the Riccati selection runs on
  have hA1spec' : ∀ x ∈ spectrum ℝ B.A1, x ≤ left - d ∨ 0 + d ≤ x := by
    intro x hx
    exact Or.inr (by simpa using hA1spec hx)
  refine ⟨canonicalContractiveRiccatiSolution B hd hleft hA0spec hA1spec' hsmall,
    canonicalContractiveRiccatiSolution_norm_lt_one B hd hleft hA0spec hA1spec'
      hsmall,
    canonicalContractiveRiccatiSolution_solves B hd hleft hA0spec hA1spec'
      hsmall, ?_, ?_⟩ <;>
  · have h := sharp_symmetricNormingFunction N B hd hA0 hA1
      (canonicalContractiveRiccatiSolution_solves B hd hleft hA0spec hA1spec'
        hsmall)
      (canonicalContractiveRiccatiSolution_norm_lt_one B hd hleft hA0spec
        hA1spec' hsmall) hB
    first
      | exact h.1
      | exact h.2

end

end DavisKahan
end TauCeti
