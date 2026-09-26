/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Basic
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta
public import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.Basic

/-!
# Source labels and external analytic inputs

This file is the only place where the development records external
analytic source material.  It deliberately records metadata, not theorem
surfaces: precise Lean statements should be added only after the corresponding
provenance has been audited against the source.
-/

@[expose] public section

namespace Homogenization.HighContrast.EntryScale

open scoped BigOperators

namespace Sources

/-- Localization estimate, `e.localization`. -/
def localization : SourceLabel :=
  SourceLabel.highMomentPaper "e.localization" 511
end Sources


/-- Exponents fixed by the high-contrast weak-norm machinery.

This record is indexed by the dimension `d` and carries the manuscript
quantitative coarse-grained ellipticity parameters `params` so that the
source-max edge-loss gaps can be stated as *pure numeric* inequalities on the
record's own parameters (no quantifiers over laws).  Consumers recover the
per-`(P4)` form via `sourceMaxLowerGap_of_params`/`sourceMaxUpperGap_of_params`
using `hP4.params = hc.params`.

Source: the high-moment paper (Armstrong–Kuusi–Loher, to appear), and
ultimately the high-contrast manuscript, label `l.weaknorms.moreproto`.
-/
structure HighContrastExponents (d : ℕ) where
  /-- The manuscript quantitative coarse-grained ellipticity parameters that the
  source-max gaps are stated against. -/
  params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d
  rhoM : ℝ
  beta : ℝ
  zeta : ℝ
  rhoM_pos : 0 < rhoM
  beta_pos : 0 < beta
  one_lt_zeta : 1 < zeta
  zeta_lt_two : zeta < 2
  /--
  Memory decay rate `kappa_H = min{rho_M, beta, beta_edge}` at which the
  Lyapunov memory variable `H` contracts.  It is bounded above by the union-bound
  exponent `rho_M` and the response exponent `beta`, while `rho_M` retains its
  other (union-bound / stochastic-decay) roles.

  Source: the high-moment paper (Armstrong–Kuusi–Loher, to appear),
  memory-decay discussion `s.memory` and `l.lyapunov`.
  -/
  kappaH : ℝ
  kappaH_pos : 0 < kappaH
  kappaH_le_rhoM : kappaH ≤ rhoM
  kappaH_le_beta : kappaH ≤ beta
  /--
  Source-max edge-loss compatibility at the lower ellipticity exponent.

  This is the exponent gap used by the faithful `p.HC.CR` source-max argument:
  the stochastic source weight must decay strictly slower than the lower
  Section 5.2 edge-loss exponent.  Stated as a pure numeric inequality on the
  record's own parameters.
  -/
  sourceMaxLowerGap :
    rhoM <
      params.sLower +
        Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBetaParams
          params
  /--
  Source-max edge-loss compatibility at the upper ellipticity exponent.

  This is the matching upper-edge gap for the same manuscript source-max
  argument.
  -/
  sourceMaxUpperGap :
    rhoM <
      params.sUpper +
        Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBetaParams
          params

namespace HighContrastExponents

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations

/-- Per-`(P4)` form of the lower source-max gap: for any law whose `(P4)`
parameters match the record, the gap holds against `section53CoarseFluctuationBeta`. -/
theorem sourceMaxLowerGap_of_params {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d} (hc : HighContrastExponents d)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (h : hP4.params = hc.params) :
    hc.rhoM < hP4.sLower + section53CoarseFluctuationBeta hP4 := by
  have hg := hc.sourceMaxLowerGap
  rw [← h] at hg
  simpa using hg

/-- Per-`(P4)` form of the upper source-max gap. -/
theorem sourceMaxUpperGap_of_params {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d} (hc : HighContrastExponents d)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (h : hP4.params = hc.params) :
    hc.rhoM < hP4.sUpper + section53CoarseFluctuationBeta hP4 := by
  have hg := hc.sourceMaxUpperGap
  rw [← h] at hg
  simpa using hg

end HighContrastExponents

/-- Constants in the localization and small-contrast handoff.

Source: `e.localization` and `e.small.contrast`.
-/
structure LocalizationSmallContrastConstants where
  C_loc : ℝ
  beta_loc : ℝ
  delta0 : ℝ
  C_sc : ℝ
  alpha0 : ℝ
  C_loc_nonneg : 0 ≤ C_loc
  beta_loc_pos : 0 < beta_loc
  delta0_pos : 0 < delta0
  delta0_le_one : delta0 ≤ 1
  C_sc_pos : 0 < C_sc
  alpha0_pos : 0 < alpha0

/-- Typed external handoff for localization and the small-contrast theorem.

Source: `e.localization` and `e.small.contrast`.  This is one of the audited
external inputs allowed at final assembly; downstream theorems should consume
this surface rather than assuming already assembled final decay.

The localization and small-contrast fields are guarded by the requirement
`hP4.params = hc.params`: the fixed constants below are the ones produced by the
Section 5.5/5.6 source theorems at the record's own manuscript parameters, so the
bounds only fire for laws whose `(P4)` parameters agree with `hc.params`.  This
guard is exactly what makes the record inhabitable (see `RecordsFinal.lean`).
-/
structure LocalizationSmallContrastInput
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d)
    extends LocalizationSmallContrastConstants where
  localization :
    ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
      (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
      (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
      (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
      hP4.params = hc.params →
      ∀ {k n : ℕ},
      k ≤ n →
        Homogenization.Book.Ch05.thetaAtScale hP hStruct (n : ℤ) ≤
            Homogenization.Book.Ch05.Section55.shiftedWidetildeThetaAtScale P
              (n : ℤ) hP4 (2 * hc.beta) ∧
          Homogenization.Book.Ch05.Section55.shiftedWidetildeThetaAtScale P
              (n : ℤ) hP4 (2 * hc.beta) ≤
            Homogenization.Book.Ch05.thetaAtScale hP hStruct (k : ℤ) +
              C_loc * (3 : ℝ) ^ (-(beta_loc * ((n - k : ℕ) : ℝ))) *
                Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  small_contrast :
    ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
      (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
      (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
      (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
      hP4.params = hc.params →
      ∀ {N : ℕ},
      Homogenization.Book.Ch05.Section55.shiftedWidetildeThetaAtScale P
          (N : ℤ) hP4 (2 * hc.beta) - 1 ≤ delta0 →
        ∀ n : ℕ,
          Homogenization.Book.Ch05.thetaAtScale hP hStruct
              ((N + n : ℕ) : ℤ) - 1 ≤
            C_sc * (3 : ℝ) ^ (-(alpha0 * (n : ℝ)))

/-- Parameters in the high centered block moment hypothesis.

Source: `a.HM`, `e.HM`, and `e.Q.large`.  The fields
`holderExponentFloor`, `p4Params`, and `two_mul_p4_xi_le_Q` record the finite
Holder-exponent thresholds from the high-contrast estimate; the TeX
requirement is represented by the concrete inequalities
`holderExponentFloor < Q` and `2 * xi <= Q`.  The latter is relative to the
fixed quantitative coarse-grained ellipticity parameters used by the theorem;
it is not quantified over every possible witness for every law.
-/
structure HighCenteredMomentParameters (d : ℕ) (hc : HighContrastExponents d) where
  p_hm : ℝ
  Q : ℝ
  gamma : ℝ
  C_Q : ℝ
  holderExponentFloor : ℝ
  p4Params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d
  p_hm_nonneg : 0 ≤ p_hm
  two_le_Q : 2 ≤ Q
  gamma_pos : 0 < gamma
  C_Q_nonneg : 0 ≤ C_Q
  Q_mul_rhoM_gt : Q * hc.rhoM > (d : ℝ) + 4
  holderExponentFloor_nonneg : 0 ≤ holderExponentFloor
  holderExponentFloor_lt_Q : holderExponentFloor < Q
  two_mul_p4_xi_le_Q : 2 * (p4Params.xi : ℝ) ≤ Q

/-- Constants for the old polynomial subthreshold contribution in `a.HM`.

Source: the high-moment paper (Armstrong–Kuusi–Loher, to appear).  This records
only the polynomial prefactor before the weak-norm weight is used; the
geometric buffer absorption is proved in `MomentConsequences.lean`.
-/
structure SubthresholdPolynomialMomentParameters where
  C_sub : ℝ
  A_sub : ℝ
  C_sub_nonneg : 0 ≤ C_sub

/-- The deterministic envelope appearing in the high-moment input `a.HM`.

The source note writes this as `C_Q 3^{-Q γ (j-N)}` for every `j ≥ N`,
uniformly over triadic translates.  We keep the `j - N` dependence explicit
so later results can substitute this exact scale decay into the descendant
union bound.
-/
noncomputable def highCenteredMomentEnvelope {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (N j : ℕ) : ENNReal :=
  ENNReal.ofReal
    (hm.C_Q *
      Real.rpow (3 : ℝ) (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ)))

/-- Moving the initial scale of the high-moment envelope forward only weakens
the decay requirement. -/
theorem highCenteredMomentEnvelope_le_of_start_le
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {N k j : ℕ}
    (hNk : N ≤ k) :
    highCenteredMomentEnvelope hm N j ≤ highCenteredMomentEnvelope hm k j := by
  dsimp [highCenteredMomentEnvelope]
  have hQ_pos : 0 < hm.Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hm.two_le_Q
  have hQg_pos : 0 < hm.Q * hm.gamma := mul_pos hQ_pos hm.gamma_pos
  have hsub : j - k ≤ j - N := Nat.sub_le_sub_left hNk j
  have hsub_real : ((j - k : ℕ) : ℝ) ≤ ((j - N : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hexp :
      -(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ) ≤
        -(hm.Q * hm.gamma) * ((j - k : ℕ) : ℝ) := by
    nlinarith
  have hrpow :
      Real.rpow (3 : ℝ) (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ)) ≤
        Real.rpow (3 : ℝ) (-(hm.Q * hm.gamma) * ((j - k : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hrpow hm.C_Q_nonneg)

/-- The scale-uniform high centered-moment assumption from `a.HM`/`e.HM`.

Here `centeredBlockDeviation j Q ω` denotes the nonnegative matrix-normalized
observable
`|Ahom_j^{-1/2}(A(Q)-Ahom_j)Ahom_j^{-1/2}|` attached to a triadic cube `Q` of
scale `j`.  The hypothesis is intentionally only a one-block input: descendant
counts, weak-norm weights, terminal normalization losses, and union bounds are
proved downstream rather than built into this assumption.
-/
structure HighCenteredMomentEstimate
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (μ : MeasureTheory.Measure Ω) (N : ℕ)
    (centeredBlockDeviation :
      ℕ → Homogenization.TriadicCube d → Ω → ENNReal) : Prop where
  measurable :
    ∀ {j : ℕ}, N ≤ j → ∀ {Q : Homogenization.TriadicCube d},
      Q.scale = (j : ℤ) →
        AEMeasurable (fun ω => centeredBlockDeviation j Q ω ^ hm.Q) μ
  moment_le :
    ∀ {j : ℕ}, N ≤ j → ∀ {Q : Homogenization.TriadicCube d},
      Q.scale = (j : ℤ) →
        ∫⁻ ω, centeredBlockDeviation j Q ω ^ hm.Q ∂ μ ≤
          highCenteredMomentEnvelope hm N j

namespace HighCenteredMomentEstimate

/-- The high centered-moment hypothesis may be restarted at any later scale. -/
theorem of_start_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    {hm : HighCenteredMomentParameters d hc} {μ : MeasureTheory.Measure Ω}
    {N k : ℕ}
    {centeredBlockDeviation :
      ℕ → Homogenization.TriadicCube d → Ω → ENNReal}
    (hNk : N ≤ k)
    (hHM : HighCenteredMomentEstimate hm μ N centeredBlockDeviation) :
    HighCenteredMomentEstimate hm μ k centeredBlockDeviation where
  measurable := by
    intro j hkj Q hQ
    exact hHM.measurable (hNk.trans hkj) hQ
  moment_le := by
    intro j hkj Q hQ
    exact (hHM.moment_le (hNk.trans hkj) hQ).trans
      (highCenteredMomentEnvelope_le_of_start_le hm hNk)

end HighCenteredMomentEstimate

/-- The subthreshold second-moment envelope after applying the weak-norm gap.

The source paragraph says that before the weak-norm weight the old
high-contrast bound contributes at most `C (2+T)^A`.  Since the subthreshold
scales have `m - j >= m - N`, the squared weak weight contributes
`3^{-2 rho_M (m-N)}`.
-/
noncomputable def subthresholdPolynomialMomentEnvelope
    {d : ℕ} (hc : HighContrastExponents d)
    (sub : SubthresholdPolynomialMomentParameters) (T : ℝ) (n : ℕ) :
    ENNReal :=
  ENNReal.ofReal
    (sub.C_sub * (((2 + T : ℝ) ^ sub.A_sub) *
      (3 : ℝ) ^ (-(2 * hc.rhoM) * (n : ℝ))))

/-- Root-level subthreshold envelope from the old high-contrast input.

This is the same source paragraph as `subthresholdPolynomialMomentEnvelope`,
but before squaring.  It is the shape needed by the lower-edge coefficient
comparison, whose residual local-window terms are controlled as
`L^{xi_edge}` roots rather than by the `L^2` union-bound estimate.
-/
noncomputable def subthresholdPolynomialRootEnvelope
    {d : ℕ} (hc : HighContrastExponents d)
    (sub : SubthresholdPolynomialMomentParameters) (T : ℝ) (n : ℕ) : ℝ :=
  sub.C_sub * (((2 + T : ℝ) ^ sub.A_sub) *
    (3 : ℝ) ^ (-(hc.rhoM) * (n : ℝ)))

/-- Source-facing old polynomial subthreshold input from `a.HM`.

Here `subthresholdMax m` denotes the already weighted contribution
`\mathcal M_m^{<N}` from scales `j < N`, including the deterministic drift
assigned to that range.  The only analytic content assumed here is the old
high-contrast polynomial bound from the corrected note; the buffer that makes
it small is proved downstream.
-/
structure SubthresholdPolynomialMomentEstimate
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (hc : HighContrastExponents d)
    (sub : SubthresholdPolynomialMomentParameters)
    (μ : MeasureTheory.Measure Ω) (T : ℝ) (N : ℕ)
    (subthresholdMax : ℕ → Ω → ℝ) : Prop where
  aestronglyMeasurable :
    ∀ {m : ℕ}, N ≤ m →
      MeasureTheory.AEStronglyMeasurable (subthresholdMax m) μ
  moment_le :
    ∀ {m : ℕ}, N ≤ m →
      ∫⁻ ω, ‖subthresholdMax m ω‖ₑ ^ (2 : ℝ) ∂ μ ≤
        subthresholdPolynomialMomentEnvelope hc sub T (m - N)
end Homogenization.HighContrast.EntryScale
