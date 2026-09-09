/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStateRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.FiniteHeadClass

/-!
# Weighted bounds for the literal signed cross-covariance defect

The covariance class follows from the actual supported harmonic families.
The requested moving stress preserves the residual class.  Their difference
is retained on every band; only the supplied tail identity makes it vanish.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SignedCrossDefectClass

open Set WeightedClasses MeanIncrementBounds CorrectionState SignedMeanGain LabelSumBounds
open scoped ContDiff BigOperators

/-- Point: an abbreviation for `SignedMeanGain.Point`. -/
abbrev Point := SignedMeanGain.Point

section Family

variable {D ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {P : ι → ℕ → D → ℝ} {α δ β η : ℝ}

/-- The primary coefficient bound is recovered from the old coefficient
and the actual old-minus-primary bound in `SignedFamily`. -/
theorem primary_bounds (f : SignedFamily s P α δ β η) (hαδ : α ≤ δ) :
    ∀ i j, UniformWaveClass s P α (fun l n x => (f.primary l).velocity n i j x) := by
  intro i j
  apply ((f.old_bounds i j).sub ((f.difference_bounds i j).mono_exponent hαδ)).congr
  intro l n x _
  exact sub_sub_cancel _ _

/-- The actual covariance of the two assembled fields has the sum of
their exponents.  Native support eliminates cross-label products. -/
theorem crossTensor_mem (f : SignedFamily s P α δ β η) (a : Assembly f)
    (hαδ : α ≤ δ) : TensorClass s (α + β) (crossTensor f a) := by
  have hcarrier (l : ι) : SameCarrier (f.primary l) (f.tangent l) :=
    ⟨(f.tangent_carrier l).frequency.trans (f.primary_carrier l).frequency.symm,
      (f.tangent_carrier l).phase.trans (f.primary_carrier l).phase.symm,
      (f.tangent_carrier l).angular.trans (f.primary_carrier l).angular.symm⟩
  have hangular (l : ι) (n : ℕ) : (f.primary l).angularFrequency n ≠ 0 := by
    rw [(f.primary_carrier l).angular]
    exact f.angular_ne_zero l n
  have hb (i j : Fin 3) : MeanClass s (α + β)
      (bilinearCovariance (primaryField f a) (tangentField f a) i j) :=
    harmonic_covariance_sum_mem a.labels a.label a.injective a.level
      a.window a.window_continuous a.auxiliary f.primary f.tangent f.bandwidth
      f.primary_band (fun l => (hcarrier l).frequency) (fun l => (hcarrier l).phase)
      (fun l => (hcarrier l).angular) (primary_bounds f hαδ) f.tangent_bounds
      f.envelope_nonneg f.envelope_le_one hangular a.primary_support a.tangent_support i j
  intro i j
  change MeanClass s (α + β)
    (bilinearCovariance (primaryField f a) (tangentField f a) i j +
      bilinearCovariance (tangentField f a) (primaryField f a) i j)
  rw [bilinearCovariance_comm (tangentField f a) (primaryField f a) i j]
  exact (hb i j).add (hb j i)

end Family

/-- The actual moving primitive retains the exact radial weight and
costs no band exponent. -/
theorem physicalSigma_mem (G : Geometry) (e : ℕ) {r : MeanIncrementBounds.Field Point} {α : ℝ}
    (hr : SmoothOn G.domain r)
    (hs : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (r n))
    (hc : MeanClass G.strip α r) : MeanClass G.strip α (physicalSigma G e r) :=
  LocalSignedRequest.meanClass_physicalBarSigma G.region G.patch e G.left_pos G.right_pos
    G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one hr hs hc

/-- A baseline class for the literal cross defect.  There is no covariance
cancellation hypothesis, either on the initial bands or on the tail. -/
theorem defect_mem (G : Geometry) {ι : Type} {P : ι → ℕ → Point → ℝ}
    {α δ β η : ℝ} (f : SignedFamily G.strip P α δ β η) (a : Assembly f)
    (hαδ : α ≤ δ) (i j : Fin 3) (e : ℕ) (r : MeanIncrementBounds.Field Point)
    (hS : SmoothOn G.domain (crossTensor f a i j))
    (hr : SmoothOn G.domain r)
    (hs : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (r n))
    (hc : MeanClass G.strip (α + β) r) :
    MeanClass G.strip (α + β)
      (StateMomentBalances.meanBar (crossTensor f a i j) - physicalSigma G e r) :=
  Class.sub (G.average_mem hS (crossTensor_mem f a hαδ i j)) (physicalSigma_mem G e hr hs hc)

/-- The same fixed finite-head cutoff yields every exponent.  The only
equality premise is the actual covariance identity on the tail. -/
theorem defect_all_exponents (G : Geometry) {ι : Type} {P : ι → ℕ → Point → ℝ}
    {α δ β η : ℝ} (f : SignedFamily G.strip P α δ β η) (a : Assembly f)
    (hαδ : α ≤ δ) (i j : Fin 3) (e : ℕ) (r : MeanIncrementBounds.Field Point)
    (hS : SmoothOn G.domain (crossTensor f a i j))
    (hr : SmoothOn G.domain r)
    (hs : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (r n))
    (hc : MeanClass G.strip (α + β) r) (N : ℕ)
    (htail : ∀ n, N ≤ n → ∀ x ∈ G.strip.domain,
      StateMomentBalances.meanBar (crossTensor f a i j) n x = physicalSigma G e r n x) :
    ∀ γ : ℝ, MeanClass G.strip γ
      (StateMomentBalances.meanBar (crossTensor f a i j) - physicalSigma G e r) := by
  apply FiniteHeadClass.meanClass_all_exponents (defect_mem G f a hαδ i j e r hS hr hs hc) N
  intro n hn x hx
  simp only [Pi.sub_apply, htail n hn x hx, sub_self]

/-- Specialization to the exponents of the actual signed step. -/
theorem actual_defect_mem (G : Geometry) {ι : Type} {P : ι → ℕ → Point → ℝ}
    {σ κ : ℝ} (f : SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : Assembly f)
    (i j : Fin 3) (e : ℕ) (r : MeanIncrementBounds.Field Point)
    (hS : SmoothOn G.domain (crossTensor f a i j))
    (hr : MovingField G r) (hc : MeanClass G.strip (1 + σ - κ) r) :
    MeanClass G.strip (1 + σ - κ)
      (StateMomentBalances.meanBar (crossTensor f a i j) - physicalSigma G e r) := by
  have he : (1 / 2 : ℝ) + (1 / 2 + σ - κ) = 1 + σ - κ := by ring
  have hc' : MeanClass G.strip ((1 / 2 : ℝ) + (1 / 2 + σ - κ)) r := by
    simpa only [he] using hc
  simpa only [he] using defect_mem G f a (by norm_num) i j e r hS hr.smooth
    (MeanStateRegularity.MovingField.movingSupport hr) hc'

/-- Both literal defects of the signed mean update have the baseline
residual exponent, with no discarded initial bands. -/
theorem residual_defects_mem (G : Geometry) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (f : SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : Assembly f)
    (hS : ∀ i j, MovingField G (crossTensor f a i j))
    (hθreg : MovingField G (u.thetaResidual c))
    (hzreg : MovingField G (u.axialResidual c))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c)) :
    MeanClass G.strip (1 + σ - κ)
      (StateMomentBalances.meanBar (crossTensor f a 0 1) - physicalSigma G 2 (u.thetaResidual c)) ∧
    MeanClass G.strip (1 + σ - κ)
      (StateMomentBalances.meanBar (crossTensor f a 0 2) - physicalSigma G 1 (u.axialResidual c)) :=
  ⟨actual_defect_mem G f a 0 1 2 _ (hS 0 1).smooth hθreg hθ,
    actual_defect_mem G f a 0 2 1 _ (hS 0 2).smooth hzreg hz⟩

/-- The requested-stress identity is required only for bands `n ≥ N`.
The literal defects remain present on all earlier bands, in every class. -/
theorem residual_defects_all_exponents (G : Geometry) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (f : SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : Assembly f)
    (hS : ∀ i j, MovingField G (crossTensor f a i j))
    (hθreg : MovingField G (u.thetaResidual c))
    (hzreg : MovingField G (u.axialResidual c))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c)) (N : ℕ)
    (htail : ∀ n, N ≤ n → ∀ x ∈ G.strip.domain, ∀ i : Fin 2,
      StateMomentBalances.meanBar (crossTensor f a 0 i.succ) n x =
        LocalSignedRequest.requestedStress G.patch G.coord c u n x i) :
    ∀ γ : ℝ,
      MeanClass G.strip γ
        (StateMomentBalances.meanBar (crossTensor f a 0 1) - physicalSigma G 2 (u.thetaResidual c))
            ∧
      MeanClass G.strip γ
        (StateMomentBalances.meanBar (crossTensor f a 0 2) - physicalSigma G 1 (u.axialResidual c))
            := by
  obtain ⟨hbaseθ, hbasez⟩ := residual_defects_mem G c u f a hS hθreg hzreg hθ hz
  have hzeroθ : ∀ n, N ≤ n → ∀ x ∈ G.strip.domain,
      (StateMomentBalances.meanBar (crossTensor f a 0 1) - physicalSigma G 2 (u.thetaResidual c)) n
          x = 0 := by
    intro n hn x hx
    have he := htail n hn x hx 0
    change StateMomentBalances.meanBar (crossTensor f a 0 1) n x =
      physicalSigma G 2 (u.thetaResidual c) n x at he
    exact sub_eq_zero.mpr he
  have hzeroz : ∀ n, N ≤ n → ∀ x ∈ G.strip.domain,
      (StateMomentBalances.meanBar (crossTensor f a 0 2) - physicalSigma G 1 (u.axialResidual c)) n
          x = 0 := by
    intro n hn x hx
    have he := htail n hn x hx 1
    change StateMomentBalances.meanBar (crossTensor f a 0 2) n x =
      physicalSigma G 1 (u.axialResidual c) n x at he
    exact sub_eq_zero.mpr he
  exact fun γ => ⟨FiniteHeadClass.meanClass_all_exponents hbaseθ N hzeroθ γ,
    FiniteHeadClass.meanClass_all_exponents hbasez N hzeroz γ⟩

/-- Primitive incoming fields and the actual reconstructed pressure give
the residual regularity needed by the preceding theorem. -/
theorem residual_defects_all_exponents_of_primitive
    (G : Geometry) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (f : SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : Assembly f)
    (hS : ∀ i j, MovingField G (crossTensor f a i j))
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : (VariableGaugeMean.reconstructState G.gauge c u).pressure = u.pressure)
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c)) (N : ℕ)
    (htail : ∀ n, N ≤ n → ∀ x ∈ G.strip.domain, ∀ i : Fin 2,
      StateMomentBalances.meanBar (crossTensor f a 0 i.succ) n x =
        LocalSignedRequest.requestedStress G.patch G.coord c u n x i) :
    ∀ γ : ℝ,
      MeanClass G.strip γ
        (StateMomentBalances.meanBar (crossTensor f a 0 1) - physicalSigma G 2 (u.thetaResidual c))
            ∧
      MeanClass G.strip γ
        (StateMomentBalances.meanBar (crossTensor f a 0 2) - physicalSigma G 1 (u.axialResidual c))
            := by
  have Hg : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c
      u := by
    simpa only [G.inner_eq, G.outer_eq] using H
  have hθreg : MovingField G (u.thetaResidual c) := H.theta G.patch.a_pos G.patch.a_lt_b
  have hzreg : MovingField G (u.axialResidual c) := by
    have he := Hg.axial_reconstructed G.inner_pos G.exponent_pos G.length_eq hfixed
    simp only [G.inner_eq, G.outer_eq] at he
    exact he
  exact residual_defects_all_exponents G c u f a hS hθreg hzreg hθ hz N htail

end NavierStokes.SignedCrossDefectClass
