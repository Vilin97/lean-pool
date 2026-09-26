/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingPotential


/-!
# Conservativity from the resolvent of the constant observable

A sub-Markov kernel semigroup loses no mass as soon as its resolvent at one positive shift has
the full mass of the exponential weight,

  `lam * R_lam 1 = 1`   (`SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one`).

The transition mass is nonincreasing in time (`SubMarkovKernelSemigroup.measure_univ_le_of_le`),
because the Chapman--Kolmogorov law integrates a mass at most one against an earlier transition
law.  The hypothesis says that the Laplace transform of the transition mass equals the Laplace
transform of the constant observable one; both integrands are integrable and ordered, so they
agree at almost every time, and monotonicity in time upgrades this to every time.

The converse is immediate from the mass of the exponential weight
(`SubMarkovKernelSemigroup.IsConservative.kernelResolvent_one`,
`SubMarkovKernelSemigroup.IsConservative.ofReal_mul_kernelResolvent_one`), so the criterion is an
equivalence and not merely a sufficient condition.

No topology on the state space is used.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)

/-- **The transition mass is nonincreasing in time.**  A later transition law is an average of
transition masses at most one against an earlier one. -/
theorem measure_univ_le_of_le {u v : NNReal} (huv : u ≤ v) (x : alpha) :
    P v x univ ≤ P u x univ := by
  obtain ⟨w, rfl⟩ := exists_add_of_le huv
  rw [P.add_apply' u w x MeasurableSet.univ]
  calc ∫⁻ y, P w y univ ∂P u x ≤ ∫⁻ _y, 1 ∂P u x :=
        lintegral_mono fun y ↦ P.measure_univ_le_one w y
    _ = P u x univ := lintegral_one

/-- The Laplace transform of the constant observable one at a positive shift. -/
theorem lintegral_expWeight_one {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) = ENNReal.ofReal lam⁻¹ := by
  have hmass : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam = laplaceWeight lam univ :=
    lintegral_one
  have hweight : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) * 1 :=
    lintegral_laplaceWeight lam measurable_const
  simp only [mul_one] at hweight
  rw [← hweight, hmass, laplaceWeight_univ hlam]

/-- **Conservativity from the resolvent of the constant observable.**  If at one positive shift
the shift times the kernel resolvent of the constant observable one is one, then no transition
law loses mass. -/
theorem isConservative_of_kernelResolvent_one {lam : ℝ} (hlam : 0 < lam)
    (hone : ∀ x, ENNReal.ofReal lam * P.kernelResolvent lam (fun _ ↦ 1) x = 1) :
    P.IsConservative := by
  have hlam0 : ENNReal.ofReal lam ≠ 0 := by
    simpa using hlam
  have hlamtop : ENNReal.ofReal lam ≠ ⊤ := ENNReal.ofReal_ne_top
  intro t x
  -- the resolvent of the constant observable one carries the full weight
  have hmass : P.kernelResolvent lam (fun _ ↦ 1) x = ENNReal.ofReal lam⁻¹ := by
    have hcancel : (ENNReal.ofReal lam)⁻¹ *
        (ENNReal.ofReal lam * P.kernelResolvent lam (fun _ ↦ 1) x) =
        P.kernelResolvent lam (fun _ ↦ 1) x := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlam0 hlamtop, one_mul]
    rw [← hcancel, hone x, mul_one, ← ENNReal.ofReal_inv_of_pos hlam]
  -- the two integrands: the weighted transition mass and the weight itself
  have hprofile : P.kernelResolvent lam (fun _ ↦ 1) x =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ := by
    unfold kernelResolvent
    exact setLIntegral_congr_fun measurableSet_Ioi fun s _hs ↦ by rw [lintegral_one]
  have hle : ∀ s : ℝ, ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ ≤
      ENNReal.ofReal (Real.exp (-lam * s)) := by
    intro s
    calc ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ
        ≤ ENNReal.ofReal (Real.exp (-lam * s)) * 1 :=
          mul_le_mul' le_rfl (P.measure_univ_le_one _ x)
      _ = ENNReal.ofReal (Real.exp (-lam * s)) := mul_one _
  have hFtop : (∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ) ≠ ⊤ := by
    rw [← hprofile, hmass]
    exact ENNReal.ofReal_ne_top
  have hGF : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s))) ≤
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ := by
    rw [← hprofile, hmass, lintegral_expWeight_one hlam]
  have hFG := ae_eq_of_ae_le_of_lintegral_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (Eventually.of_forall hle) hFtop (measurable_laplaceDensity lam).aemeasurable hGF
  -- almost every positive time carries the full mass
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), P (Real.toNNReal s) x univ = 1 := by
    filter_upwards [hFG] with s hs
    have hpos : ENNReal.ofReal (Real.exp (-lam * s)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.exp_pos _
    refine (ENNReal.mul_right_inj hpos ENNReal.ofReal_ne_top).mp ?_
    rw [hs, mul_one]
  -- a later time with the full mass forces the full mass at the given time
  have hinterval : MeasurableSet (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2)) := measurableSet_Ioo
  have hsub : Ioo ((t : ℝ) + 1) ((t : ℝ) + 2) ⊆ Ioi (0 : ℝ) := fun s hs ↦
    lt_trans (by positivity) hs.1
  have haeI : ∀ᵐ s ∂(volume.restrict (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2))),
      P (Real.toNNReal s) x univ = 1 :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hae
  have hne : volume.restrict (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2)) ≠ 0 := by
    intro hzero
    have hmeasure : volume.restrict (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2))
        (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2)) = 0 := by
      rw [hzero]
      rfl
    rw [Measure.restrict_apply_self, Real.volume_Ioo] at hmeasure
    exact absurd hmeasure (by
      simp only [add_sub_add_left_eq_sub, ENNReal.ofReal_eq_zero, tsub_le_iff_right, zero_add,
        Nat.not_ofNat_le_one, not_false_eq_true])
  have : (ae (volume.restrict (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2)))).NeBot :=
    ae_neBot.mpr hne
  obtain ⟨s, hsone, hsmem⟩ := (haeI.and (self_mem_ae_restrict hinterval)).exists
  have hts : t ≤ Real.toNNReal s := by
    have hcoe : Real.toNNReal (t : ℝ) = t := Real.toNNReal_coe
    rw [← hcoe]
    exact Real.toNNReal_le_toNNReal (le_of_lt (lt_trans (by linarith) hsmem.1))
  refine le_antisymm (P.measure_univ_le_one t x) ?_
  calc (1 : ℝ≥0∞) = P (Real.toNNReal s) x univ := hsone.symm
    _ ≤ P t x univ := P.measure_univ_le_of_le hts x

/-- **The resolvent of the constant observable one under conservativity.**  A conservative
semigroup carries the full mass of the exponential weight, so its kernel resolvent of the
constant observable one is the reciprocal of the shift. -/
theorem IsConservative.kernelResolvent_one {P : SubMarkovKernelSemigroup alpha}
    (hP : P.IsConservative) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    P.kernelResolvent lam (fun _ ↦ 1) x = ENNReal.ofReal lam⁻¹ := by
  rw [← lintegral_expWeight_one hlam]
  unfold kernelResolvent
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ht ↦ ?_
  rw [lintegral_one, hP _ x, mul_one]

/-- **The conservativity criterion is an equivalence.**  For a conservative semigroup the shift
times the kernel resolvent of the constant observable one is one at every positive shift, which
is the converse of `isConservative_of_kernelResolvent_one`. -/
theorem IsConservative.ofReal_mul_kernelResolvent_one {P : SubMarkovKernelSemigroup alpha}
    (hP : P.IsConservative) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    ENNReal.ofReal lam * P.kernelResolvent lam (fun _ ↦ 1) x = 1 := by
  rw [hP.kernelResolvent_one hlam x, ← ENNReal.ofReal_mul hlam.le,
    mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]

end MarkovProcess.SubMarkovKernelSemigroup

end

end PortComputability
