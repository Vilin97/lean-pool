/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientPotential
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientRemainder
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.WeakPressureSlice

/-! # The selected weak pressure gradient on one slice

Display (3.5) of the pressure-gradient section estimates the weak spatial
gradient of a pressure slice after the local decomposition
`p = p₁ + p_har + (p₇ + p₈)`.  The first summand is a coordinate sum of
Newtonian derivative potentials of a divergence-form source `V` and is
differentiated by the Calderón–Zygmund selection; the second is smooth on the
inner ball and is differentiated classically; the third is differentiated by
its own potential identities.

This file performs the assembly: it produces one `Vec3`-valued slice field
whose coordinates are locally integrable, which lies in `L^{6/5}` on the inner
set, which is the coordinate weak gradient of the pressure slice there, and
whose coordinate norms obey the three-term bound of display (3.5).
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

private theorem eLpNorm_six_fifths_add_le {μ : Measure Vec3} (a b : Vec3 → ℝ) :
    eLpNorm (fun x => a x + b x) (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm a (ENNReal.ofReal (6 / 5 : ℝ)) μ +
        eLpNorm b (ENNReal.ofReal (6 / 5 : ℝ)) μ :=
  eLpNorm_add_le (f := a) (g := b) (μ := μ) (p := ENNReal.ofReal (6 / 5 : ℝ))
    (ENNReal.one_le_ofReal.2 (by norm_num))

/-- Each coordinate of a globally `L^{6/5}` vector field is locally integrable
on every set.  This is the local integrability that display (3.5) requires of
the Calderón–Zygmund part of the selected gradient. -/
theorem potentialComponent_locallyIntegrableOn {Dpot : Vec3 → Vec3}
    (hDmem : MemLp Dpot (ENNReal.ofReal (6 / 5 : ℝ)) volume) (k : Fin 3)
    (B : Set Vec3) :
    LocallyIntegrableOn (fun x => Dpot x k) B volume := by
  have hmeas : AEStronglyMeasurable (fun x => Dpot x k) volume :=
    (ContinuousLinearMap.proj (R := ℝ) k).continuous.comp_aestronglyMeasurable
      hDmem.aestronglyMeasurable
  have hcomp : eLpNorm (fun x => Dpot x k) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      eLpNorm Dpot (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    eLpNorm_mono_ae hmeas
      (Eventually.of_forall fun x => norm_le_pi_norm (Dpot x) k)
  have hmem : MemLp (fun x => Dpot x k) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    hcomp.trans_lt hDmem.eLpNorm_lt_top
  exact (hmem.locallyIntegrable
    (ENNReal.one_le_ofReal.2 (by norm_num))).locallyIntegrableOn B

/-- The one-slice assembly behind display (3.5) of the pressure-gradient
section.

On an open set `B` the pressure slice `p` agrees almost everywhere with the
sum of the coordinate Newtonian derivative potentials of a compactly supported
`L^{6/5}` source `V`, of a function `h` which is `C¹` on `B`, and of a
function `w` carrying its own coordinate weak derivatives `gw`.  The
Calderón–Zygmund selection `hP1` supplies the weak gradient of the potential
part together with its `L^{6/5}` bound.  The conclusion is a single field `D`
whose coordinates are locally integrable on `B`, which lies in `L^{6/5}` on
`B'`, which is the coordinate weak gradient of `p` on `B`, and which obeys the
three-term bound of display (3.5). -/
theorem slice_selected_gradient_of_potential_representation
    (C_CZ : ℝ) {Sh Sw : ℝ≥0∞} (hSh : Sh ≠ ∞) (hSw : Sw ≠ ∞)
    {B B' : Set Vec3} (hB : IsOpen B)
    {p h w : Vec3 → ℝ} {V : Vec3 → Vec3} {gw : Fin 3 → Vec3 → ℝ}
    (hP1 : ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hV : ∀ i : Fin 3, MemLp (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i))
    (hrep : p =ᵐ[volume.restrict B] fun x =>
      (∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x) + (h x + w x))
    (hh : ContDiffOn ℝ (1 : ℕ∞) h B)
    (hhbound : ∀ k : Fin 3, eLpNorm (fun x => classicalGradient h x k)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ≤ Sh)
    (hwloc : LocallyIntegrableOn w B volume)
    (hw : ∀ k : Fin 3, HasWeakPartialDerivOn B k w (gw k))
    (hgwloc : ∀ k : Fin 3, LocallyIntegrableOn (gw k) B volume)
    (hgwbound : ∀ k : Fin 3, eLpNorm (gw k) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict B') ≤ Sw) :
    ∃ D : Vec3 → Vec3,
      (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k) B volume) ∧
      MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ∧
      (∀ k : Fin 3, HasWeakPartialDerivOn B k p (fun x => D x k)) ∧
      (∀ k : Fin 3, eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B') ≤
        ENNReal.ofReal C_CZ *
          (∑ i : Fin 3, eLpNorm (fun x => V x i)
            (ENNReal.ofReal (6 / 5 : ℝ)) volume) + Sh + Sw) := by
  classical
  obtain ⟨Dpot, hDmem, hDpair, hDbound⟩ :=
    newtonian_derivative_sum_weak_gradient_of_extension C_CZ hP1 hV hVc
  set D : Vec3 → Vec3 :=
    fun x k => Dpot x k + (classicalGradient h x k + gw k x) with hDdef
  have hbound : ∀ k : Fin 3,
      eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B') ≤
        ENNReal.ofReal C_CZ *
          (∑ i : Fin 3, eLpNorm (fun x => V x i)
            (ENNReal.ofReal (6 / 5 : ℝ)) volume) + Sh + Sw := by
    intro k
    have hsplit := (eLpNorm_six_fifths_add_le (μ := volume.restrict B')
      (fun x => Dpot x k) (fun x => classicalGradient h x k + gw k x)).trans
      (add_le_add le_rfl (eLpNorm_six_fifths_add_le (μ := volume.restrict B')
        (fun x => classicalGradient h x k) (gw k)))
    have hpot : eLpNorm (fun x => Dpot x k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B') ≤
        ENNReal.ofReal C_CZ *
          ∑ i : Fin 3, eLpNorm (fun x => V x i)
            (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
      have hmeas : AEStronglyMeasurable (fun x => Dpot x k) volume :=
        (ContinuousLinearMap.proj (R := ℝ) k).continuous.comp_aestronglyMeasurable
          hDmem.aestronglyMeasurable
      have hcomp : eLpNorm (fun x => Dpot x k)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          eLpNorm Dpot (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
        eLpNorm_mono_ae hmeas
          (Eventually.of_forall fun x => norm_le_pi_norm (Dpot x) k)
      exact ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        hcomp).trans hDbound
    calc
      eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict B') ≤
          eLpNorm (fun x => Dpot x k) (ENNReal.ofReal (6 / 5 : ℝ))
              (volume.restrict B') +
            (eLpNorm (fun x => classicalGradient h x k)
                (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') +
              eLpNorm (gw k) (ENNReal.ofReal (6 / 5 : ℝ))
                (volume.restrict B')) := hsplit
      _ ≤ ENNReal.ofReal C_CZ *
            (∑ i : Fin 3, eLpNorm (fun x => V x i)
              (ENNReal.ofReal (6 / 5 : ℝ)) volume) + (Sh + Sw) :=
        add_le_add hpot (add_le_add (hhbound k) (hgwbound k))
      _ = ENNReal.ofReal C_CZ *
            (∑ i : Fin 3, eLpNorm (fun x => V x i)
              (ENNReal.ofReal (6 / 5 : ℝ)) volume) + Sh + Sw := by
        rw [add_assoc]
  refine ⟨D, ?_, ?_, ?_, hbound⟩
  · intro k
    exact (potentialComponent_locallyIntegrableOn hDmem k B).add
      ((locallyIntegrableOn_classicalGradient hB k hh).add (hgwloc k))
  · have hfin : ENNReal.ofReal C_CZ *
        (∑ i : Fin 3, eLpNorm (fun x => V x i)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume) + Sh + Sw < ∞ := by
      refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, hSh.lt_top⟩, hSw.lt_top⟩
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.mpr fun i _ => (hV i).eLpNorm_lt_top)
    exact memLp_pi_iff.mpr fun k => (hbound k).trans_lt hfin
  · intro k
    have hP : HasWeakPartialDerivOn B k
        (fun x => ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x)
        (fun x => Dpot x k) :=
      CKN.Core.Endgame.weak_partial_deriv_on_of_global_pairing hB
        (fun ψ hψ hψc => hDpair k ψ hψ hψc)
    have hHW : HasWeakPartialDerivOn B k (fun x => h x + w x)
        (fun x => classicalGradient h x k + gw k x) :=
      hasWeakPartialDerivOn_add hB
        (hasWeakPartialDerivOn_classicalGradient hB k hh) (hw k)
        (hh.continuousOn.locallyIntegrableOn hB.measurableSet) hwloc
        (locallyIntegrableOn_classicalGradient hB k hh) (hgwloc k)
    exact CKN.Core.Endgame.weak_partial_deriv_of_ae_sum (k := k) hB
      (P := fun x => ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x)
      (H := fun x => h x + w x)
      (gp := fun x => Dpot x k)
      (gh := fun x => classicalGradient h x k + gw k x)
      hrep hP hHW
      ((newtonianDerivativeSum_locallyIntegrable hV hVc).locallyIntegrableOn B)
      ((hh.continuousOn.locallyIntegrableOn hB.measurableSet).add hwloc)
      (potentialComponent_locallyIntegrableOn hDmem k B)
      ((locallyIntegrableOn_classicalGradient hB k hh).add (hgwloc k))

/-- The coordinate sum of source norms appearing in the assembled bound is
controlled by the norm of the source on the ball carrying its support, which is
the form of the first term of display (3.5).  The factor three is the number of
spatial coordinates. -/
theorem sum_source_eLpNorm_le_restrict {V : Vec3 → Vec3} {x₀ : Vec3} {r : ℝ}
    (hmeas : AEStronglyMeasurable V volume)
    (hVsupport : ∀ i : Fin 3, tsupport (fun x => V x i) ⊆ euclideanBall x₀ r) :
    ∑ i : Fin 3, eLpNorm (fun x => V x i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      3 * eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x₀ r)) := by
  have hball : MeasurableSet (euclideanBall x₀ r) := by
    change MeasurableSet {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
      continuous_const).measurableSet
  have hterm : ∀ i : Fin 3, eLpNorm (fun x => V x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x₀ r)) := by
    intro i
    have hae : (fun x => V x i) =ᵐ[volume]
        (euclideanBall x₀ r).indicator (fun x => V x i) := by
      filter_upwards [] with x
      by_cases hx : x ∈ euclideanBall x₀ r
      · simp only [Set.indicator_of_mem hx]
      · have hxs : x ∉ tsupport (fun x => V x i) := fun hxt => hx (hVsupport i hxt)
        simp only [Set.indicator_of_notMem hx]
        exact image_eq_zero_of_notMem_tsupport (f := fun y => V y i) hxs
    have hrestrict : eLpNorm (fun x => V x i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume =
        eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x₀ r)) := by
      rw [eLpNorm_congr_ae hae, eLpNorm_indicator_eq_eLpNorm_restrict hball]
    rw [hrestrict]
    refine eLpNorm_mono_ae ?_ (Eventually.of_forall fun x => norm_le_pi_norm (V x) i)
    exact ((ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
      hmeas).restrict
  have hthree : (3 : ℝ≥0∞) * eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) =
      eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x₀ r)) +
        eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x₀ r)) +
        eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x₀ r)) := by
    rw [show (3 : ℝ≥0∞) = 1 + 1 + 1 by norm_num]
    ring
  rw [Fin.sum_univ_three, hthree]
  exact add_le_add (add_le_add (hterm 0) (hterm 1)) (hterm 2)

/-- The assembled bound rewritten with the source norm taken on the ball
carrying the support of the source, which is the first term of display (3.5).
The three spatial coordinates are absorbed into the constant. -/
theorem eLpNorm_le_ball_source_of_sum_source {C_CZ : ℝ}
    {V : Vec3 → Vec3} {x₀ : Vec3} {r : ℝ} {g : Vec3 → ℝ}
    {μ : Measure Vec3} {S : ℝ≥0∞}
    (hmeas : AEStronglyMeasurable V volume)
    (hVsupport : ∀ i : Fin 3, tsupport (fun x => V x i) ⊆ euclideanBall x₀ r)
    (hg : eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      ENNReal.ofReal C_CZ *
        (∑ i : Fin 3, eLpNorm (fun x => V x i)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume) + S) :
    eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      ENNReal.ofReal (3 * C_CZ) *
        eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x₀ r)) + S := by
  refine hg.trans (add_le_add ?_ le_rfl)
  have hsum := sum_source_eLpNorm_le_restrict hmeas hVsupport
  calc
    ENNReal.ofReal C_CZ *
        (∑ i : Fin 3, eLpNorm (fun x => V x i)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume) ≤
        ENNReal.ofReal C_CZ * (3 * eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x₀ r))) :=
      mul_le_mul le_rfl hsum (by exact zero_le) (by exact zero_le)
    _ = ENNReal.ofReal (3 * C_CZ) *
        eLpNorm V (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x₀ r)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        show ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) by simp]
      ring

end CKN.Core.Step4
