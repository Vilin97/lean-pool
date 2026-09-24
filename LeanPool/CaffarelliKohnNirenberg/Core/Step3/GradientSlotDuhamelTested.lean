/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationGradientTransfers
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.GradientSlotDuhamelAtoms
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationConvectionTransfer

/-!
# Gradient Slot Duhamel Tested

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

section

/-!
# Gradient Slot Duhamel Transfers

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Step3

/-! # Scalar and pressure forms of the localized gradient transfers

The paper label `lem:local-equation` records the localized form of the
Caffarelli–Kohn–Nirenberg equation tested against a product cutoff `φ · ψ`.
The two statements below extract from it the two ingredients used when the
cutoff is frozen in the time variable and only the spatial slot structure
matters:

* `gradientSlot_diffusion_transfer_of_sws` is the scalar-coordinate form of the
  vector diffusion transfer `localized_diffusion_transfer_of_sws`; it is the
  version in which every component of the vector test field is the same scalar
  field `ψ` in the selected slot `i`.
* `gradientSlot_pressure_transfer` transfers the pressure pairing against the
  product cutoff to a weak pressure gradient, with no solution hypothesis at
  all, since the pressure enters the localized equation only through its weak
  gradient. -/

/-- Scalar form of the diffusion transfer of `lem:local-equation`: testing the
vector localized equation with the vector field whose `i`-th component is a
scalar cutoff `ψ` and whose other components vanish collapses the transfer
identity to the scalar identity in the `i`-th coordinate. No divergence
information is used beyond what `IsSuitableWeakSolutionIntegrable` already provides. -/
theorem gradientSlot_diffusion_transfer_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (i j : Fin 3) :
    -(∫ z : ParabolicPoint, Du z i j * (spatialPartial φ j z * ψ z)) +
        (∫ z : ParabolicPoint,
          u z i * (spatialPartial φ j z * spatialPartial ψ j z)) =
      (∫ z : ParabolicPoint, u z i * (spatialSecondPartial φ j j z * ψ z)) +
        2 * (∫ z : ParabolicPoint,
          u z i * (spatialPartial φ j z * spatialPartial ψ j z)) := by
  let Ψ : Vec3 × ℝ → Vec3 := fun z k => if k = i then ψ z else 0
  have hΨ : Ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ := by
    refine ⟨?_, ?_, by simp [spaceTimeSet]⟩
    · rw [contDiff_pi]
      intro k
      by_cases hki : k = i
      · subst k
        simpa [Ψ] using hψ.1
      · simpa [Ψ, hki] using (contDiff_const (c := (0 : ℝ)))
    · apply HasCompactSupport.of_support_subset_isCompact hψ.2.1.isCompact
      intro z hz
      by_contra hnot
      apply hz
      have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport hnot
      funext k
      simp [Ψ, hzero]
  have hΨval : ∀ z : ParabolicPoint, Ψ z i = ψ z := by
    intro z
    simp [Ψ]
  have h := localized_diffusion_transfer_of_sws hsol hφ hbox hφbox hΨ i j
  simp only [hΨval] at h
  simpa only [mul_assoc] using h

/-- Pressure transfer of `lem:local-equation` against the product cutoff: the
pairing of the pressure with the spatial derivative of `φ · ψ` equals the
pairing of the weak pressure gradient with `φ · ψ`. The pressure enters the
localized equation only through its weak gradient, so this transfer carries no
solution hypothesis: all it needs is the weak-gradient pairing rule on the
support box of `φ`. -/
theorem gradientSlot_pressure_transfer
    {Ω' : Set Vec3} {J : Set ℝ}
    {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3}
    {φ : Vec3 × ℝ → ℝ} (hφd : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (hDpweak : ∀ i : Fin 3, ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport χ ⊆ Ω' ×ˢ J →
      (∫ z : ParabolicPoint, p z * spatialPartial χ i z) =
        -(∫ z : ParabolicPoint, Dp z i * χ z))
    (i : Fin 3) :
    (∫ z : ParabolicPoint, p z * spatialPartial (fun w => φ w * ψ w) i z) =
      -(∫ z : ParabolicPoint, Dp z i * (φ z * ψ z)) := by
  have htest : (fun z : Vec3 × ℝ => φ z * ψ z) ∈
      spaceTimeTestFunction (V := ℝ) Set.univ Set.univ := by
    have h := spaceTimeTestFunction_mul_smooth (Ω := Set.univ) (I := Set.univ)
      hψ hφd
    convert h using 1
    funext z
    exact mul_comm (φ z) (ψ z)
  have hsupp : tsupport (fun z : Vec3 × ℝ => φ z * ψ z) ⊆ Ω' ×ˢ J :=
    (tsupport_mul_subset_left (f := φ) (g := ψ)).trans hφbox
  exact hDpweak i (fun z : Vec3 × ℝ => φ z * ψ z) htest hsupp

end CKN.Core.Step3
end

end

section

/-!
# Gradient Slot Duhamel Split

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Core.Step4


noncomputable section

namespace CKN.Core.Step3

/-!
# Regrouped integrands for the local equation

The tested form of the localized equation (`lem:local-equation`) pairs the
divergence-form sources `localizedDivergenceG`, `localizedDivergenceH` with a
test field and its first spatial derivative.  The paper writes the same
expression after moving the derivative of the product `φ * ψ` onto the cutoff
factor, which is what the identities below record.

`gradientSlot_divergence_integrand` is the divergence-form regrouping: the
source integrand together with the derivative slot equals the time, force,
convection, derivative and pressure contributions collected on the right.
`gradientSlot_gradient_integrand` is the corresponding regrouping for the
pressure-gradient slot of `localizedGradientSourceG`, where the second spatial
derivatives of the cutoff appear explicitly; it needs no smoothness hypotheses
because the product rule is not used.
-/

/-- The divergence-form tested integrand of the local equation, regrouped onto
the cutoff product `φ * ψ` (`lem:local-equation`).  The only analytic input is
the product rule `spatialPartial_mul_full` for the smooth cutoff factors. -/
theorem gradientSlot_divergence_integrand
    {φ ψ : Vec3 × ℝ → ℝ}
    (hφd : ContDiff ℝ (⊤ : ℕ∞) φ) (hψd : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (i : Fin 3) (z : ParabolicPoint) :
    localizedDivergenceG φ u Du p f z i * ψ z +
        ∑ j, localizedDivergenceH φ u p j z i * spatialPartial ψ j z =
      (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
        (∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) +
        (∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
          u z i * (spatialPartial φ j z * spatialPartial ψ j z))) +
        p z * spatialPartial (fun w => φ w * ψ w) i z := by
  have hsp : ∀ j : Fin 3, spatialPartial (fun w => φ w * ψ w) j z =
      spatialPartial φ j z * ψ z + φ z * spatialPartial ψ j z :=
    fun j => spatialPartial_mul_full hφd hψd j z
  simp only [localizedDivergenceG, localizedDivergenceH, hsp]
  simp only [Fin.sum_univ_three]
  fin_cases i <;> simp <;> ring

/-- The pressure-gradient tested integrand of the local equation, regrouped
onto the cutoff product `φ * ψ` (`lem:local-equation`).  No derivative of the
test field is moved, so no smoothness hypothesis is needed. -/
theorem gradientSlot_gradient_integrand
    {φ ψ : Vec3 × ℝ → ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {f : ParabolicPoint → Vec3} {Dp : ParabolicPoint → Vec3}
    (i : Fin 3) (z : ParabolicPoint) :
    localizedGradientSourceG φ u Du f Dp z i * ψ z +
        ∑ j, (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z =
      (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
        (-((φ z * ψ z) * localizedConvection u Du z i)) +
        (∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
          2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) +
        (-(Dp z i * (φ z * ψ z))) := by
  simp only [localizedGradientSourceG, localizedGradientSourceH,
    localizedEquationG, localizedEquationH]
  rw [show spatialLaplacian (fun x => φ (x, z.2)) z.1 =
      ∑ j : Fin 3, spatialSecondPartial φ j j z by rfl]
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  fin_cases i <;> ring

end CKN.Core.Step3
end

end

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Core.Step4


noncomputable section

namespace CKN.Core.Step3

/-!
# Trading the divergence-form pressure slot for the gradient slot

Paper label `lem:local-equation`. The cutoff-tested identity for the localized
velocity is first obtained with the pressure sitting in the divergence-form
slot, as `p ∂ᵢφ` together with the diagonal entry `δᵢⱼ p φ`.  The estimates of
Step 4 instead need the pressure as `φ Dp` in the heat slot, the convection in
the form `φ (u · ∇) u`, and the second cutoff derivative `Δφ u` explicit.  The
theorem below performs that exchange once and for all at the level of the
tested identity: the divergence-form right-hand side and the gradient-slot
right-hand side agree for every space-time test function.  The three inputs are
the convection transfer (`∑ⱼ ∫ uᵢuⱼ ∂ⱼ(φψ) = −∫ φψ (u · ∇)uᵢ`), the diffusion
transfer (one integration by parts in `∂ⱼφ ψ`) and the weak pressure gradient
tested against the product cutoff `φψ`.
-/

/-- An integrable factor times a continuous compactly supported factor is
integrable. -/
private lemma integrable_mul_of_compact_continuous
    {a : ParabolicPoint → ℝ} (ha : Integrable a volume)
    {b : Vec3 × ℝ → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun z : ParabolicPoint => a z * b z) volume := by
  obtain ⟨C, hC⟩ := hbc.exists_bound_of_continuous hb
  exact ha.mul_bdd hb.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hC z)

/-- The divergence-form and gradient-slot right-hand sides of the tested local
equation agree, for every space-time test function `ψ`.  Paper label
`lem:local-equation`: this is the passage from the raw tested identity to the
displayed equation `eq:local-equation`, in which the pressure enters through
its weak gradient `Dp`. -/
theorem gradientSlot_tested_transfer_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {Dp : ParabolicPoint → Vec3}
    (hDpInt : ∀ i : Fin 3, Integrable (fun z => Dp z i)
      (volume.restrict (spaceTimeSet Ω' J)))
    (hDpweak : ∀ i : Fin 3, ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport χ ⊆ Ω' ×ˢ J →
      (∫ z : ParabolicPoint, p z * spatialPartial χ i z) =
        -(∫ z : ParabolicPoint, Dp z i * χ z))
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (i : Fin 3) :
    (∫ z : ParabolicPoint, localizedDivergenceG φ u Du p f z i * ψ z) +
        ∑ j, ∫ z : ParabolicPoint,
          localizedDivergenceH φ u p j z i * spatialPartial ψ j z =
      (∫ z : ParabolicPoint, localizedGradientSourceG φ u Du f Dp z i * ψ z) +
        ∑ j, ∫ z : ParabolicPoint,
          (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z := by
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9⟩ :=
    gradientSlot_tested_integrable_of_sws hsol hφ hbox hφbox hDpInt hψ i
  obtain ⟨-, hGInt, hHInt, -, -, -⟩ :=
    localized_divergence_source_data_of_sws hsol hφ hbox hφbox
  obtain ⟨hGradInt, hGradHInt, -, -⟩ :=
    localized_gradient_source_data_of_sws hsol hφ hbox hφbox hDpInt
  have hφd : ContDiff ℝ (⊤ : ℕ∞) φ := hφ.1
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := hψ.1
  have hψc : HasCompactSupport ψ := hψ.2.1
  have hψsp (j : Fin 3) : Continuous
      (fun z : Vec3 × ℝ => spatialPartial ψ j z) :=
    (spatialPartial_contDiff hψd j).continuous
  have hψspc (j : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial ψ j z) := by
    apply HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    intro z hz
    by_contra hnot
    exact hz (spatialPartial_zero_of_not_mem_tsupport_public hψd hnot j)
  have hGdivψ : Integrable (fun z : ParabolicPoint =>
      localizedDivergenceG φ u Du p f z i * ψ z) volume :=
    integrable_mul_of_compact_continuous (hGInt i) hψd.continuous hψc
  have hHdivψ (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      localizedDivergenceH φ u p j z i * spatialPartial ψ j z) volume :=
    integrable_mul_of_compact_continuous (hHInt j i) (hψsp j) (hψspc j)
  have hGgradψ : Integrable (fun z : ParabolicPoint =>
      localizedGradientSourceG φ u Du f Dp z i * ψ z) volume :=
    integrable_mul_of_compact_continuous (hGradInt i) hψd.continuous hψc
  have hHgradψ (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z) volume :=
    integrable_mul_of_compact_continuous (hGradHInt j i) (hψsp j) (hψspc j)
  have hAint : Integrable (fun z : ParabolicPoint =>
      u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) volume :=
    hA1.add hA2
  have hBint : Integrable (fun z : ParabolicPoint =>
      ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) volume :=
    integrable_finsetSum _ (fun j _ => hA3 j)
  have hnegD (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      -(Du z i j * (spatialPartial φ j z * ψ z))) volume := (hA4 j).neg
  have hA5two (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z))) volume :=
    (hA5 j).const_mul 2
  have hCjint (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      -(Du z i j * (spatialPartial φ j z * ψ z)) +
        u z i * (spatialPartial φ j z * spatialPartial ψ j z)) volume :=
    (hnegD j).add (hA5 j)
  have hCint : Integrable (fun z : ParabolicPoint =>
      ∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
        u z i * (spatialPartial φ j z * spatialPartial ψ j z))) volume :=
    integrable_finsetSum _ (fun j _ => hCjint j)
  have hB'int : Integrable (fun z : ParabolicPoint =>
      -((φ z * ψ z) * localizedConvection u Du z i)) volume := hA9.neg
  have hC'jint (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      u z i * (spatialSecondPartial φ j j z * ψ z) +
        2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z))) volume :=
    (hA6 j).add (hA5two j)
  have hC'int : Integrable (fun z : ParabolicPoint =>
      ∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
        2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) volume :=
    integrable_finsetSum _ (fun j _ => hC'jint j)
  have hD'int : Integrable (fun z : ParabolicPoint =>
      -(Dp z i * (φ z * ψ z))) volume := hA8.neg
  have hABint : Integrable (fun z : ParabolicPoint =>
      (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
        ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) volume :=
    hAint.add hBint
  have hABCint : Integrable (fun z : ParabolicPoint =>
      ((u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
          ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) +
        ∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
          u z i * (spatialPartial φ j z * spatialPartial ψ j z))) volume :=
    hABint.add hCint
  have hAB'int : Integrable (fun z : ParabolicPoint =>
      (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
        -((φ z * ψ z) * localizedConvection u Du z i)) volume :=
    hAint.add hB'int
  have hAB'C'int : Integrable (fun z : ParabolicPoint =>
      ((u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
          -((φ z * ψ z) * localizedConvection u Du z i)) +
        ∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
          2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) volume :=
    hAB'int.add hC'int
  have hHdivψsum : Integrable (fun z : ParabolicPoint =>
      ∑ j, localizedDivergenceH φ u p j z i * spatialPartial ψ j z) volume :=
    integrable_finsetSum _ (fun j _ => hHdivψ j)
  have hHgradψsum : Integrable (fun z : ParabolicPoint =>
      ∑ j, (-localizedGradientSourceH φ u j z i) *
        spatialPartial ψ j z) volume :=
    integrable_finsetSum _ (fun j _ => hHgradψ j)
  have hBeq : (∫ z : ParabolicPoint,
      ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) =
      ∫ z : ParabolicPoint, -((φ z * ψ z) * localizedConvection u Du z i) := by
    rw [integral_finsetSum _ (fun j _ => hA3 j), integral_neg]
    exact localized_convection_transfer_no_trace hsol hφ hbox hφbox hψ i
  have hCeq : (∫ z : ParabolicPoint,
      ∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
        u z i * (spatialPartial φ j z * spatialPartial ψ j z))) =
      ∫ z : ParabolicPoint,
        ∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
          2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z))) := by
    rw [integral_finsetSum _ (fun j _ => hCjint j),
      integral_finsetSum _ (fun j _ => hC'jint j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_add (hnegD j) (hA5 j), integral_neg,
      integral_add (hA6 j) (hA5two j), integral_const_mul]
    exact gradientSlot_diffusion_transfer_of_sws hsol hφ hbox hφbox hψ i j
  have hDeq : (∫ z : ParabolicPoint,
      p z * spatialPartial (fun w => φ w * ψ w) i z) =
      ∫ z : ParabolicPoint, -(Dp z i * (φ z * ψ z)) := by
    rw [integral_neg]
    exact gradientSlot_pressure_transfer hφd hφbox hψ hDpweak i
  calc
    (∫ z : ParabolicPoint, localizedDivergenceG φ u Du p f z i * ψ z) +
        ∑ j, ∫ z : ParabolicPoint,
          localizedDivergenceH φ u p j z i * spatialPartial ψ j z =
        ∫ z : ParabolicPoint,
          (localizedDivergenceG φ u Du p f z i * ψ z +
            ∑ j, localizedDivergenceH φ u p j z i * spatialPartial ψ j z) := by
      rw [← integral_finsetSum _ (fun j _ => hHdivψ j),
        ← integral_add hGdivψ hHdivψsum]
    _ = ∫ z : ParabolicPoint,
          ((u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
            (∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) +
            (∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
              u z i * (spatialPartial φ j z * spatialPartial ψ j z))) +
            p z * spatialPartial (fun w => φ w * ψ w) i z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      exact gradientSlot_divergence_integrand hφd hψd i z
    _ = ((∫ z : ParabolicPoint,
            (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z))) +
          (∫ z : ParabolicPoint,
            ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) +
          (∫ z : ParabolicPoint,
            ∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
              u z i * (spatialPartial φ j z * spatialPartial ψ j z))) +
          (∫ z : ParabolicPoint,
            p z * spatialPartial (fun w => φ w * ψ w) i z)) := by
      rw [integral_add hABCint hA7, integral_add hABint hCint,
        integral_add hAint hBint]
    _ = ((∫ z : ParabolicPoint,
            (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z))) +
          (∫ z : ParabolicPoint,
            -((φ z * ψ z) * localizedConvection u Du z i)) +
          (∫ z : ParabolicPoint,
            ∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
              2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) +
          (∫ z : ParabolicPoint, -(Dp z i * (φ z * ψ z)))) := by
      rw [hBeq, hCeq, hDeq]
    _ = ∫ z : ParabolicPoint,
          ((u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
            (-((φ z * ψ z) * localizedConvection u Du z i)) +
            (∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
              2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) +
            (-(Dp z i * (φ z * ψ z)))) := by
      rw [integral_add hAB'C'int hD'int, integral_add hAB'int hC'int,
        integral_add hAint hB'int]
    _ = ∫ z : ParabolicPoint,
          (localizedGradientSourceG φ u Du f Dp z i * ψ z +
            ∑ j, (-localizedGradientSourceH φ u j z i) *
              spatialPartial ψ j z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      exact (gradientSlot_gradient_integrand i z).symm
    _ = (∫ z : ParabolicPoint,
          localizedGradientSourceG φ u Du f Dp z i * ψ z) +
        ∑ j, ∫ z : ParabolicPoint,
          (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z := by
      rw [integral_add hGgradψ hHgradψsum,
        integral_finsetSum _ (fun j _ => hHgradψ j)]

end CKN.Core.Step3
