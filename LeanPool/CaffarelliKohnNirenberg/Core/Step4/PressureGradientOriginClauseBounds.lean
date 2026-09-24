/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseProduct

/-!
# Carrier cell bounds from slicewise bounds on the pressure

The one-sided estimate of `prop:bootstrap` sees the selected pressure gradient
only through the indicator of the backward carrier
`parabolicCylinder 0 0 R₁`.  A cell bound for that indicator is a bound for the
integral of the gradient over the intersection of the cell with the carrier,
and by the product decomposition of that intersection the integral splits into
a time integral of spatial slice integrals whose times all lie in
`(-R₁ ^ 2, 0]`.

This module turns a multiscale slicewise `L^{6/5}` majorant for the weak
gradients of the pressure slices into exactly those carrier cell bounds.  The
majorant is measured on the intersection `vec3Ball x r ∩ vec3Ball 0 R₁` of the
cell ball with the carrier ball, and its two time integrals are taken over the
clipped windows.  Nothing here refers to the gradient at a time outside the
time factor of the unit cylinder.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-- The integral of a gradient component over the part of a cell that meets
the backward carrier is bounded by the clipped time integral of a slicewise
`L^{6/5}` majorant.  Only the times in `(-R₁ ^ 2, 0]`, which the domain
hypothesis of `thm:A` places inside the solution interval, are used. -/
theorem originClauseCarrierCellIntegral_le_of_slice_bounds
    {I : Set ℝ} {R₀ R₁ : ℝ} {p : ParabolicPoint → ℝ} {M : ℝ → ℝ≥0∞}
    {Dp : ParabolicPoint → Vec3} {i : Fin 3} {x : Vec3} {t r : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₁one : R₁ ≤ 1) (hI : Icc (-1 : ℝ) 0 ⊆ I)
    (hDmeas : AEMeasurable (fun z => Dp z i)
      (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I)))
    (hid : ∀ᵐ s ∂(volume.restrict I), ∀ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume →
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) i (fun y => p (y, s)) g →
      (fun y => Dp (y, s) i) =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R₁)] g)
    (hslice : ∀ᵐ s ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) i (fun y => p (y, s)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)) ≤ M s) :
    (∫⁻ w in parabolicCylinder x t r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
      ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0, M s ^ (6 / 5 : ℝ) := by
  have hFI : Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0 ⊆ I :=
    originClauseWindow_subset_of_unitTime hR₁ hR₁one hI t r
  have hEsub : vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁ ⊆ vec3Ball (0 : Vec3) R₁ :=
    inter_subset_right
  have hmeas : AEMeasurable (fun z => Dp z i)
      (volume.restrict ((vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁) ×ˢ
        (Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0))) :=
    hDmeas.mono_measure
      (Measure.restrict_mono_set volume (Set.prod_mono hEsub hFI))
  have hsl : ∀ᵐ s ∂(volume.restrict (Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0)),
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)) ≤ M s := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hFI hid,
      ae_restrict_of_ae_restrict_of_subset hFI hslice] with s hids hsls
    obtain ⟨g, hgli, hgweak, hgbound⟩ := hsls
    have hidg : (fun y => Dp (y, s) i)
        =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R₁)] g := hids g hgli hgweak
    have heq : (fun y => Dp (y, s) i)
        =ᵐ[volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)] g :=
      hidg.filter_mono (ae_mono (Measure.restrict_mono_set volume hEsub))
    exact (eLpNorm_congr_ae heq).trans_le hgbound
  rw [parabolicCylinder_inter_origin_eq_prod]
  exact prodPowerIntegral_le_of_slice_eLpNorm (by norm_num : (0 : ℝ) < 6 / 5) hmeas hsl

/-- The two carrier integral constants of the one-sided Morrey transfer, from a
multiscale slicewise majorant with clipped time windows.  The majorant
`M i x r s` bounds the `L^{6/5}` norm of the slice weak gradient on the
intersection of the cell ball with the carrier ball; `hgrowth` and `hglobal`
record the two clipped time integrals it has to satisfy.  Every cell scale is
used, which a single-scale slicewise bound cannot replace. -/
theorem originClauseCellBounds_of_multiscale_majorant
    {I : Set ℝ} {R₀ R₁ θ : ℝ} {p : ParabolicPoint → ℝ} {A B : ℝ≥0∞}
    {M : Fin 3 → Vec3 → ℝ → ℝ → ℝ≥0∞}
    (hR₁ : 0 ≤ R₁) (hR₁one : R₁ ≤ 1) (hI : Icc (-1 : ℝ) 0 ⊆ I)
    (hslice : ∀ (i : Fin 3) (x : Vec3) (r : ℝ),
      ∀ᵐ s ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) i (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)) ≤ M i x r s)
    (hgrowth : ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ R₁ →
      (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
        M i z.1 r s ^ (6 / 5 : ℝ)) ≤ A * ENNReal.ofReal (r ^ θ))
    (hglobal : ∀ i : Fin 3,
      (∫⁻ s in Ioc (-(R₁ ^ 2)) 0, M i (0 : Vec3) R₁ s ^ (6 / 5 : ℝ)) ≤ B)
    (Dp : ParabolicPoint → Vec3)
    (hDmeas : ∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
      (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I)))
    (hid : ∀ i : Fin 3, ∀ᵐ s ∂(volume.restrict I), ∀ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume →
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) i (fun y => p (y, s)) g →
      (fun y => Dp (y, s) i) =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R₁)] g) :
    (∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ R₁ →
      (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ A * ENNReal.ofReal (r ^ θ)) ∧
    (∀ i : Fin 3, (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R₁,
      ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ B) := by
  constructor
  · intro i z hz r hr hrR₁
    exact (originClauseCarrierCellIntegral_le_of_slice_bounds (R₀ := R₀) (p := p)
      hR₁ hR₁one hI (hDmeas i) (hid i) (hslice i z.1 r)).trans
      (hgrowth i z hz r hr hrR₁)
  · intro i
    have hkey := originClauseCarrierCellIntegral_le_of_slice_bounds (R₀ := R₀) (p := p)
      (x := (0 : Vec3)) (t := (0 : ℝ)) (r := R₁)
      hR₁ hR₁one hI (hDmeas i) (hid i) (hslice i (0 : Vec3) R₁)
    rw [inter_self] at hkey
    have hwin : Ioc ((0 : ℝ) - R₁ ^ 2) 0 ∩ Ioc (-(R₁ ^ 2)) 0 = Ioc (-(R₁ ^ 2)) 0 := by
      rw [zero_sub, inter_self]
    rw [hwin] at hkey
    exact hkey.trans (hglobal i)

end CKN.Core.Step4
