/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientBase
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.NewtonianDerivativeLocalLp
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientProduct
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSlice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection

/-!
# Pressure Gradient

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The selector is scalar.  This wrapper applies it to the three spatial
components and packages the resulting representatives as one native `Vec3`
field.  All analytic work is deliberately left in the slice hypothesis: the
wrapper only performs the finite-dimensional measurable assembly. -/


theorem pressure_gradient_spacetime_selection_with_slice_bounds
    {B B' : Set Vec3} {J : Set ℝ} {p : ParabolicPoint → ℝ}
    {K : Fin 3 → ℝ → ℝ≥0∞}
    (hB : IsOpen B) (hB' : MeasurableSet B')
    (hB'c : IsCompact (closure B')) (hB'B : closure B' ⊆ B)
    (hp : IntegrableOn p (B ×ˢ J) volume)
    (hslice : ∀ k : Fin 3, ∀ᵐ t ∂(volume.restrict J), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume ∧
        HasWeakPartialDerivOn B k (fun x => p (x, t)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict B') ≤ K k t) :
    ∃ Dp : ParabolicPoint → Vec3,
      (∀ k : Fin 3, AEMeasurable (fun z => Dp z k)
        (volume.restrict (B' ×ˢ J))) ∧
      (∀ k : Fin 3, ∀ᵐ t ∂(volume.restrict J),
        eLpNorm (fun x => Dp (x, t) k) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict B') ≤ K k t) ∧
      (∀ k : Fin 3, ∀ Ψ : Vec3 × ℝ → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ →
        tsupport Ψ ⊆ B' ×ˢ J →
        (∫ t in J, ∫ x in B', p (x, t) * spatialPartial Ψ k (x, t)) =
          -∫ t in J, ∫ x in B', Dp (x, t) k * Ψ (x, t)) ∧
      (∀ k : Fin 3, ∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ →
        HasCompactSupport Ψ → tsupport Ψ ⊆ B' ×ˢ J →
        IntegrableOn (fun z => p z * spatialPartial Ψ k z) (B' ×ˢ J) volume →
        IntegrableOn (fun z => Dp z k * Ψ z) (B' ×ˢ J) volume →
        (∫ z in B' ×ˢ J, p z * spatialPartial Ψ k z) =
          -∫ z in B' ×ˢ J, Dp z k * Ψ z) := by
  classical
  have hselect : ∀ k : Fin 3, ∃ Dk : ParabolicPoint → ℝ,
      AEMeasurable Dk (volume.restrict (B' ×ˢ J)) ∧
      (∀ᵐ t ∂(volume.restrict J), ∀ g : Vec3 → ℝ,
        LocallyIntegrableOn g B volume →
        HasWeakPartialDerivOn B k (fun x => p (x, t)) g →
        (fun x => Dk (x, t)) =ᵐ[volume.restrict B'] g) ∧
      (∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ →
        HasCompactSupport Ψ → tsupport Ψ ⊆ B' ×ˢ J →
        (∫ t in J, ∫ x in B', p (x, t) * spatialPartial Ψ k (x, t)) =
          -∫ t in J, ∫ x in B', Dk (x, t) * Ψ (x, t)) ∧
      (∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ →
        HasCompactSupport Ψ → tsupport Ψ ⊆ B' ×ˢ J →
        IntegrableOn (fun z => p z * spatialPartial Ψ k z) (B' ×ˢ J) volume →
        IntegrableOn (fun z => Dk z * Ψ z) (B' ×ˢ J) volume →
        (∫ z in B' ×ˢ J, p z * spatialPartial Ψ k z) =
          -∫ z in B' ×ˢ J, Dk z * Ψ z) := by
    intro k
    obtain ⟨Dk, hmeas, hae, hidentity, _hproduct⟩ :=
      exists_spacetime_weak_gradient_of_slices k hB hB' hB'c hB'B hp
        (by
          filter_upwards [hslice k] with t ht
          obtain ⟨g, hgloc, hgw, _hbound⟩ := ht
          exact ⟨g, hgloc, hgw⟩)
    exact ⟨Dk, hmeas, hae, hidentity, _hproduct⟩
  choose D hDmeas hDae hDidentity using hselect
  refine ⟨fun z k => D k z, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hDmeas k
  · intro k
    filter_upwards [hslice k, hDae k] with t ht hDt
    obtain ⟨g, _hgloc, _hgw, hbound⟩ := ht
    have heq := hDt g _hgloc _hgw
    rw [eLpNorm_congr_ae heq]
    exact hbound
  · intro k Ψ hΨ hΨc hΨsupport
    exact (hDidentity k).1 Ψ hΨ hΨc hΨsupport
  · intro k Ψ hΨ hΨc hΨsupport hF hD
    exact (hDidentity k).2 Ψ hΨ hΨc hΨsupport hF hD

/-! Integrating the one-scale display over a one-sided time interval is a
direct order argument.  The spatial fields may be chosen independently on
the almost-everywhere set; this is the form consumed by the parabolic decay
layer. -/


theorem pressure_gradient_two_scale_decay
    {Φ V : ℝ → ℝ} {C₃ ρ r : ℝ}
    (hC₃ : 0 ≤ C₃) (_ : 0 < ρ) (_ : 0 < r) (_ : r ≤ ρ / 8)
    (hΦ : 0 ≤ Φ ρ)
    (hdecomp : Φ r ≤ V r + Φ (r / 2))
    (hpart : V r ≤ C₃ * (r / ρ) ^ (3 : ℕ) * V ρ)
    (hharm : Φ (r / 2) ≤ C₃ * (r / ρ) ^ (3 : ℕ) *
      (Φ ρ + V ρ)) :
    Φ r ≤ 2 * C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by
  have hratio : 0 ≤ (r / ρ) ^ (3 : ℕ) := by positivity
  have hV : V r ≤ C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by
    calc
      V r ≤ C₃ * (r / ρ) ^ (3 : ℕ) * V ρ := hpart
      _ ≤ C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by
        gcongr
        linarith only [hΦ]
  calc
    Φ r ≤ V r + Φ (r / 2) := hdecomp
    _ ≤ C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) +
        C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := add_le_add hV hharm
    _ = 2 * C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by ring

theorem pressure_gradient_morrey_bound
    {κ : ℝ} {g : ParabolicPoint → ℝ} {C : ℝ≥0∞}
    (hcell : ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
      morreyCell (6 / 5 : ℝ) κ g z r.1 ≤ C) :
    morreyNorm (6 / 5 : ℝ) κ g ≤ C := by
  exact morreyNorm_le_of_cell_bound hcell


end CKN.Core.Step4
