/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSource

/-!
# Slice Selected Gradient Centred Source Tensor Def

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-!
# The force-free centred pressure source

The first pressure potential is paired with the singly centred tensor
`pressureUTensor u c`. Its divergence source contains neither the force term
nor the centring correction. The force remains in the separate `p₇ + p₈`
pressure contribution.
-/

/-- Force-free centred divergence-form source paired with `η · pressureUTensor`. -/
@[expose]
def pressureDivergenceCutoffSourceCentredTensor
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3)
    (c : Vec3) : Vec3 → Vec3 :=
  fun x i => ∑ j, (η x * Du x i j * (u x j - c j) +
      dη j x * u x i * (u x j - c j))

/-- Source-Morrey alias for `pressureDivergenceCutoffSourceCentredTensor`. -/
@[expose]
def sourceMorreyCutoffVCentredTensor
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3)
    (c : Vec3) : Vec3 → Vec3 :=
  pressureDivergenceCutoffSourceCentredTensor η dη u Du c

/-- Spacetime force-free source with a time-dependent spatial mean. -/
@[expose]
def sourceMorreyCutoffVCentredTensorSpacetime
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (c : ℝ → Vec3) : ParabolicPoint → Vec3 :=
  fun z => sourceMorreyCutoffVCentredTensor η dη
    (fun y => u (y, z.2)) (fun y i j => Du (y, z.2) i j) (c z.2) z.1

private theorem centred_tensor_zero_outside
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {c : Vec3}
    (hηsupport : tsupport η ⊆ B)
    (hdηsupport : ∀ j : Fin 3, tsupport (dη j) ⊆ B)
    {x : Vec3} (hx : x ∉ B) :
    pressureDivergenceCutoffSourceCentredTensor η dη u Du c x = 0 := by
  have hηzero : η x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hηx => hx (hηsupport hηx))
  have hdηzero : ∀ j : Fin 3, dη j x = 0 := by
    intro j
    exact image_eq_zero_of_notMem_tsupport (fun hdηx => hx (hdηsupport j hdηx))
  funext i
  simp [pressureDivergenceCutoffSourceCentredTensor, hηzero, hdηzero]

/-- Each source component has compact support wherever the cutoff and its
derivatives are supported. -/
theorem sourceMorreyCutoffVCentredTensor_hasCompactSupport
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {c : Vec3}
    (hηsupport : tsupport η ⊆ B)
    (hdηsupport : ∀ j : Fin 3, tsupport (dη j) ⊆ B)
    (hBcompact : IsCompact B) (i : Fin 3) :
    HasCompactSupport
      (fun x => sourceMorreyCutoffVCentredTensor η dη u Du c x i) := by
  apply HasCompactSupport.of_support_subset_isCompact hBcompact
  intro x hx
  by_contra hnot
  exact hx (congrFun (centred_tensor_zero_outside hηsupport hdηsupport hnot) i)

/-- The force-free centred source is the old force-bearing centred source plus
the force contribution `η f`. -/
theorem sourceMorreyCutoffVCentredTensor_add_force
    {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {f : Vec3 → Vec3}
    {c : Vec3} {x : Vec3} {i : Fin 3} :
    sourceMorreyCutoffVCentredTensor η dη u Du c x i =
      sourceMorreyCutoffVCentred η dη u Du f c x i + η x * f x i := by
  simp only [sourceMorreyCutoffVCentred, sourceMorreyCutoffVCentredTensor,
    pressureDivergenceCutoffSourceCentredTensor,
    pressureDivergenceCutoffSourceCentred]
  ring

/-- On every `L^p` endpoint with `p ≥ 1`, its slice norm is bounded by the norm
of the full centred source plus the norm of `η f`. -/
theorem sourceMorreyCutoffVCentredTensor_slice_bound_le_full_add_force
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {f : Vec3 → Vec3}
    {c : Vec3} {i : Fin 3} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x => sourceMorreyCutoffVCentredTensor η dη u Du c x i) p
        (volume.restrict B) ≤
      eLpNorm (fun x => sourceMorreyCutoffVCentred η dη u Du f c x i) p
        (volume.restrict B) +
      eLpNorm (fun x => η x * f x i) p (volume.restrict B) := by
  have h := eLpNorm_add_le (μ := volume.restrict B) (p := p)
    (f := fun x => sourceMorreyCutoffVCentred η dη u Du f c x i)
    (g := fun x => η x * f x i) hp
  have heq : (fun x => sourceMorreyCutoffVCentred η dη u Du f c x i) +
      (fun x => η x * f x i) =
      (fun x => sourceMorreyCutoffVCentredTensor η dη u Du c x i) := by
    funext x
    simp only [Pi.add_apply]
    exact sourceMorreyCutoffVCentredTensor_add_force.symm
  rw [heq] at h
  exact h

end CKN.Core.Step4
