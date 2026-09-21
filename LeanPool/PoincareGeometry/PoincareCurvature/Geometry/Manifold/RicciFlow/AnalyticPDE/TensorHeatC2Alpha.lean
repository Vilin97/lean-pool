/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildC2Alpha
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatSecondJet

/-!
# Full parabolic Schauder control for Euclidean tensor heat flow

This file lifts the scalar finite-cylinder theorem to every coefficient of a
finite matrix, the coordinate model for a covariant two-tensor.  The lift is
entrywise and therefore preserves the exact scalar derivative witnesses and
explicit constants.  A separate theorem records preservation of symmetry.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Initial matrix coefficient data with a bounded genuine scalar `C²`
witness in every entry. -/
def matrixEuclideanBoundedC2ValueND {n d : ℕ}
    (D : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n)) :
    Matrix (Fin d) (Fin d) (BoundedContinuousFunction (Fin n → ℝ) ℝ) :=
  fun i j ↦ (D i j).value

/-- Entrywise full parabolic `C^{2+r,1+r/2}` control of a matrix field. -/
def MatrixEntrywiseParabolicC2AlphaNormLe {n d : ℕ}
    (R r : ℝ) (u : ℝ × (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (s : Set (ℝ × (Fin n → ℝ))) : Prop :=
  ∀ i j, ParabolicC2AlphaNormLe R r (fun z ↦ u z i j) s

/-- **Full Euclidean symmetric-two-tensor Schauder estimate.**  Every
coefficient of the actual matrix heat-kernel solution has a genuine second
jet and lies in the same explicit `C^{2+r,1+r/2}` ball. -/
theorem matrixEntrywiseParabolicC2AlphaNormLe_heatMildSpaceTimeND_Ioc
    {n d : ℕ} {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r) (hr1 : r < 1)
    (D : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n))
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ i j a b x y,
      |(D i j).second a b x - (D i j).second a b y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H Hq : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hHq : 0 ≤ Hq)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (hqParabolic : ∀ i j, ParabolicHolderWith Hq r
      (fun z : ℝ × (Fin n → ℝ) ↦ q z.1 i j z.2)
      (euclideanMildFiniteCylinderND n t₀ T)) :
    MatrixEntrywiseParabolicC2AlphaNormLe
      (∑ i : Fin d, ∑ j : Fin d,
        heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D i j)) r
      (matrixHeatMildSpaceTimeND n d t₀
        (matrixEuclideanBoundedC2ValueND D) q)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  intro i j
  have hij := parabolicC2AlphaNormLe_heatMildSpaceTimeND_Ioc
    hT hr0 hr1 (D i j) hH₀ (hsecondHolder i j) (hq i j)
    hC hH hHq (fun s y ↦ hqb s y i j)
    (fun s x y ↦ hqholder s x y i j) (hqParabolic i j)
  have hconst_nonneg : ∀ a b : Fin d,
      0 ≤ heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D a b) := by
    intro a b
    exact (parabolicC2AlphaNormLe_heatMildSpaceTimeND_Ioc
      hT hr0 hr1 (D a b) hH₀ (hsecondHolder a b) (hq a b)
      hC hH hHq (fun s y ↦ hqb s y a b)
      (fun s x y ↦ hqholder s x y a b) (hqParabolic a b)).nonneg
  have hle : heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D i j) ≤
      ∑ i : Fin d, ∑ j : Fin d,
        heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D i j) := by
    classical
    have hinner : heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D i j) ≤
        ∑ b : Fin d, heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D i b) :=
      Finset.single_le_sum (fun b _ ↦ hconst_nonneg i b) (Finset.mem_univ j)
    have houter :
        (∑ b : Fin d, heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D i b)) ≤
        ∑ a : Fin d, ∑ b : Fin d,
          heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D a b) :=
      Finset.single_le_sum
        (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ hconst_nonneg a b)
        (Finset.mem_univ i)
    exact hinner.trans houter
  change ParabolicC2AlphaNormLe
    (∑ a : Fin d, ∑ b : Fin d,
      heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq (D a b)) r
    (heatMildSpaceTimeND t₀ (D i j).value (fun s ↦ q s i j))
    (euclideanMildFiniteCylinderND n t₀ T)
  exact hij.mono_const hle

/-- Symmetric coefficient data and forcing make the matrix solution from the
preceding estimate a symmetric covariant-two-tensor field at every point. -/
theorem matrixHeatMildSpaceTimeND_isSymm_of_boundedC2
    {n d : ℕ} (t₀ : ℝ)
    (D : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n))
    (q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hD : ∀ i j, (D i j).value = (D j i).value)
    (hqSymm : ∀ s i j, q s i j = q s j i)
    (z : ℝ × (Fin n → ℝ)) :
    (matrixHeatMildSpaceTimeND n d t₀
      (matrixEuclideanBoundedC2ValueND D) q z).IsSymm := by
  exact matrixHeatMildParabolicSecondJetND_isSymm t₀ z.1
    (matrixEuclideanBoundedC2ValueND D) q hD hqSymm z.2

end AnalyticPDE
end RicciFlow
