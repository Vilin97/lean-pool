/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalExact
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.LocalizedZeroTrace

/-! # Field Spaces -/

namespace Homogenization
namespace Book
namespace Ch01

/-!
# Chapter 1 public field-space predicates

This module exposes the literal Hilbert-space potential/solenoidal quartet on
nonempty bounded open convex domains, together with representative-level
predicates retained for statements formulated for concrete functions.
-/

/-- The literal range of `H¹(U)` gradients in `HilbertVectorL2 U`.

The domain hypotheses are part of the Chapter 1 facade; the underlying exact
submodule construction itself is available on an arbitrary carrier. -/
noncomputable abbrev PotentialHilbertL2 {d : ℕ} (U : Set (Vec d))
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    Submodule ℝ (HilbertVectorL2 U) :=
  let _ := hU
  let _ := hne
  PotentialSolenoidalExact.potential U

/-- The literal range of `H¹₀(U)` gradients in `HilbertVectorL2 U`. -/
noncomputable abbrev PotentialZeroTraceHilbertL2 {d : ℕ} (U : Set (Vec d))
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    Submodule ℝ (HilbertVectorL2 U) :=
  let _ := hU
  let _ := hne
  PotentialSolenoidalExact.potentialZeroTrace U

/-- The exact solenoidal submodule, orthogonal to `PotentialZeroTraceHilbertL2`. -/
noncomputable abbrev SolenoidalHilbertL2 {d : ℕ} (U : Set (Vec d))
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    Submodule ℝ (HilbertVectorL2 U) :=
  let _ := hU
  let _ := hne
  PotentialSolenoidalExact.solenoidal U

/-- The exact zero-normal-trace solenoidal submodule, orthogonal to
`PotentialHilbertL2`. -/
noncomputable abbrev SolenoidalZeroNormalTraceHilbertL2 {d : ℕ} (U : Set (Vec d))
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    Submodule ℝ (HilbertVectorL2 U) :=
  let _ := hU
  let _ := hne
  PotentialSolenoidalExact.solenoidalZeroNormalTrace U

/-- The exact doubled submodule
`PotentialHilbertL2 U hU hne × SolenoidalHilbertL2 U hU hne`. -/
noncomputable abbrev PotentialSolenoidalHilbertL2 {d : ℕ} (U : Set (Vec d))
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    Submodule ℝ (HilbertVectorL2 U × HilbertVectorL2 U) :=
  let _ := hU
  let _ := hne
  PotentialSolenoidalExact.blockPotentialSolenoidal U

/-- The exact doubled submodule
`PotentialZeroTraceHilbertL2 U hU hne × SolenoidalZeroNormalTraceHilbertL2 U hU hne`. -/
noncomputable abbrev PotentialZeroTraceSolenoidalZeroNormalTraceHilbertL2
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) : Submodule ℝ (HilbertVectorL2 U × HilbertVectorL2 U) :=
  let _ := hU
  let _ := hne
  PotentialSolenoidalExact.blockPotentialZeroTraceSolenoidalZeroNormalTrace U

theorem mem_potentialHilbertL2_iff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (g : HilbertVectorL2 U) :
    g ∈ PotentialHilbertL2 U hU hne ↔
      ∃ u : H1Function U, u.gradToHilbertVectorL2 = g :=
  PotentialSolenoidalExact.mem_potential_iff g

theorem mem_potentialZeroTraceHilbertL2_iff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (g : HilbertVectorL2 U) :
    g ∈ PotentialZeroTraceHilbertL2 U hU hne ↔
      ∃ u : H10Function U, u.toH1Function.gradToHilbertVectorL2 = g :=
  PotentialSolenoidalExact.mem_potentialZeroTrace_iff g

theorem mem_solenoidalHilbertL2_iff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (g : HilbertVectorL2 U) :
    g ∈ SolenoidalHilbertL2 U hU hne ↔
      ∀ u : H10Function U, inner ℝ g u.toH1Function.gradToHilbertVectorL2 = 0 :=
  PotentialSolenoidalExact.mem_solenoidal_iff g

theorem mem_solenoidalZeroNormalTraceHilbertL2_iff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (g : HilbertVectorL2 U) :
    g ∈ SolenoidalZeroNormalTraceHilbertL2 U hU hne ↔
      ∀ u : H1Function U, inner ℝ g u.gradToHilbertVectorL2 = 0 :=
  PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff g

theorem potentialZeroTraceHilbertL2_le_potentialHilbertL2 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    PotentialZeroTraceHilbertL2 U hU hne ≤ PotentialHilbertL2 U hU hne :=
  PotentialSolenoidalExact.potentialZeroTrace_le_potential

theorem solenoidalZeroNormalTraceHilbertL2_le_solenoidalHilbertL2 {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    SolenoidalZeroNormalTraceHilbertL2 U hU hne ≤ SolenoidalHilbertL2 U hU hne :=
  PotentialSolenoidalExact.solenoidalZeroNormalTrace_le_solenoidal

theorem mem_potentialSolenoidalHilbertL2_iff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (g : HilbertVectorL2 U × HilbertVectorL2 U) :
    g ∈ PotentialSolenoidalHilbertL2 U hU hne ↔
      g.1 ∈ PotentialHilbertL2 U hU hne ∧ g.2 ∈ SolenoidalHilbertL2 U hU hne :=
  PotentialSolenoidalExact.mem_blockPotentialSolenoidal_iff g

theorem mem_potentialZeroTraceSolenoidalZeroNormalTraceHilbertL2_iff {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (g : HilbertVectorL2 U × HilbertVectorL2 U) :
    g ∈ PotentialZeroTraceSolenoidalZeroNormalTraceHilbertL2 U hU hne ↔
      g.1 ∈ PotentialZeroTraceHilbertL2 U hU hne ∧
        g.2 ∈ SolenoidalZeroNormalTraceHilbertL2 U hU hne :=
  PotentialSolenoidalExact.mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace_iff g

/-- A field in the manuscript space `L_sol,0(U)` has zero restricted-volume
integral. -/
theorem integral_eq_zero_of_mem_solenoidalZeroNormalTraceHilbertL2 {d : ℕ} [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (g : HilbertVectorL2 U) (hg : g ∈ SolenoidalZeroNormalTraceHilbertL2 U hU hne) :
    ∫ x, g x ∂volumeMeasureOn U = 0 :=
  PotentialSolenoidalExact.integral_eq_zero_of_mem_solenoidalZeroNormalTrace hU g hg

/-- The normalized-domain average of a field in the manuscript space
`L_sol,0(U)` vanishes. -/
theorem normalizedAverage_eq_zero_of_mem_solenoidalZeroNormalTraceHilbertL2
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) (g : HilbertVectorL2 U)
    (hg : g ∈ SolenoidalZeroNormalTraceHilbertL2 U hU hne) :
    (hU.toBoundedMeasurableDomain hne).average g (by
      change MeasureTheory.Integrable g (volumeMeasureOn U)
      let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
        hU.isFiniteMeasure_restrict_volume
      exact (MeasureTheory.Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)) = 0 :=
  PotentialSolenoidalExact.average_eq_zero_of_mem_solenoidalZeroNormalTrace hU hne g hg

/-- Representative-level `L²` potential predicate on `U`, stated up to a.e.
equality.  The literal Hilbert-space submodule is `PotentialHilbertL2`. -/
def PotentialFieldOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  MemVectorL2 U f ∧ ∃ u : H1Function U, f =ᵐ[volumeMeasureOn U] u.grad

/-- Representative-level zero-trace `L²` potential predicate on `U`, stated up
to a.e. equality.  The literal Hilbert-space submodule is
`PotentialZeroTraceHilbertL2`. -/
def PotentialZeroTraceFieldOn {d : ℕ} (U : Set (Vec d))
    (f : Vec d → Vec d) : Prop :=
  MemVectorL2 U f ∧
    ∃ u : H10Function U, f =ᵐ[volumeMeasureOn U] u.toH1Function.grad

/-- Public localized scalar zero-trace condition.

This is the a.e./Sobolev replacement for saying that a scalar function vanishes
on the part of `∂Ω` seen through the localization window `V`: every smooth
compactly supported cutoff localized in `V` turns the function into an
admissible `H¹₀(Ω)` test function. -/
abbrev LocalizedZeroTraceFunctionOn {d : ℕ} (Ω V : Set (Vec d))
    (u : Vec d → ℝ) : Prop :=
  Homogenization.LocalizedZeroTraceFunctionOn Ω V u

/-- Representative-level `L²` solenoidal predicate on `U`. The integral
formulation is a.e.-insensitive once the `L²` representative is fixed; the
literal Hilbert-space submodule is `SolenoidalHilbertL2`. -/
def SolenoidalFieldOn {d : ℕ} (U : Set (Vec d)) (g : Vec d → Vec d) : Prop :=
  MemVectorL2 U g ∧
    ∀ φ : H10Function U,
      ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume = 0

/-- Representative-level `L²` solenoidal predicate with zero normal trace on
`U`.  The literal Hilbert-space submodule is
`SolenoidalZeroNormalTraceHilbertL2`. -/
def SolenoidalZeroNormalTraceFieldOn {d : ℕ} (U : Set (Vec d))
    (g : Vec d → Vec d) : Prop :=
  MemVectorL2 U g ∧
    ∀ φ : H1Function U,
      ∫ x in U, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume = 0

end Ch01
end Book
end Homogenization
