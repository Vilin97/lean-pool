/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.NaturalClarkOcone
import LeanPool.Malliavin.Malliavin.WienerChaos

/-!
# Martingale representation from the Brownian chaos tower

This file connects the selected homogeneous Wiener chaos tower to the closed range of the
natural Brownian Itô integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [CompleteSpace W] [BorelSpace W] in
/-- Any total graded family whose zeroth component is killed by centering and whose positive
components lie in the natural Itô range supplies martingale representation. -/
theorem naturalMartingaleRepresentation_of_total_submodules
    (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (K : ℕ → Submodule ℝ (RandomL2 P))
    (htotal : (⨆ n : ℕ, K n).topologicalClosure = ⊤)
    (hzero : K 0 ≤ (centeredPartCLM (P := P)).ker)
    (hpositive : ∀ n : ℕ, 0 < n → K n ≤ naturalItoRange hB hsm hnat) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  let M : Submodule ℝ (RandomL2 P) :=
    (naturalItoRange hB hsm hnat).comap
      (centeredPartCLM (P := P)).toLinearMap
  have hMclosed : IsClosed (M : Set (RandomL2 P)) := by
    exact (isClosed_naturalItoRange hB hsm hnat).preimage
      (centeredPartCLM (P := P)).continuous
  have hgraded (n : ℕ) : K n ≤ M := by
    cases n with
    | zero =>
        intro F hF
        change centeredPartCLM F ∈ naturalItoRange hB hsm hnat
        rw [show centeredPartCLM F = 0 by exact hzero hF]
        exact zero_mem _
    | succ n =>
        intro F hF
        change centeredPartCLM F ∈ naturalItoRange hB hsm hnat
        have hFmem : F ∈ naturalItoRange hB hsm hnat :=
          hpositive (n + 1) (Nat.zero_lt_succ n) hF
        have hcentered : CameronMartin.expectationMap P F = 0 :=
          naturalItoRange_le_expectationMap_ker hB hsm hnat hFmem
        have hexpect : expectationL2 F = 0 := by
          rw [expectationL2, ← CameronMartin.expectationMap_apply, hcentered]
          exact map_zero _
        rw [centeredPartCLM_apply, hexpect, sub_zero]
        exact hFmem
  have htop : (⊤ : Submodule ℝ (RandomL2 P)) ≤ M := by
    rw [← htotal]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hgraded) hMclosed
  intro F
  have hmem : centeredPartCLM F ∈ naturalItoRange hB hsm hnat := by
    exact htop (Submodule.mem_top : F ∈ (⊤ : Submodule ℝ (RandomL2 P)))
  obtain ⟨U, hU⟩ := hmem
  refine ⟨U, ?_⟩
  rw [centeredPartCLM_apply] at hU
  change naturalItoIntegral hB hsm hnat U = F - expectationL2 F at hU
  calc
    F = expectationL2 F + (F - expectationL2 F) := by abel
    _ = expectationL2 F + naturalItoIntegral hB hsm hnat U := by rw [← hU]

omit [CompleteSpace W] [BorelSpace W] in
/-- If every positive selected homogeneous chaos is represented by a natural Itô terminal
value, then the natural Itô integral has the martingale-representation property. -/
theorem naturalMartingaleRepresentation_of_positiveChaos_le_naturalItoRange
    (hB : IsPreBrownianReal B P) (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  let K : Submodule ℝ (RandomL2 P) :=
    (naturalItoRange hB hsm hnat).comap
      (centeredPartCLM (P := P)).toLinearMap
  have hKclosed : IsClosed (K : Set (RandomL2 P)) := by
    exact (isClosed_naturalItoRange hB hsm hnat).preimage
      (centeredPartCLM (P := P)).continuous
  have hconstant : constantRandomVariables P ≤
      (centeredPartCLM (P := P)).ker := by
    unfold constantRandomVariables
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨c, rfl⟩
      rw [LinearMap.mem_ker]
      change centeredPartCLM ((Lp.constL 2 P ℝ) c) = 0
      rw [centeredPartCLM_apply, expectationL2]
      have hconst : ∫ w, (Lp.const 2 P c) w ∂P = c := by
        rw [integral_congr_ae (Lp.coeFn_const 2 P c)]
        simp
      rw [Lp.constL_apply, hconst, sub_self]
    · exact (centeredPartCLM (P := P)).isClosed_ker
  have hzero :
      (homogeneousChaos hB 0 : Submodule ℝ (RandomL2 P)) ≤ K := by
    intro F hF
    change centeredPartCLM F ∈ naturalItoRange hB hsm hnat
    have hFconst : F ∈ constantRandomVariables P := by
      rw [← homogeneousChaos_zero_eq_constants hB]
      exact hF
    rw [show centeredPartCLM F = 0 by exact hconstant hFconst]
    exact zero_mem _
  have hpositiveCentered (n : ℕ) (hn : 0 < n) :
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤ K := by
    intro F hF
    change centeredPartCLM F ∈ naturalItoRange hB hsm hnat
    have hcentered : CameronMartin.expectationMap P F = 0 := by
      have hle : (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
          (CameronMartin.expectationMap P).ker := by
        unfold homogeneousChaos
        apply Submodule.topologicalClosure_minimal
        · rintro _ ⟨f, rfl⟩
          rw [LinearMap.mem_ker]
          change CameronMartin.expectationMap P (multipleIntegralCLM hB n f) = 0
          rw [CameronMartin.expectationMap_apply]
          exact integral_multipleIntegralCLM hB hn f
        · exact (CameronMartin.expectationMap P).isClosed_ker
      exact hle hF
    have hexpect : expectationL2 F = 0 := by
      rw [expectationL2, ← CameronMartin.expectationMap_apply, hcentered]
      exact map_zero _
    rw [centeredPartCLM_apply, hexpect, sub_zero]
    exact hpositive n hn hF
  have hchaos (n : ℕ) :
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤ K := by
    cases n with
    | zero => exact hzero
    | succ n => exact hpositiveCentered (n + 1) (Nat.zero_lt_succ n)
  have htop : (⊤ : Submodule ℝ (RandomL2 P)) ≤ K := by
    rw [← homogeneousChaos_total hB generated]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hchaos) hKclosed
  intro F
  have hmem : centeredPartCLM F ∈ naturalItoRange hB hsm hnat := by
    exact htop (Submodule.mem_top : F ∈ (⊤ : Submodule ℝ (RandomL2 P)))
  obtain ⟨U, hU⟩ := hmem
  refine ⟨U, ?_⟩
  rw [centeredPartCLM_apply] at hU
  change naturalItoIntegral hB hsm hnat U = F - expectationL2 F at hU
  calc
    F = expectationL2 F + (F - expectationL2 F) := by abel
    _ = expectationL2 F + naturalItoIntegral hB hsm hnat U := by rw [← hU]

/-- Construct the natural Brownian Clark--Ocone family from two inputs localized to the selected
chaos tower and the smooth Malliavin core, respectively. -/
noncomputable def ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat)
    (hDuality : SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalIto hB coordinate coordinate_apply generated hsm hnat
    (naturalMartingaleRepresentation_of_positiveChaos_le_naturalItoRange
      hB generated hsm hnat hpositive)
    (naturalItoDuality_of_smooth
      hB coordinate coordinate_apply generated hsm hnat hDuality)

/-- The chaos/smooth-core constructor uses the genuine Brownian integral on every elementary
adapted process. -/
theorem ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat)
    (hDuality : SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    (ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality
      hB coordinate coordinate_apply generated hsm hnat hpositive hDuality
      ).IsBrownianOnElementary := by
  apply ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
  rfl

/-- A fully localized constructor: positive-chaos range inclusion supplies MRT, while duality is
needed only for smooth terminal functionals against one-step adapted processes. -/
noncomputable def ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothElementaryDuality
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat)
    (hElementary : SmoothElementaryNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality
    hB coordinate coordinate_apply generated hsm hnat hpositive
      (smoothNaturalItoDuality_of_elementary
        hB coordinate coordinate_apply generated hsm hnat hElementary)

/-- The fully localized constructor is Brownian-compatible on elementary adapted processes. -/
theorem ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothElementaryDuality_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat)
    (hElementary : SmoothElementaryNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    (ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothElementaryDuality
      hB coordinate coordinate_apply generated hsm hnat hpositive hElementary
      ).IsBrownianOnElementary := by
  apply ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
  rfl

end Malliavin

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
