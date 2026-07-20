/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.Localization
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H2

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.LocalizationH2`

Chart-based localization of scalar functions on a compact manifold, at `C²` regularity.

This extends `RellichKondrachov.Geometry.Manifold.Sobolev.Localization` by showing that if
`f : M → ℝ` is `C²` in the manifold sense, then its chart localization belongs to Euclidean
`C²_c` (hence can be fed into the Euclidean `H²` baseline graph construction).

## Main result

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.localize_mem_C2c`
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped _root_.Manifold

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
variable [I.Boundaryless]
variable [T2Space M] [CompactSpace M]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceLocalizationH2 : MeasurableSpace M := borel M
local instance instBorelSpaceLocalizationH2 : BorelSpace M := ⟨rfl⟩

namespace FiniteChartData

variable (d : FiniteChartData (H := H) (M := M) I)

private abbrev chart (i : d.ι) : PartialEquiv M E :=
  extChartAt I (d.center i)

private abbrev Iℝ : ModelWithCorners ℝ ℝ ℝ := 𝓘(ℝ, ℝ)

omit [CompleteSpace E] [IsManifold I (1 : WithTop ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
private lemma contDiffOn_localize_target {f : M → ℝ}
    (hf : ContMDiff I Iℝ 2 f) (i : d.ι) :
    ContDiffOn ℝ 2 (localize (d := d) f i) (chart (d := d) i).target := by
  classical
  have hOn :
      ContDiffOn ℝ 2
        (fun y =>
          d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y))
        (chart (d := d) i).target := by
    have hρ : ContMDiff I Iℝ 2 fun x : M => d.ρ i x := by
      simpa using
        (d.ρ i).contMDiff.of_le
          (by
            -- `SmoothPartitionOfUnity` yields order `↑(⊤ : ℕ∞)`, so any finite order is admissible.
            exact (by decide : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
    have hg : ContMDiff I Iℝ 2 fun x : M => d.ρ i x * f x :=
      hρ.mul hf
    have hs :
        ContMDiffOn 𝓘(ℝ, E) I 2 (chart (d := d) i).symm (chart (d := d) i).target := by
      simpa [chart] using
        (contMDiffOn_extChartAt_symm (I := I) (n := (2 : WithTop ℕ∞)) (x := d.center i))
    have hComp :
        ContMDiffOn 𝓘(ℝ, E) Iℝ 2
          (fun y : E => (fun x : M => d.ρ i x * f x) ((chart (d := d) i).symm y))
          (chart (d := d) i).target :=
      (hg.comp_contMDiffOn hs)
    simpa using (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := E) (E' := ℝ)).1 hComp
  have hEq :
      EqOn (localize (d := d) f i)
        (fun y =>
          d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y))
        (chart (d := d) i).target := by
    intro y hy
    simpa [FiniteChartData.localize] using
      (Set.indicator_of_mem (s := (chart (d := d) i).target) (a := y)
        (f := fun y => d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y)) hy)
  exact hOn.congr hEq

section

omit [CompleteSpace E] [IsManifold I (1 : WithTop ℕ∞) M] [T2Space M]

/-- For a `C²` function on a compact manifold, the chart-localization is a Euclidean `C2c`
function. -/
lemma localize_mem_C2c {f : M → ℝ} (hf : ContMDiff I Iℝ 2 f) (i : d.ι) :
    localize (d := d) f i ∈
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C2c (E := E) := by
  classical
  have hOpen : IsOpen (chart (d := d) i).target :=
    isOpen_extChartAt_target (I := I) (x := d.center i)
  have hDiffOn : ContDiffOn ℝ 2 (localize (d := d) f i) (chart (d := d) i).target :=
    contDiffOn_localize_target (d := d) (I := I) (f := f) hf i
  have hTsupport : tsupport (localize (d := d) f i) ⊆ (chart (d := d) i).target :=
    FiniteChartData.tsupport_localize_subset_target (d := d) (I := I) (f := f) i
  have hDiff : ContDiff ℝ 2 (localize (d := d) f i) :=
    RellichKondrachov.Analysis.Calculus.ContDiff.contDiff_of_contDiffOn_of_tsupport_subset
      (𝕜 := ℝ) (E := E) (F := ℝ) hOpen hDiffOn hTsupport
  have hCs : HasCompactSupport (localize (d := d) f i) :=
    FiniteChartData.hasCompactSupport_localize (d := d) (I := I) (f := f) i
  exact ⟨hDiff, hCs⟩

end

end FiniteChartData

end

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
