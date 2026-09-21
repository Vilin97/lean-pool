/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.Calculus.ContDiff.Support
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.ChartData

/-! # Localization -/

@[expose] public section



/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.Localization`

Chart-based localization of scalar functions on a compact manifold.

Given finite vendorGeometryManifoldSobolevLocalization_chart data `d : FiniteChartData` (a finite family of vendorGeometryManifoldSobolevLocalization_chart centers with a smooth
partition of unity subordinate to those charts), we define a localization operation

`localize d f i : E → ℝ`

on the model space `E`, obtained by pulling back `ρ_i • f` along the extended vendorGeometryManifoldSobolevLocalization_chart
`(extChartAt I (d.center i)).symm` and extending by `0` outside the vendorGeometryManifoldSobolevLocalization_chart target.

For compact manifolds, the resulting function has compact support and is `C^1` (hence belongs to
the Euclidean `C1c` submodule used in the Euclidean Sobolev baseline).
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped _root_.Manifold

local notation "n∞" => (↑(⊤ : ℕ∞) : WithTop ℕ∞)

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
variable [I.Boundaryless]
variable [T2Space M] [CompactSpace M]

local instance instMeasurableSpaceM_SobolevLocalization : MeasurableSpace M := borel M
local instance instBorelSpaceM_SobolevLocalization : BorelSpace M := ⟨rfl⟩

abbrev vendorGeometryManifoldSobolevLocalization_Iℝ : ModelWithCorners ℝ ℝ ℝ := 𝓘(ℝ, ℝ)

namespace FiniteChartData

variable (d : FiniteChartData (H := H) (M := M) I)

abbrev vendorGeometryManifoldSobolevLocalization_chart (i : d.ι) : PartialEquiv M E :=
  extChartAt I (d.center i)

/-- The localization of a scalar function `f : M → ℝ` to a vendorGeometryManifoldSobolevLocalization_chart `i`, as a function on `E`. -/
noncomputable def localize (f : M → ℝ) (i : d.ι) : E → ℝ :=
  Set.indicator (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target fun y =>
    d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y)

/-- The closed set `closure (support (ρ i))` used to control the support of localizations. -/
def rhoSupportClosure (i : d.ι) : Set M :=
  closure (Function.support (d.ρ i : M → ℝ))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
lemma rhoSupportClosure_subset_source (i : d.ι) :
    rhoSupportClosure (d := d) i ⊆ (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).source := by
  simp [rhoSupportClosure, vendorGeometryManifoldSobolevLocalization_chart]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma isCompact_rhoSupportClosure (i : d.ι) : IsCompact (rhoSupportClosure (d := d) i) :=
  (isClosed_closure.isCompact)

/-- A compact subset of the vendorGeometryManifoldSobolevLocalization_chart model space containing the supports of all localizations. -/
def rhoSupportImage (i : d.ι) : Set E :=
  (vendorGeometryManifoldSobolevLocalization_chart (d := d) i) '' rhoSupportClosure (d := d) i

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma isCompact_rhoSupportImage (i : d.ι) : IsCompact (rhoSupportImage (d := d) i) := by
  classical
  -- `extChartAt` is continuous on its source, hence on `rhoSupportClosure`
  -- (which is contained in the source).
  refine (isCompact_rhoSupportClosure (d := d) i).image_of_continuousOn ?_
  exact (continuousOn_extChartAt (I := I) (x := d.center i)).mono
    (rhoSupportClosure_subset_source (d := d) (i := i))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] [CompactSpace M] in
lemma support_localize_subset_rhoSupportImage (f : M → ℝ) (i : d.ι) :
    Function.support (localize (d := d) f i) ⊆ rhoSupportImage (d := d) i := by
  intro y hy
  have hyT : y ∈ (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target := by
    by_contra hyT
    have : localize (d := d) f i y = 0 := by
      -- `indicator` vanishes outside the target.
      simpa [localize] using!
        (Set.indicator_of_notMem (s := (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target) (a := y)
            (f := fun y =>
              d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y)) hyT)
    exact hy this
  have hEq :
      localize (d := d) f i y =
        d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) := by
    -- On the target, `indicator` is the identity.
    simpa [localize] using!
      (Set.indicator_of_mem (s := (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target) (a := y)
        (f := fun y =>
          d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y)) hyT)
  have hyVal :
      d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) ≠ 0 := by
    intro h0
    apply hy
    calc
      localize (d := d) f i y =
          d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) := hEq
      _ = 0 := h0
  have hxRho : d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) ≠ 0 := by
    intro hx
    apply hyVal
    -- Avoid `simp` rewriting `mul_eq_zero` into a disjunction.
    rw [hx]
    simp
  have hx : (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y ∈ rhoSupportClosure (d := d) i := by
    -- A nonzero value implies membership in the (topological) support.
    refine subset_closure ?_
    exact hxRho
  refine ⟨(vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y, hx, ?_⟩
  -- On the target, `extChartAt` and its inverse satisfy `right_inv`.
  exact (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).right_inv hyT

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma tsupport_localize_subset_rhoSupportImage (f : M → ℝ) (i : d.ι) :
    tsupport (localize (d := d) f i) ⊆ rhoSupportImage (d := d) i := by
  have hImgClosed : IsClosed (rhoSupportImage (d := d) i) :=
    (isCompact_rhoSupportImage (d := d) i).isClosed
  refine (closure_minimal (support_localize_subset_rhoSupportImage (d := d) f i) hImgClosed)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] [CompactSpace M] in
lemma rhoSupportImage_subset_target (i : d.ι) :
    rhoSupportImage (d := d) i ⊆ (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).map_source (rhoSupportClosure_subset_source (d := d) (i := i) hx)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma tsupport_localize_subset_target (f : M → ℝ) (i : d.ι) :
    tsupport (localize (d := d) f i) ⊆ (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target :=
  (tsupport_localize_subset_rhoSupportImage (d := d) f i).trans
    (rhoSupportImage_subset_target (d := d) i)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma hasCompactSupport_localize (f : M → ℝ) (i : d.ι) :
    HasCompactSupport (localize (d := d) f i) := by
  -- `HasCompactSupport` is `IsCompact` of `tsupport`.
  have hClosed : IsClosed (tsupport (localize (d := d) f i)) :=
    isClosed_tsupport (f := localize (d := d) f i)
  exact (isCompact_rhoSupportImage (d := d) i).of_isClosed_subset hClosed
    (tsupport_localize_subset_rhoSupportImage (d := d) f i)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
lemma vendorGeometryManifoldSobolevLocalization_contDiffOn_localize_target {f : M → ℝ}
    (hf : ContMDiff I vendorGeometryManifoldSobolevLocalization_Iℝ 1 f) (i : d.ι) :
    ContDiffOn ℝ 1 (localize (d := d) f i) (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target := by
  classical
  -- On the vendorGeometryManifoldSobolevLocalization_chart target, `localize` is just composition with `extChartAt.symm`.
  have hOn :
      ContDiffOn ℝ 1
        (fun y =>
          d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y))
        (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target := by
    -- First show `C^1` smoothness in the manifold sense, then convert to `ContDiffOn`.
    have hρ : ContMDiff I vendorGeometryManifoldSobolevLocalization_Iℝ 1 fun x : M => d.ρ i x := by
      -- Each partition-of-unity function is `C^∞`, hence `C^1`.
      simpa using!
        (d.ρ i).contMDiff.of_le
          (by
            -- `SmoothPartitionOfUnity` yields `C^∞` functions, i.e. order `↑(⊤ : ℕ∞)`.
            simp : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    have hg : ContMDiff I vendorGeometryManifoldSobolevLocalization_Iℝ 1 fun x : M => d.ρ i x * f x :=
      hρ.mul hf
    have hs : ContMDiffOn 𝓘(ℝ, E) I 1 (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target := by
      -- This is `C^1` on the vendorGeometryManifoldSobolevLocalization_chart target.
      simpa [vendorGeometryManifoldSobolevLocalization_chart] using!
        (contMDiffOn_extChartAt_symm (I := I) (n := (1 : WithTop ℕ∞)) (x := d.center i))
    have hComp :
        ContMDiffOn 𝓘(ℝ, E) vendorGeometryManifoldSobolevLocalization_Iℝ 1
          (fun y : E => (fun x : M => d.ρ i x * f x) ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y))
          (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target :=
      (hg.comp_contMDiffOn hs)
    -- Convert `ContMDiffOn` to `ContDiffOn` for maps between vector spaces.
    simpa using! (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := E) (E' := ℝ)).1 hComp
  -- Rewrite `localize` as an indicator and use that on the target it's equal to
  -- the underlying function.
  have hEq :
      EqOn (localize (d := d) f i)
        (fun y =>
          d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y))
        (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target := by
    intro y hy
    simpa [localize] using!
      (Set.indicator_of_mem (s := (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target) (a := y)
        (f := fun y => d.ρ i ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y) * f ((vendorGeometryManifoldSobolevLocalization_chart (d := d) i).symm y)) hy)
  -- Transfer `ContDiffOn` along the pointwise equality on the domain set.
  exact hOn.congr hEq

section

omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]

/-- For a `C^1` function on a compact manifold, the vendorGeometryManifoldSobolevLocalization_chart-localization is a Euclidean `C1c`
function. -/
lemma localize_mem_C1c {f : M → ℝ} (hf : ContMDiff I vendorGeometryManifoldSobolevLocalization_Iℝ 1 f) (i : d.ι) :
    localize (d := d) f i ∈
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c (E := E) := by
  classical
  -- `localize` is `C^1` on the open vendorGeometryManifoldSobolevLocalization_chart target, and has support contained in it.
  have hOpen : IsOpen (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target :=
    isOpen_extChartAt_target (I := I) (x := d.center i)
  have hDiffOn : ContDiffOn ℝ 1 (localize (d := d) f i) (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target :=
    vendorGeometryManifoldSobolevLocalization_contDiffOn_localize_target (d := d) (f := f) hf i
  have hTsupport : tsupport (localize (d := d) f i) ⊆ (vendorGeometryManifoldSobolevLocalization_chart (d := d) i).target :=
    tsupport_localize_subset_target (d := d) (f := f) i
  have hDiff : ContDiff ℝ 1 (localize (d := d) f i) :=
    RellichKondrachov.Analysis.Calculus.ContDiff.contDiff_of_contDiffOn_of_tsupport_subset
      (𝕜 := ℝ) (E := E) (F := ℝ) hOpen hDiffOn hTsupport
  have hCs : HasCompactSupport (localize (d := d) f i) :=
    hasCompactSupport_localize (d := d) (f := f) i
  exact ⟨hDiff, hCs⟩

end

end FiniteChartData

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
