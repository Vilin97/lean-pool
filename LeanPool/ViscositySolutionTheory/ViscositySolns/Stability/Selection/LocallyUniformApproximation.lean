/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.Selection.CompactContact

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact selection lemmas for stability arguments (LocallyUniformApproximation)

Part of the compact-extremum selection tools used in viscosity stability
proofs. Split from `Selection.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Under locally uniform convergence, selected compact maximum contacts whose
points and jets converge give tail-closure membership for the limiting
superjet triple.
-/
theorem tailClosureSuperjetGraph_of_locallyUniform_isMaxOn_sub_hasSecondOrderExpansionWithin
    {ι : Type*} {C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hxC : x ∈ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ C ∧
      IsMaxOn (fun y => uᵢ i y - φ y) C (xᵢ i) ∧
      HasSecondOrderExpansionWithin C φ (xᵢ i) (Jᵢ i)) :
    ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l := by
  have hmem : ∀ᶠ i in l, xᵢ i ∈ C := hcontact.mono fun _ hi => hi.1
  have hscalar : Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)) :=
    locallyUniformTendstoOn_tendsto_comp_of_tendsto_nhds_eventually_mem
      hlu hu hxC hx hmem
  exact tailClosureSuperjetGraph_of_tendsto_isMaxOn_sub_hasSecondOrderExpansionWithin
    hx hscalar hJ hcontact

/--
Under locally uniform convergence, selected compact minimum contacts whose
points and jets converge give tail-closure membership for the limiting subjet
triple.
-/
theorem tailClosureSubjetGraph_of_locallyUniform_isMinOn_sub_hasSecondOrderExpansionWithin
    {ι : Type*} {C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hxC : x ∈ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ C ∧
      IsMinOn (fun y => uᵢ i y - φ y) C (xᵢ i) ∧
      HasSecondOrderExpansionWithin C φ (xᵢ i) (Jᵢ i)) :
    ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l := by
  have hmem : ∀ᶠ i in l, xᵢ i ∈ C := hcontact.mono fun _ hi => hi.1
  have hscalar : Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)) :=
    locallyUniformTendstoOn_tendsto_comp_of_tendsto_nhds_eventually_mem
      hlu hu hxC hx hmem
  exact tailClosureSubjetGraph_of_tendsto_isMinOn_sub_hasSecondOrderExpansionWithin
    hx hscalar hJ hcontact

/--
Let `K ⊆ C`. Suppose `uᵢ` converges locally uniformly to `u` on `K`,
`u` is continuous within `K` at `x`, `x ∈ K`, `xᵢ → x`, and `Jᵢ → J` along `l`.
Assume that the set of indices `i` for which `xᵢ i ∈ K`,
`IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i)`, and
`HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i)` all hold belongs to `l`.
Assume also that the set of indices `i` for which
`K ∈ nhdsWithin (xᵢ i) C` belongs to `l`. Then `((x, u x), J)` belongs to the
tail closure of the superjet graphs on `C`.
-/
theorem tailClosureSuperjetGraph_to_ambient_of_locallyUniform_isMaxOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x) (hxK : x ∈ K)
    (hx : Tendsto xᵢ l (nhds x))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i))
    (hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C) :
    ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l := by
  have hmem : ∀ᶠ i in l, xᵢ i ∈ K := hcontact.mono fun _ hi => hi.1
  have hscalar : Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)) :=
    locallyUniformTendstoOn_tendsto_comp_of_tendsto_nhds_eventually_mem
      hlu hu hxK hx hmem
  exact tailClosureSuperjetGraph_to_ambient_of_tendsto_isMaxOn_sub
    hKC hx hscalar hJ hcontact hKnhds

/--
Let `K ⊆ C`. Suppose `uᵢ` converges locally uniformly to `u` on `K`,
`u` is continuous within `K` at `x`, `x ∈ K`, `xᵢ → x`, and `Jᵢ → J` along `l`.
Assume that the set of indices `i` for which `xᵢ i ∈ K`,
`IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i)`, and
`HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i)` all hold belongs to `l`.
Assume also that the set of indices `i` for which
`K ∈ nhdsWithin (xᵢ i) C` belongs to `l`. Then `((x, u x), J)` belongs to the
tail closure of the subjet graphs on `C`.
-/
theorem tailClosureSubjetGraph_to_ambient_of_locallyUniform_isMinOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x) (hxK : x ∈ K)
    (hx : Tendsto xᵢ l (nhds x))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i))
    (hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C) :
    ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l := by
  have hmem : ∀ᶠ i in l, xᵢ i ∈ K := hcontact.mono fun _ hi => hi.1
  have hscalar : Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)) :=
    locallyUniformTendstoOn_tendsto_comp_of_tendsto_nhds_eventually_mem
      hlu hu hxK hx hmem
  exact tailClosureSubjetGraph_to_ambient_of_tendsto_isMinOn_sub
    hKC hx hscalar hJ hcontact hKnhds

/--
Selected compact maximum contacts on a compact relative neighborhood give
tail-closure membership over the ambient domain.
-/
theorem tailClosureSuperjetGraph_to_ambient_of_compactRelativeNeighborhood_isMaxOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hK : CompactRelativeNeighborhood C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hx : Tendsto xᵢ l (nhds x))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i)) :
    ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l := by
  have hmemC : ∀ᶠ i in l, xᵢ i ∈ C :=
    hcontact.mono fun _ hi => hK.subset hi.1
  have hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C :=
    hK.eventually_mem_nhdsWithin hx hmemC
  exact tailClosureSuperjetGraph_to_ambient_of_locallyUniform_isMaxOn_sub
    hK.subset hlu hu hK.point_mem hx hJ hcontact hKnhds

/--
Selected compact minimum contacts on a compact relative neighborhood give
tail-closure membership over the ambient domain.
-/
theorem tailClosureSubjetGraph_to_ambient_of_compactRelativeNeighborhood_isMinOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hK : CompactRelativeNeighborhood C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hx : Tendsto xᵢ l (nhds x))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i)) :
    ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l := by
  have hmemC : ∀ᶠ i in l, xᵢ i ∈ C :=
    hcontact.mono fun _ hi => hK.subset hi.1
  have hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C :=
    hK.eventually_mem_nhdsWithin hx hmemC
  exact tailClosureSubjetGraph_to_ambient_of_locallyUniform_isMinOn_sub
    hK.subset hlu hu hK.point_mem hx hJ hcontact hKnhds

/--
Assume `K` is nonempty and compact, and `φ` is continuous on `K`. If the set of
indices `i` for which `uᵢ i` is upper semicontinuous on `K` belongs to `l`,
then the set of indices `i` for which there exists `x ∈ K` satisfying
`IsMaxOn (fun y => uᵢ i y - φ y) K x` belongs to `l`.
-/
theorem eventually_exists_isMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
    {ι : Type*} {K : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {φ : Point n -> Real} {l : Filter ι}
    (hne : K.Nonempty) (hK : IsCompact K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hφ : ContinuousOn φ K) :
    ∀ᶠ i in l, ∃ x ∈ K, IsMaxOn (fun y => uᵢ i y - φ y) K x := by
  exact husc.mono fun i hi =>
    exists_isMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
      hne hK hi hφ

/--
A strict compact maximizer of `u - φ` attracts compact maximizers of
`uᵢ - φ` under uniform convergence on the compact set.

The strictness hypothesis is deliberately local-neighborhood shaped: outside
each neighborhood of `x₀`, the value of `u - φ` on `K` is separated below its
value at `x₀` by a positive gap.
-/
theorem tendsto_argmax_sub_of_uniformTendstoOn_of_strict
    {ι : Type*} {K : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {u φ : Point n -> Real} {l : Filter ι}
    {x₀ : Point n} {xᵢ : ι -> Point n}
    (hunif : UniformTendstoOn uᵢ u l K)
    (hx₀ : x₀ ∈ K)
    (hargmax : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i))
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x₀ ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x₀ - φ x₀ - δ) :
    Tendsto xᵢ l (nhdsWithin x₀ K) := by
  have hmemK : ∀ᶠ i in l, xᵢ i ∈ K := hargmax.mono fun _ hi => hi.1
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within xᵢ ?_ hmemK
  rw [Filter.Tendsto]
  intro V hV
  change ∀ᶠ i in l, xᵢ i ∈ V
  rcases hstrict V hV with ⟨δ, hδpos, hgap⟩
  let ε : Real := δ / 3
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have htwice : 2 * ε < δ := by
    dsimp [ε]
    linarith
  have hupper := hunif.eventually_forall_le_add hεpos
  have hlower := hunif.eventually_forall_sub_le hεpos
  filter_upwards [hargmax, hupper, hlower] with i hi hle hsub
  by_contra hnotV
  have hmax :
      uᵢ i x₀ - φ x₀ <= uᵢ i (xᵢ i) - φ (xᵢ i) :=
    isMaxOn_iff.mp hi.2 x₀ hx₀
  have hx₀approx : u x₀ - φ x₀ <= uᵢ i x₀ - φ x₀ + ε := by
    have hsubx₀ := hsub x₀ hx₀
    linarith
  have hxiapprox :
      uᵢ i (xᵢ i) - φ (xᵢ i) <= u (xᵢ i) - φ (xᵢ i) + ε := by
    have hlexi := hle (xᵢ i) hi.1
    linarith
  have hnear : u x₀ - φ x₀ <= u (xᵢ i) - φ (xᵢ i) + 2 * ε := by
    linarith
  have hgapxi : u (xᵢ i) - φ (xᵢ i) <= u x₀ - φ x₀ - δ :=
    hgap (xᵢ i) hi.1 hnotV
  linarith

/--
A strict compact minimizer of `u - φ` attracts compact minimizers of
`uᵢ - φ` under uniform convergence on the compact set.

The strictness hypothesis is deliberately local-neighborhood shaped: outside
each neighborhood of `x₀`, the value of `u - φ` on `K` is separated above its
value at `x₀` by a positive gap.
-/
theorem tendsto_argmin_sub_of_uniformTendstoOn_of_strict
    {ι : Type*} {K : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {u φ : Point n -> Real} {l : Filter ι}
    {x₀ : Point n} {xᵢ : ι -> Point n}
    (hunif : UniformTendstoOn uᵢ u l K)
    (hx₀ : x₀ ∈ K)
    (hargmin : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i))
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x₀ ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x₀ - φ x₀ + δ <= u y - φ y) :
    Tendsto xᵢ l (nhdsWithin x₀ K) := by
  have hmemK : ∀ᶠ i in l, xᵢ i ∈ K := hargmin.mono fun _ hi => hi.1
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within xᵢ ?_ hmemK
  rw [Filter.Tendsto]
  intro V hV
  change ∀ᶠ i in l, xᵢ i ∈ V
  rcases hstrict V hV with ⟨δ, hδpos, hgap⟩
  let ε : Real := δ / 3
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have htwice : 2 * ε < δ := by
    dsimp [ε]
    linarith
  have hupper := hunif.eventually_forall_le_add hεpos
  have hlower := hunif.eventually_forall_sub_le hεpos
  filter_upwards [hargmin, hupper, hlower] with i hi hle hsub
  by_contra hnotV
  have hmin :
      uᵢ i (xᵢ i) - φ (xᵢ i) <= uᵢ i x₀ - φ x₀ :=
    isMinOn_iff.mp hi.2 x₀ hx₀
  have hx₀approx : uᵢ i x₀ - φ x₀ <= u x₀ - φ x₀ + ε := by
    have hlex₀ := hle x₀ hx₀
    linarith
  have hxiapprox :
      u (xᵢ i) - φ (xᵢ i) <= uᵢ i (xᵢ i) - φ (xᵢ i) + ε := by
    have hsubxi := hsub (xᵢ i) hi.1
    linarith
  have hnear : u (xᵢ i) - φ (xᵢ i) <= u x₀ - φ x₀ + 2 * ε := by
    linarith
  have hgapxi : u x₀ - φ x₀ + δ <= u (xᵢ i) - φ (xᵢ i) :=
    hgap (xᵢ i) hi.1 hnotV
  linarith

/--
Compact relative neighborhood version of the strict maximum selection theorem.

The hypothesis `hJ` says that the jet assigned to the test function varies
continuously at the contact point, and `hφexp` says this assigned jet is a
second-order expansion of the test function at every selected point.
-/
theorem tailClosureSuperjetGraph_to_ambient_of_compactRelativeNeighborhood_strict_exists_isMaxOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {JAt : Point n -> Jet n}
    (hK : CompactRelativeNeighborhood C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hJ : ContinuousWithinAt JAt K x)
    (hφcont : ContinuousOn φ K)
    (hφexp : ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (JAt y))
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ) :
    ((x, u x), JAt x) ∈ TailClosureSuperjetGraph C uᵢ l := by
  classical
  let xᵢ : ι -> Point n := fun i =>
    if h : ∃ y ∈ K, IsMaxOn (fun z => uᵢ i z - φ z) K y then
      Classical.choose h
    else x
  have hexists : ∀ᶠ i in l, ∃ y ∈ K,
      IsMaxOn (fun z => uᵢ i z - φ z) K y :=
    eventually_exists_isMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
      hK.nonempty hK.isCompact husc hφcont
  have hargmax : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) := by
    filter_upwards [hexists] with i hi
    have hchoose := Classical.choose_spec hi
    simpa [xᵢ, hi] using hchoose
  have hunif : UniformTendstoOn uᵢ u l K :=
    locallyUniformTendstoOn_uniformTendstoOn_of_isCompact hlu hK.isCompact
  have hxWithin : Tendsto xᵢ l (nhdsWithin x K) :=
    tendsto_argmax_sub_of_uniformTendstoOn_of_strict
      hunif hK.point_mem hargmax hstrict
  have hx : Tendsto xᵢ l (nhds x) := tendsto_nhds_of_tendsto_nhdsWithin hxWithin
  have hJtendsto : Tendsto (fun i => JAt (xᵢ i)) l (nhds (JAt x)) :=
    hJ.tendsto.comp hxWithin
  have hcontact : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (JAt (xᵢ i)) :=
    hargmax.mono fun _ hi => ⟨hi.1, hi.2, hφexp _ hi.1⟩
  exact tailClosureSuperjetGraph_to_ambient_of_compactRelativeNeighborhood_isMaxOn_sub
    hK hlu hu hx hJtendsto hcontact

/--
Compact relative neighborhood version of the strict minimum selection theorem.

The hypothesis `hJ` says that the jet assigned to the test function varies
continuously at the contact point, and `hφexp` says this assigned jet is a
second-order expansion of the test function at every selected point.
-/
theorem tailClosureSubjetGraph_to_ambient_of_compactRelativeNeighborhood_strict_exists_isMinOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {JAt : Point n -> Jet n}
    (hK : CompactRelativeNeighborhood C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hJ : ContinuousWithinAt JAt K x)
    (hφcont : ContinuousOn φ K)
    (hφexp : ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (JAt y))
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y) :
    ((x, u x), JAt x) ∈ TailClosureSubjetGraph C uᵢ l := by
  classical
  let xᵢ : ι -> Point n := fun i =>
    if h : ∃ y ∈ K, IsMinOn (fun z => uᵢ i z - φ z) K y then
      Classical.choose h
    else x
  have hexists : ∀ᶠ i in l, ∃ y ∈ K,
      IsMinOn (fun z => uᵢ i z - φ z) K y := by
    exact hlsc.mono fun i hi =>
      exists_isMinOn_sub_continuousOn_of_lowerSemicontinuousOn_isCompact
        hK.nonempty hK.isCompact hi hφcont
  have hargmin : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) := by
    filter_upwards [hexists] with i hi
    have hchoose := Classical.choose_spec hi
    simpa [xᵢ, hi] using hchoose
  have hunif : UniformTendstoOn uᵢ u l K :=
    locallyUniformTendstoOn_uniformTendstoOn_of_isCompact hlu hK.isCompact
  have hxWithin : Tendsto xᵢ l (nhdsWithin x K) :=
    tendsto_argmin_sub_of_uniformTendstoOn_of_strict
      hunif hK.point_mem hargmin hstrict
  have hx : Tendsto xᵢ l (nhds x) := tendsto_nhds_of_tendsto_nhdsWithin hxWithin
  have hJtendsto : Tendsto (fun i => JAt (xᵢ i)) l (nhds (JAt x)) :=
    hJ.tendsto.comp hxWithin
  have hcontact : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (JAt (xᵢ i)) :=
    hargmin.mono fun _ hi => ⟨hi.1, hi.2, hφexp _ hi.1⟩
  exact tailClosureSubjetGraph_to_ambient_of_compactRelativeNeighborhood_isMinOn_sub
    hK hlu hu hx hJtendsto hcontact

/--
Locally uniform approximation theorem with a positive identity-Hessian
perturbation for superjets.

If `J = (p, X)` belongs to `Superjet C u x`, `δ > 0`, and `uᵢ` converges
locally uniformly to `u` on `C`, then `((x, u x), (p, X + δ I))` belongs to
`TailClosureSuperjetGraph C uᵢ l`. Equivalently, for every set of indices `A`
with `A ∈ l`, this graph point lies in the closure of
`⋃ i ∈ A, SuperjetGraph C (uᵢ i)`.
-/
theorem tailClosureSuperjetGraph_of_locallyUniform_superjet_hessian_add_identity
    {ι : Type*} {C : Set (Point n)} [LocallyCompactSpace C]
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n} {δ : Real}
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hxC : x ∈ C)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) C)
    (hδ : 0 < δ) (hJ : J ∈ Superjet C u x) :
    ((x, u x), { gradient := J.gradient, hessian := J.hessian + δ • (1 : Hessian n) }) ∈
      TailClosureSuperjetGraph C uᵢ l := by
  let P : Set (Point n) := {y |
    u y <= quadraticModel x (u x) J.gradient
      (J.hessian + (δ / 2) • (1 : Hessian n)) y}
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hP : P ∈ nhdsWithin x C := by
    exact
      eventually_le_quadraticModel_hessian_add_identity_of_superjet hhalf hJ
  rcases exists_inter_closedBall_compactRelativeNeighborhood_subset_of_mem_nhdsWithin
      (C := C) (P := P) hxC hP with
    ⟨r, _hr, hK, hKP⟩
  let K : Set (Point n) := C ∩ Metric.closedBall x r
  let H : Hessian n := J.hessian + δ • (1 : Hessian n)
  let φ : Point n -> Real := fun y => quadraticModel x (u x) J.gradient H y
  let JAt : Point n -> Jet n := quadraticModelJetAt x J.gradient H
  have hsupport : ∀ y : Point n, y ∈ K ->
      u y <= quadraticModel x (u x) J.gradient
        (J.hessian + (δ / 2) • (1 : Hessian n)) y := by
    intro y hy
    exact hKP hy
  have hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ η > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - η := by
    simpa [K, H, φ] using
      strict_isMaxOn_sub_quadraticModel_add_identity_of_forall_le_half
        (K := K) (u := u) (x := x) (p := J.gradient) (X := J.hessian)
        (δ := δ) hδ hsupport
  have hluK : LocallyUniformTendstoOn uᵢ u l K :=
    locallyUniformTendstoOn_mono hlu hK.subset
  have huK : ContinuousWithinAt u K x := by
    rw [ContinuousWithinAt, hK.nhdsWithin_eq]
    exact hu
  have hJAt : ContinuousWithinAt JAt K x :=
    (continuous_quadraticModelJetAt x J.gradient H).continuousWithinAt
  have hφcont : ContinuousOn φ K :=
    (continuous_quadraticModel x (u x) J.gradient H).continuousOn
  have hφexp : ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (JAt y) := by
    intro y _hy
    exact hasSecondOrderExpansionWithin_quadraticModel_recenter x (u x) J.gradient H y
  have huscK : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K :=
    husc.mono fun _ hi => hi.mono hK.subset
  have htail :
      ((x, u x), JAt x) ∈ TailClosureSuperjetGraph C uᵢ l :=
    tailClosureSuperjetGraph_to_ambient_of_compactRelativeNeighborhood_strict_exists_isMaxOn_sub
      hK hluK huK hJAt hφcont hφexp huscK hstrict
  simpa [JAt, H, quadraticModelJetAt] using htail

/--
Locally uniform approximation theorem with a negative identity-Hessian
perturbation for subjets.

If `J = (p, X)` belongs to `Subjet C u x`, `δ > 0`, and `uᵢ` converges locally
uniformly to `u` on `C`, then `((x, u x), (p, X - δ I))` belongs to
`TailClosureSubjetGraph C uᵢ l`. Equivalently, for every set of indices `A`
with `A ∈ l`, this graph point lies in the closure of
`⋃ i ∈ A, SubjetGraph C (uᵢ i)`.
-/
theorem tailClosureSubjetGraph_of_locallyUniform_subjet_hessian_sub_identity
    {ι : Type*} {C : Set (Point n)} [LocallyCompactSpace C]
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n} {δ : Real}
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hxC : x ∈ C)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) C)
    (hδ : 0 < δ) (hJ : J ∈ Subjet C u x) :
    ((x, u x), { gradient := J.gradient, hessian := J.hessian - δ • (1 : Hessian n) }) ∈
      TailClosureSubjetGraph C uᵢ l := by
  let P : Set (Point n) := {y |
    quadraticModel x (u x) J.gradient
      (J.hessian - (δ / 2) • (1 : Hessian n)) y <= u y}
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hP : P ∈ nhdsWithin x C := by
    exact
      eventually_quadraticModel_hessian_sub_identity_le_of_subjet hhalf hJ
  rcases exists_inter_closedBall_compactRelativeNeighborhood_subset_of_mem_nhdsWithin
      (C := C) (P := P) hxC hP with
    ⟨r, _hr, hK, hKP⟩
  let K : Set (Point n) := C ∩ Metric.closedBall x r
  let H : Hessian n := J.hessian - δ • (1 : Hessian n)
  let φ : Point n -> Real := fun y => quadraticModel x (u x) J.gradient H y
  let JAt : Point n -> Jet n := quadraticModelJetAt x J.gradient H
  have hsupport : ∀ y : Point n, y ∈ K ->
      quadraticModel x (u x) J.gradient
        (J.hessian - (δ / 2) • (1 : Hessian n)) y <= u y := by
    intro y hy
    exact hKP hy
  have hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ η > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + η <= u y - φ y := by
    simpa [K, H, φ] using
      strict_isMinOn_sub_quadraticModel_sub_identity_of_forall_half_le
        (K := K) (u := u) (x := x) (p := J.gradient) (X := J.hessian)
        (δ := δ) hδ hsupport
  have hluK : LocallyUniformTendstoOn uᵢ u l K :=
    locallyUniformTendstoOn_mono hlu hK.subset
  have huK : ContinuousWithinAt u K x := by
    rw [ContinuousWithinAt, hK.nhdsWithin_eq]
    exact hu
  have hJAt : ContinuousWithinAt JAt K x :=
    (continuous_quadraticModelJetAt x J.gradient H).continuousWithinAt
  have hφcont : ContinuousOn φ K :=
    (continuous_quadraticModel x (u x) J.gradient H).continuousOn
  have hφexp : ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (JAt y) := by
    intro y _hy
    exact hasSecondOrderExpansionWithin_quadraticModel_recenter x (u x) J.gradient H y
  have hlscK : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K :=
    hlsc.mono fun _ hi => hi.mono hK.subset
  have htail :
      ((x, u x), JAt x) ∈ TailClosureSubjetGraph C uᵢ l :=
    tailClosureSubjetGraph_to_ambient_of_compactRelativeNeighborhood_strict_exists_isMinOn_sub
      hK hluK huK hJAt hφcont hφexp hlscK hstrict
  simpa [JAt, H, quadraticModelJetAt] using htail

/--
Locally uniform approximation theorem for superjets, in tail-closure graph
form.

If `J ∈ Superjet C u x` and `uᵢ` converges locally uniformly to `u` on `C`,
then `((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l`. Equivalently, for
every set of indices `A` with `A ∈ l`, this graph point lies in the closure of
`⋃ i ∈ A, SuperjetGraph C (uᵢ i)`.
-/
theorem tailClosureSuperjetGraph_of_locallyUniform_superjet
    {ι : Type*} {C : Set (Point n)} [LocallyCompactSpace C]
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hxC : x ∈ C)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) C)
    (hJ : J ∈ Superjet C u x) :
    ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l := by
  cases J with
  | mk p X =>
    refine tailClosureSuperjetGraph_of_nat_hessian_add_identity ?_
    intro k
    have hδ : 0 < 1 / ((k : Real) + 1) := by positivity
    exact tailClosureSuperjetGraph_of_locallyUniform_superjet_hessian_add_identity
      hlu hu hxC husc hδ hJ

/--
Locally uniform approximation theorem for subjets, in tail-closure graph form.

If `J ∈ Subjet C u x` and `uᵢ` converges locally uniformly to `u` on `C`, then
`((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l`. Equivalently, for every set
of indices `A` with `A ∈ l`, this graph point lies in the closure of
`⋃ i ∈ A, SubjetGraph C (uᵢ i)`.
-/
theorem tailClosureSubjetGraph_of_locallyUniform_subjet
    {ι : Type*} {C : Set (Point n)} [LocallyCompactSpace C]
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hxC : x ∈ C)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) C)
    (hJ : J ∈ Subjet C u x) :
    ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l := by
  cases J with
  | mk p X =>
    refine tailClosureSubjetGraph_of_nat_hessian_sub_identity ?_
    intro k
    have hδ : 0 < 1 / ((k : Real) + 1) := by positivity
    exact tailClosureSubjetGraph_of_locallyUniform_subjet_hessian_sub_identity
      hlu hu hxC hlsc hδ hJ

end ViscositySolns
