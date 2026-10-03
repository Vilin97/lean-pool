/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Locally uniform convergence infrastructure

This file packages mathlib's locally uniform convergence definitions and
theorems in the concrete `Point n -> Real` setting used by the viscosity
solution development.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {ι : Type*}

/-- Locally uniform convergence on a domain of functions `Point n -> Real`. -/
abbrev LocallyUniformTendstoOn (uᵢ : ι -> Point n -> Real) (u : Point n -> Real)
    (l : Filter ι) (C : Set (Point n)) : Prop :=
  TendstoLocallyUniformlyOn uᵢ u l C

/-- Uniform convergence on a domain of functions `Point n -> Real`. -/
abbrev UniformTendstoOn (uᵢ : ι -> Point n -> Real) (u : Point n -> Real)
    (l : Filter ι) (C : Set (Point n)) : Prop :=
  TendstoUniformlyOn uᵢ u l C

theorem locallyUniformTendstoOn_iff
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)} :
    LocallyUniformTendstoOn uᵢ u l C ↔
      ∀ ε > 0, ∀ x ∈ C, ∃ t ∈ nhdsWithin x C,
        ∀ᶠ i in l, ∀ y ∈ t, dist (u y) (uᵢ i y) < ε :=
  Metric.tendstoLocallyUniformlyOn_iff

theorem uniformTendstoOn_iff
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)} :
    UniformTendstoOn uᵢ u l C ↔
      ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ C, dist (u x) (uᵢ i x) < ε :=
  Metric.tendstoUniformlyOn_iff

theorem UniformTendstoOn.eventually_forall_abs_sub_lt
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)}
    (h : UniformTendstoOn uᵢ u l C) {ε : Real} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ C, |uᵢ i x - u x| < ε := by
  exact (uniformTendstoOn_iff.mp h ε hε).mono fun i hi x hx =>
    by simpa [Real.dist_eq, abs_sub_comm] using hi x hx

theorem UniformTendstoOn.eventually_forall_le_add
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)}
    (h : UniformTendstoOn uᵢ u l C) {ε : Real} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ C, uᵢ i x <= u x + ε := by
  exact (h.eventually_forall_abs_sub_lt hε).mono fun i hi x hx =>
    le_of_lt <| by
      simpa [add_comm] using lt_add_of_sub_right_lt (abs_lt.mp (hi x hx)).2

theorem UniformTendstoOn.eventually_forall_sub_le
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)}
    (h : UniformTendstoOn uᵢ u l C) {ε : Real} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ C, u x <= uᵢ i x + ε := by
  exact (h.eventually_forall_abs_sub_lt hε).mono fun i hi x hx =>
    have hlt : |u x - uᵢ i x| < ε := by
      simpa [abs_sub_comm] using hi x hx
    le_of_lt <| by
      simpa [add_comm] using lt_add_of_sub_right_lt (abs_lt.mp hlt).2

theorem UniformTendstoOn.locallyUniformTendstoOn
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)}
    (h : UniformTendstoOn uᵢ u l C) :
    LocallyUniformTendstoOn uᵢ u l C :=
  h.tendstoLocallyUniformlyOn

theorem locallyUniformTendstoOn_mono
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C D : Set (Point n)}
    (h : LocallyUniformTendstoOn uᵢ u l C) (hDC : D ⊆ C) :
    LocallyUniformTendstoOn uᵢ u l D :=
  TendstoLocallyUniformlyOn.mono h hDC

theorem locallyUniformTendstoOn_tendsto_at
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)} {x : Point n}
    (h : LocallyUniformTendstoOn uᵢ u l C) (hx : x ∈ C) :
    Tendsto (fun i => uᵢ i x) l (nhds (u x)) :=
  TendstoLocallyUniformlyOn.tendsto_at h hx

theorem locallyUniformTendstoOn_uniformTendstoOn_of_isCompact
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {K : Set (Point n)}
    (h : LocallyUniformTendstoOn uᵢ u l K) (hK : IsCompact K) :
    UniformTendstoOn uᵢ u l K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp h

theorem locallyUniformTendstoOn_uniformTendstoOn_compact_subset
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C K : Set (Point n)}
    (h : LocallyUniformTendstoOn uᵢ u l C) (hKC : K ⊆ C) (hK : IsCompact K) :
    UniformTendstoOn uᵢ u l K :=
  locallyUniformTendstoOn_uniformTendstoOn_of_isCompact
    (TendstoLocallyUniformlyOn.mono h hKC) hK

theorem locallyUniformTendstoOn_continuousOn
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)}
    (h : LocallyUniformTendstoOn uᵢ u l C)
    (hcont : ∃ᶠ i in l, ContinuousOn (uᵢ i) C) :
    ContinuousOn u C :=
  TendstoLocallyUniformlyOn.continuousOn h hcont

theorem locallyUniformTendstoOn_tendsto_comp
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {xᵢ : ι -> Point n}
    (h : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hx : x ∈ C)
    (hxᵢ : Tendsto xᵢ l (nhdsWithin x C)) :
    Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)) :=
  TendstoLocallyUniformlyOn.tendsto_comp h hu hx hxᵢ

/--
Moving-point scalar convergence under locally uniform convergence, stated with
ordinary convergence plus eventual membership in the domain.
-/
theorem locallyUniformTendstoOn_tendsto_comp_of_tendsto_nhds_eventually_mem
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real}
    {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {xᵢ : ι -> Point n}
    (h : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hx : x ∈ C)
    (hxᵢ : Tendsto xᵢ l (nhds x))
    (hmem : ∀ᶠ i in l, xᵢ i ∈ C) :
    Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)) :=
  locallyUniformTendstoOn_tendsto_comp h hu hx
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within xᵢ hxᵢ hmem)

end ViscositySolns
