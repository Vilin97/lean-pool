/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.HalfRelaxedLimits.CompactSelection

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Semijet approximation for half-relaxed limits

This file proves that ordinary semijets of half-relaxed limits belong to the
tail closures of the approximating semijet graphs.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {ι : Type*}

/--
If the hypotheses in
`exists_isMaxOn_hasSecondOrderExpansionWithin_mem_nhds_upperHalfRelaxedLimit`
hold for every set of indices `A` with `A ∈ l` and every neighborhood of
`((x, upperHalfRelaxedLimit uᵢ l C x), JAt x)`, then that graph point belongs
to `TailClosureSuperjetGraph C uᵢ l`.
-/
theorem tailClosureSuperjetGraph_upperHalfRelaxedLimit_of_strictContact
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {JAt : Point n -> Jet n}
    (hxC : x ∈ C)
    (hKne : K.Nonempty) (hKcompact : IsCompact K) (hKC : K ⊆ C)
    (hKnhds : K ∈ nhdsWithin x C)
    (hbddAbove : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousOn φ C) (hφK : ContinuousOn φ K)
    (hJAt : ContinuousWithinAt JAt K x)
    (hφexp : ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (JAt y))
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        upperHalfRelaxedLimit uᵢ l C y - φ y <=
          upperHalfRelaxedLimit uᵢ l C x - φ x - δ) :
    ((x, upperHalfRelaxedLimit uᵢ l C x), JAt x) ∈
      TailClosureSuperjetGraph C uᵢ l := by
  refine tailClosureSuperjetGraph_of_forall_nhds_exists_components ?_
  intro A hA W hW
  rcases exists_isMaxOn_hasSecondOrderExpansionWithin_mem_nhds_upperHalfRelaxedLimit
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      (JAt := JAt) hxC hKne hKcompact hKC hKnhds hbddAbove hcobddBelow
      hφC hφK hJAt hφexp husc hstrict hA hW with
    ⟨i, hiA, z, hzK, Jᵢ, hKz, hmax, hφ, hWmem⟩
  have hgraphK : ((z, uᵢ i z), Jᵢ) ∈ SuperjetGraph K (uᵢ i) :=
    superjetGraph_of_isMaxOn_sub_hasSecondOrderExpansionWithin hzK hmax hφ
  have hnhds : nhdsWithin z K = nhdsWithin z C :=
    nhdsWithin_eq_of_subset_of_mem_nhdsWithin hKC hKz
  have hgraphC : ((z, uᵢ i z), Jᵢ) ∈ SuperjetGraph C (uᵢ i) :=
    mem_superjetGraph_of_mem_of_nhdsWithin_eq hKC hnhds hgraphK
  exact ⟨i, hiA, z, uᵢ i z, Jᵢ, hgraphC, hWmem⟩

/--
If the hypotheses in
`exists_isMinOn_hasSecondOrderExpansionWithin_mem_nhds_lowerHalfRelaxedLimit`
hold for every set of indices `A` with `A ∈ l` and every neighborhood of
`((x, lowerHalfRelaxedLimit uᵢ l C x), JAt x)`, then that graph point belongs
to `TailClosureSubjetGraph C uᵢ l`.
-/
theorem tailClosureSubjetGraph_lowerHalfRelaxedLimit_of_strictContact
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {JAt : Point n -> Jet n}
    (hxC : x ∈ C)
    (hKne : K.Nonempty) (hKcompact : IsCompact K) (hKC : K ⊆ C)
    (hKnhds : K ∈ nhdsWithin x C)
    (hbddBelow : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousOn φ C) (hφK : ContinuousOn φ K)
    (hJAt : ContinuousWithinAt JAt K x)
    (hφexp : ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (JAt y))
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        lowerHalfRelaxedLimit uᵢ l C x - φ x + δ <=
          lowerHalfRelaxedLimit uᵢ l C y - φ y) :
    ((x, lowerHalfRelaxedLimit uᵢ l C x), JAt x) ∈
      TailClosureSubjetGraph C uᵢ l := by
  refine tailClosureSubjetGraph_of_forall_nhds_exists_components ?_
  intro A hA W hW
  rcases exists_isMinOn_hasSecondOrderExpansionWithin_mem_nhds_lowerHalfRelaxedLimit
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      (JAt := JAt) hxC hKne hKcompact hKC hKnhds hbddBelow hcobddAbove
      hφC hφK hJAt hφexp hlsc hstrict hA hW with
    ⟨i, hiA, z, hzK, Jᵢ, hKz, hmin, hφ, hWmem⟩
  have hgraphK : ((z, uᵢ i z), Jᵢ) ∈ SubjetGraph K (uᵢ i) :=
    subjetGraph_of_isMinOn_sub_hasSecondOrderExpansionWithin hzK hmin hφ
  have hnhds : nhdsWithin z K = nhdsWithin z C :=
    nhdsWithin_eq_of_subset_of_mem_nhdsWithin hKC hKz
  have hgraphC : ((z, uᵢ i z), Jᵢ) ∈ SubjetGraph C (uᵢ i) :=
    mem_subjetGraph_of_mem_of_nhdsWithin_eq hKC hnhds hgraphK
  exact ⟨i, hiA, z, uᵢ i z, Jᵢ, hgraphC, hWmem⟩

/--
Let `upperLimit x = upperHalfRelaxedLimit uᵢ l C x`. If
`J ∈ Superjet C upperLimit x` and `δ > 0`, then the graph point with the same value
and gradient as `J` and Hessian `J.hessian + δ I` belongs to
`TailClosureSuperjetGraph C uᵢ l`.

The proof uses the superjet inequality with Hessian
`J.hessian + (δ / 2) I` to obtain a compact set `K ⊆ C` on which the
quadratic polynomial with Hessian `J.hessian + δ I` has strict maximum
contact with `upperLimit` at `x`.
-/
theorem tailClosureSuperjetGraph_upperHalfRelaxedLimit_superjet_hessian_add_identity
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {C : Set (Point n)} [LocallyCompactSpace C]
    {x : Point n} {J : Jet n} {δ : Real}
    (hxC : x ∈ C)
    (hbddAbove : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) C)
    (hδ : 0 < δ)
    (hJ : J ∈ Superjet C (upperHalfRelaxedLimit uᵢ l C) x) :
    ((x, upperHalfRelaxedLimit uᵢ l C x),
        { gradient := J.gradient, hessian := J.hessian + δ • (1 : Hessian n) }) ∈
      TailClosureSuperjetGraph C uᵢ l := by
  let ubar : Point n -> Real := upperHalfRelaxedLimit uᵢ l C
  let P : Set (Point n) := {y |
    ubar y <= quadraticModel x (ubar x) J.gradient
      (J.hessian + (δ / 2) • (1 : Hessian n)) y}
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hP : P ∈ nhdsWithin x C := by
    exact
      eventually_le_quadraticModel_hessian_add_identity_of_superjet
        (C := C) (u := ubar) (x := x) (J := J) hhalf hJ
  rcases exists_inter_closedBall_compactRelativeNeighborhood_subset_of_mem_nhdsWithin
      (C := C) (P := P) hxC hP with
    ⟨r, _hr, hK, hKP⟩
  let K : Set (Point n) := C ∩ Metric.closedBall x r
  let H : Hessian n := J.hessian + δ • (1 : Hessian n)
  let φ : Point n -> Real := fun y => quadraticModel x (ubar x) J.gradient H y
  let JAt : Point n -> Jet n := quadraticModelJetAt x J.gradient H
  have hsupport : ∀ y : Point n, y ∈ K ->
      ubar y <= quadraticModel x (ubar x) J.gradient
        (J.hessian + (δ / 2) • (1 : Hessian n)) y := by
    intro y hy
    exact hKP hy
  have hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ η > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        ubar y - φ y <= ubar x - φ x - η := by
    simpa [K, H, φ, ubar] using
      strict_isMaxOn_sub_quadraticModel_add_identity_of_forall_le_half
        (K := K) (u := ubar) (x := x) (p := J.gradient) (X := J.hessian)
        (δ := δ) hδ hsupport
  have hφC : ContinuousOn φ C :=
    (continuous_quadraticModel x (ubar x) J.gradient H).continuousOn
  have hφK : ContinuousOn φ K :=
    (continuous_quadraticModel x (ubar x) J.gradient H).continuousOn
  have hJAt : ContinuousWithinAt JAt K x :=
    (continuous_quadraticModelJetAt x J.gradient H).continuousWithinAt
  have hφexp : ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (JAt y) := by
    intro y _hy
    exact hasSecondOrderExpansionWithin_quadraticModel_recenter x (ubar x) J.gradient H y
  have huscK : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K :=
    husc.mono fun _ hi => hi.mono hK.subset
  have htail :
      ((x, upperHalfRelaxedLimit uᵢ l C x), JAt x) ∈
        TailClosureSuperjetGraph C uᵢ l :=
    tailClosureSuperjetGraph_upperHalfRelaxedLimit_of_strictContact
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      (JAt := JAt) hxC hK.nonempty hK.isCompact hK.subset hK.mem_nhdsWithin
      hbddAbove (hcobddBelow x hxC) hφC hφK hJAt hφexp huscK hstrict
  simpa [JAt, H, quadraticModelJetAt, ubar] using htail

/--
Let `lowerLimit x = lowerHalfRelaxedLimit uᵢ l C x`. If
`J ∈ Subjet C lowerLimit x` and `δ > 0`, then the graph point with the same value
and gradient as `J` and Hessian `J.hessian - δ I` belongs to
`TailClosureSubjetGraph C uᵢ l`.

The proof uses the subjet inequality with Hessian
`J.hessian - (δ / 2) I` to obtain a compact set `K ⊆ C` on which the
quadratic polynomial with Hessian `J.hessian - δ I` has strict minimum
contact with `lowerLimit` at `x`.
-/
theorem tailClosureSubjetGraph_lowerHalfRelaxedLimit_subjet_hessian_sub_identity
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {C : Set (Point n)} [LocallyCompactSpace C]
    {x : Point n} {J : Jet n} {δ : Real}
    (hxC : x ∈ C)
    (hbddBelow : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) C)
    (hδ : 0 < δ)
    (hJ : J ∈ Subjet C (lowerHalfRelaxedLimit uᵢ l C) x) :
    ((x, lowerHalfRelaxedLimit uᵢ l C x),
        { gradient := J.gradient, hessian := J.hessian - δ • (1 : Hessian n) }) ∈
      TailClosureSubjetGraph C uᵢ l := by
  let uunder : Point n -> Real := lowerHalfRelaxedLimit uᵢ l C
  let P : Set (Point n) := {y |
    quadraticModel x (uunder x) J.gradient
      (J.hessian - (δ / 2) • (1 : Hessian n)) y <= uunder y}
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hP : P ∈ nhdsWithin x C := by
    exact
      eventually_quadraticModel_hessian_sub_identity_le_of_subjet
        (C := C) (u := uunder) (x := x) (J := J) hhalf hJ
  rcases exists_inter_closedBall_compactRelativeNeighborhood_subset_of_mem_nhdsWithin
      (C := C) (P := P) hxC hP with
    ⟨r, _hr, hK, hKP⟩
  let K : Set (Point n) := C ∩ Metric.closedBall x r
  let H : Hessian n := J.hessian - δ • (1 : Hessian n)
  let φ : Point n -> Real := fun y => quadraticModel x (uunder x) J.gradient H y
  let JAt : Point n -> Jet n := quadraticModelJetAt x J.gradient H
  have hsupport : ∀ y : Point n, y ∈ K ->
      quadraticModel x (uunder x) J.gradient
        (J.hessian - (δ / 2) • (1 : Hessian n)) y <= uunder y := by
    intro y hy
    exact hKP hy
  have hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ η > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        uunder x - φ x + η <= uunder y - φ y := by
    simpa [K, H, φ, uunder] using
      strict_isMinOn_sub_quadraticModel_sub_identity_of_forall_half_le
        (K := K) (u := uunder) (x := x) (p := J.gradient) (X := J.hessian)
        (δ := δ) hδ hsupport
  have hφC : ContinuousOn φ C :=
    (continuous_quadraticModel x (uunder x) J.gradient H).continuousOn
  have hφK : ContinuousOn φ K :=
    (continuous_quadraticModel x (uunder x) J.gradient H).continuousOn
  have hJAt : ContinuousWithinAt JAt K x :=
    (continuous_quadraticModelJetAt x J.gradient H).continuousWithinAt
  have hφexp : ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (JAt y) := by
    intro y _hy
    exact hasSecondOrderExpansionWithin_quadraticModel_recenter x (uunder x) J.gradient H y
  have hlscK : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K :=
    hlsc.mono fun _ hi => hi.mono hK.subset
  have htail :
      ((x, lowerHalfRelaxedLimit uᵢ l C x), JAt x) ∈
        TailClosureSubjetGraph C uᵢ l :=
    tailClosureSubjetGraph_lowerHalfRelaxedLimit_of_strictContact
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      (JAt := JAt) hxC hK.nonempty hK.isCompact hK.subset hK.mem_nhdsWithin
      hbddBelow (hcobddAbove x hxC) hφC hφK hJAt hφexp hlscK hstrict
  simpa [JAt, H, quadraticModelJetAt, uunder] using htail

/--
Let `upperLimit x = upperHalfRelaxedLimit uᵢ l C x`. If
`J ∈ Superjet C upperLimit x`, then `((x, upperLimit x), J)` belongs to
`TailClosureSuperjetGraph C uᵢ l`.
-/
theorem tailClosureSuperjetGraph_upperHalfRelaxedLimit_superjet
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {C : Set (Point n)} [LocallyCompactSpace C]
    {x : Point n} {J : Jet n}
    (hxC : x ∈ C)
    (hbddAbove : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) C)
    (hJ : J ∈ Superjet C (upperHalfRelaxedLimit uᵢ l C) x) :
    ((x, upperHalfRelaxedLimit uᵢ l C x), J) ∈
      TailClosureSuperjetGraph C uᵢ l := by
  cases J with
  | mk p X =>
    refine tailClosureSuperjetGraph_of_nat_hessian_add_identity ?_
    intro k
    have hδ : 0 < 1 / ((k : Real) + 1) := by positivity
    exact tailClosureSuperjetGraph_upperHalfRelaxedLimit_superjet_hessian_add_identity
      (uᵢ := uᵢ) (l := l) (C := C) (x := x)
      (J := { gradient := p, hessian := X })
      hxC hbddAbove hcobddBelow husc hδ hJ

/--
Let `lowerLimit x = lowerHalfRelaxedLimit uᵢ l C x`. If
`J ∈ Subjet C lowerLimit x`, then `((x, lowerLimit x), J)` belongs to
`TailClosureSubjetGraph C uᵢ l`.
-/
theorem tailClosureSubjetGraph_lowerHalfRelaxedLimit_subjet
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {C : Set (Point n)} [LocallyCompactSpace C]
    {x : Point n} {J : Jet n}
    (hxC : x ∈ C)
    (hbddBelow : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) C)
    (hJ : J ∈ Subjet C (lowerHalfRelaxedLimit uᵢ l C) x) :
    ((x, lowerHalfRelaxedLimit uᵢ l C x), J) ∈
      TailClosureSubjetGraph C uᵢ l := by
  cases J with
  | mk p X =>
    refine tailClosureSubjetGraph_of_nat_hessian_sub_identity ?_
    intro k
    have hδ : 0 < 1 / ((k : Real) + 1) := by positivity
    exact tailClosureSubjetGraph_lowerHalfRelaxedLimit_subjet_hessian_sub_identity
      (uᵢ := uᵢ) (l := l) (C := C) (x := x)
      (J := { gradient := p, hessian := X })
      hxC hbddBelow hcobddAbove hlsc hδ hJ

/--
Compact-contact neighborhood criterion for half-relaxed superjet
approximation.

Let `upperLimit x = upperHalfRelaxedLimit uᵢ l C x`. Suppose that for every set of
indices `A` with `A ∈ l` and every neighborhood `W` of `((x, upperLimit x), J)`,
there exist `i ∈ A`, `z ∈ K`, and a jet `Jᵢ` such that `K` is a relative
neighborhood of `z` in `C`, `z` is a maximum point of `uᵢ i - φ` on `K`, `φ`
has second-order expansion `Jᵢ` at `z` within `K`, and
`((z, uᵢ i z), Jᵢ) ∈ W`. Then `((x, upperLimit x), J)` belongs to the tail closure of
the approximating superjet graphs on `C`.
-/
theorem tailClosureSuperjetGraph_upperHalfRelaxedLimit_of_forall_nhds_exists_isMaxOn
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {J : Jet n} {φ : Point n -> Real}
    (hKC : K ⊆ C)
    (h : ∀ A : Set ι, A ∈ l ->
      ∀ W : Set ((Point n × Real) × Jet n),
        W ∈ nhds ((x, upperHalfRelaxedLimit uᵢ l C x), J) ->
          ∃ i ∈ A, ∃ z ∈ K, ∃ Jᵢ : Jet n,
            K ∈ nhdsWithin z C ∧
            IsMaxOn (fun y => uᵢ i y - φ y) K z ∧
            HasSecondOrderExpansionWithin K φ z Jᵢ ∧
            ((z, uᵢ i z), Jᵢ) ∈ W) :
    ((x, upperHalfRelaxedLimit uᵢ l C x), J) ∈
      TailClosureSuperjetGraph C uᵢ l := by
  refine tailClosureSuperjetGraph_of_forall_nhds_exists_components ?_
  intro A hA W hW
  rcases h A hA W hW with
    ⟨i, hiA, z, hzK, Jᵢ, hKnhds, hmax, hφ, hWmem⟩
  have hgraphK : ((z, uᵢ i z), Jᵢ) ∈ SuperjetGraph K (uᵢ i) :=
    superjetGraph_of_isMaxOn_sub_hasSecondOrderExpansionWithin hzK hmax hφ
  have hnhds : nhdsWithin z K = nhdsWithin z C :=
    nhdsWithin_eq_of_subset_of_mem_nhdsWithin hKC hKnhds
  have hgraphC : ((z, uᵢ i z), Jᵢ) ∈ SuperjetGraph C (uᵢ i) :=
    mem_superjetGraph_of_mem_of_nhdsWithin_eq hKC hnhds hgraphK
  exact ⟨i, hiA, z, uᵢ i z, Jᵢ, hgraphC, hWmem⟩

/--
Compact-contact neighborhood criterion for half-relaxed subjet approximation.

Let `lowerLimit x = lowerHalfRelaxedLimit uᵢ l C x`. Suppose that for every set of
indices `A` with `A ∈ l` and every neighborhood `W` of `((x, lowerLimit x), J)`,
there exist `i ∈ A`, `z ∈ K`, and a jet `Jᵢ` such that `K` is a relative
neighborhood of `z` in `C`, `z` is a minimum point of `uᵢ i - φ` on `K`, `φ`
has second-order expansion `Jᵢ` at `z` within `K`, and
`((z, uᵢ i z), Jᵢ) ∈ W`. Then `((x, lowerLimit x), J)` belongs to the tail closure of
the approximating subjet graphs on `C`.
-/
theorem tailClosureSubjetGraph_lowerHalfRelaxedLimit_of_forall_nhds_exists_isMinOn
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {J : Jet n} {φ : Point n -> Real}
    (hKC : K ⊆ C)
    (h : ∀ A : Set ι, A ∈ l ->
      ∀ W : Set ((Point n × Real) × Jet n),
        W ∈ nhds ((x, lowerHalfRelaxedLimit uᵢ l C x), J) ->
          ∃ i ∈ A, ∃ z ∈ K, ∃ Jᵢ : Jet n,
            K ∈ nhdsWithin z C ∧
            IsMinOn (fun y => uᵢ i y - φ y) K z ∧
            HasSecondOrderExpansionWithin K φ z Jᵢ ∧
            ((z, uᵢ i z), Jᵢ) ∈ W) :
    ((x, lowerHalfRelaxedLimit uᵢ l C x), J) ∈
      TailClosureSubjetGraph C uᵢ l := by
  refine tailClosureSubjetGraph_of_forall_nhds_exists_components ?_
  intro A hA W hW
  rcases h A hA W hW with
    ⟨i, hiA, z, hzK, Jᵢ, hKnhds, hmin, hφ, hWmem⟩
  have hgraphK : ((z, uᵢ i z), Jᵢ) ∈ SubjetGraph K (uᵢ i) :=
    subjetGraph_of_isMinOn_sub_hasSecondOrderExpansionWithin hzK hmin hφ
  have hnhds : nhdsWithin z K = nhdsWithin z C :=
    nhdsWithin_eq_of_subset_of_mem_nhdsWithin hKC hKnhds
  have hgraphC : ((z, uᵢ i z), Jᵢ) ∈ SubjetGraph C (uᵢ i) :=
    mem_subjetGraph_of_mem_of_nhdsWithin_eq hKC hnhds hgraphK
  exact ⟨i, hiA, z, uᵢ i z, Jᵢ, hgraphC, hWmem⟩

end ViscositySolns
