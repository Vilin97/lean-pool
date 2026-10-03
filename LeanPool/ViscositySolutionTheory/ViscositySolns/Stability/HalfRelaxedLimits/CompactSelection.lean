/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.HalfRelaxedLimits.Basic
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.Selection

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact selection for half-relaxed limits

This file proves the compact maximum and minimum selection statements used to
approximate semijets of half-relaxed limits.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {ι : Type*}

/--
Assume the set of indices `i` such that `xᵢ i ∈ K` and
`IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i)` belongs to `l`. Then for every
`ε > 0` and every set of indices `A` with `A ∈ l`, there exists `i ∈ A`
such that `xᵢ i ∈ K` and
`upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i (xᵢ i) - φ (xᵢ i)`.
-/
theorem exists_selected_isMaxOn_upperHalfRelaxedLimit_sub_test_sub_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {xᵢ : ι -> Point n}
    {ε : Real} (hε : 0 < ε)
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφ : ContinuousWithinAt φ C x) (hKnhds : K ∈ nhdsWithin x C)
    (hargmax : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i))
    {A : Set ι} (hA : A ∈ l) :
    ∃ i ∈ A, xᵢ i ∈ K ∧
      upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i (xᵢ i) - φ (xᵢ i) := by
  let G : Set ι :=
    {i | xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i)}
  have hAG : A ∩ G ∈ l := inter_mem hA hargmax
  rcases exists_upperHalfRelaxedLimit_sub_test_sub_lt
      (uᵢ := uᵢ) (l := l) (C := C) (x := x) (φ := φ)
      hε hcobddBelow hφ hAG hKnhds with
    ⟨i, hiAG, y, hyK, hyval⟩
  have hiG : xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) := hiAG.2
  have hmax : uᵢ i y - φ y <= uᵢ i (xᵢ i) - φ (xᵢ i) := hiG.2 hyK
  exact ⟨i, hiAG.1, hiG.1, lt_of_lt_of_le hyval hmax⟩

/--
Assume the set of indices `i` such that `xᵢ i ∈ K` and
`IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i)` belongs to `l`. Then for every
`ε > 0` and every set of indices `A` with `A ∈ l`, there exists `i ∈ A`
such that `xᵢ i ∈ K` and
`uᵢ i (xᵢ i) - φ (xᵢ i) < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε`.
-/
theorem exists_selected_isMinOn_lt_lowerHalfRelaxedLimit_sub_test_add
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {xᵢ : ι -> Point n}
    {ε : Real} (hε : 0 < ε)
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφ : ContinuousWithinAt φ C x) (hKnhds : K ∈ nhdsWithin x C)
    (hargmin : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i))
    {A : Set ι} (hA : A ∈ l) :
    ∃ i ∈ A, xᵢ i ∈ K ∧
      uᵢ i (xᵢ i) - φ (xᵢ i) < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε := by
  let G : Set ι :=
    {i | xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i)}
  have hAG : A ∩ G ∈ l := inter_mem hA hargmin
  rcases exists_lt_lowerHalfRelaxedLimit_sub_test_add
      (uᵢ := uᵢ) (l := l) (C := C) (x := x) (φ := φ)
      hε hcobddAbove hφ hAG hKnhds with
    ⟨i, hiAG, y, hyK, hyval⟩
  have hiG : xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) := hiAG.2
  have hmin : uᵢ i (xᵢ i) - φ (xᵢ i) <= uᵢ i y - φ y := hiG.2 hyK
  exact ⟨i, hiAG.1, hiG.1, lt_of_le_of_lt hmin hyval⟩

/--
Assume `K` is nonempty and compact, `φ` is continuous on `K`, and the set of
indices `i` for which `uᵢ i` is upper semicontinuous on `K` belongs to `l`.
Then for every `ε > 0` and every set of indices `A` with `A ∈ l`, there
exist `i ∈ A` and `z ∈ K` such that
`IsMaxOn (fun y => uᵢ i y - φ y) K z` and
`upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i z - φ z`.
-/
theorem exists_isMaxOn_upperHalfRelaxedLimit_sub_test_sub_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousWithinAt φ C x) (hφK : ContinuousOn φ K)
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKnhds : K ∈ nhdsWithin x C)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    {A : Set ι} (hA : A ∈ l) :
    ∃ i ∈ A, ∃ z ∈ K,
      IsMaxOn (fun y => uᵢ i y - φ y) K z ∧
        upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i z - φ z := by
  have hmaxExists : ∀ᶠ i in l, ∃ z ∈ K,
      IsMaxOn (fun y => uᵢ i y - φ y) K z :=
    eventually_exists_isMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
      hKne hKcompact husc hφK
  let G : Set ι := {i | ∃ z ∈ K, IsMaxOn (fun y => uᵢ i y - φ y) K z}
  have hAG : A ∩ G ∈ l := inter_mem hA hmaxExists
  rcases exists_upperHalfRelaxedLimit_sub_test_sub_lt
      (uᵢ := uᵢ) (l := l) (C := C) (x := x) (φ := φ)
      hε hcobddBelow hφC hAG hKnhds with
    ⟨i, hiAG, y, hyK, hyval⟩
  rcases hiAG.2 with ⟨z, hzK, hzmax⟩
  have hmax : uᵢ i y - φ y <= uᵢ i z - φ z := hzmax hyK
  exact ⟨i, hiAG.1, z, hzK, hzmax, lt_of_lt_of_le hyval hmax⟩

/--
Assume `K` is nonempty and compact, `φ` is continuous on `K`, and the set of
indices `i` for which `uᵢ i` is lower semicontinuous on `K` belongs to `l`.
Then for every `ε > 0` and every set of indices `A` with `A ∈ l`, there
exist `i ∈ A` and `z ∈ K` such that
`IsMinOn (fun y => uᵢ i y - φ y) K z` and
`uᵢ i z - φ z < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε`.
-/
theorem exists_isMinOn_lt_lowerHalfRelaxedLimit_sub_test_add
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousWithinAt φ C x) (hφK : ContinuousOn φ K)
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKnhds : K ∈ nhdsWithin x C)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    {A : Set ι} (hA : A ∈ l) :
    ∃ i ∈ A, ∃ z ∈ K,
      IsMinOn (fun y => uᵢ i y - φ y) K z ∧
        uᵢ i z - φ z < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε := by
  have hminExists : ∀ᶠ i in l, ∃ z ∈ K,
      IsMinOn (fun y => uᵢ i y - φ y) K z := by
    exact hlsc.mono fun i hi =>
      exists_isMinOn_sub_continuousOn_of_lowerSemicontinuousOn_isCompact
        hKne hKcompact hi hφK
  let G : Set ι := {i | ∃ z ∈ K, IsMinOn (fun y => uᵢ i y - φ y) K z}
  have hAG : A ∩ G ∈ l := inter_mem hA hminExists
  rcases exists_lt_lowerHalfRelaxedLimit_sub_test_add
      (uᵢ := uᵢ) (l := l) (C := C) (x := x) (φ := φ)
      hε hcobddAbove hφC hAG hKnhds with
    ⟨i, hiAG, y, hyK, hyval⟩
  rcases hiAG.2 with ⟨z, hzK, hzmin⟩
  have hmin : uᵢ i z - φ z <= uᵢ i y - φ y := hzmin hyK
  exact ⟨i, hiAG.1, z, hzK, hzmin, lt_of_le_of_lt hmin hyval⟩

/--
For a strict maximum contact of the upper half-relaxed limit on a compact set
`K`, compact maximum points of `uᵢ i - φ` can be chosen in any prescribed
neighborhood of the contact point.

More precisely, for every `ε > 0`, every set of indices `A` with `A ∈ l`,
and every neighborhood `V` of `x`, there exist `i ∈ A` and `z ∈ K ∩ V` such
that `z` is a maximum point of `uᵢ i - φ` on `K` and
`upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i z - φ z`.
-/
theorem exists_isMaxOn_mem_nhds_upperHalfRelaxedLimit_sub_test_sub_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hxC : x ∈ C)
    (hKne : K.Nonempty) (hKcompact : IsCompact K) (hKC : K ⊆ C)
    (hKnhds : K ∈ nhdsWithin x C)
    (hbddAbove : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousOn φ C) (hφK : ContinuousOn φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        upperHalfRelaxedLimit uᵢ l C y - φ y <=
          upperHalfRelaxedLimit uᵢ l C x - φ x - δ)
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhds x) :
    ∃ i ∈ A, ∃ z ∈ K, z ∈ V ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K z ∧
        upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i z - φ z := by
  classical
  let O : Set (Point n) := interior V
  have hOopen : IsOpen O := isOpen_interior
  have hxO : x ∈ O := mem_interior_iff_mem_nhds.2 hV
  have hOnhds : O ∈ nhds x := hOopen.mem_nhds hxO
  have hOV : O ⊆ V := interior_subset
  rcases hstrict O hOnhds with ⟨δ, hδpos, hgap⟩
  let η : Real := min ε (δ / 3)
  have hηpos : 0 < η := lt_min hε (by positivity)
  let M : Real := upperHalfRelaxedLimit uᵢ l C x - φ x
  let E : Set (Point n) := K ∩ Oᶜ
  have hEcompact : IsCompact E := hKcompact.inter_right hOopen.isClosed_compl
  have hEC : E ⊆ C := fun y hy => hKC hy.1
  have hEbound : ∀ y ∈ E,
      upperHalfRelaxedLimit uᵢ l C y - φ y < M - δ / 2 := by
    intro y hy
    have hygap := hgap y hy.1 hy.2
    dsimp [M]
    linarith
  have hφE : ∀ y ∈ E, ContinuousWithinAt φ C y := fun y hy =>
    hφC.continuousWithinAt (hEC hy)
  have hupperE : ∀ᶠ i in l, ∀ y ∈ E, uᵢ i y - φ y < M - δ / 3 :=
    eventually_forall_sub_test_lt_of_isCompact_upperHalfRelaxedLimit_sub_test_lt
      hEcompact hEC hbddAbove hφE hEbound (by dsimp [M]; linarith)
  let B : Set ι := {i | ∀ y ∈ E, uᵢ i y - φ y < M - δ / 3}
  have hB : B ∈ l := hupperE
  have hAB : A ∩ B ∈ l := inter_mem hA hB
  rcases exists_isMaxOn_upperHalfRelaxedLimit_sub_test_sub_lt
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      hηpos hcobddBelow (hφC.continuousWithinAt hxC) hφK hKne hKcompact
      hKnhds husc hAB with
    ⟨i, hiAB, z, hzK, hmax, hzval⟩
  have hzO : z ∈ O := by
    by_contra hznotO
    have hzE : z ∈ E := ⟨hzK, hznotO⟩
    have hlt_upper : uᵢ i z - φ z < M - δ / 3 := hiAB.2 z hzE
    have hηleδ : η <= δ / 3 := min_le_right ε (δ / 3)
    have hlt_lower : M - δ / 3 < uᵢ i z - φ z := by
      dsimp [M] at hzval ⊢
      linarith
    linarith
  have hηleε : η <= ε := min_le_left ε (δ / 3)
  have hzvalε :
      upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i z - φ z := by
    linarith
  exact ⟨i, hiAB.1, z, hzK, hOV hzO, hmax, hzvalε⟩

/--
For a strict minimum contact of the lower half-relaxed limit on a compact set
`K`, compact minimum points of `uᵢ i - φ` can be chosen in any prescribed
neighborhood of the contact point.

More precisely, for every `ε > 0`, every set of indices `A` with `A ∈ l`,
and every neighborhood `V` of `x`, there exist `i ∈ A` and `z ∈ K ∩ V` such
that `z` is a minimum point of `uᵢ i - φ` on `K` and
`uᵢ i z - φ z < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε`.
-/
theorem exists_isMinOn_mem_nhds_lowerHalfRelaxedLimit_sub_test_add
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hxC : x ∈ C)
    (hKne : K.Nonempty) (hKcompact : IsCompact K) (hKC : K ⊆ C)
    (hKnhds : K ∈ nhdsWithin x C)
    (hbddBelow : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousOn φ C) (hφK : ContinuousOn φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        lowerHalfRelaxedLimit uᵢ l C x - φ x + δ <=
          lowerHalfRelaxedLimit uᵢ l C y - φ y)
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhds x) :
    ∃ i ∈ A, ∃ z ∈ K, z ∈ V ∧
      IsMinOn (fun y => uᵢ i y - φ y) K z ∧
        uᵢ i z - φ z < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε := by
  classical
  let O : Set (Point n) := interior V
  have hOopen : IsOpen O := isOpen_interior
  have hxO : x ∈ O := mem_interior_iff_mem_nhds.2 hV
  have hOnhds : O ∈ nhds x := hOopen.mem_nhds hxO
  have hOV : O ⊆ V := interior_subset
  rcases hstrict O hOnhds with ⟨δ, hδpos, hgap⟩
  let η : Real := min ε (δ / 3)
  have hηpos : 0 < η := lt_min hε (by positivity)
  let M : Real := lowerHalfRelaxedLimit uᵢ l C x - φ x
  let E : Set (Point n) := K ∩ Oᶜ
  have hEcompact : IsCompact E := hKcompact.inter_right hOopen.isClosed_compl
  have hEC : E ⊆ C := fun y hy => hKC hy.1
  have hEbound : ∀ y ∈ E, M + δ / 2 < lowerHalfRelaxedLimit uᵢ l C y - φ y := by
    intro y hy
    have hygap := hgap y hy.1 hy.2
    dsimp [M]
    linarith
  have hφE : ∀ y ∈ E, ContinuousWithinAt φ C y := fun y hy =>
    hφC.continuousWithinAt (hEC hy)
  have hlowerE : ∀ᶠ i in l, ∀ y ∈ E, M + δ / 3 < uᵢ i y - φ y :=
    eventually_forall_lt_sub_test_of_lt_isCompact_lowerHalfRelaxedLimit_sub_test
      hEcompact hEC hbddBelow hφE hEbound (by dsimp [M]; linarith)
  let B : Set ι := {i | ∀ y ∈ E, M + δ / 3 < uᵢ i y - φ y}
  have hB : B ∈ l := hlowerE
  have hAB : A ∩ B ∈ l := inter_mem hA hB
  rcases exists_isMinOn_lt_lowerHalfRelaxedLimit_sub_test_add
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      hηpos hcobddAbove (hφC.continuousWithinAt hxC) hφK hKne hKcompact
      hKnhds hlsc hAB with
    ⟨i, hiAB, z, hzK, hmin, hzval⟩
  have hzO : z ∈ O := by
    by_contra hznotO
    have hzE : z ∈ E := ⟨hzK, hznotO⟩
    have hlt_lower : M + δ / 3 < uᵢ i z - φ z := hiAB.2 z hzE
    have hηleδ : η <= δ / 3 := min_le_right ε (δ / 3)
    have hlt_upper : uᵢ i z - φ z < M + δ / 3 := by
      dsimp [M] at hzval ⊢
      linarith
    linarith
  have hηleε : η <= ε := min_le_left ε (δ / 3)
  have hzvalε :
      uᵢ i z - φ z < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε := by
    linarith
  exact ⟨i, hiAB.1, z, hzK, hOV hzO, hmin, hzvalε⟩

/--
Assume that `φ` has strict maximum contact with
`upperHalfRelaxedLimit uᵢ l C` at `x` on `K`. For every `ε > 0`, every
`A ∈ l`, and every neighborhood `V` of `x`, there exist `i ∈ A` and
`z ∈ K ∩ V` such that `z` maximizes `uᵢ i - φ` on `K` and
`|(uᵢ i z - φ z) - (upperHalfRelaxedLimit uᵢ l C x - φ x)| < ε`.
-/
theorem exists_isMaxOn_mem_nhds_abs_sub_test_upperHalfRelaxedLimit_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hxC : x ∈ C)
    (hKne : K.Nonempty) (hKcompact : IsCompact K) (hKC : K ⊆ C)
    (hKnhds : K ∈ nhdsWithin x C)
    (hbddAbove : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousOn φ C) (hφK : ContinuousOn φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        upperHalfRelaxedLimit uᵢ l C y - φ y <=
          upperHalfRelaxedLimit uᵢ l C x - φ x - δ)
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhds x) :
    ∃ i ∈ A, ∃ z ∈ K, z ∈ V ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K z ∧
        |(uᵢ i z - φ z) - (upperHalfRelaxedLimit uᵢ l C x - φ x)| < ε := by
  classical
  let M : Real := upperHalfRelaxedLimit uᵢ l C x - φ x
  have hε2 : 0 < ε / 2 := by positivity
  have hupperEvent :
      {q : ι × Point n | uᵢ q.1 q.2 - φ q.2 < M + ε} ∈
        halfRelaxedFilter l C x := by
    exact eventually_sub_test_lt_of_upperHalfRelaxedLimit_sub_test_lt
      (hbddAbove x hxC) (hφC.continuousWithinAt hxC)
      (a := M + ε / 2) (b := M + ε) (by dsimp [M]; linarith) (by linarith)
  rcases Filter.mem_prod_iff.mp hupperEvent with ⟨A₀, hA₀, V₀, hV₀, hsub₀⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV₀ with ⟨U, hU, hUV₀⟩
  have hAA₀ : A ∩ A₀ ∈ l := inter_mem hA hA₀
  have hVU : V ∩ U ∈ nhds x := inter_mem hV hU
  rcases exists_isMaxOn_mem_nhds_upperHalfRelaxedLimit_sub_test_sub_lt
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      hε hxC hKne hKcompact hKC hKnhds hbddAbove hcobddBelow
      hφC hφK husc hstrict hAA₀ hVU with
    ⟨i, hiAA₀, z, hzK, hzVU, hmax, hzlower⟩
  have hzV₀ : z ∈ V₀ := hUV₀ ⟨hzVU.2, hKC hzK⟩
  have hp₀ : (i, z) ∈ A₀ ×ˢ V₀ := ⟨hiAA₀.2, hzV₀⟩
  have hzupper : uᵢ i z - φ z < M + ε :=
    hsub₀ hp₀
  refine ⟨i, hiAA₀.1, z, hzK, hzVU.1, hmax, ?_⟩
  rw [abs_sub_lt_iff]
  constructor <;> dsimp [M] at hzlower hzupper ⊢ <;> linarith

/--
Assume that `φ` has strict minimum contact with
`lowerHalfRelaxedLimit uᵢ l C` at `x` on `K`. For every `ε > 0`, every
`A ∈ l`, and every neighborhood `V` of `x`, there exist `i ∈ A` and
`z ∈ K ∩ V` such that `z` minimizes `uᵢ i - φ` on `K` and
`|(uᵢ i z - φ z) - (lowerHalfRelaxedLimit uᵢ l C x - φ x)| < ε`.
-/
theorem exists_isMinOn_mem_nhds_abs_sub_test_lowerHalfRelaxedLimit_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hxC : x ∈ C)
    (hKne : K.Nonempty) (hKcompact : IsCompact K) (hKC : K ⊆ C)
    (hKnhds : K ∈ nhdsWithin x C)
    (hbddBelow : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousOn φ C) (hφK : ContinuousOn φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        lowerHalfRelaxedLimit uᵢ l C x - φ x + δ <=
          lowerHalfRelaxedLimit uᵢ l C y - φ y)
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhds x) :
    ∃ i ∈ A, ∃ z ∈ K, z ∈ V ∧
      IsMinOn (fun y => uᵢ i y - φ y) K z ∧
        |(uᵢ i z - φ z) - (lowerHalfRelaxedLimit uᵢ l C x - φ x)| < ε := by
  classical
  let M : Real := lowerHalfRelaxedLimit uᵢ l C x - φ x
  have hε2 : 0 < ε / 2 := by positivity
  have hlowerEvent :
      {q : ι × Point n | M - ε < uᵢ q.1 q.2 - φ q.2} ∈
        halfRelaxedFilter l C x := by
    exact eventually_lt_sub_test_of_lt_lowerHalfRelaxedLimit_sub_test
      (hbddBelow x hxC) (hφC.continuousWithinAt hxC)
      (a := M - ε / 2) (b := M - ε) (by dsimp [M]; linarith) (by linarith)
  rcases Filter.mem_prod_iff.mp hlowerEvent with ⟨A₀, hA₀, V₀, hV₀, hsub₀⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV₀ with ⟨U, hU, hUV₀⟩
  have hAA₀ : A ∩ A₀ ∈ l := inter_mem hA hA₀
  have hVU : V ∩ U ∈ nhds x := inter_mem hV hU
  rcases exists_isMinOn_mem_nhds_lowerHalfRelaxedLimit_sub_test_add
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      hε hxC hKne hKcompact hKC hKnhds hbddBelow hcobddAbove
      hφC hφK hlsc hstrict hAA₀ hVU with
    ⟨i, hiAA₀, z, hzK, hzVU, hmin, hzupper⟩
  have hzV₀ : z ∈ V₀ := hUV₀ ⟨hzVU.2, hKC hzK⟩
  have hp₀ : (i, z) ∈ A₀ ×ˢ V₀ := ⟨hiAA₀.2, hzV₀⟩
  have hzlower : M - ε < uᵢ i z - φ z :=
    hsub₀ hp₀
  refine ⟨i, hiAA₀.1, z, hzK, hzVU.1, hmin, ?_⟩
  rw [abs_sub_lt_iff]
  constructor <;> dsimp [M] at hzlower hzupper ⊢ <;> linarith

/--
Assume that `φ` has strict maximum contact with
`upperHalfRelaxedLimit uᵢ l C` at `x` on `K` and that `K ∈ nhdsWithin x C`.
For every `ε > 0`, every `A ∈ l`, and every neighborhood `V` of `x`, there
exist `i ∈ A` and `z ∈ K ∩ V` such that `K ∈ nhdsWithin z C`, `z` maximizes
`uᵢ i - φ` on `K`, and
`|uᵢ i z - upperHalfRelaxedLimit uᵢ l C x| < ε`.
-/
theorem exists_isMaxOn_mem_nhds_abs_upperHalfRelaxedLimit_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hxC : x ∈ C)
    (hKne : K.Nonempty) (hKcompact : IsCompact K) (hKC : K ⊆ C)
    (hKnhds : K ∈ nhdsWithin x C)
    (hbddAbove : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousOn φ C) (hφK : ContinuousOn φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        upperHalfRelaxedLimit uᵢ l C y - φ y <=
          upperHalfRelaxedLimit uᵢ l C x - φ x - δ)
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhds x) :
    ∃ i ∈ A, ∃ z ∈ K, z ∈ V ∧ K ∈ nhdsWithin z C ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K z ∧
        |uᵢ i z - upperHalfRelaxedLimit uᵢ l C x| < ε := by
  classical
  have hε2 : 0 < ε / 2 := by positivity
  rcases exists_nhds_forall_mem_nhdsWithin hKnhds with ⟨UK, hUK, hUKprop⟩
  have hφnhds : {y : Point n | |φ y - φ x| < ε / 2} ∈ nhdsWithin x C := by
    exact (hφC.continuousWithinAt hxC).tendsto
      (by simpa [Real.dist_eq] using Metric.ball_mem_nhds (φ x) hε2)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hφnhds with ⟨Uφ, hUφ, hUφsub⟩
  have hV' : V ∩ UK ∩ Uφ ∈ nhds x := inter_mem (inter_mem hV hUK) hUφ
  rcases exists_isMaxOn_mem_nhds_abs_sub_test_upperHalfRelaxedLimit_lt
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      hε2 hxC hKne hKcompact hKC hKnhds hbddAbove hcobddBelow hφC hφK
      husc hstrict hA hV' with
    ⟨i, hiA, z, hzK, hzV', hmax, hadj⟩
  have hzV : z ∈ V := hzV'.1.1
  have hzUK : z ∈ UK := hzV'.1.2
  have hzUφ : z ∈ Uφ := hzV'.2
  have hzC : z ∈ C := hKC hzK
  have hKz : K ∈ nhdsWithin z C := hUKprop z hzUK hzC
  have hφabs : |φ z - φ x| < ε / 2 := hUφsub ⟨hzUφ, hzC⟩
  have hdecomp :
      uᵢ i z - upperHalfRelaxedLimit uᵢ l C x =
        ((uᵢ i z - φ z) - (upperHalfRelaxedLimit uᵢ l C x - φ x)) +
          (φ z - φ x) := by ring
  have hsum :
      |((uᵢ i z - φ z) - (upperHalfRelaxedLimit uᵢ l C x - φ x)) +
          (φ z - φ x)| < ε := by
    calc
      |((uᵢ i z - φ z) - (upperHalfRelaxedLimit uᵢ l C x - φ x)) +
          (φ z - φ x)|
          <= |(uᵢ i z - φ z) - (upperHalfRelaxedLimit uᵢ l C x - φ x)| +
              |φ z - φ x| := abs_add_le _ _
      _ < ε := by linarith
  exact ⟨i, hiA, z, hzK, hzV, hKz, hmax, by simpa [hdecomp] using hsum⟩

/--
Assume that `φ` has strict minimum contact with
`lowerHalfRelaxedLimit uᵢ l C` at `x` on `K` and that `K ∈ nhdsWithin x C`.
For every `ε > 0`, every `A ∈ l`, and every neighborhood `V` of `x`, there
exist `i ∈ A` and `z ∈ K ∩ V` such that `K ∈ nhdsWithin z C`, `z` minimizes
`uᵢ i - φ` on `K`, and
`|uᵢ i z - lowerHalfRelaxedLimit uᵢ l C x| < ε`.
-/
theorem exists_isMinOn_mem_nhds_abs_lowerHalfRelaxedLimit_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C K : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hxC : x ∈ C)
    (hKne : K.Nonempty) (hKcompact : IsCompact K) (hKC : K ⊆ C)
    (hKnhds : K ∈ nhdsWithin x C)
    (hbddBelow : ∀ y ∈ C,
      (halfRelaxedFilter l C y).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφC : ContinuousOn φ C) (hφK : ContinuousOn φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        lowerHalfRelaxedLimit uᵢ l C x - φ x + δ <=
          lowerHalfRelaxedLimit uᵢ l C y - φ y)
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhds x) :
    ∃ i ∈ A, ∃ z ∈ K, z ∈ V ∧ K ∈ nhdsWithin z C ∧
      IsMinOn (fun y => uᵢ i y - φ y) K z ∧
        |uᵢ i z - lowerHalfRelaxedLimit uᵢ l C x| < ε := by
  classical
  have hε2 : 0 < ε / 2 := by positivity
  rcases exists_nhds_forall_mem_nhdsWithin hKnhds with ⟨UK, hUK, hUKprop⟩
  have hφnhds : {y : Point n | |φ y - φ x| < ε / 2} ∈ nhdsWithin x C := by
    exact (hφC.continuousWithinAt hxC).tendsto
      (by simpa [Real.dist_eq] using Metric.ball_mem_nhds (φ x) hε2)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hφnhds with ⟨Uφ, hUφ, hUφsub⟩
  have hV' : V ∩ UK ∩ Uφ ∈ nhds x := inter_mem (inter_mem hV hUK) hUφ
  rcases exists_isMinOn_mem_nhds_abs_sub_test_lowerHalfRelaxedLimit_lt
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      hε2 hxC hKne hKcompact hKC hKnhds hbddBelow hcobddAbove hφC hφK
      hlsc hstrict hA hV' with
    ⟨i, hiA, z, hzK, hzV', hmin, hadj⟩
  have hzV : z ∈ V := hzV'.1.1
  have hzUK : z ∈ UK := hzV'.1.2
  have hzUφ : z ∈ Uφ := hzV'.2
  have hzC : z ∈ C := hKC hzK
  have hKz : K ∈ nhdsWithin z C := hUKprop z hzUK hzC
  have hφabs : |φ z - φ x| < ε / 2 := hUφsub ⟨hzUφ, hzC⟩
  have hdecomp :
      uᵢ i z - lowerHalfRelaxedLimit uᵢ l C x =
        ((uᵢ i z - φ z) - (lowerHalfRelaxedLimit uᵢ l C x - φ x)) +
          (φ z - φ x) := by ring
  have hsum :
      |((uᵢ i z - φ z) - (lowerHalfRelaxedLimit uᵢ l C x - φ x)) +
          (φ z - φ x)| < ε := by
    calc
      |((uᵢ i z - φ z) - (lowerHalfRelaxedLimit uᵢ l C x - φ x)) +
          (φ z - φ x)|
          <= |(uᵢ i z - φ z) - (lowerHalfRelaxedLimit uᵢ l C x - φ x)| +
              |φ z - φ x| := abs_add_le _ _
      _ < ε := by linarith
  exact ⟨i, hiA, z, hzK, hzV, hKz, hmin, by simpa [hdecomp] using hsum⟩

/--
Let `upperLimit x = upperHalfRelaxedLimit uᵢ l C x`. Assume that `φ` has strict
maximum contact with `upperLimit` at `x` on the compact set `K`, that `K ⊆ C`, and
that `K` is a relative neighborhood of `x` in `C`. Let `JAt` be a function
from points to jets such that `JAt` is continuous at `x` relative to `K`, and
such that for every `y ∈ K`, the function `φ` has second-order expansion
`JAt y` at `y` relative to `K`.

Then for every `A ∈ l` and every neighborhood `W` of
`((x, upperLimit x), JAt x)`, there exist `i ∈ A`, `z ∈ K`, and the jet `JAt z`
such that `K ∈ nhdsWithin z C`, `z` maximizes `uᵢ i - φ` on `K`,
`φ` has second-order expansion `JAt z` at `z` relative to `K`, and
`((z, uᵢ i z), JAt z) ∈ W`.
-/
theorem exists_isMaxOn_hasSecondOrderExpansionWithin_mem_nhds_upperHalfRelaxedLimit
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
          upperHalfRelaxedLimit uᵢ l C x - φ x - δ)
    {A : Set ι} (hA : A ∈ l)
    {W : Set ((Point n × Real) × Jet n)}
    (hW : W ∈ nhds ((x, upperHalfRelaxedLimit uᵢ l C x), JAt x)) :
    ∃ i ∈ A, ∃ z ∈ K, ∃ Jᵢ : Jet n,
      K ∈ nhdsWithin z C ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K z ∧
      HasSecondOrderExpansionWithin K φ z Jᵢ ∧
      ((z, uᵢ i z), Jᵢ) ∈ W := by
  classical
  rcases mem_nhds_prod_iff.1 hW with
    ⟨Wxr, hWxr, WJ, hWJ, hWsub⟩
  rcases mem_nhds_prod_iff.1 hWxr with
    ⟨Vx, hVx, Vr, hVr, hWxrsub⟩
  rcases Metric.mem_nhds_iff.1 hVr with ⟨ε, hε, hεsub⟩
  have hJnhds : {y : Point n | JAt y ∈ WJ} ∈ nhdsWithin x K :=
    hJAt.tendsto hWJ
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hJnhds with
    ⟨UJ, hUJ, hUJsub⟩
  have hV : Vx ∩ UJ ∈ nhds x := inter_mem hVx hUJ
  rcases exists_isMaxOn_mem_nhds_abs_upperHalfRelaxedLimit_lt
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      hε hxC hKne hKcompact hKC hKnhds hbddAbove hcobddBelow hφC hφK
      husc hstrict hA hV with
    ⟨i, hiA, z, hzK, hzV, hKz, hmax, hval⟩
  have hzVx : z ∈ Vx := hzV.1
  have hzUJ : z ∈ UJ := hzV.2
  have hvalVr : uᵢ i z ∈ Vr := by
    exact hεsub (by simpa [Metric.mem_ball, Real.dist_eq] using hval)
  have hpair : (z, uᵢ i z) ∈ Wxr :=
    hWxrsub ⟨hzVx, hvalVr⟩
  have hJmem : JAt z ∈ WJ :=
    hUJsub ⟨hzUJ, hzK⟩
  have hWmem : ((z, uᵢ i z), JAt z) ∈ W :=
    hWsub ⟨hpair, hJmem⟩
  exact ⟨i, hiA, z, hzK, JAt z, hKz, hmax, hφexp z hzK, hWmem⟩

/--
Let `lowerLimit x = lowerHalfRelaxedLimit uᵢ l C x`. Assume that `φ` has strict
minimum contact with `lowerLimit` at `x` on the compact set `K`, that `K ⊆ C`, and
that `K` is a relative neighborhood of `x` in `C`. Let `JAt` be a function
from points to jets such that `JAt` is continuous at `x` relative to `K`, and
such that for every `y ∈ K`, the function `φ` has second-order expansion
`JAt y` at `y` relative to `K`.

Then for every `A ∈ l` and every neighborhood `W` of
`((x, lowerLimit x), JAt x)`, there exist `i ∈ A`, `z ∈ K`, and the jet `JAt z`
such that `K ∈ nhdsWithin z C`, `z` minimizes `uᵢ i - φ` on `K`,
`φ` has second-order expansion `JAt z` at `z` relative to `K`, and
`((z, uᵢ i z), JAt z) ∈ W`.
-/
theorem exists_isMinOn_hasSecondOrderExpansionWithin_mem_nhds_lowerHalfRelaxedLimit
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
          lowerHalfRelaxedLimit uᵢ l C y - φ y)
    {A : Set ι} (hA : A ∈ l)
    {W : Set ((Point n × Real) × Jet n)}
    (hW : W ∈ nhds ((x, lowerHalfRelaxedLimit uᵢ l C x), JAt x)) :
    ∃ i ∈ A, ∃ z ∈ K, ∃ Jᵢ : Jet n,
      K ∈ nhdsWithin z C ∧
      IsMinOn (fun y => uᵢ i y - φ y) K z ∧
      HasSecondOrderExpansionWithin K φ z Jᵢ ∧
      ((z, uᵢ i z), Jᵢ) ∈ W := by
  classical
  rcases mem_nhds_prod_iff.1 hW with
    ⟨Wxr, hWxr, WJ, hWJ, hWsub⟩
  rcases mem_nhds_prod_iff.1 hWxr with
    ⟨Vx, hVx, Vr, hVr, hWxrsub⟩
  rcases Metric.mem_nhds_iff.1 hVr with ⟨ε, hε, hεsub⟩
  have hJnhds : {y : Point n | JAt y ∈ WJ} ∈ nhdsWithin x K :=
    hJAt.tendsto hWJ
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hJnhds with
    ⟨UJ, hUJ, hUJsub⟩
  have hV : Vx ∩ UJ ∈ nhds x := inter_mem hVx hUJ
  rcases exists_isMinOn_mem_nhds_abs_lowerHalfRelaxedLimit_lt
      (uᵢ := uᵢ) (l := l) (C := C) (K := K) (x := x) (φ := φ)
      hε hxC hKne hKcompact hKC hKnhds hbddBelow hcobddAbove hφC hφK
      hlsc hstrict hA hV with
    ⟨i, hiA, z, hzK, hzV, hKz, hmin, hval⟩
  have hzVx : z ∈ Vx := hzV.1
  have hzUJ : z ∈ UJ := hzV.2
  have hvalVr : uᵢ i z ∈ Vr := by
    exact hεsub (by simpa [Metric.mem_ball, Real.dist_eq] using hval)
  have hpair : (z, uᵢ i z) ∈ Wxr :=
    hWxrsub ⟨hzVx, hvalVr⟩
  have hJmem : JAt z ∈ WJ :=
    hUJsub ⟨hzUJ, hzK⟩
  have hWmem : ((z, uᵢ i z), JAt z) ∈ W :=
    hWsub ⟨hpair, hJmem⟩
  exact ⟨i, hiA, z, hzK, JAt z, hKz, hmin, hφexp z hzK, hWmem⟩

end ViscositySolns
