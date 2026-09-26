/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Helly

/-!
# Centerpoints in convex flags

This file states Corollary 3.14, the centerpoint consequence of the flag
Helly theorem.  We use a finite indexed weight function rather than measure
theory, exactly matching the finite weighted set in the paper and its later
application to local lifted mass.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.ConvexFlag

/-- The total weight of the input points that lie on or above `center` for a
flag functional.  Points outside the functional's domain are omitted, as in
equation `ceq` of the paper. -/
noncomputable def upperWeight {F : ConvexFlag} {n : ℕ}
    (points : Fin n → F.Point) (weight : Fin n → ℝ)
    (xi : F.LinearFunction) (center : F.Point)
    (hcenter : xi.EvaluableAt center) : ℝ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i ↦
      ∃ hi : xi.EvaluableAt (points i),
        xi.eval center hcenter ≤ xi.eval (points i) hi),
    weight i

/-- Nonnegative point weights give nonnegative weight to every functional
upper side. -/
theorem upperWeight_nonneg {F : ConvexFlag} {n : ℕ}
    (points : Fin n → F.Point) (weight : Fin n → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (xi : F.LinearFunction) (center : F.Point)
    (hcenter : xi.EvaluableAt center) :
    0 ≤ upperWeight points weight xi center hcenter := by
  classical
  unfold upperWeight
  exact Finset.sum_nonneg fun i _ ↦ hweight i

/-- Positive total nonnegative weight, together with proper integrality of
the input points, guarantees that the denominator in the centerpoint bound
is positive. -/
theorem hellyConstant_pos_of_weighted_points {F : ConvexFlag}
    {Ω : F.ProperPointSet} {n : ℕ} (points : Fin n → F.Point)
    (weight : Fin n → ℝ) (hproper : ∀ i, points i ∈ Ω)
    (hintegral : ∀ i, (points i).IsIntegral)
    (hweight : ∀ i, 0 ≤ weight i)
    (htotal : 0 < ∑ i, weight i) :
    0 < hellyConstant Ω := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at htotal
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  exact hellyConstant_pos (hproper i) (hintegral i)

/-- If each member of a family of at most `H` subsets carries more than
`1 - 1 / H` of a nonnegative finite weight, then the subsets have a common
index.  This is the finite weighted union-bound step in the centerpoint
argument. -/
private theorem exists_common_of_large
    {ι κ : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (H : ℕ) (hH : 0 < H) (G : Finset κ) (hG : G.Nonempty)
    (A : κ → Finset ι)
    (hlarge : ∀ s ∈ G,
      (∑ i, w i) - (∑ i, w i) / (H : ℝ) < ∑ i ∈ A s, w i)
    (hcard : G.card ≤ H) :
    ∃ i, ∀ s ∈ G, i ∈ A s := by
  classical
  by_contra hcommon
  push Not at hcommon
  have hcompl (s : κ) (hs : s ∈ G) :
      (∑ i ∈ (A s)ᶜ, w i) < (∑ i, w i) / (H : ℝ) := by
    have hsplit : (∑ i, w i) =
        (∑ i ∈ A s, w i) + ∑ i ∈ (A s)ᶜ, w i := by
      rw [← Finset.sum_union disjoint_compl_right]
      simp
    linarith [hlarge s hs]
  have hterm (i : ι) :
      w i ≤ ∑ s ∈ G, if i ∉ A s then w i else 0 := by
    obtain ⟨s, hsG, his⟩ := hcommon i
    have hsfilter : s ∈ G.filter (fun s ↦ i ∉ A s) := by
      simp [hsG, his]
    calc
      w i ≤ ∑ s ∈ G.filter (fun s ↦ i ∉ A s), w i :=
        Finset.single_le_sum (fun _ _ ↦ hw i) hsfilter
      _ = ∑ s ∈ G, if i ∉ A s then w i else 0 := by
        rw [Finset.sum_filter]
  have htotal_le :
      (∑ i, w i) ≤ ∑ s ∈ G, ∑ i ∈ (A s)ᶜ, w i := by
    calc
      (∑ i, w i) ≤ ∑ i, ∑ s ∈ G, if i ∉ A s then w i else 0 :=
        Finset.sum_le_sum fun i _ ↦ hterm i
      _ = ∑ s ∈ G, ∑ i, if i ∉ A s then w i else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ s ∈ G, ∑ i ∈ (A s)ᶜ, w i := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp
  have hdouble_lt :
      (∑ s ∈ G, ∑ i ∈ (A s)ᶜ, w i) <
        ∑ _s ∈ G, (∑ i, w i) / (H : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hG hcompl
  have hcard_bound :
      ∑ _s ∈ G, (∑ i, w i) / (H : ℝ) ≤ ∑ i, w i := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have htotal_nonneg : 0 ≤ ∑ i, w i :=
      Finset.sum_nonneg fun i _ ↦ hw i
    have hdiv_nonneg : 0 ≤ (∑ i, w i) / (H : ℝ) :=
      div_nonneg htotal_nonneg (Nat.cast_nonneg H)
    calc
      (G.card : ℝ) * ((∑ i, w i) / (H : ℝ)) ≤
          (H : ℝ) * ((∑ i, w i) / (H : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hdiv_nonneg
      _ = ∑ i, w i := by
        rw [mul_div_cancel₀]
        exact_mod_cast (Nat.ne_of_gt hH)
  linarith

/-- Corollary 3.14 (`central`): the centerpoint theorem for convex flags.

The quantified sum includes precisely those input points at which `xi` is
defined and whose value is at least its value at the centerpoint. -/
theorem flagCenterpoint_family {F : ConvexFlag} (Ω : F.ProperPointSet)
    {n : ℕ} (points : Fin n → F.Point)
    (hproper : ∀ i, points i ∈ Ω)
    (hintegral : ∀ i, (points i).IsIntegral)
    (weight : Fin n → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (htotal : 0 < ∑ i, weight i) :
    ∃ q, q ∈ Ω ∧ q.IsIntegral ∧
      ∀ (xi : F.LinearFunction) (hq : xi.EvaluableAt q),
        (∑ i, weight i) / (hellyConstant Ω : ℝ) ≤
          upperWeight points weight xi q hq := by
  classical
  let total : ℝ := ∑ i, weight i
  let H : ℕ := hellyConstant Ω
  have hH : 0 < H := by
    simpa [H] using hellyConstant_pos_of_weighted_points
      points weight hproper hintegral hweight htotal
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at htotal
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hnonempty : ∃ q, q ∈ Ω ∧ q.IsIntegral :=
    ⟨points i₀, hproper i₀, hintegral i₀⟩
  let ℱ : Set (Set F.Point) :=
    {S | ∃ A : Finset (Fin n),
      S = points '' (A : Set (Fin n)) ∧
        total - total / (H : ℝ) < ∑ i ∈ A, weight i}
  have hlocal : ∀ G : Finset (Set F.Point),
      (G : Set (Set F.Point)) ⊆ ℱ → G.Nonempty →
      G.card ≤ hellyConstant Ω →
      HasCommonWeakHullPoint Ω (G : Set (Set F.Point)) := by
    intro G hGsub hGne hGcard
    let K := {S : Set F.Point // S ∈ G}
    let A : K → Finset (Fin n) := fun S ↦
      Classical.choose (hGsub S.property)
    have hAset (S : K) :
        S.1 = points '' (A S : Set (Fin n)) :=
      (Classical.choose_spec (hGsub S.property)).1
    have hAlarge (S : K) :
        total - total / (H : ℝ) < ∑ i ∈ A S, weight i :=
      (Classical.choose_spec (hGsub S.property)).2
    let s₀ : K := ⟨Classical.choose hGne, Classical.choose_spec hGne⟩
    have hKuniv : (Finset.univ : Finset K).Nonempty :=
      ⟨s₀, Finset.mem_univ s₀⟩
    have hKcard : Fintype.card K ≤ H := by
      simpa [K, H] using hGcard
    obtain ⟨i, hi⟩ := exists_common_of_large weight hweight H hH
      (Finset.univ : Finset K) hKuniv A
      (by simpa [total] using hAlarge) (by simpa using hKcard)
    refine ⟨points i, hproper i, hintegral i, ?_⟩
    intro S hSG
    let s : K := ⟨S, hSG⟩
    apply subset_weakConvexHull F S
    have his : points i ∈ (s.1 : Set F.Point) := by
      rw [hAset s]
      exact ⟨i, hi s (Finset.mem_univ s), rfl⟩
    exact his
  obtain ⟨q, hqΩ, hqint, hqfamily⟩ :=
    flagHelly Ω hnonempty ℱ hlocal
  refine ⟨q, hqΩ, hqint, ?_⟩
  intro xi hq
  by_contra hbound
  have hupper_lt :
      upperWeight points weight xi q hq < total / (H : ℝ) := by
    exact lt_of_not_ge (by simpa [total, H] using hbound)
  let Good (i : Fin n) : Prop :=
    ∃ hi : xi.EvaluableAt (points i),
      xi.eval q hq ≤ xi.eval (points i) hi
  let good : Finset (Fin n) := Finset.univ.filter Good
  let bad : Finset (Fin n) := goodᶜ
  have hupper_eq :
      upperWeight points weight xi q hq = ∑ i ∈ good, weight i := by
    rfl
  have hsplit : total =
      (∑ i ∈ good, weight i) + ∑ i ∈ bad, weight i := by
    dsimp [total, bad]
    rw [← Finset.sum_union disjoint_compl_right]
    simp
  have hbad_large :
      total - total / (H : ℝ) < ∑ i ∈ bad, weight i := by
    linarith
  have hbad_family : points '' (bad : Set (Fin n)) ∈ ℱ := by
    exact ⟨bad, rfl, hbad_large⟩
  have hqbad := hqfamily _ hbad_family xi hq
  obtain ⟨s, ⟨i, hibad, his⟩, hi, hqi⟩ := hqbad
  have hiGood : Good i := by
    subst s
    exact ⟨hi, hqi⟩
  have higood : i ∈ good := by
    simp [good, hiGood]
  exact (Finset.mem_compl.mp (by simpa [bad] using hibad)) higood

/-- Compatibility form for a weighted set of distinct flag points. The
centerpoint argument itself also applies to labelled points with repetition. -/
theorem flagCenterpoint {F : ConvexFlag} (Ω : F.ProperPointSet)
    {n : ℕ} (points : Fin n → F.Point)
    (_hpoints_injective : Function.Injective points)
    (hproper : ∀ i, points i ∈ Ω)
    (hintegral : ∀ i, (points i).IsIntegral)
    (weight : Fin n → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (htotal : 0 < ∑ i, weight i) :
    ∃ q, q ∈ Ω ∧ q.IsIntegral ∧
      ∀ (xi : F.LinearFunction) (hq : xi.EvaluableAt q),
        (∑ i, weight i) / (hellyConstant Ω : ℝ) ≤
          upperWeight points weight xi q hq :=
  flagCenterpoint_family Ω points hproper hintegral weight hweight htotal

/-- Numbered alias for Corollary 3.14. -/
alias corollary_3_14 := flagCenterpoint

end EGZ.ConvexFlag
