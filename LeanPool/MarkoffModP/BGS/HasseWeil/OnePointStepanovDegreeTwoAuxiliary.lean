/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointSectionSelection
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointStepanovBasisGrid
import LeanPool.MarkoffModP.BGS.HasseWeil.StepanovParameters
import LeanPool.MarkoffModP.BGS.HasseWeil.StepanovRestrictionMaps
import Mathlib.Tactic

/-!
# Stepanov auxiliaries at places of degree at most two

At a degree-two place the strict-level filtration can jump by two.  Choosing
one section per strict level for both tensor factors therefore loses the
factor of two needed by the Stepanov dimension count.  The first factor still
uses bounded distinct pole-order digits, while the second factor is now a
full basis of its one-point Riemann space.  The basis-grid theorem proves
that the first restriction remains injective.

With `ell = #K - 1` and `m = #K + 2g`, the same large-field hypothesis as in
the degree-one construction makes the coefficient dimension exceed the
second restriction target for every place degree `r ≤ 2`.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance degreeTwoAuxiliaryConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance degreeTwoAuxiliaryConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The one-point Riemann space at level `N` has dimension at most
`N * degree(P) + 1` when the constants are exactly `K`. -/
theorem finiteExtensionOnePointRiemannSpace_finrank_upper
    (P : FiniteExtensionPlace K L)
    (hconstants : algebraicClosure K L = ⊥) :
    ∀ N, Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L P N) ≤
        N * finiteExtensionPlaceDegree K L P + 1 := by
  intro N
  induction N with
  | zero =>
      simpa using
        (finiteExtensionOnePointRiemannSpace_zero_finrank K L P hconstants).le
  | succ N ih =>
      have hstep := finiteExtensionOnePointRiemannSpace_finrank_succ_le
        K L P N
      calc
        Module.finrank K
            (finiteExtensionOnePointRiemannSpace K L P (N + 1)) ≤
            Module.finrank K
              (finiteExtensionOnePointRiemannSpace K L P N) +
                finiteExtensionPlaceDegree K L P := hstep
        _ ≤ (N * finiteExtensionPlaceDegree K L P + 1) +
            finiteExtensionPlaceDegree K L P :=
          Nat.add_le_add_right ih _
        _ = (N + 1) * finiteExtensionPlaceDegree K L P + 1 := by
          rw [Nat.add_mul]
          omega

/-- The full-basis Stepanov coefficient space beats the target dimension at
every positive place degree at most two. -/
theorem stepanov_dimension_inequality_degree_le_two
    {g s r : ℕ} (hlarge : (g + 1) * (g + 2) ≤ s)
    (hrpos : 0 < r) (hrle : r ≤ 2) :
    r * (s * stepanovEll s + stepanovM g s) + 1 <
      (stepanovEll s + 1 - g) *
        (r * stepanovM g s + 1 - g) := by
  have hr : r = 1 ∨ r = 2 := by omega
  rcases hr with rfl | rfl
  · simpa only [one_mul, Nat.mul_comm s (stepanovEll s)] using
      (stepanov_dimension_inequality hlarge)
  · have hs : 0 < s := by nlinarith
    have hgs : g ≤ s := by nlinarith
    have hell : stepanovEll s + 1 - g = s - g := by
      simp only [stepanovEll]
      omega
    have hm : 2 * stepanovM g s + 1 - g = 2 * s + 3 * g + 1 := by
      simp only [stepanovM]
      omega
    have hleft : 2 * (s * stepanovEll s + stepanovM g s) + 1 =
        2 * s ^ 2 + 4 * g + 1 := by
      simp only [stepanovEll, stepanovM]
      nlinarith [Nat.sub_add_cancel (show 1 ≤ s by omega)]
    rw [hell, hm, hleft]
    have hlargeZ : (((g + 1) * (g + 2) : ℕ) : ℤ) ≤ (s : ℤ) := by
      exact_mod_cast hlarge
    have hgoalZ :
        ((2 * s ^ 2 + 4 * g + 1 : ℕ) : ℤ) <
          (((s - g) * (2 * s + 3 * g + 1) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub hgs]
      push_cast at hlargeZ ⊢
      nlinarith [sq_nonneg (g : ℤ),
        mul_nonneg (by positivity : (0 : ℤ) ≤ g) (sq_nonneg (g : ℤ))]
    exact_mod_cast hgoalZ

/-- A Riemann lower bound at a place of degree at most two produces a
nonzero Stepanov coefficient grid.  The first family has bounded distinct
pole orders; the second family is a full basis of `L(mP)`.

The returned second restriction equality is in the ambient function field,
so it can be consumed directly by the local square-Frobenius vanishing
argument. -/
theorem exists_onePointStepanovBasisAuxiliary_of_degree_le_two
    (P : FiniteExtensionPlace K L) (g : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hdegreeLe : finiteExtensionPlaceDegree K L P ≤ 2)
    (hriemann : ∀ N,
      N * finiteExtensionPlaceDegree K L P + 1 ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P N) + g)
    (hlarge : (g + 1) * (g + 2) ≤ Fintype.card K) :
    let s := Fintype.card K
    let ell := stepanovEll s
    let m := stepanovM g s
    let V := finiteExtensionOnePointRiemannSpace K L P m
    ∃ (u : Option (Fin (ell - g)) → L)
      (du : Option (Fin (ell - g)) → ℕ)
      (v : Fin (Module.finrank K V) → L)
      (c : (Option (Fin (ell - g)) ×
        Fin (Module.finrank K V)) →₀ K),
      (∀ i, u i ∈ finiteExtensionOnePointRiemannSpace K L P ell) ∧
      (∀ i, u i ≠ 0) ∧
      (∀ i, finiteExtensionPrincipalDivisor K L (u i) P = -(du i : ℤ)) ∧
      Function.Injective du ∧
      (∀ i, du i ≤ ell) ∧
      LinearIndependent K u ∧
      (∀ j, v j ∈ V) ∧
      LinearIndependent K v ∧
      c ≠ 0 ∧
      onePointStepanovSecondRestrictionMap K L u v s c = 0 ∧
      onePointStepanovFirstRestrictionMap K L u v s c ≠ 0 := by
  let r := finiteExtensionPlaceDegree K L P
  let s := Fintype.card K
  let ell := stepanovEll s
  let m := stepanovM g s
  let V := finiteExtensionOnePointRiemannSpace K L P m
  have hrpos : 0 < r := finiteExtensionPlaceDegree_pos K L P
  have hrle : r ≤ 2 := hdegreeLe
  have hlarge' : (g + 1) * (g + 2) ≤ s := hlarge
  have hgltS : g < s := by nlinarith
  have hgell : g ≤ ell := by
    simp only [ell, stepanovEll]
    omega
  have helllt : ell < s := stepanovEll_lt hlarge'
  have hellDecomp : ell = (ell - g) + g := by omega
  have hstrictLower :
      1 + r * (ell - g) ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P ell) := by
    have hcoarse := hriemann ell
    change ell * r + 1 ≤
      Module.finrank K
        (finiteExtensionOnePointRiemannSpace K L P ell) + g at hcoarse
    have hellMul : ell * r = (ell - g) * r + g * r := by
      calc
        ell * r = ((ell - g) + g) * r := by rw [← hellDecomp]
        _ = (ell - g) * r + g * r := Nat.add_mul _ _ _
    rw [hellMul] at hcoarse
    have hgr : g ≤ g * r := Nat.le_mul_of_pos_right g hrpos
    have htarget : 1 + (ell - g) * r ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P ell) := by
      omega
    simpa only [Nat.mul_comm r (ell - g)] using htarget
  have hstrict : ell - g ≤
      (strictFiltrationLevels
        (fun n => finiteExtensionOnePointRiemannSpace K L P n) ell).card :=
    le_card_onePointStrictLevels_of_finrank_lower
      K L P ell (ell - g) hconstants hstrictLower
  obtain ⟨u, du, huMem, huNe, huOrder, hduInjective, hduLe, huLI⟩ :=
    exists_onePointSectionsWithConstant_of_le_card_strictLevels
      K L P ell (ell - g) hstrict
  letI : Module.Finite K V :=
    finiteExtensionOnePointRiemannSpace_moduleFinite K L P m
  let b := Module.finBasis K V
  let v : Fin (Module.finrank K V) → L := fun j => (b j : V)
  have hvMem : ∀ j, v j ∈ V := fun j => (b j).property
  have hvLI : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    apply (Fintype.linearIndependent_iff.mp b.linearIndependent c) _ j
    apply V.subtype_injective
    simpa only [map_sum, map_smul, map_zero, Submodule.subtype_apply, v]
      using hc
  have hgridLI : LinearIndependent K
      (fun ij : Option (Fin (ell - g)) × Fin (Module.finrank K V) =>
        u ij.1 * (v ij.2) ^ s) := by
    exact onePointStepanovBasisGrid_linearIndependent K L P u du v
      huNe huOrder hduInjective (fun i => (hduLe i).trans_lt helllt) hvLI
  have hupper : Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L P (s * ell + m)) ≤
        r * (s * ell + m) + 1 := by
    have h := finiteExtensionOnePointRiemannSpace_finrank_upper
      K L P hconstants (s * ell + m)
    simpa only [r, Nat.mul_comm] using h
  have hVlower : r * m + 1 - g ≤ Module.finrank K V := by
    have h := hriemann m
    simpa only [r, V, Nat.mul_comm] using (Nat.sub_le_iff_le_add.mpr h)
  have hfirstCard : ell - g + 1 = ell + 1 - g := by omega
  have hnumericBase := stepanov_dimension_inequality_degree_le_two
    hlarge' hrpos hrle
  have hnumeric : r * (s * ell + m) + 1 <
      Fintype.card (Option (Fin (ell - g))) *
        Fintype.card (Fin (Module.finrank K V)) := by
    simp only [Fintype.card_option, Fintype.card_fin, hfirstCard]
    exact hnumericBase.trans_le
      (Nat.mul_le_mul_left (ell + 1 - g) hVlower)
  obtain ⟨c, hcNe, hsecond, hfirst⟩ :=
    exists_onePointStepanovAuxiliary_of_target_finrank_upper
      K L P u v ell m s (r * (s * ell + m) + 1)
      huMem hvMem hgridLI hupper hnumeric
  have hsecondRaw :
      onePointStepanovSecondRestrictionMap K L u v s c = 0 := by
    have h := congrArg Subtype.val hsecond
    simpa only [onePointStepanovSecondCodRestrictionMap_coe,
      Submodule.coe_zero] using h
  exact ⟨u, du, v, c, huMem, huNe, huOrder, hduInjective, hduLe,
    huLI, hvMem, hvLI, hcNe, hsecondRaw, hfirst⟩

end

end BGS.HasseWeil
