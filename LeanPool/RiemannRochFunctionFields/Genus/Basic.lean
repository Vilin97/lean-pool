/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.AdeleSpace.Basic
public import LeanPool.RiemannRochFunctionFields.Genus.Polar
public import Mathlib.Algebra.Algebra.IsSimpleRing
import LeanPool.RiemannRochFunctionFields.Genus.Ramification
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Genus, Riemann inequality, and the index of specialty

This file defines the genus of a function field and the specialty index `i(D)`.

## Main definitions

* `FunctionField.defect`: `deg D + 1 − ℓ(D)`.
* `FunctionField.genus`: the maximal defect.
* `FunctionField.indexOfSpecialty`: `ℓ(D) − (deg D + 1 − g)`.

## Main results

* `FunctionField.riemann_ineq`
* `FunctionField.finrank_adele_quotient`
* `FunctionField.genus_ratFunc`
* `FunctionField.deg_polarX_eq_finrank`
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

variable [IsFullConstantField k K]

/-- The classical decidable equality on `k(X)` used by the coordinate places. -/
local instance instDecidableEqRatFuncGenus : DecidableEq k⟮X⟯ := Classical.decEq _

/-- The defect `deg D + 1 − ℓ(D)`. -/
noncomputable def defect (D : DivisorA k K) : ℤ :=
  deg k K D + 1 - ell k K D

/-- Stichtenoth 1.4.11 for the chart variable `X_K` (equality; ≤ half proved in `Polar.lean`). -/
theorem deg_polarX_eq_finrank :
    deg k K (polarDivisor k K (XK k K)) = Module.finrank k⟮X⟯ K := by
  exact le_antisymm (deg_polarX_le_finrank (k := k) (K := K))
    (finrank_le_deg_polarX (k := k) (K := K))

section RiemannFamily

omit [IsFullConstantField k K] in
/-- Monotonicity of the defect along divisor domination. -/
theorem defect_mono' {D D' : DivisorA k K} (h : D ≤ D') :
    defect k K D ≤ defect k K D' := by
  dsimp only [defect]
  have := defect_mono (k := k) (K := K) h
  omega

omit [IsFullConstantField k K] in
/-- Defect is unchanged by adding a principal divisor. -/
theorem defect_add_principal (D : DivisorA k K) (x : Kˣ) :
    defect k K (D + principalDivisorA k K (Additive.ofMul x)) = defect k K D := by
  dsimp only [defect]
  rw [deg_add, deg_principalDivisor_eq_zero (k := k) (K := K) x, ell_add_principal, add_zero]

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
/-- From membership in `L(D₁ - D₀)`, the pole divisor of `f` moves `D₀` below `D₁ + (f)`. -/
theorem le_add_principal_of_memRRspace {D₀ D₁ : DivisorA k K} {f : K} (hf : f ≠ 0)
    (hmem : memRRspace k K (D₁ - D₀) f) :
    D₀ ≤ D₁ + principalDivisorA k K (Additive.ofMul (Units.mk0 f hf)) := by
  rw [le_iff_sub_effective]
  intro v
  dsimp only [Finsupp.add_apply, Finsupp.sub_apply]
  have hv := hmem v
  have hxval := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul (Units.mk0 f hf)) v
  change placeValuation k K v f ≤ WithZero.exp ((D₁ - D₀) v) at hv
  change placeValuation k K v f =
    WithZero.exp (-(principalDivisorA k K (Additive.ofMul (Units.mk0 f hf)) v)) at hxval
  rw [hxval] at hv
  have hexp := WithZero.exp_le_exp.mp hv
  have hsubv : (D₁ - D₀) v = D₁ v - D₀ v := rfl
  have hexp' :
      -(principalDivisorA k K (Additive.ofMul (Units.mk0 f hf)) v) ≤ D₁ v - D₀ v := by
    simpa [hsubv] using hexp
  linarith

omit [IsFullConstantField k K] in
/-- `ℓ(D + E) − deg E ≤ ℓ(D)` for effective `E`. -/
theorem ell_sub_effective_sub_ge {D E : DivisorA k K} (hE : IsEffective k K E) :
    (ell k K (D + E) : ℤ) - deg k K E ≤ ell k K D := by
  have hle : D ≤ D + E := by
    intro v
    simp only [Finsupp.add_apply]
    linarith [hE v]
  have hsum := finrankRRspaceDiff_add_ell (k := k) (K := K) hle
  have hq := finrankRRspaceDiff_add_effective_le (k := k) (K := K) D E hE
  have hdeg : 0 ≤ deg k K E := deg_nonneg (k := k) (K := K) hE
  have htoNat : ((deg k K E).toNat : ℤ) = deg k K E := Int.toNat_of_nonneg hdeg
  have hqZ : (finrankRRspaceDiff k K D (D + E) : ℤ) ≤ deg k K E := by
    rw [← htoNat]
    exact_mod_cast hq
  have hsum' : (finrankRRspaceDiff k K D (D + E) : ℤ) + ell k K D = ell k K (D + E) := by
    exact_mod_cast hsum
  omega

omit [IsFullConstantField k K] in
/-- Every defect is bounded by `c₀` once the pole family has defect `≤ c₀` and grows in
rank. -/
theorem defect_le_of_family (B C : DivisorA k K) (c₀ : ℤ)
    (hmono : ∀ r : ℕ, defect k K (C + r • B) ≤ c₀)
    (hgrow : ∀ m : ℤ, ∃ r : ℕ, m ≤ ell k K (C + r • B)) :
    ∀ D : DivisorA k K, defect k K D ≤ c₀ := by
  intro D
  let Dpos := D ⊔ (0 : DivisorA k K)
  have hDle : D ≤ Dpos := le_sup_left (a := D) (b := 0)
  have hDposeff : IsEffective k K Dpos := fun v => le_max_right (D v) 0
  obtain ⟨r, hr⟩ := hgrow (deg k K Dpos + 1)
  let Dr := C + r • B
  have hsub := ell_sub_effective_sub_ge (k := k) (K := K) (D := Dr - Dpos) (E := Dpos) hDposeff
  rw [sub_add_cancel] at hsub
  have hellpos : 0 < ell k K (Dr - Dpos) := by
    linarith
  obtain ⟨f, hfne⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)).1 hellpos
  let fK : K := f.val
  have hfKne : fK ≠ 0 := fun h => hfne (Subtype.ext h)
  have hmem : memRRspace k K (Dr - Dpos) fK := f.property
  have hDposle : Dpos ≤ Dr + principalDivisorA k K (Additive.ofMul (Units.mk0 fK hfKne)) :=
    le_add_principal_of_memRRspace (k := k) (K := K) hfKne hmem
  have hDle' : D ≤ Dr + principalDivisorA k K (Additive.ofMul (Units.mk0 fK hfKne)) :=
    le_trans hDle hDposle
  calc
    defect k K D ≤
        defect k K (Dr + principalDivisorA k K (Additive.ofMul (Units.mk0 fK hfKne))) :=
      defect_mono' (k := k) (K := K) hDle'
    _ = defect k K Dr := defect_add_principal (k := k) (K := K) Dr _
    _ ≤ c₀ := hmono r

end RiemannFamily

/-- Along the chart pole family, every defect is at most `deg C + 1 − n`. -/
theorem defect_le_chart_family (D : DivisorA k K) :
    defect k K D ≤
      deg k K (basisPoleBound k K (Module.finBasis k⟮X⟯ K)) + 1 -
        Module.finrank k⟮X⟯ K := by
  let b := Module.finBasis k⟮X⟯ K
  let n := Module.finrank k⟮X⟯ K
  let C := basisPoleBound k K b
  let B := polarDivisor k K (XK k K)
  let c₀ := deg k K C + 1 - n
  have hmono : ∀ r : ℕ, defect k K (C + r • B) ≤ c₀ := by
    intro r
    have hdeg : deg k K (C + r • B) = deg k K C + (r : ℤ) * deg k K B := by
      rw [add_comm, ← nsmul_eq_mul, deg_add, deg_nsmul, nsmul_eq_mul, add_comm]
    have hell := ell_family_ge (k := k) (K := K) (n := n) (r := r) b
    have hBdeg : deg k K B = (n : ℤ) := deg_polarX_eq_finrank (k := k) (K := K)
    have hcast : (n * (r + 1) : ℤ) ≤ ell k K (C + r • B) := Nat.cast_le.mpr hell
    dsimp only [defect]
    rw [hdeg, hBdeg]
    linarith
  have hn : 0 < n := Module.finrank_pos
  have hgrow : ∀ m : ℤ, ∃ r : ℕ, m ≤ ell k K (C + r • B) := by
    intro m
    by_cases hm : m ≤ 0
    · refine ⟨0, ?_⟩
      have h0le : (0 : DivisorA k K) ≤ C + 0 • B := fun v =>
        show 0 ≤ (C + 0 • B) v by
          simpa [Finsupp.add_apply, Finsupp.nsmul_apply] using
            basisPoleBound_nonneg (k := k) (K := K) b v
      have hmono0 : (ell k K (0 : DivisorA k K) : ℤ) ≤ ell k K (C + 0 • B) := by
        exact_mod_cast Submodule.finrank_mono (RRspace_mono (k := k) (K := K) h0le)
      rw [ell_zero (k := k) (K := K)] at hmono0
      linarith
    · have hmpos : 0 < m := by omega
      let mnat := Int.toNat m
      have hmNat : (mnat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
      refine ⟨mnat, ?_⟩
      have hge := ell_family_ge (k := k) (K := K) (n := n) (r := mnat) b
      have hcast : (n * (mnat + 1) : ℤ) ≤ ell k K (C + mnat • B) := Nat.cast_le.mpr hge
      have hbound : m ≤ (n * (mnat + 1) : ℤ) := by
        rw [← hmNat]
        have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
        nlinarith [show (0 : ℤ) < m from hmpos]
      linarith
  exact defect_le_of_family (k := k) (K := K) B C c₀ hmono hgrow D

/-- Riemann's bounded-defect theorem: the integer defects have a nonnegative maximum. -/
theorem exists_max_defect :
    ∃ g : ℕ, (∀ D : DivisorA k K, defect k K D ≤ (g : ℤ)) ∧
      ∃ D : DivisorA k K, defect k K D = (g : ℤ) := by
  let b := Module.finBasis k⟮X⟯ K
  let n := Module.finrank k⟮X⟯ K
  let C := basisPoleBound k K b
  let c₀ := deg k K C + 1 - n
  have hbound : ∀ D : DivisorA k K, defect k K D ≤ c₀ :=
    fun D => defect_le_chart_family (k := k) (K := K) D
  have hzero : defect k K (0 : DivisorA k K) = 0 := by
    dsimp only [defect]
    rw [deg_zero (k := k) (K := K), ell_zero (k := k) (K := K)]
    omega
  have hInh : ∃ z : ℤ, ∃ D : DivisorA k K, defect k K D = z := ⟨0, 0, hzero⟩
  have hBdd : ∃ b : ℤ, ∀ z : ℤ, (∃ D : DivisorA k K, defect k K D = z) → z ≤ b := by
    refine ⟨c₀, ?_⟩
    intro z ⟨D, hD⟩
    simpa [hD] using hbound D
  obtain ⟨g', hg', hgmax⟩ := Int.exists_greatest_of_bdd hBdd hInh
  have hg'nn : 0 ≤ g' := hgmax 0 ⟨0, hzero⟩
  refine ⟨g'.toNat, ?_, ?_⟩
  · intro D
    have hle := hgmax (defect k K D) ⟨D, rfl⟩
    calc defect k K D ≤ g' := hle
      _ = (g'.toNat : ℤ) := (Int.toNat_of_nonneg hg'nn).symm
  · obtain ⟨D, hD⟩ := hg'
    refine ⟨D, ?_⟩
    rw [Int.toNat_of_nonneg hg'nn]
    exact hD

/-- The genus of the function field `K/k`. -/
noncomputable def genus : ℕ :=
  Classical.choose (exists_max_defect k K)

theorem riemann_ineq (D : DivisorA k K) :
    (ell k K D : ℤ) ≥ deg k K D + 1 - (genus k K : ℤ) := by
  have h := (Classical.choose_spec (exists_max_defect k K)).1 D
  simp only [defect, genus] at h ⊢
  omega

theorem defect_le (D : DivisorA k K) : defect k K D ≤ genus k K := by
  have h := riemann_ineq k K D
  simp only [defect]
  omega

theorem exists_defect_eq : ∃ D : DivisorA k K, defect k K D = genus k K := by
  simpa only [genus] using (Classical.choose_spec (exists_max_defect k K)).2

/-- Riemann's inequality along a growing pole family: the genus is at most `c₀`. -/
theorem genus_le_of_family (B C : DivisorA k K) (c₀ : ℤ)
    (hmono : ∀ r : ℕ, defect k K (C + r • B) ≤ c₀)
    (hgrow : ∀ m : ℤ, ∃ r : ℕ, m ≤ ell k K (C + r • B)) :
    (genus k K : ℤ) ≤ c₀ := by
  have hbound := defect_le_of_family (k := k) (K := K) B C c₀ hmono hgrow
  obtain ⟨D, hD⟩ := exists_defect_eq (k := k) (K := K)
  simpa [hD] using hbound D

/-- The index of specialty `i(D) = ℓ(D) − (deg D + 1 − g)`. -/
noncomputable def indexOfSpecialty (D : DivisorA k K) : ℕ :=
  (ell k K D - (deg k K D + 1 - (genus k K : ℤ))).toNat

theorem indexOfSpecialty_eq (D : DivisorA k K) :
    (indexOfSpecialty k K D : ℤ) = ell k K D - (deg k K D + 1 - (genus k K : ℤ)) := by
  have h := riemann_ineq k K D
  rw [indexOfSpecialty, Int.toNat_of_nonneg]
  omega

/-- `finrank k (A_K ⧸ (A(D) + diag(K)))`. -/
noncomputable def finrankAdeleQuotient (D : DivisorA k K) : ℕ :=
  Module.finrank k <|
    (AdeleSpace k K) ⧸ (adeleFilt k K D + diagonalSubmodule k K)

section PolarDivisor

omit [IsFullConstantField k K] in
theorem polar_deg_pos {x : K} (hx : ¬IsAlgebraic k x) :
    0 < deg k K (polarDivisor k K x) := by
  by_cases hx0 : x = 0
  · subst hx0
    exact absurd isAlgebraic_zero hx
  · exact polarDivisor_pos k K hx0 hx

end PolarDivisor

section RatFunc

/-- The genus of the rational function field `RatFunc k` is zero. -/
theorem genus_ratFunc : genus k (RatFunc k) = 0 := by
  let K := k⟮X⟯
  have hn : Module.finrank k⟮X⟯ K = 1 := Module.finrank_self k⟮X⟯
  let hb : Module.Basis (Fin 1) k⟮X⟯ K := Module.Basis.singleton (Fin 1) k⟮X⟯
  let B := polarDivisor k K (XK k K)
  let C := (0 : DivisorA k K)
  have hCeq : basisPoleBound k K hb = C := by
    have hpol : polarDivisor k K (1 : K) = 0 :=
      polarDivisor_eq_zero_of_algebraic (k := k) (K := K) isAlgebraic_one
    ext v
    simp only [basisPoleBound, C, Finsupp.zero_apply]
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_one]
    dsimp [hb]
    simp only [Module.Basis.singleton_apply, hpol]
    rfl
  have hmono : ∀ r : ℕ, defect k K (C + r • B) ≤ 0 := by
    intro r
    dsimp only [defect]
    have hdeg : deg k K (C + r • B) = (r : ℤ) * deg k K B := by
      rw [zero_add, deg_nsmul]
    have hell := ell_family_ge (k := k) (K := K) (n := 1) (r := r) hb
    have hell' : ((r + 1 : ℕ) : ℤ) ≤ (ell k K (C + r • B) : ℤ) := by
      have hellNat : r + 1 ≤ ell k K (C + r • B) := by
        simpa [hCeq, one_mul, B] using hell
      exact_mod_cast hellNat
    norm_num [Nat.cast_add, Nat.cast_one] at hell'
    have hBdeg : deg k K B = 1 := by
      rw [deg_polarX_eq_finrank (k := k) (K := K)]
      exact_mod_cast hn
    rw [hdeg, hBdeg]
    linarith
  have hgrow : ∀ m : ℤ, ∃ r : ℕ, m ≤ ell k K (C + r • B) := by
    intro m
    by_cases hm : m ≤ 0
    · refine ⟨0, ?_⟩
      have h0le : (0 : DivisorA k K) ≤ C + 0 • B := fun v => by simp [C]
      have hmono0 : (ell k K (0 : DivisorA k K) : ℤ) ≤ ell k K (C + 0 • B) := by
        exact_mod_cast Submodule.finrank_mono (RRspace_mono (k := k) (K := K) h0le)
      rw [ell_zero (k := k) (K := K)] at hmono0
      linarith
    · have hmpos : 0 < m := by omega
      let mnat := Int.toNat m
      have hmNat : (mnat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
      refine ⟨mnat, ?_⟩
      have hge := ell_family_ge (k := k) (K := K) (n := 1) (r := mnat) hb
      have hcast : ((mnat + 1 : ℕ) : ℤ) ≤ (ell k K (C + mnat • B) : ℤ) := by
        have hgeNat : mnat + 1 ≤ ell k K (C + mnat • B) := by
          simpa [hCeq, one_mul, B] using hge
        exact_mod_cast hgeNat
      norm_num [Nat.cast_add, Nat.cast_one] at hcast
      linarith
  have hle : (genus k K : ℤ) ≤ 0 :=
    genus_le_of_family (k := k) (K := K) B C 0 hmono hgrow
  have hge : 0 ≤ (genus k K : ℤ) := by
    have := defect_le (k := k) (K := K) (0 : DivisorA k K)
    dsimp [defect] at this
    rw [deg_zero (k := k) (K := K), ell_zero (k := k) (K := K)] at this
    exact this
  linarith

end RatFunc

end FunctionField.Chart

end
