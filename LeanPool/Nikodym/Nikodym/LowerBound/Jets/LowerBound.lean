/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LinearNormalization
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LocalParameters

/-!
# The local jet minimum

This file implements blueprint node **J02** of the algebra backend (see
`docs/algebra_backend_design.md`, §2, J02): for a prime ideal `I` of `P := MvPolynomial (Fin d) K`
of quotient dimension `k = quotDim I` and a rational point `x` on `I`, the jet space
`Q_{I,x}(r) = P ⧸ (I ⊔ 𝔪ₓ ^ r)` has dimension at least `(r + k - 1).choose k`.

Over an infinite field this is proved at the origin first. The linear Noether normalization of
the tangent-cone ideal `J := tangentIdeal I` (A02) provides `s := quotDim J ≥ k` (J01) linear
forms `y` such that `aeval (mk J ∘ y)` is injective. The key lemma
`aeval_eq_zero_of_mem_sup_pow_idealOfVars` shows that if `aeval y G ∈ I ⊔ 𝔪 ^ r` for a
polynomial `G` in `s` variables of total degree `< r`, then `G = 0`: the lowest nonzero
homogeneous component of `G` would give a form in `I ⊔ 𝔪 ^ (n + 1)`, hence in `J`, contradicting
injectivity. So the polynomials of total degree `≤ r - 1` in `s` variables embed into
`Q_{I,0}(r)`, which yields the bound `(r - 1 + s).choose s ≤ jetDim I 0 r`.

## Main results

* `choose_le_jetDim_origin`: the bound at the origin;
* `choose_le_jetDim_of_infinite`: the bound at an arbitrary rational point, obtained by
  translation (`quotDim_comap_translate`, `jetDim_eq_jetDim_comap_translate`).

The hypothesis `[Infinite K]` is removed by base change in the assembly (node TR).
-/

namespace Nikodym.LowerBound

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {d : ℕ}

/-! ### The injectivity lemma -/

section Injectivity

variable {I : Ideal (MvPolynomial (Fin d) K)} {s : ℕ} {y : Fin s → MvPolynomial (Fin d) K}

/-- Blueprint J02 (auxiliary): the class in `P ⧸ J` of `aeval y G` is `aeval (mk J ∘ y) G`. -/
theorem mk_aeval (J : Ideal (MvPolynomial (Fin d) K)) (y : Fin s → MvPolynomial (Fin d) K)
    (G : MvPolynomial (Fin s) K) :
    Ideal.Quotient.mk J (aeval y G) = aeval (fun i ↦ Ideal.Quotient.mk J (y i)) G := by
  rw [← Ideal.Quotient.mkₐ_eq_mk K, ← comp_aeval]
  rfl

/-- Blueprint J02 (auxiliary): substituting linear forms into a form of degree `n` gives a form
of degree `n`. -/
theorem isHomogeneous_aeval_of_forall_isHomogeneous_one (hy : ∀ i, (y i).IsHomogeneous 1)
    {n : ℕ} {G : MvPolynomial (Fin s) K} (hG : G.IsHomogeneous n) :
    (aeval y G).IsHomogeneous n := by
  have := hG.aeval y hy
  rwa [one_mul] at this

/-- Blueprint J02 (key step): if `aeval (mk (tangentIdeal I) ∘ y)` is injective for linear forms
`y`, and `aeval y G ∈ I ⊔ 𝔪 ^ r` for a polynomial `G` of total degree `< r`, then all
homogeneous components of `G` of degree `< m` vanish, for every `m`. Induction on `m`: the
degree-`m` component `G_m` satisfies `aeval y G_m ∈ I ⊔ 𝔪 ^ (m + 1)`, so `aeval y G_m` lies in
the tangent-cone ideal and `G_m = 0` by injectivity. -/
theorem homogeneousComponent_eq_zero_of_aeval_mem_sup_pow_idealOfVars
    (hy : ∀ i, (y i).IsHomogeneous 1)
    (hinj : Function.Injective
      (aeval (fun i ↦ Ideal.Quotient.mk (tangentIdeal I) (y i)) :
        MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin d) K ⧸ tangentIdeal I))
    {r : ℕ} {G : MvPolynomial (Fin s) K} (hG : G.totalDegree < r)
    (h : aeval y G ∈ I ⊔ idealOfVars (Fin d) K ^ r) (m : ℕ) :
    ∀ n < m, homogeneousComponent n G = 0 := by
  classical
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    suffices hm0 : homogeneousComponent m G = 0 by
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
      · exact ih n hn
      · exact hm0
    by_cases hm : G.totalDegree < m
    · exact homogeneousComponent_eq_zero m G hm
    have hmem : m ∈ Finset.range (G.totalDegree + 1) := Finset.mem_range.mpr (by omega)
    have hsum : aeval y (homogeneousComponent m G) =
        aeval y G - ∑ i ∈ (Finset.range (G.totalDegree + 1)).erase m,
          aeval y (homogeneousComponent i G) := by
      rw [eq_sub_iff_add_eq, ← map_sum, ← map_add,
        Finset.add_sum_erase _ (fun i ↦ homogeneousComponent i G) hmem, sum_homogeneousComponent]
    have hrest : ∀ i ∈ (Finset.range (G.totalDegree + 1)).erase m,
        aeval y (homogeneousComponent i G) ∈ idealOfVars (Fin d) K ^ (m + 1) := by
      intro i hi
      rw [Finset.mem_erase] at hi
      rcases lt_or_gt_of_ne hi.1 with hi' | hi'
      · rw [ih i hi', map_zero]
        exact zero_mem _
      · exact Ideal.pow_le_pow_right hi' (mem_pow_idealOfVars_of_isHomogeneous
          (isHomogeneous_aeval_of_forall_isHomogeneous_one hy
            (homogeneousComponent_isHomogeneous i G)))
    have hFm : aeval y (homogeneousComponent m G) ∈ I ⊔ idealOfVars (Fin d) K ^ (m + 1) := by
      rw [hsum]
      refine Submodule.sub_mem _ ?_ (Ideal.mem_sup_right (Submodule.sum_mem _ hrest))
      have hle : I ⊔ idealOfVars (Fin d) K ^ r ≤ I ⊔ idealOfVars (Fin d) K ^ (m + 1) :=
        sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) I
      exact hle h
    have hJ : aeval y (homogeneousComponent m G) ∈ tangentIdeal I :=
      (mem_tangentIdeal_iff I (isHomogeneous_aeval_of_forall_isHomogeneous_one hy
        (homogeneousComponent_isHomogeneous m G))).mpr hFm
    apply hinj
    rw [map_zero, ← mk_aeval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hJ

/-- Blueprint J02 (key step): if `aeval (mk (tangentIdeal I) ∘ y)` is injective for linear forms
`y`, and `aeval y G ∈ I ⊔ 𝔪 ^ r` for a polynomial `G` of total degree `< r`, then `G = 0`. -/
theorem aeval_eq_zero_of_mem_sup_pow_idealOfVars (hy : ∀ i, (y i).IsHomogeneous 1)
    (hinj : Function.Injective
      (aeval (fun i ↦ Ideal.Quotient.mk (tangentIdeal I) (y i)) :
        MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin d) K ⧸ tangentIdeal I))
    {r : ℕ} {G : MvPolynomial (Fin s) K} (hG : G.totalDegree < r)
    (h : aeval y G ∈ I ⊔ idealOfVars (Fin d) K ^ r) : G = 0 := by
  rw [← sum_homogeneousComponent G]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [Finset.mem_range] at hn
  exact homogeneousComponent_eq_zero_of_aeval_mem_sup_pow_idealOfVars hy hinj hG h r n (by omega)

end Injectivity

/-! ### The bound at the origin -/

section Origin

/-- Blueprint J02: if `aeval (mk (tangentIdeal I) ∘ y)` is injective for `s` linear forms `y`,
then `(r - 1 + s).choose s ≤ jetDim I 0 r` for `r ≥ 1`: the polynomials of total degree `≤ r - 1`
in `s` variables embed `K`-linearly into `Q_{I,0}(r)` via `G ↦ mk (aeval y G)`. -/
theorem choose_le_jetDim_origin_of_injective (I : Ideal (MvPolynomial (Fin d) K)) {s : ℕ}
    {y : Fin s → MvPolynomial (Fin d) K} (hy : ∀ i, (y i).IsHomogeneous 1)
    (hinj : Function.Injective
      (aeval (fun i ↦ Ideal.Quotient.mk (tangentIdeal I) (y i)) :
        MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin d) K ⧸ tangentIdeal I))
    {r : ℕ} (hr : 1 ≤ r) : (r - 1 + s).choose s ≤ jetDim I 0 r := by
  set φ : restrictTotalDegree (Fin s) K (r - 1) →ₗ[K] JetSpace I 0 r :=
    (Ideal.Quotient.mkₐ K (jetIdeal I 0 r)).toLinearMap ∘ₗ (aeval y).toLinearMap ∘ₗ
      (restrictTotalDegree (Fin s) K (r - 1)).subtype with hφ
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro G hG
    have hG' : aeval y (G : MvPolynomial (Fin s) K) ∈ I ⊔ idealOfVars (Fin d) K ^ r := by
      have h0 : Ideal.Quotient.mk (jetIdeal I 0 r) (aeval y (G : MvPolynomial (Fin s) K)) = 0 :=
        hG
      rw [Ideal.Quotient.eq_zero_iff_mem, jetIdeal, pointIdeal_zero] at h0
      exact h0
    have hdeg : (G : MvPolynomial (Fin s) K).totalDegree < r := by
      have := mem_restrictTotalDegree_iff.mp G.2
      omega
    exact Subtype.ext (aeval_eq_zero_of_mem_sup_pow_idealOfVars hy hinj hdeg hG')
  have := LinearMap.finrank_le_finrank_of_injective hφinj
  rwa [finrank_restrictTotalDegree] at this

/-- Blueprint J02 (auxiliary): `(t + a).choose a ≤ (t + b).choose b` for `a ≤ b`. -/
theorem choose_add_le_choose_add {a b : ℕ} (t : ℕ) (h : a ≤ b) :
    (t + a).choose a ≤ (t + b).choose b := by
  rw [← Nat.choose_symm_add, ← Nat.choose_symm_add]
  exact Nat.choose_le_choose t (by omega)

/-- Blueprint J02: **the local jet minimum at the origin.** For `K` infinite, `I` a prime ideal
of `P = MvPolynomial (Fin d) K` contained in the ideal `𝔪` of the origin, and `r ≥ 1`,
`(r + k - 1).choose k ≤ jetDim I 0 r` where `k = quotDim I`. -/
theorem choose_le_jetDim_origin [Infinite K] (I : Ideal (MvPolynomial (Fin d) K)) [I.IsPrime]
    (hI : I ≤ idealOfVars (Fin d) K) {r : ℕ} (hr : 1 ≤ r) :
    (r + quotDim I - 1).choose (quotDim I) ≤ jetDim I 0 r := by
  obtain ⟨y, hy, hinj, N, hN⟩ := exists_linear_normalization (tangentIdeal I)
    (tangentIdeal_ne_top hI) (tangentIdeal_isHomogeneous I)
  have hk : quotDim I ≤ quotDim (tangentIdeal I) :=
    quotDim_le_of_pow_idealOfVars_le_tangentIdeal_sup I hI hy hN
  calc (r + quotDim I - 1).choose (quotDim I)
      = (r - 1 + quotDim I).choose (quotDim I) := by congr 1; omega
    _ ≤ (r - 1 + quotDim (tangentIdeal I)).choose (quotDim (tangentIdeal I)) :=
        choose_add_le_choose_add (r - 1) hk
    _ ≤ jetDim I 0 r := choose_le_jetDim_origin_of_injective I hy hinj hr

end Origin

/-! ### Translation to an arbitrary rational point -/

section Translate

variable (I : Ideal (MvPolynomial (Fin d) K)) (x : Fin d → K)

/-- Blueprint J02 (auxiliary): the translated ideal `τₓ⁻¹(I) = I.comap (translate x)` has the
same quotient dimension as `I`. -/
theorem quotDim_comap_translate :
    quotDim (I.comap (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K)) =
      quotDim I := by
  have e : (MvPolynomial (Fin d) K ⧸
      I.comap (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K)) ≃+*
        MvPolynomial (Fin d) K ⧸ I :=
    Ideal.quotientEquiv _ I (translate x).toRingEquiv
      (Ideal.map_comap_of_surjective
        (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K)
        (translate x).surjective I).symm
  unfold quotDim
  rw [ringKrullDim_eq_of_ringEquiv e]

/-- Blueprint J02 (auxiliary): if `I ≤ 𝔪ₓ`, then the translated ideal `τₓ⁻¹(I)` is contained in
the ideal `𝔪` of the origin. -/
theorem comap_translate_le_idealOfVars (hx : I ≤ pointIdeal x) :
    I.comap (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K) ≤
      idealOfVars (Fin d) K := by
  refine (Ideal.comap_mono hx).trans ?_
  rw [pointIdeal_eq_map, Ideal.comap_map_of_bijective
    (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K) (translate x).bijective]

/-- Blueprint J02 (auxiliary): the jet dimension of `I` at `x` is the jet dimension of the
translated ideal `τₓ⁻¹(I)` at the origin. -/
theorem jetDim_eq_jetDim_comap_translate (r : ℕ) :
    jetDim I x r =
      jetDim (I.comap (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K)) 0 r := by
  set I' := I.comap (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K)
  have h : I' ⊔ idealOfVars (Fin d) K ^ r = jetIdeal I' 0 r := by
    rw [jetIdeal, pointIdeal_zero]
  rw [jetDim, jetDim, ← (jetSpaceEquivOrigin I x r).toLinearEquiv.finrank_eq]
  exact (Ideal.quotientEquivAlgOfEq K h).toLinearEquiv.finrank_eq

/-- Blueprint J02: **the local jet minimum.** For `K` infinite, `I` a prime ideal of
`P = MvPolynomial (Fin d) K`, `x` a rational point on `I` (i.e. `I ≤ 𝔪ₓ`) and `r ≥ 1`,
`(r + k - 1).choose k ≤ jetDim I x r` where `k = quotDim I`. -/
theorem choose_le_jetDim_of_infinite [Infinite K] (I : Ideal (MvPolynomial (Fin d) K)) [I.IsPrime]
    (x : Fin d → K) (hx : I ≤ pointIdeal x) {r : ℕ} (hr : 1 ≤ r) :
    (r + quotDim I - 1).choose (quotDim I) ≤ jetDim I x r := by
  have : (I.comap (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K)).IsPrime :=
    Ideal.IsPrime.comap _
  rw [jetDim_eq_jetDim_comap_translate, ← quotDim_comap_translate I x]
  exact choose_le_jetDim_origin _ (comap_translate_le_idealOfVars I x hx) hr

end Translate

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
