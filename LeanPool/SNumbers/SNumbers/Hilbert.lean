/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Approximation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Hilbert numbers `h_n`

The Hilbert numbers are defined by factoring an operator through `ℓ₂` as a
Hilbert space. They are defined over any `RCLike` scalar field `𝕜`
(i.e. `ℝ` or `ℂ`):

`h_n S = sup { a_n (B ∘ S ∘ A) / (‖B‖ * ‖A‖) :
                 A : ℓ₂ →L X, B : Y →L ℓ₂, A ≠ 0, B ≠ 0 }`,

where `ℓ₂ = L2 𝕜` is `lp (fun _ : ℕ => 𝕜) 2`.

## Main results

* `SNumbers.hilbertNumber` — the `n`-th Hilbert number.
* `SNumbers.hilbertNumber_nonneg`, `hilbertNumber_zero_eq_norm`,
  `hilbertNumber_le_norm`, `hilbertNumber_antitone`, `hilbertNumber_add_le`,
  `hilbertNumber_comp_comp_le`, `hilbertNumber_eq_zero_of_rank_le` — the
  axioms (S1)–(S4).
* `SNumbers.isSNumberSequence_hilbertNumber` — the Hilbert numbers form an
  s-number sequence (S1)–(S5).

The two non-trivial halves are:

* `norm_le_hilbertNumber_zero` (the `‖S‖ ≤ h₀ S` half of (S1a)): a
  Hahn–Banach norming functional `φ` (`‖φ‖ = 1`, `φ(S x) = ‖S x‖`) builds a
  rank-one pair `(A, B)` realising the ratio `‖S x‖ → ‖S‖`.
* `one_le_hilbertNumber_id` (the `1 ≤ hₙ(id)` half of (S5)): the isometric
  section `exists_l2_section` (`ℓ₂ⁿ⁺¹ ↪ ℓ₂` with contractive retraction
  `A ∘ B = id`) reduces the bound to `aₙ(id_{ℓ₂ⁿ⁺¹}) = 1`
  (`approximationNumber_id_euclidean`) via the (S3) ideal property.
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A model of `ℓ₂` over `𝕜`: the space `lp` with exponent `2` over `ℕ`.
For `RCLike 𝕜` this is a Hilbert space, and—crucially—it lives in the same
universe as `X` and `Y`. -/
abbrev L2 (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) 2

/-! ### Definition -/

/-- The set of ratios `a_n (B ∘ S ∘ A) / (‖B‖ ‖A‖)` over nonzero
`A : ℓ₂ → X`, `B : Y → ℓ₂`, whose supremum is the Hilbert number. -/
def hilbertSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜),
      A ≠ 0 ∧ B ≠ 0 ∧
      r = approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖)}

/-- The `n`-th **Hilbert number** of a continuous linear map between
`𝕜`-Banach spaces (`𝕜 = ℝ` or `ℂ`).

`h_n S = sup { a_n (B ∘ S ∘ A) / (‖B‖ * ‖A‖) :
                  A : ℓ₂ →L X, B : Y →L ℓ₂, A ≠ 0, B ≠ 0 }`. -/
noncomputable def hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sSup (hilbertSet S n)

lemma hilbertNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n = sSup (hilbertSet S n) := rfl

/-! ### A norm bound on the triple composition -/

/-- `‖B ∘ S ∘ A‖ ≤ ‖B‖ ‖S‖ ‖A‖`. -/
lemma norm_comp_comp_le {W' X' Y' Z' : Type*}
    [NormedAddCommGroup W'] [NormedSpace 𝕜 W'] [NormedAddCommGroup X'] [NormedSpace 𝕜 X']
    [NormedAddCommGroup Y'] [NormedSpace 𝕜 Y'] [NormedAddCommGroup Z'] [NormedSpace 𝕜 Z']
    (A : W' →L[𝕜] X') (S : X' →L[𝕜] Y') (B : Y' →L[𝕜] Z') :
    ‖B.comp (S.comp A)‖ ≤ ‖B‖ * ‖S‖ * ‖A‖ := by
  calc ‖B.comp (S.comp A)‖
      ≤ ‖B‖ * ‖S.comp A‖ := opNorm_comp_le _ _
    _ ≤ ‖B‖ * (‖S‖ * ‖A‖) := by gcongr; exact opNorm_comp_le _ _
    _ = ‖B‖ * ‖S‖ * ‖A‖ := by ring

/-! ### Basic facts about the ratio set -/

/-- Every ratio `a_n (B S A)/(‖B‖‖A‖)` is `≤ ‖S‖`. -/
lemma ratio_le_norm (S : X →L[𝕜] Y) (n : ℕ) {A : L2 𝕜 →L[𝕜] X} {B : Y →L[𝕜] L2 𝕜}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖) ≤ ‖S‖ := by
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  rw [div_le_iff₀ hpos]
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ ‖B.comp (S.comp A)‖ := approximationNumber_le_norm _ _
    _ ≤ ‖B‖ * ‖S‖ * ‖A‖ := norm_comp_comp_le A S B
    _ = ‖S‖ * (‖B‖ * ‖A‖) := by ring

lemma hilbertSet_bddAbove (S : X →L[𝕜] Y) (n : ℕ) : BddAbove (hilbertSet S n) :=
  ⟨‖S‖, by rintro r ⟨A, B, hA, hB, rfl⟩; exact ratio_le_norm S n hA hB⟩

/-- Each admissible ratio is `≤ h_n S`. -/
lemma ratio_le_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) {A : L2 𝕜 →L[𝕜] X} {B : Y →L[𝕜] L2 𝕜}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖) ≤ hilbertNumber S n :=
  le_csSup (hilbertSet_bddAbove S n) ⟨A, B, hA, hB, rfl⟩

/-! ### (S1) Non-negativity and monotonicity -/

lemma hilbertNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) : 0 ≤ hilbertNumber S n :=
  Real.sSup_nonneg <| by
    rintro r ⟨A, B, hA, hB, rfl⟩
    exact div_nonneg (approximationNumber_nonneg _ _) (by positivity)

/-- (S1b) `h_{n+1} S ≤ h_n S`. -/
lemma hilbertNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S (n + 1) ≤ hilbertNumber S n := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (hilbertNumber_nonneg S n)
  rintro r ⟨A, B, hA, hB, rfl⟩
  refine le_trans ?_ (ratio_le_hilbertNumber S n hA hB)
  gcongr
  exact approximationNumber_antitone _ _

/-! ### (S2) Subadditivity -/

/-- (S2) `h_n (S + T) ≤ h_n S + ‖T‖`. -/
lemma hilbertNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber (S + T) n ≤ hilbertNumber S n + ‖T‖ := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (by have := hilbertNumber_nonneg S n; linarith [norm_nonneg T])
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  -- `B ∘ (S + T) ∘ A = B∘S∘A + B∘T∘A`.
  have hcomp : B.comp ((S + T).comp A) = B.comp (S.comp A) + B.comp (T.comp A) := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  rw [hcomp, div_le_iff₀ hpos]
  calc approximationNumber (B.comp (S.comp A) + B.comp (T.comp A)) n
      ≤ approximationNumber (B.comp (S.comp A)) n + ‖B.comp (T.comp A)‖ :=
        approximationNumber_add_le _ _ _
    _ ≤ approximationNumber (B.comp (S.comp A)) n + ‖B‖ * ‖T‖ * ‖A‖ := by
        gcongr; exact norm_comp_comp_le A T B
    _ ≤ hilbertNumber S n * (‖B‖ * ‖A‖) + ‖B‖ * ‖T‖ * ‖A‖ := by
        gcongr
        rw [← div_le_iff₀ hpos]; exact ratio_le_hilbertNumber S n hA hB
    _ = (hilbertNumber S n + ‖T‖) * (‖B‖ * ‖A‖) := by ring

/-! ### (S3) Ideal property -/

/-- (S3) `h_n (B ∘ S ∘ A) ≤ ‖B‖ * h_n S * ‖A‖`. -/
lemma hilbertNumber_comp_comp_le (A₀ : W →L[𝕜] X) (S : X →L[𝕜] Y) (B₀ : Y →L[𝕜] Z) (n : ℕ) :
    hilbertNumber (B₀.comp (S.comp A₀)) n ≤ ‖B₀‖ * hilbertNumber S n * ‖A₀‖ := by
  have hRHS : 0 ≤ ‖B₀‖ * hilbertNumber S n * ‖A₀‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (hilbertNumber_nonneg S n)) (norm_nonneg _)
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ hRHS
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  -- Re-bracket `B ∘ (B₀ ∘ S ∘ A₀) ∘ A = (B ∘ B₀) ∘ S ∘ (A₀ ∘ A)`.
  have hcomp : B.comp ((B₀.comp (S.comp A₀)).comp A)
      = (B.comp B₀).comp (S.comp (A₀.comp A)) := by
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hcomp]
  set B' := B.comp B₀ with hB'def
  set A' := A₀.comp A with hA'def
  have hb' : ‖B'‖ ≤ ‖B‖ * ‖B₀‖ := opNorm_comp_le B B₀
  have ha' : ‖A'‖ ≤ ‖A₀‖ * ‖A‖ := opNorm_comp_le A₀ A
  rw [div_le_iff₀ hpos]
  -- If either new factor is zero the composite vanishes, so `aₙ = 0`.
  by_cases hA'0 : A' = 0
  · have hz : B'.comp (S.comp A') = 0 := by rw [hA'0]; simp
    rw [hz, approximationNumber_eq_zero_of_rank_le (by simp)]
    exact mul_nonneg hRHS (by positivity)
  by_cases hB'0 : B' = 0
  · have hz : B'.comp (S.comp A') = 0 := by rw [hB'0]; simp
    rw [hz, approximationNumber_eq_zero_of_rank_le (by simp)]
    exact mul_nonneg hRHS (by positivity)
  -- Both nonzero: bound `a_n (B' S A')` by `h_n S · ‖B'‖ ‖A'‖`.
  have hkey : approximationNumber (B'.comp (S.comp A')) n ≤ hilbertNumber S n * (‖B'‖ * ‖A'‖) := by
    rw [← div_le_iff₀ (mul_pos (norm_pos_iff.mpr hB'0) (norm_pos_iff.mpr hA'0))]
    exact ratio_le_hilbertNumber S n hA'0 hB'0
  calc approximationNumber (B'.comp (S.comp A')) n
      ≤ hilbertNumber S n * (‖B'‖ * ‖A'‖) := hkey
    _ ≤ hilbertNumber S n * ((‖B‖ * ‖B₀‖) * (‖A₀‖ * ‖A‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hb' ha' (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (hilbertNumber_nonneg S n)
    _ = (‖B₀‖ * hilbertNumber S n * ‖A₀‖) * (‖B‖ * ‖A‖) := by ring

/-! ### (S4) Vanishing on low rank

Now that `ℓ₂ = L2 𝕜` lives in the same universe as `X` and `Y`, the rank
comparison is the universe-monomorphic `ContinuousLinearMap.rank_comp_comp_le`
and the proof is immediate. -/

/-- (S4) `rank S ≤ n ⇒ h_n S = 0`, since `rank (B∘S∘A) ≤ rank S ≤ n`. -/
lemma hilbertNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) : hilbertNumber S n = 0 := by
  have hkey : ∀ (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜),
      approximationNumber (B.comp (S.comp A)) n = 0 := fun A B =>
    approximationNumber_eq_zero_of_rank_le
      ((ContinuousLinearMap.rank_comp_comp_le A S B).trans hS)
  rw [hilbertNumber_def]
  refine le_antisymm (Real.sSup_le ?_ le_rfl) (hilbertNumber_nonneg S n)
  rintro r ⟨A, B, _, _, rfl⟩
  rw [hkey A B, zero_div]

/-! ### (S1a, hard half) and (S5) — the two non-trivial halves -/

/-- (S1a, hard half) `‖S‖ ≤ h₀ S`.

For each `x` with `S x ≠ 0`, take a Hahn–Banach norming functional
`φ` for `S x` (`‖φ‖ = 1`, `φ (S x) = ‖S x‖`) and form the rank-one pair

* `A := ⟨e₀, ·⟩ • x : ℓ₂ →L X` (so `A e₀ = x`, `‖A‖ = ‖x‖`),
* `B := φ(·) • e₀ : Y →L ℓ₂` (so `‖B‖ = 1`),

with `e₀` the first standard basis vector of `ℓ₂`. Evaluating `B ∘ S ∘ A`
at `e₀` gives `‖B ∘ S ∘ A‖ ≥ ‖S x‖`, so the admissible ratio
`‖B ∘ S ∘ A‖ / (‖B‖‖A‖) = ‖B ∘ S ∘ A‖ / ‖x‖ ≥ ‖S x‖ / ‖x‖` is `≤ h₀ S`.
Hence `‖S x‖ ≤ h₀ S · ‖x‖` for all `x`, i.e. `‖S‖ ≤ h₀ S`. -/
lemma norm_le_hilbertNumber_zero (S : X →L[𝕜] Y) : ‖S‖ ≤ hilbertNumber S 0 := by
  refine S.opNorm_le_bound (hilbertNumber_nonneg S 0) fun x => ?_
  -- Goal: `‖S x‖ ≤ h₀ S * ‖x‖`. Trivial when `S x = 0`.
  by_cases hSx : S x = 0
  · rw [hSx, norm_zero]
    exact mul_nonneg (hilbertNumber_nonneg S 0) (norm_nonneg x)
  have hx : x ≠ 0 := fun h => hSx (by rw [h, map_zero])
  -- First standard basis vector of `ℓ₂`, a unit vector.
  set e₀ : L2 𝕜 := lp.single 2 (0 : ℕ) (1 : 𝕜) with he₀
  have he₀norm : ‖e₀‖ = 1 := by
    rw [he₀, lp.norm_single (show (0 : ENNReal) < 2 by norm_num), norm_one]
  -- Hahn–Banach norming functional for `S x`.
  obtain ⟨φ, hφnorm, hφval⟩ :=
    exists_dual_vector (𝕜 := 𝕜) (S x) (norm_ne_zero_iff.mpr hSx)
  -- The rank-one pair.
  set A : L2 𝕜 →L[𝕜] X := (innerSL 𝕜 e₀).smulRight x with hA
  set B : Y →L[𝕜] L2 𝕜 := φ.smulRight e₀ with hB
  have hAnorm : ‖A‖ = ‖x‖ := by
    rw [hA, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, he₀norm, one_mul]
  have hBnorm : ‖B‖ = 1 := by
    rw [hB, ContinuousLinearMap.norm_smulRight_apply, hφnorm, he₀norm, mul_one]
  have hAne : A ≠ 0 := by rw [← norm_pos_iff, hAnorm]; exact norm_pos_iff.mpr hx
  have hBne : B ≠ 0 := by rw [← norm_pos_iff, hBnorm]; exact one_pos
  -- `A e₀ = x` (since `⟨e₀, e₀⟩ = ‖e₀‖² = 1`).
  have hAe₀ : A e₀ = x := by
    rw [hA, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      inner_self_eq_norm_sq_to_K, he₀norm]
    simp
  -- `(B ∘ S ∘ A) e₀ = ‖S x‖ • e₀`.
  have hBSA_e₀ : (B.comp (S.comp A)) e₀ = (‖S x‖ : 𝕜) • e₀ := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hAe₀, hB, ContinuousLinearMap.smulRight_apply, hφval]
  -- Hence `‖S x‖ ≤ ‖B ∘ S ∘ A‖`.
  have hge : ‖S x‖ ≤ ‖B.comp (S.comp A)‖ := by
    have h := (B.comp (S.comp A)).le_opNorm e₀
    rw [hBSA_e₀, norm_smul, he₀norm, mul_one, mul_one, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _)] at h
    exact h
  -- The admissible ratio is `≤ h₀ S`; rearrange.
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hratio := ratio_le_hilbertNumber S 0 hAne hBne
  rw [approximationNumber_zero_eq_norm, hBnorm, hAnorm, one_mul, div_le_iff₀ hxpos] at hratio
  exact le_trans hge hratio

/-- (S1a) `h_0 S = ‖S‖`: the upper half is the easy bound `h_0 S ≤ ‖S‖`, the lower
half is `norm_le_hilbertNumber_zero`. -/
lemma hilbertNumber_zero_eq_norm (S : X →L[𝕜] Y) : hilbertNumber S 0 = ‖S‖ :=
  le_antisymm
    (Real.sSup_le (by rintro r ⟨A, B, hA, hB, rfl⟩; exact ratio_le_norm S 0 hA hB)
      (norm_nonneg S))
    (norm_le_hilbertNumber_zero S)

/-- (S1a, easy half) `h_n S ≤ ‖S‖`, since `h_n S ≤ h_0 S = ‖S‖`. -/
lemma hilbertNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) : hilbertNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (hilbertNumber_antitone S) (Nat.zero_le n)).trans_eq
    (hilbertNumber_zero_eq_norm S)

/-- A contractive **section** of `ℓ₂ⁿ⁺¹` through `ℓ₂`: an isometric embedding
`B : ℓ₂ⁿ⁺¹ → ℓ₂` together with a contraction `A : ℓ₂ → ℓ₂ⁿ⁺¹` retracting it,
`A ∘ B = id`, with `‖A‖, ‖B‖ ≤ 1`.

Concretely `B` extends a vector by zeros (`v ↦ (v₀, …, vₙ, 0, 0, …)`) and `A`
restricts to the first `n+1` coordinates; both are norm-`≤ 1` and
`A ∘ B = id` coordinatewise. -/
lemma exists_l2_section (n : ℕ) :
    ∃ (B : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] L2 𝕜)
      (A : L2 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      A.comp B = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ∧
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 := by
  classical
  -- The first `n+1` standard basis vectors of `ℓ₂`, an orthonormal family.
  set s : Fin (n + 1) → L2 𝕜 := fun k => lp.single 2 (k : ℕ) (1 : 𝕜) with hsdef
  have hs : Orthonormal 𝕜 s := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [hsdef, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    by_cases h : i = j
    · rw [if_pos h, h, lp.single_apply_self]
    · rw [if_neg h]
      exact lp.single_apply_ne _ _ _ (fun he => h (Fin.ext he))
  -- The embedding `f v = Σ vₖ · eₖ`, as an inner-preserving linear map.
  set f : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] L2 𝕜 :=
    ∑ k : Fin (n + 1),
      (innerSL 𝕜 (EuclideanSpace.single k (1 : 𝕜))).toLinearMap.smulRight (s k) with hfdef
  have hf_apply : ∀ v, f v = ∑ k : Fin (n + 1), v k • s k := by
    intro v
    rw [hfdef]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply, EuclideanSpace.inner_single_left,
      map_one, one_mul]
  have hf : ∀ x y, (inner 𝕜 (f x) (f y) : 𝕜) = inner 𝕜 x y := by
    intro x y
    rw [hf_apply x, hf_apply y, sum_inner]
    simp_rw [inner_smul_left, hs.inner_right_sum y (Finset.mem_univ _)]
    rw [PiLp.inner_apply]
    simp_rw [RCLike.inner_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- Package as a linear isometry; its adjoint is the contraction `A`.
  set Bᵢ : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] L2 𝕜 := LinearMap.isometryOfInner f hf with hBᵢ
  refine ⟨Bᵢ.toContinuousLinearMap, (Bᵢ.toContinuousLinearMap).adjoint, ?_, ?_, ?_⟩
  · exact LinearIsometry.adjoint_comp_self Bᵢ
  · rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [LinearIsometry.coe_toContinuousLinearMap, Bᵢ.norm_map, one_mul]
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [LinearIsometry.coe_toContinuousLinearMap, Bᵢ.norm_map, one_mul]

/-- (S5, hard half) `1 ≤ h_n (id_{ℓ₂ⁿ⁺¹})`.

From a contractive section `A ∘ B = id_{ℓ₂ⁿ⁺¹}` (`exists_l2_section`) we get
`id = A ∘ (B ∘ A) ∘ B`, so the (S3) ideal property of the approximation
numbers and `aₙ(id_{ℓ₂ⁿ⁺¹}) = 1` (`approximationNumber_id_euclidean`) give
`1 ≤ aₙ(B ∘ A)`. The pair `(A, B)` is admissible for `hₙ(id)` with
`‖A‖, ‖B‖ ≤ 1`, so its ratio `aₙ(B ∘ A) / (‖B‖‖A‖) ≥ 1 ≤ hₙ(id)`. -/
lemma one_le_hilbertNumber_id (n : ℕ) :
    1 ≤ hilbertNumber (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
  obtain ⟨B, A, hAB, hA, hB⟩ := exists_l2_section (𝕜 := 𝕜) n
  have hidne : ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ≠ 0 := by
    intro h
    have h2 : (EuclideanSpace.single (0 : Fin (n + 1)) (1 : 𝕜)) = 0 := by
      have h3 := DFunLike.congr_fun h (EuclideanSpace.single (0 : Fin (n + 1)) (1 : 𝕜))
      simp only [ContinuousLinearMap.id_apply, zero_apply] at h3
      exact h3
    rw [PiLp.single_eq_zero_iff] at h2
    exact one_ne_zero h2
  have hBne : B ≠ 0 := by
    rintro rfl; rw [ContinuousLinearMap.comp_zero] at hAB; exact hidne hAB.symm
  have hAne : A ≠ 0 := by
    rintro rfl; rw [ContinuousLinearMap.zero_comp] at hAB; exact hidne hAB.symm
  -- `id = A ∘ (B ∘ A) ∘ B`.
  have hfact : A.comp ((B.comp A).comp B) =
      ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [ContinuousLinearMap.comp_assoc, hAB, ContinuousLinearMap.comp_id, hAB]
  -- `1 = aₙ(id) ≤ ‖A‖ · aₙ(B∘A) · ‖B‖`.
  have hid1 : (1 : ℝ) ≤ ‖A‖ * approximationNumber (B.comp A) n * ‖B‖ := by
    have h := approximationNumber_comp_comp_le B (B.comp A) A n
    rw [hfact, approximationNumber_id_euclidean] at h
    exact h
  have hsn := approximationNumber_nonneg (B.comp A) n
  -- hence `1 ≤ aₙ(B∘A)`.
  have e1 : ‖A‖ * approximationNumber (B.comp A) n ≤ approximationNumber (B.comp A) n := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) hsn]
  have hprod : ‖A‖ * approximationNumber (B.comp A) n * ‖B‖
      ≤ approximationNumber (B.comp A) n := by
    nlinarith [e1, mul_nonneg (mul_nonneg (norm_nonneg A) hsn) (sub_nonneg.mpr hB)]
  have haBA : (1 : ℝ) ≤ approximationNumber (B.comp A) n := le_trans hid1 hprod
  -- The ratio of the admissible pair `(A, B)` is `≥ 1`.
  have hratio := ratio_le_hilbertNumber
    (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n hAne hBne
  rw [ContinuousLinearMap.id_comp] at hratio
  refine le_trans ?_ hratio
  rw [le_div_iff₀ (mul_pos (norm_pos_iff.mpr hBne) (norm_pos_iff.mpr hAne)), one_mul]
  calc ‖B‖ * ‖A‖
      ≤ 1 * 1 := mul_le_mul hB hA (norm_nonneg A) zero_le_one
    _ = 1 := one_mul 1
    _ ≤ approximationNumber (B.comp A) n := haBA

/-! ### The Hilbert numbers form an s-number sequence -/

/-- The Hilbert numbers form an s-number sequence. The axioms (S1)–(S4) are
the lemmas above; (S1a≥) and (S5) are `norm_le_hilbertNumber_zero` and
`one_le_hilbertNumber_id`. -/
theorem isSNumberSequence_hilbertNumber :
    IsSNumberSequence (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => hilbertNumber S n) where
  nonneg := fun S n => hilbertNumber_nonneg S n
  norm_at_zero := fun S => hilbertNumber_zero_eq_norm S
  antitone := fun S n => hilbertNumber_antitone S n
  subadditive := fun S T n => hilbertNumber_add_le S T n
  ideal := fun A S B n => hilbertNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => hilbertNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n =>
    le_antisymm ((hilbertNumber_le_norm _ n).trans norm_id_le) (one_le_hilbertNumber_id n)

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
