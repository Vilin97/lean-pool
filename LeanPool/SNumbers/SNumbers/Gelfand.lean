/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.SNumbers.SNumbers.Helpers
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Gelfand numbers `c_n`

The Gelfand numbers `c_n S` of a continuous linear map `S : X →L[𝕜] Y`
between normed `𝕜`-vector spaces measure the smallest possible operator
norm of `S` after restricting it to a closed subspace of `X` of
codimension at most `n`:

  `c_n S = inf_{M ⊆ X closed, codim M ≤ n} ‖S|_M‖`,

where `S|_M = S.comp M.subtypeL` is the restriction of `S` to the closed
subspace `M`.

## Structure

The development closely mirrors `SNumbers.Kolmogorov`: where Kolmogorov
numbers descend `S` to a quotient `Y ⧸ V` and minimise over small `V`,
Gelfand numbers restrict `S` to a subspace `M ⊆ X` and minimise over
*large* (small-codimension) `M`. The two are dual under the
domain ↔ codomain swap, and the proofs follow the same skeleton.

Unlike Kolmogorov's (S5'), Gelfand's strict normalisation does **not**
require Riesz's lemma: the inclusion `M.subtypeL` is an isometry, so
`‖id_X.comp M.subtypeL‖ = ‖M.subtypeL‖ = 1` whenever `M ≠ ⊥`. In
particular, the strict-normalisation proof needs no `[CompleteSpace 𝕜]`
hypothesis.
-/

@[expose] public section

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-! ### Definitions -/

/-- The norm of `S` restricted to a (closed) subspace `M` of `X`. -/
noncomputable def deviationFromRestriction (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) : ℝ :=
  ‖S.comp M.subtypeL‖

/-- The set of admissible deviations at stage `n`: the numbers `‖S|_M‖` for
closed subspaces `M ⊆ X` of codimension at most `n`. The `n`-th Gelfand
number is its infimum. -/
def gelfandSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ M : Submodule 𝕜 X,
      IsClosed (M : Set X) ∧
      Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) ∧
      r = deviationFromRestriction S M}

/-- The `n`-th **Gelfand number** of a continuous linear map.

`c_n S = inf_{M ⊆ X closed, codim M ≤ n} ‖S|_M‖`. -/
noncomputable def gelfandNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (gelfandSet S n)

lemma gelfandNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n = sInf (gelfandSet S n) := rfl

/-! ### Basic facts about `deviationFromRestriction` -/

lemma deviationFromRestriction_nonneg (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    0 ≤ deviationFromRestriction S M :=
  norm_nonneg (S.comp M.subtypeL)

lemma deviationFromRestriction_le_norm (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    deviationFromRestriction S M ≤ ‖S‖ := by
  unfold deviationFromRestriction
  calc ‖S.comp M.subtypeL‖
      ≤ ‖S‖ * ‖M.subtypeL‖ := opNorm_comp_le _ _
    _ ≤ ‖S‖ * 1 :=
        mul_le_mul_of_nonneg_left M.norm_subtypeL_le (norm_nonneg _)
    _ = ‖S‖ := mul_one _

/-! ### Basic facts about `gelfandSet` -/

/-- The set of admissible deviations is non-empty: the whole space `⊤` is
closed of codimension `0 ≤ n`, so it is admissible at every stage. -/
lemma gelfandSet_nonempty (S : X →L[𝕜] Y) (n : ℕ) :
    (gelfandSet S n).Nonempty := by
  refine ⟨_, ⊤, ?_, ?_, rfl⟩
  · -- `(⊤ : Submodule 𝕜 X) : Set X` is `Set.univ`, which is closed.
    rw [Submodule.top_coe]; exact isClosed_univ
  · -- `rank (X ⧸ ⊤) = 0` since `X ⧸ ⊤` is subsingleton.
    have h0 : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) = 0 :=
      rank_zero_iff.mpr inferInstance
    rw [h0]; exact bot_le

/-- The set of admissible deviations is bounded below by `0`. -/
lemma bddBelow_gelfandSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (gelfandSet S n) :=
  ⟨0, by rintro _ ⟨M, _, _, rfl⟩; exact deviationFromRestriction_nonneg S M⟩

lemma gelfandNumber_le_deviation {S : X →L[𝕜] Y} {n : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X))
    (hM_rank : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) :
    gelfandNumber S n ≤ deviationFromRestriction S M :=
  csInf_le (bddBelow_gelfandSet S n) ⟨M, hM_closed, hM_rank, rfl⟩

/-- Lower bound for the Gelfand number: if `f` is a lower bound for the restriction
deviation over every admissible (closed, codimension `≤ n`) subspace, then `f ≤ c_n(S)`. -/
lemma le_gelfandNumber {S : X →L[𝕜] Y} {n : ℕ} {f : ℝ}
    (h : ∀ M : Submodule 𝕜 X, IsClosed (M : Set X) →
        Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) → f ≤ deviationFromRestriction S M) :
    f ≤ gelfandNumber S n :=
  le_csInf (gelfandSet_nonempty S n) <| by
    rintro _ ⟨M, hM_closed, hM_rank, rfl⟩; exact h M hM_closed hM_rank

/-! ## (S1c) Non-negativity -/

lemma gelfandNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ gelfandNumber S n :=
  Real.sInf_nonneg <| by
    rintro _ ⟨M, _, _, rfl⟩; exact deviationFromRestriction_nonneg S M

/-! ## (S1b) Antitone in `n` -/

/-- Raising `n` allows subspaces of larger codimension, hence more deviations
become admissible. -/
lemma gelfandSet_subset (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    gelfandSet S n ⊆ gelfandSet S m := by
  rintro _ ⟨M, hM_closed, hM_rank, rfl⟩
  exact ⟨M, hM_closed, hM_rank.trans (by exact_mod_cast h), rfl⟩

/-- If `n ≤ m`, then `c_m S ≤ c_n S`. -/
lemma gelfandNumber_antitone' (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    gelfandNumber S m ≤ gelfandNumber S n :=
  csInf_le_csInf (bddBelow_gelfandSet S m) (gelfandSet_nonempty S n)
    (gelfandSet_subset S h)

lemma gelfandNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S (n + 1) ≤ gelfandNumber S n :=
  gelfandNumber_antitone' S (Nat.le_succ n)

/-! ## (S1a) Value at `n = 0`: `gelfandNumber S 0 = ‖S‖`

For `M = ⊤` the restriction `S.comp ⊤.subtypeL` has the same operator
norm as `S` (the inclusion `⊤.subtypeL : ⊤ →L X` is an isometry from
the subtype). The matching lower bound holds because every admissible
`M` at `n = 0` must satisfy `rank (X ⧸ M) = 0`, hence `M = ⊤`. -/

private lemma deviationFromRestriction_top (S : X →L[𝕜] Y) :
    deviationFromRestriction S (⊤ : Submodule 𝕜 X) = ‖S‖ := by
  unfold deviationFromRestriction
  refine le_antisymm ?_ ?_
  · -- `‖S.comp ⊤.subtypeL‖ ≤ ‖S‖ * ‖⊤.subtypeL‖ ≤ ‖S‖`.
    calc ‖S.comp (⊤ : Submodule 𝕜 X).subtypeL‖
        ≤ ‖S‖ * ‖(⊤ : Submodule 𝕜 X).subtypeL‖ := opNorm_comp_le _ _
      _ ≤ ‖S‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (⊤ : Submodule 𝕜 X).norm_subtypeL_le (norm_nonneg _)
      _ = ‖S‖ := mul_one _
  · -- For every `x : X`, `‖S x‖ ≤ ‖S.comp ⊤.subtypeL‖ * ‖x‖`.
    refine opNorm_le_bound _
      (norm_nonneg (S.comp (⊤ : Submodule 𝕜 X).subtypeL)) fun x => ?_
    have h_eq :
        S x = (S.comp (⊤ : Submodule 𝕜 X).subtypeL) ⟨x, Submodule.mem_top⟩ := rfl
    rw [h_eq]
    exact (S.comp (⊤ : Submodule 𝕜 X).subtypeL).le_opNorm
      ⟨x, Submodule.mem_top⟩

lemma gelfandNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    gelfandNumber S 0 = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · -- Take `M = ⊤`.
    have h_rank : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) ≤ ((0 : ℕ) : Cardinal) := by
      have h0 : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) = 0 :=
        rank_zero_iff.mpr inferInstance
      rw [h0]; exact_mod_cast Nat.zero_le 0
    have h_closed : IsClosed ((⊤ : Submodule 𝕜 X) : Set X) := by
      rw [Submodule.top_coe]; exact isClosed_univ
    exact (gelfandNumber_le_deviation h_closed h_rank).trans_eq
      (deviationFromRestriction_top S)
  · refine le_csInf (gelfandSet_nonempty S 0) ?_
    rintro _ ⟨M, _, hM_rank, rfl⟩
    -- `rank (X ⧸ M) ≤ 0` ⇒ `X ⧸ M` subsingleton ⇒ `M = ⊤`.
    have h_rank_zero : Module.rank 𝕜 (X ⧸ M) = 0 :=
      le_antisymm (by exact_mod_cast hM_rank) zero_le
    have h_subsingleton : Subsingleton (X ⧸ M) := rank_zero_iff.mp h_rank_zero
    have hM_top : M = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp h_subsingleton
    rw [hM_top, deviationFromRestriction_top]

/-- Upper bound by the operator norm: `c_n S ≤ ‖S‖`, since `c_n S ≤ c_0 S = ‖S‖`. -/
lemma gelfandNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (gelfandNumber_antitone S) (Nat.zero_le n)).trans_eq
    (gelfandNumber_zero_eq_norm S)

/-! ## (S2) Subadditivity -/

lemma gelfandNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber (S + T) n ≤ gelfandNumber S n + ‖T‖ := by
  rw [← sub_le_iff_le_add]
  refine le_csInf (gelfandSet_nonempty S n) ?_
  rintro _ ⟨M, hM_closed, hM_rank, rfl⟩
  -- `(S+T).comp ι_M = S.comp ι_M + T.comp ι_M`. Triangle:
  -- `‖(S+T).comp ι_M‖ ≤ ‖S.comp ι_M‖ + ‖T.comp ι_M‖ ≤ deviation S M + ‖T‖`.
  have h_dist : gelfandNumber (S + T) n
      ≤ deviationFromRestriction S M + deviationFromRestriction T M := by
    refine (gelfandNumber_le_deviation hM_closed hM_rank).trans ?_
    unfold deviationFromRestriction
    have h_eq : (S + T).comp M.subtypeL = S.comp M.subtypeL + T.comp M.subtypeL :=
      ContinuousLinearMap.add_comp _ _ _
    rw [h_eq]
    exact norm_add_le (S.comp M.subtypeL) (T.comp M.subtypeL)
  have h_T : deviationFromRestriction T M ≤ ‖T‖ := deviationFromRestriction_le_norm T M
  linarith

/-! ## (S3) Ideal property

For `M ⊆ X` closed of codim ≤ n and `A : W →L[𝕜] X`, set
`M' := M.comap A`. Then `M'` is closed (preimage of a closed set under a
continuous map) and has codim ≤ n: the map `mkQ ∘ A : W →ₗ X/M`
has kernel exactly `M'`, so `W/M' ↪ X/M` and rank is preserved or
shrinks. The norm bound on the restriction is then a pointwise estimate
in the spirit of Pietsch, *Eigenvalues and s-numbers*, §2.4: for
`w ∈ M'` we have `A w ∈ M`, so
`‖S(A w)‖ ≤ ‖S|_M‖ · ‖A w‖ ≤ ‖S|_M‖ · ‖A‖ · ‖w‖`, and one more `‖B‖` on
the left finishes it. -/

private lemma rank_quotient_comap_le (A : W →L[𝕜] X) (M : Submodule 𝕜 X) :
    Module.rank 𝕜 (W ⧸ M.comap (A : W →ₗ[𝕜] X)) ≤ Module.rank 𝕜 (X ⧸ M) := by
  -- The map `f : W →ₗ X/M`, `f w = mkQ (A w)`, has kernel `M.comap A`.
  -- Hence `W ⧸ ker f ≃ range f ≤ X/M`, giving the rank bound.
  set g : W →ₗ[𝕜] (X ⧸ M) := M.mkQ.comp (A : W →ₗ[𝕜] X) with hg_def
  have h_ker : LinearMap.ker g = M.comap (A : W →ₗ[𝕜] X) := by
    rw [hg_def, LinearMap.ker_comp, Submodule.ker_mkQ]
  -- Quotient by kernel is isomorphic to the range, hence has rank ≤ rank (X/M).
  calc Module.rank 𝕜 (W ⧸ M.comap (A : W →ₗ[𝕜] X))
      = Module.rank 𝕜 (W ⧸ LinearMap.ker g) := by rw [h_ker]
    _ = Module.rank 𝕜 (LinearMap.range g) :=
        (LinearMap.quotKerEquivRange g).rank_eq
    _ ≤ Module.rank 𝕜 (X ⧸ M) :=
        (LinearMap.range g).rank_le

/-- Per-subspace (S3) bound:
`deviation(B ∘ S ∘ A, M.comap A) ≤ ‖B‖ * ‖A‖ * deviation(S, M)`. -/
lemma deviationFromRestriction_comp_comp_comap_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (M : Submodule 𝕜 X) :
    deviationFromRestriction (B.comp (S.comp A))
        (M.comap (A : W →ₗ[𝕜] X))
      ≤ ‖B‖ * ‖A‖ * deviationFromRestriction S M := by
  unfold deviationFromRestriction
  -- Pointwise on `M' := M.comap A`. For `w ∈ M'` we have `A w ∈ M`, so we can
  -- evaluate `S ∘ ι_M` at `⟨A w, w.2⟩` and chain `le_opNorm` for `B`, for
  -- `S ∘ ι_M`, and for `A`.
  have h_bound_nn : 0 ≤ ‖B‖ * ‖A‖ * ‖S.comp M.subtypeL‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg A))
      (norm_nonneg (S.comp M.subtypeL))
  refine opNorm_le_bound _ h_bound_nn fun w => ?_
  set y : M := ⟨A (w : W), w.2⟩
  change ‖B (S (A (w : W)))‖ ≤ ‖B‖ * ‖A‖ * ‖S.comp M.subtypeL‖ * ‖w‖
  have h_y : S (A (w : W)) = (S.comp M.subtypeL) y := rfl
  rw [h_y]
  calc ‖B ((S.comp M.subtypeL) y)‖
      ≤ ‖B‖ * ‖(S.comp M.subtypeL) y‖ := B.le_opNorm _
    _ ≤ ‖B‖ * (‖S.comp M.subtypeL‖ * ‖A (w : W)‖) := by
        gcongr; exact (S.comp M.subtypeL).le_opNorm y
    _ ≤ ‖B‖ * (‖S.comp M.subtypeL‖ * (‖A‖ * ‖w‖)) := by
        gcongr; exact A.le_opNorm (w : W)
    _ = ‖B‖ * ‖A‖ * ‖S.comp M.subtypeL‖ * ‖w‖ := by ring

lemma gelfandNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    gelfandNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * gelfandNumber S n * ‖A‖ := by
  -- Same scalar-pull-out trick as for the Kolmogorov / approximation
  -- numbers: every admissible `M ⊆ X` produces an admissible
  -- `M.comap A ⊆ W` for `B ∘ S ∘ A`, with the per-subspace bound
  -- `‖B‖ * ‖A‖ * deviation(S, M)`.
  have hkey : ∀ M : Submodule 𝕜 X, IsClosed (M : Set X) →
      Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) →
      gelfandNumber (B.comp (S.comp A)) n ≤
        ‖B‖ * ‖A‖ * deviationFromRestriction S M := by
    intro M hM_closed hM_rank
    -- `M.comap A` is closed (preimage of closed under continuous A).
    have hM'_closed : IsClosed ((M.comap (A : W →ₗ[𝕜] X)) : Set W) := by
      have : ((M.comap (A : W →ₗ[𝕜] X)) : Set W) = A ⁻¹' (M : Set X) := rfl
      rw [this]; exact hM_closed.preimage A.continuous
    have hM'_rank :
        Module.rank 𝕜 (W ⧸ M.comap (A : W →ₗ[𝕜] X)) ≤ (n : Cardinal) :=
      (rank_quotient_comap_le A M).trans hM_rank
    exact (gelfandNumber_le_deviation hM'_closed hM'_rank).trans
      (deviationFromRestriction_comp_comp_comap_le A S B M)
  have h_inf : gelfandNumber (B.comp (S.comp A)) n
                ≤ ‖B‖ * ‖A‖ * gelfandNumber S n := by
    change _ ≤ (‖B‖ * ‖A‖) • sInf
      {r | ∃ M : Submodule 𝕜 X,
            IsClosed (M : Set X) ∧
            Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) ∧
            r = deviationFromRestriction S M}
    rw [← Real.sInf_smul_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    refine le_csInf ((gelfandSet_nonempty S n).image _) ?_
    rintro _ ⟨_, ⟨M, hM_closed, hM_rank, rfl⟩, rfl⟩
    exact hkey M hM_closed hM_rank
  exact h_inf.trans_eq (by ring)

/-! ## (S4) Vanishing on operators of rank at most `n` -/

lemma gelfandNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    gelfandNumber S n = 0 := by
  refine le_antisymm ?_ (gelfandNumber_nonneg S n)
  -- Take `M = ker S`. Then `S.comp M.subtypeL = 0`, so `deviation = 0`.
  set M : Submodule 𝕜 X := LinearMap.ker (S : X →ₗ[𝕜] Y) with hM_def
  -- (a) `M` is closed, since `S` is continuous and `{0}` is closed.
  have hM_closed : IsClosed (M : Set X) := by
    have h_eq : (M : Set X) = S ⁻¹' ({0} : Set Y) := by
      ext x
      simp [hM_def, LinearMap.mem_ker]
    rw [h_eq]
    exact isClosed_singleton.preimage S.continuous
  -- (b) `codim M = rank S ≤ n` via the first iso `X ⧸ ker S ≃ range S`.
  have hM_rank : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) := by
    calc Module.rank 𝕜 (X ⧸ M)
        = Module.rank 𝕜 (LinearMap.range (S : X →ₗ[𝕜] Y)) :=
          (LinearMap.quotKerEquivRange (S : X →ₗ[𝕜] Y)).rank_eq
      _ ≤ (n : Cardinal) := hS
  refine (gelfandNumber_le_deviation hM_closed hM_rank).trans ?_
  -- (c) `S.comp M.subtypeL = 0`: every `x ∈ M = ker S` has `S x = 0`.
  have h_comp_zero : S.comp M.subtypeL = 0 := by
    ext x
    simp only [coe_comp, Function.comp_apply, zero_apply,
      Submodule.subtypeL_apply]
    exact x.2
  change ‖S.comp M.subtypeL‖ ≤ 0
  rw [h_comp_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero

/-! ## (S5') Strict normalisation `gelfandNumber (id_X) n = 1` whenever `dim X > n`

For Gelfand numbers this is much simpler than for Kolmogorov: the
inclusion `M.subtypeL : M →L X` is an *isometry*, so

  `‖id_X.comp M.subtypeL‖ = ‖M.subtypeL‖ = 1`

whenever `M ≠ ⊥`. The constraint `codim M ≤ n < dim X` forces
`dim M ≥ 1`, hence `M ≠ ⊥`. No Riesz, no `[CompleteSpace 𝕜]`. -/

/-- (S5') Strict normalisation: `gelfandNumber (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma gelfandNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    gelfandNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have h_finrank_pos : 0 < Module.finrank 𝕜 X :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have : FiniteDimensional 𝕜 X := .of_finrank_pos h_finrank_pos
  have : Nontrivial X := Module.nontrivial_of_finrank_pos h_finrank_pos
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: take `M = ⊤`. `deviation(I, ⊤) = ‖I‖ = 1`.
    have h_rank_top : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) ≤ (n : Cardinal) := by
      have h0 : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) = 0 :=
        rank_zero_iff.mpr inferInstance
      rw [h0]; exact zero_le
    have h_closed : IsClosed ((⊤ : Submodule 𝕜 X) : Set X) := by
      rw [Submodule.top_coe]; exact isClosed_univ
    calc gelfandNumber I n
        ≤ deviationFromRestriction I ⊤ := gelfandNumber_le_deviation h_closed h_rank_top
      _ = ‖I‖ := deviationFromRestriction_top _
      _ = 1 := norm_id
  · -- `≥ 1`: every admissible `M` is non-trivial, so
    -- `‖I.comp M.subtypeL‖ = ‖M.subtypeL‖ = 1`.
    refine le_csInf (gelfandSet_nonempty I n) ?_
    rintro _ ⟨M, _, hM_rank, rfl⟩
    -- Show `Nontrivial M` from `codim M ≤ n < finrank X`.
    have hM_finrank_quot_le : Module.finrank 𝕜 (X ⧸ M) ≤ n :=
      Module.finrank_le_of_rank_le hM_rank
    have h_sum :
        Module.finrank 𝕜 (X ⧸ M) + Module.finrank 𝕜 M = Module.finrank 𝕜 X :=
      Submodule.finrank_quotient_add_finrank M
    have hM_finrank_pos : 0 < Module.finrank 𝕜 M := by omega
    have : Nontrivial M := Module.nontrivial_of_finrank_pos hM_finrank_pos
    -- `I.comp M.subtypeL = M.subtypeL`, and its norm is 1.
    have h_dev_eq : deviationFromRestriction I M = ‖M.subtypeL‖ := by
      change ‖I.comp M.subtypeL‖ = ‖M.subtypeL‖
      rw [hI_def, ContinuousLinearMap.id_comp]
    rw [h_dev_eq, M.norm_subtypeL]

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma gelfandNumber_id_euclidean (n : ℕ) :
    gelfandNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin' (n + 1)]; exact Nat.lt_succ_self n
  exact gelfandNumber_strict n h

/-! ## Summary: Gelfand numbers form a strict s-number sequence -/

theorem isSNumberSequence_gelfandNumber :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) where
  nonneg := fun S n => gelfandNumber_nonneg S n
  norm_at_zero := fun S => gelfandNumber_zero_eq_norm S
  antitone := fun S n => gelfandNumber_antitone S n
  subadditive := fun S T n => gelfandNumber_add_le S T n
  ideal := fun A S B n => gelfandNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => gelfandNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => gelfandNumber_id_euclidean n

theorem isStrictSNumberSequence_gelfandNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) where
  toIsSNumberSequence := isSNumberSequence_gelfandNumber
  strictly_normalised_at_id := fun n h => gelfandNumber_strict n h

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
