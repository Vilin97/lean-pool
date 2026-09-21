/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Helpers
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Kolmogorov numbers `d_n`

The Kolmogorov numbers `d_n S` of a continuous linear map `S : X →L[𝕜] Y`
between normed `𝕜`-vector spaces measure the worst-case error of
approximating the image `S(B_X)` by an `n`-dimensional subspace of `Y`.

The classical definition is

  `d_n S = inf_{V ⊆ Y, dim V ≤ n} sup_{x ∈ B_X} inf_{y ∈ V} ‖S x - y‖`,

which we recast in terms of operator norms on quotient spaces:

  `d_n S = inf_{V ⊆ Y, dim V ≤ n} ‖π_V ∘ S‖`,

where `π_V : Y →L[𝕜] (Y ⧸ V)` is the canonical quotient map. The inner
`inf_y ‖S x − y‖` is exactly the quotient norm `‖[S x]‖_{Y/V}`, and the
outer `sup_{‖x‖ ≤ 1}` is the operator norm of the composition.

The development requires `[NontriviallyNormedField 𝕜]` throughout, plus
`[CompleteSpace 𝕜]` for (S5') (Riesz needs finite-dim subspaces of a
complete-field normed space to be closed). It does **not** require
`[DenselyNormedField 𝕜]` (the quotient form `‖[y]‖_{Y/⊥} = ‖y‖` for
`V = ⊥` avoids the density-of-norm scaling) and **not**
`[CompleteSpace X]`, so the Kolmogorov numbers here are defined for every
normed space `X`.

## Alternative: Pietsch's lifting identity

The companion file `SNumbers.KolmogorovLifting` gives an alternative
development via Pietsch's identity `d_n S = a_n(S ∘ Q_X)`, where
`Q_X : ℓ¹(B_X) →L[𝕜] X` is the canonical summation surjection. That
development is shorter (many axioms become one-liners over `a_n`) but
requires `[CompleteSpace X]` because `Q_X` is an infinite series in `X`,
and is therefore restricted to **Banach spaces**. The two definitions
agree on Banach spaces.

-/

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

/-- Quotient form of the deviation: `‖π_V ∘ S‖`, where `π_V` is the
quotient projection `Y →L[𝕜] Y ⧸ V`. -/
noncomputable def deviationFromSubspace (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) : ℝ :=
  ‖V.mkQL.comp S‖

/-- The set of admissible deviations at stage `n`: the numbers
`‖π_V ∘ S‖` for subspaces `V ⊆ Y` of dimension at most `n`. The `n`-th
Kolmogorov number is its infimum. -/
def kolmogorovSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ V : Submodule 𝕜 Y,
      Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace S V}

/-- Quotient form of the `n`-th Kolmogorov number. -/
noncomputable def kolmogorovNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (kolmogorovSet S n)

lemma kolmogorovNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n = sInf (kolmogorovSet S n) := rfl

/-! ### Basic facts about `deviationFromSubspace` -/

lemma deviationFromSubspace_nonneg (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    0 ≤ deviationFromSubspace S V :=
  norm_nonneg (V.mkQL.comp S)

lemma deviationFromSubspace_le_norm (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace S V ≤ ‖S‖ := by
  unfold deviationFromSubspace
  calc ‖V.mkQL.comp S‖
      ≤ ‖V.mkQL‖ * ‖S‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right V.norm_mkQL_le (norm_nonneg _)
    _ = ‖S‖ := one_mul _

/-! ### Basic facts about `kolmogorovSet` -/

/-- The set of admissible deviations is non-empty: the zero subspace `⊥` has
dimension `0 ≤ n`, so it is admissible at every stage. -/
lemma kolmogorovSet_nonempty (S : X →L[𝕜] Y) (n : ℕ) :
    (kolmogorovSet S n).Nonempty :=
  ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩

/-- The set of admissible deviations is bounded below by `0`. -/
lemma bddBelow_kolmogorovSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (kolmogorovSet S n) :=
  ⟨0, by rintro _ ⟨V, _, rfl⟩; exact deviationFromSubspace_nonneg S V⟩

lemma kolmogorovNumber_le_deviation {S : X →L[𝕜] Y} {n : ℕ} {V : Submodule 𝕜 Y}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    kolmogorovNumber S n ≤ deviationFromSubspace S V :=
  csInf_le (bddBelow_kolmogorovSet S n) ⟨V, hV, rfl⟩

/-- Lower bound for the Kolmogorov number: if `f` is a lower bound for the
quotient deviation over every admissible (dimension `≤ n`) subspace, then
`f ≤ d_n(S)`. Dual to `le_gelfandNumber`. -/
lemma le_kolmogorovNumber {S : X →L[𝕜] Y} {n : ℕ} {f : ℝ}
    (h : ∀ V : Submodule 𝕜 Y, Module.rank 𝕜 V ≤ (n : Cardinal) →
        f ≤ deviationFromSubspace S V) :
    f ≤ kolmogorovNumber S n :=
  le_csInf (kolmogorovSet_nonempty S n) <| by
    rintro _ ⟨V, hV, rfl⟩; exact h V hV

/-! ## (S1c) Non-negativity -/

lemma kolmogorovNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ kolmogorovNumber S n :=
  Real.sInf_nonneg <| by
    rintro _ ⟨V, _, rfl⟩; exact deviationFromSubspace_nonneg S V

/-! ## (S1b) Antitone in `n` -/

/-- Raising `n` allows subspaces of larger dimension, hence more deviations
become admissible. -/
lemma kolmogorovSet_subset (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    kolmogorovSet S n ⊆ kolmogorovSet S m := by
  rintro _ ⟨V, hV, rfl⟩
  exact ⟨V, hV.trans (by exact_mod_cast h), rfl⟩

/-- If `n ≤ m`, then `d_m S ≤ d_n S`. -/
lemma kolmogorovNumber_antitone' (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    kolmogorovNumber S m ≤ kolmogorovNumber S n :=
  csInf_le_csInf (bddBelow_kolmogorovSet S m) (kolmogorovSet_nonempty S n)
    (kolmogorovSet_subset S h)

lemma kolmogorovNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S (n + 1) ≤ kolmogorovNumber S n :=
  kolmogorovNumber_antitone' S (Nat.le_succ n)

/-! ## (S1a) Value at `n = 0`: `kolmogorovNumber S 0 = ‖S‖`

The bound `‖V.mkQL ∘ S‖ ≤ ‖S‖` holds in general (since `‖V.mkQL‖ ≤ 1`),
but the matching lower bound `‖S‖ ≤ ‖(⊥).mkQL ∘ S‖` requires that
`Y ⧸ ⊥` is isometric to `Y` — i.e. `‖[y]‖ = ‖y‖` for the trivial
subspace. We get this from `Submodule.Quotient.norm_mk_lt`: a
representative `y'` of `[y]` with `‖y'‖ < ‖[y]‖ + ε` must satisfy
`y' - y ∈ ⊥`, i.e. `y' = y`. -/

/-- The quotient-norm bound `‖[y]‖ = ‖y‖` for the trivial submodule. -/
private lemma norm_mk_bot (y : Y) :
    ‖((⊥ : Submodule 𝕜 Y).mkQ y : Y ⧸ (⊥ : Submodule 𝕜 Y))‖ = ‖y‖ := by
  refine le_antisymm ?_ ?_
  · simpa using _root_.Submodule.Quotient.norm_mk_le (S := (⊥ : Submodule 𝕜 Y)) y
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y', hy'_eq, hy'_lt⟩ :=
      Submodule.Quotient.norm_mk_lt
        ((⊥ : Submodule 𝕜 Y).mkQ y : Y ⧸ (⊥ : Submodule 𝕜 Y)) hε
    -- `Submodule.Quotient.mk y' = mkQ y` and `mkQ y' = mkQ y`, so `y' - y ∈ ⊥ = {0}`.
    have h_eq : y' = y := by
      have hker : y' - y ∈ (⊥ : Submodule 𝕜 Y) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hy'_eq]
        change (⊥ : Submodule 𝕜 Y).mkQ y - (⊥ : Submodule 𝕜 Y).mkQ y = 0
        simp
      rwa [Submodule.mem_bot, sub_eq_zero] at hker
    have h_norm_eq : ‖y‖ = ‖y'‖ := by rw [h_eq]
    rw [h_norm_eq]
    exact hy'_lt.le

private lemma deviationFromSubspace_bot (S : X →L[𝕜] Y) :
    deviationFromSubspace S (⊥ : Submodule 𝕜 Y) = ‖S‖ := by
  unfold deviationFromSubspace
  refine le_antisymm ?_ ?_
  · -- `‖(⊥).mkQL ∘ S‖ ≤ ‖S‖`: pointwise `‖[S x]‖ = ‖S x‖ ≤ ‖S‖ * ‖x‖`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [coe_comp, Function.comp_apply, Submodule.mkQL_apply, norm_mk_bot]
    exact S.le_opNorm x
  · -- `‖S‖ ≤ ‖(⊥).mkQL ∘ S‖`: pointwise `‖S x‖ = ‖[S x]‖ ≤ ‖(⊥).mkQL ∘ S‖ * ‖x‖`.
    refine opNorm_le_bound _
      (norm_nonneg ((⊥ : Submodule 𝕜 Y).mkQL.comp S)) fun x => ?_
    rw [← norm_mk_bot (𝕜 := 𝕜) (S x)]
    change ‖((⊥ : Submodule 𝕜 Y).mkQL.comp S) x‖ ≤ _
    exact ((⊥ : Submodule 𝕜 Y).mkQL.comp S).le_opNorm x

lemma kolmogorovNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    kolmogorovNumber S 0 = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · have h_rank : Module.rank 𝕜 (⊥ : Submodule 𝕜 Y) ≤ ((0 : ℕ) : Cardinal) := by
      rw [rank_bot]; exact_mod_cast Nat.zero_le 0
    exact (kolmogorovNumber_le_deviation h_rank).trans_eq (deviationFromSubspace_bot S)
  · refine le_csInf (kolmogorovSet_nonempty S 0) ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_bot : V = ⊥ := by
      rw [← Submodule.rank_eq_zero]
      exact le_antisymm (by exact_mod_cast hV) zero_le
    rw [hV_bot, deviationFromSubspace_bot]

/-- Upper bound by the operator norm: `d_n S ≤ ‖S‖`, since `d_n S ≤ d_0 S = ‖S‖`. -/
lemma kolmogorovNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (kolmogorovNumber_antitone S) (Nat.zero_le n)).trans_eq
    (kolmogorovNumber_zero_eq_norm S)


/-! ## (S2) Subadditivity -/

lemma kolmogorovNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber (S + T) n ≤ kolmogorovNumber S n + ‖T‖ := by
  rw [← sub_le_iff_le_add]
  refine le_csInf (kolmogorovSet_nonempty S n) ?_
  rintro _ ⟨V, hV, rfl⟩
  -- `V.mkQL.comp (S+T) = V.mkQL.comp S + V.mkQL.comp T`. Triangle:
  -- `‖V.mkQL.comp (S+T)‖ ≤ ‖V.mkQL.comp S‖ + ‖V.mkQL.comp T‖ ≤ deviation S V + ‖T‖`.
  have h_dist : kolmogorovNumber (S + T) n
      ≤ deviationFromSubspace S V + deviationFromSubspace T V := by
    refine (kolmogorovNumber_le_deviation hV).trans ?_
    unfold deviationFromSubspace
    have h_eq : V.mkQL.comp (S + T) = V.mkQL.comp S + V.mkQL.comp T :=
      ContinuousLinearMap.comp_add _ _ _
    rw [h_eq]
    exact norm_add_le (V.mkQL.comp S) (V.mkQL.comp T)
  have h_T : deviationFromSubspace T V ≤ ‖T‖ := deviationFromSubspace_le_norm T V
  linarith

/-! ## (S3) Ideal property

Pointwise, in the style of Pietsch, *Eigenvalues and s-numbers*, §2.4
(dual to the Gelfand argument). For `w : W` we evaluate the deviation
at `w` and chain three `le_opNorm` applications:
one for the descent of `B` to a map `Y/V →L[𝕜] Z/B(V)` (constructed
inline via `V.liftQL`), one for `V.mkQL.comp S`, and one for `A`. -/

/-- Per-subspace (S3) bound:
`deviation(B ∘ S ∘ A, B(V)) ≤ ‖B‖ * ‖A‖ * deviation(S, V)`. -/
lemma deviationFromSubspace_comp_comp_map_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (B.comp (S.comp A)) (V.map (B : Y →ₗ[𝕜] Z))
      ≤ ‖B‖ * ‖A‖ * deviationFromSubspace S V := by
  unfold deviationFromSubspace
  -- The CLM `(V.map B).mkQL ∘ B : Y →L[𝕜] Z/(V.map B)` has `V` in its
  -- kernel: for `v ∈ V`, `B v ∈ V.map B`, hence `[B v]_{Z/(V.map B)} = 0`.
  -- It therefore descends through `V.mkQL` via `V.liftQL` to a CLM
  -- `Y/V →L[𝕜] Z/(V.map B)` whose norm is bounded by `‖B‖`.
  set BL : Y →L[𝕜] (Z ⧸ V.map (B : Y →ₗ[𝕜] Z)) :=
    (V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B with hBL_def
  have h_ker :
      V ≤ LinearMap.ker (BL : Y →ₗ[𝕜] (Z ⧸ V.map (B : Y →ₗ[𝕜] Z))) := by
    intro v hv
    show (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B v) = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨v, hv, rfl⟩
  have h_BL_norm : ‖BL‖ ≤ ‖B‖ := by
    rw [hBL_def]
    calc ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B‖
        ≤ ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL‖ * ‖B‖ := opNorm_comp_le _ _
      _ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right
          (V.map (B : Y →ₗ[𝕜] Z)).norm_mkQL_le (norm_nonneg _)
      _ = ‖B‖ := one_mul _
  have h_lift_norm : ‖V.liftQL BL h_ker‖ ≤ ‖B‖ :=
    (V.norm_liftQL_le BL h_ker).trans h_BL_norm
  -- Pointwise bound on `w : W`.
  have h_bound_nn : 0 ≤ ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg A))
      (norm_nonneg (V.mkQL.comp S))
  refine opNorm_le_bound _ h_bound_nn fun w => ?_
  show ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL (B (S (A w)))‖ ≤
       ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ * ‖w‖
  -- Apply the descent: `BL (S (A w)) = V.liftQL BL _ (V.mkQL (S (A w)))`.
  have h_apply : (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B (S (A w)))
      = V.liftQL BL h_ker (V.mkQL (S (A w))) :=
    (V.liftQL_mkQL BL h_ker (S (A w))).symm
  rw [h_apply]
  calc ‖V.liftQL BL h_ker (V.mkQL (S (A w)))‖
      ≤ ‖V.liftQL BL h_ker‖ * ‖(V.mkQL.comp S) (A w)‖ :=
        (V.liftQL BL h_ker).le_opNorm _
    _ ≤ ‖B‖ * ‖(V.mkQL.comp S) (A w)‖ :=
        mul_le_mul_of_nonneg_right h_lift_norm (norm_nonneg _)
    _ ≤ ‖B‖ * (‖V.mkQL.comp S‖ * ‖A w‖) :=
        mul_le_mul_of_nonneg_left ((V.mkQL.comp S).le_opNorm (A w))
          (norm_nonneg B)
    _ ≤ ‖B‖ * (‖V.mkQL.comp S‖ * (‖A‖ * ‖w‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (A.le_opNorm w)
            (norm_nonneg (V.mkQL.comp S)))
          (norm_nonneg B)
    _ = ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ * ‖w‖ := by ring

lemma kolmogorovNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber S n * ‖A‖ := by
  -- Same scalar-pull-out trick as for the approximation numbers, but the
  -- per-subspace bound is a one-line consequence of operator-norm
  -- submultiplicativity.
  have hkey : ∀ V : Submodule 𝕜 Y, Module.rank 𝕜 V ≤ (n : Cardinal) →
      kolmogorovNumber (B.comp (S.comp A)) n ≤ ‖B‖ * ‖A‖ * deviationFromSubspace S V :=
    fun V hV =>
      (kolmogorovNumber_le_deviation ((rank_map_le _ _).trans hV)).trans
        (deviationFromSubspace_comp_comp_map_le A S B V)
  have h_inf : kolmogorovNumber (B.comp (S.comp A)) n
                ≤ ‖B‖ * ‖A‖ * kolmogorovNumber S n := by
    show _ ≤ (‖B‖ * ‖A‖) • sInf
      {r | ∃ V : Submodule 𝕜 Y,
            Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace S V}
    rw [← Real.sInf_smul_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    refine le_csInf ((kolmogorovSet_nonempty S n).image _) ?_
    rintro _ ⟨_, ⟨V, hV, rfl⟩, rfl⟩
    exact hkey V hV
  exact h_inf.trans_eq (by ring)

/-! ## (S4) Vanishing on operators of rank at most `n` -/

lemma kolmogorovNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    kolmogorovNumber S n = 0 := by
  refine le_antisymm ?_ (kolmogorovNumber_nonneg S n)
  -- Take `V = range S`. Then `V.mkQL ∘ S = 0`, so `deviation = 0`.
  set V : Submodule 𝕜 Y := LinearMap.range (S : X →ₗ[𝕜] Y) with hV_def
  have hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal) := hS
  refine (kolmogorovNumber_le_deviation hV_rank).trans ?_
  -- `V.mkQL.comp S = 0` because every `S x ∈ V`, so `[S x] = 0` in `Y/V`.
  have h_comp_zero : V.mkQL.comp S = 0 := by
    ext x
    simp only [coe_comp, Function.comp_apply, zero_apply,
      Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self (S : X →ₗ[𝕜] Y) x
  show ‖V.mkQL.comp S‖ ≤ 0
  rw [h_comp_zero]; exact le_of_eq (ContinuousLinearMap.opNorm_zero)


/-! ## (S5') Strict normalisation `kolmogorovNumber (id_X) n = 1` whenever `dim X > n`

For any closed proper finite-dim `V ⊆ X`, Riesz's lemma gives
`x₀ ∉ V` with `(1 − ε) * ‖x₀‖ ≤ ‖x₀ − y‖` for every `y ∈ V`. The infimum
on the RHS is exactly `‖V.mkQL x₀‖`. Combining with `le_opNorm` and
cancelling `‖x₀‖ > 0` gives `(1 − ε) ≤ ‖V.mkQL‖`. Letting ε → 0 finishes
the lower bound. The upper bound `‖V.mkQL.comp id‖ = ‖V.mkQL‖ ≤ 1` is
already in `Submodule.norm_mkQL_le`. -/

variable [CompleteSpace 𝕜]

private lemma one_le_norm_mkQL_of_proper {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {V : Submodule 𝕜 X} [FiniteDimensional 𝕜 V] (hV_ne_top : V ≠ ⊤) :
    (1 : ℝ) ≤ ‖V.mkQL‖ := by
  have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  have hV_exists : ∃ x : X, x ∉ V := SetLike.exists_not_mem_of_ne_top V hV_ne_top
  -- Limit `r → 1`: enough to show `1 ≤ ‖V.mkQL‖ + ε` for every `ε > 0`. The
  -- `ε ≥ 1` case is trivial (RHS ≥ 0 + 1); for `ε ∈ (0, 1)` we run Riesz at
  -- level `1 − ε`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hε1 : 1 ≤ ε
  · linarith [norm_nonneg V.mkQL]
  have hε1' : ε < 1 := lt_of_not_ge hε1
  have h_aux : (1 - ε : ℝ) < 1 := by linarith
  obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ := riesz_lemma hV_closed hV_exists h_aux
  have hx₀_ne_zero : x₀ ≠ 0 := fun h0 => hx₀_ne (h0 ▸ V.zero_mem)
  have hx₀_norm_pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀_ne_zero
  -- `‖V.mkQL x₀‖ = infDist x₀ V ≥ (1 − ε) · ‖x₀‖` via Riesz.
  have h_quot_ge : (1 - ε) * ‖x₀‖ ≤ ‖V.mkQL x₀‖ := by
    have h_norm_eq : ‖V.mkQL x₀‖ = Metric.infDist x₀ V :=
      QuotientAddGroup.norm_mk (S := V.toAddSubgroup) x₀
    rw [h_norm_eq, Metric.le_infDist ⟨0, V.zero_mem⟩]
    intro y hy
    rw [dist_eq_norm]
    exact hx₀_dist y hy
  -- `‖V.mkQL‖ · ‖x₀‖ ≥ ‖V.mkQL x₀‖ ≥ (1 − ε) · ‖x₀‖`. Cancel `‖x₀‖ > 0`,
  -- then rearrange.
  have h_op : ‖V.mkQL x₀‖ ≤ ‖V.mkQL‖ * ‖x₀‖ := V.mkQL.le_opNorm x₀
  have h_chain : (1 - ε) * ‖x₀‖ ≤ ‖V.mkQL‖ * ‖x₀‖ := h_quot_ge.trans h_op
  linarith [le_of_mul_le_mul_right h_chain hx₀_norm_pos]

/-- (S5') Strict normalisation: `kolmogorovNumber (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma kolmogorovNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    kolmogorovNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have h_finrank_pos : 0 < Module.finrank 𝕜 X :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have : FiniteDimensional 𝕜 X := .of_finrank_pos h_finrank_pos
  have : Nontrivial X := Module.nontrivial_of_finrank_pos h_finrank_pos
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: take `V = ⊥`. `deviation(I, ⊥) = ‖I‖ = 1`.
    have h_rank_bot : Module.rank 𝕜 (⊥ : Submodule 𝕜 X) ≤ (n : Cardinal) := by
      rw [rank_bot]; exact zero_le
    calc kolmogorovNumber I n
        ≤ deviationFromSubspace I ⊥ := kolmogorovNumber_le_deviation h_rank_bot
      _ = ‖I‖ := deviationFromSubspace_bot _
      _ = 1 := norm_id
  · -- `≥ 1`: every admissible `V` is proper, so `‖V.mkQL‖ ≥ 1`, and
    -- `deviation(I, V) = ‖V.mkQL.comp I‖ = ‖V.mkQL‖`.
    refine le_csInf (kolmogorovSet_nonempty I n) ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_finrank_le : Module.finrank 𝕜 V ≤ n := Module.finrank_le_of_rank_le hV
    have hV_finrank_lt : Module.finrank 𝕜 V < Module.finrank 𝕜 X :=
      lt_of_le_of_lt hV_finrank_le h
    have hV_ne_top : V ≠ ⊤ := by
      intro h_top
      rw [h_top, finrank_top] at hV_finrank_lt
      exact lt_irrefl _ hV_finrank_lt
    have : FiniteDimensional 𝕜 V := FiniteDimensional.finiteDimensional_submodule V
    have h_dev_eq : deviationFromSubspace I V = ‖V.mkQL‖ := by
      show ‖V.mkQL.comp I‖ = ‖V.mkQL‖
      rw [hI_def, ContinuousLinearMap.comp_id]
    rw [h_dev_eq]
    exact one_le_norm_mkQL_of_proper hV_ne_top

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma kolmogorovNumber_id_euclidean (n : ℕ) :
    kolmogorovNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin' (n + 1)]; exact Nat.lt_succ_self n
  exact kolmogorovNumber_strict n h

/-! ## Summary: Kolmogorov numbers (quotient form) form a strict s-number sequence -/

theorem isSNumberSequence_kolmogorovNumber :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) where
  nonneg := fun S n => kolmogorovNumber_nonneg S n
  norm_at_zero := fun S => kolmogorovNumber_zero_eq_norm S
  antitone := fun S n => kolmogorovNumber_antitone S n
  subadditive := fun S T n => kolmogorovNumber_add_le S T n
  ideal := fun A S B n => kolmogorovNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => kolmogorovNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => kolmogorovNumber_id_euclidean n

theorem isStrictSNumberSequence_kolmogorovNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) where
  toIsSNumberSequence := isSNumberSequence_kolmogorovNumber
  strictly_normalised_at_id := fun n h => kolmogorovNumber_strict n h

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
