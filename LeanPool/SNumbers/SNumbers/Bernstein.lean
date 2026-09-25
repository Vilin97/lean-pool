/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.SNumbers.SNumbers.Helpers
public import LeanPool.SNumbers.SNumbers.Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Bernstein numbers `b_n`

The Bernstein numbers `b_n S` of a continuous linear map `S : X →L[𝕜] Y`
between normed `𝕜`-vector spaces measure the *largest* possible
"smallest gain" of `S` on an `(n+1)`-dimensional subspace of the domain:

  `b_n S = sup_{M ⊆ X, dim M = n+1} inf_{x ∈ M, x ≠ 0} ‖S x‖ / ‖x‖`,

i.e. the largest constant `c ≥ 0` with the property that there exists an
`(n+1)`-dimensional subspace `M ⊆ X` on which `S` is bounded below by
`c · ‖·‖`.

The Bernstein numbers are the *smallest injective strict s-number sequence*
(`bernsteinNumber_le_of_injective_strict`), and hence satisfy (S1)-(S5)+(S5').

The development needs only `[NontriviallyNormedField 𝕜]`.
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

/-- The smallest gain `inf_{x ∈ M, x ≠ 0} ‖S x‖ / ‖x‖` of an operator `S` on
a subspace `M`. By the conventional `sInf ∅ = 0` for `ℝ`, this is `0`
when `M = ⊥`. -/
noncomputable def gainOnSubspace (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) : ℝ :=
  sInf {r | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖}

/-- The set of admissible gains at stage `n`: the numbers
`gainOnSubspace S M` for subspaces `M ⊆ X` of dimension exactly `n + 1`.
The `n`-th Bernstein number is its supremum. -/
def bernsteinSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ M : Submodule 𝕜 X,
      Module.rank 𝕜 M = (n + 1 : ℕ) ∧ r = gainOnSubspace S M}

/-- The `n`-th **Bernstein number** of a continuous linear map.

`b_n S = sup_{M ⊆ X, dim M = n + 1} gainOnSubspace S M`. -/
noncomputable def bernsteinNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sSup (bernsteinSet S n)

lemma bernsteinNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n = sSup (bernsteinSet S n) := rfl

/-! ### Basic facts about `gainOnSubspace` -/

private lemma gainSet_bddBelow (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    BddBelow {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖} :=
  ⟨0, by rintro _ ⟨_, _, _, rfl⟩; exact div_nonneg (norm_nonneg _) (norm_nonneg _)⟩

private lemma gainSet_nonempty_of_ne_bot (S : X →L[𝕜] Y) {M : Submodule 𝕜 X}
    (hM : M ≠ ⊥) :
    {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖}.Nonempty := by
  obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  exact ⟨_, x, hx_mem, hx_ne, rfl⟩

lemma gainOnSubspace_nonneg (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    0 ≤ gainOnSubspace S M :=
  Real.sInf_nonneg fun _ ⟨_, _, _, hr⟩ =>
    hr.symm ▸ div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Pointwise upper bound: every nonzero `x ∈ M` upper-bounds the gain. -/
lemma gainOnSubspace_le_div {S : X →L[𝕜] Y} {M : Submodule 𝕜 X} {x : X}
    (hx_mem : x ∈ M) (hx_ne : x ≠ 0) :
    gainOnSubspace S M ≤ ‖S x‖ / ‖x‖ :=
  csInf_le (gainSet_bddBelow S M) ⟨x, hx_mem, hx_ne, rfl⟩

/-- Lower bound on the gain: if every nonzero `x ∈ M` satisfies
`c ≤ ‖S x‖/‖x‖`, then `c ≤ gainOnSubspace S M`. -/
lemma le_gainOnSubspace {S : X →L[𝕜] Y} {M : Submodule 𝕜 X} (hM : M ≠ ⊥)
    {c : ℝ} (h : ∀ x ∈ M, x ≠ 0 → c ≤ ‖S x‖ / ‖x‖) :
    c ≤ gainOnSubspace S M := by
  refine le_csInf (gainSet_nonempty_of_ne_bot S hM) ?_
  rintro _ ⟨x, hx_mem, hx_ne, rfl⟩
  exact h x hx_mem hx_ne

lemma gainOnSubspace_le_norm (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    gainOnSubspace S M ≤ ‖S‖ := by
  by_cases hM : M = ⊥
  · -- gainSet is empty when `M = ⊥`, so `sInf = 0 ≤ ‖S‖`.
    have h_empty : {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      rintro x ⟨hx_mem, hx_ne, _⟩
      exact hx_ne (by rwa [hM, Submodule.mem_bot] at hx_mem)
    change sInf _ ≤ ‖S‖
    rw [h_empty, Real.sInf_empty]; exact norm_nonneg _
  · obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    exact (gainOnSubspace_le_div hx_mem hx_ne).trans (S.ratio_le_opNorm x)

/-! ### Basic facts about `bernsteinSet` -/

/-- The set of admissible gains is bounded above by `‖S‖`. -/
lemma bddAbove_bernsteinSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddAbove (bernsteinSet S n) :=
  ⟨‖S‖, by rintro _ ⟨M, _, rfl⟩; exact gainOnSubspace_le_norm S M⟩

/-- The `(n+1)`-rank constraint forces `M ≠ ⊥`. -/
private lemma rank_eq_succ_implies_ne_bot {M : Submodule 𝕜 X} {n : ℕ}
    (hM_rank : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal)) :
    M ≠ ⊥ := fun hM_bot => by
  rw [hM_bot, rank_bot] at hM_rank
  exact Nat.succ_ne_zero n (by exact_mod_cast hM_rank.symm)

/-- Rank of the span of an `n`-element linearly independent family. -/
private lemma rank_span_range_fin {V : Type u} [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} {g : Fin n → V} (hg : LinearIndependent 𝕜 g) :
    Module.rank 𝕜 (Submodule.span 𝕜 (Set.range g)) = (n : Cardinal) := by
  classical
  have : Fintype (Set.range g) := Set.fintypeRange g
  rw [rank_span hg, Cardinal.mk_fintype, Set.card_range_of_injective hg.injective,
      Fintype.card_fin]

/-! ## (S1c) Non-negativity -/

lemma bernsteinNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ bernsteinNumber S n :=
  Real.sSup_nonneg <| by rintro _ ⟨M, _, rfl⟩; exact gainOnSubspace_nonneg S M

/-! ## (S1a) Value at `n = 0`: `bernsteinNumber S 0 = ‖S‖`

For `n = 0`, `dim M = 1`, so `M = span {v}` for some `v ≠ 0`. Then every
`x ∈ M, x ≠ 0` is `x = c · v` for some scalar `c ≠ 0`, and
`‖S x‖/‖x‖ = ‖S v‖/‖v‖`. Hence `gainOnSubspace S M = ‖S v‖/‖v‖`, and
the supremum over 1-dim subspaces equals `sup_v ‖S v‖/‖v‖ = ‖S‖`. -/

/-- For a one-dimensional subspace `M = span {v}` with `v ≠ 0`,
`gainOnSubspace S M = ‖S v‖ / ‖v‖`. -/
private lemma gainOnSubspace_span_singleton {S : X →L[𝕜] Y} {v : X} (hv_ne : v ≠ 0) :
    gainOnSubspace S (Submodule.span 𝕜 {v}) = ‖S v‖ / ‖v‖ := by
  set M : Submodule 𝕜 X := Submodule.span 𝕜 {v}
  have hv_mem : v ∈ M := Submodule.subset_span (Set.mem_singleton _)
  have hM_ne_bot : M ≠ ⊥ := fun hM_bot =>
    hv_ne (by rwa [hM_bot, Submodule.mem_bot] at hv_mem)
  refine le_antisymm (gainOnSubspace_le_div hv_mem hv_ne) ?_
  refine le_gainOnSubspace hM_ne_bot ?_
  rintro _ hx_mem hx_ne
  rw [Submodule.mem_span_singleton] at hx_mem
  obtain ⟨c, rfl⟩ := hx_mem
  have hc_ne : c ≠ 0 := fun hc => hx_ne (by rw [hc, zero_smul])
  rw [map_smul, norm_smul, norm_smul,
      mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hc_ne)]

@[simp] lemma bernsteinNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    bernsteinNumber S 0 = ‖S‖ := by
  refine le_antisymm
    (Real.sSup_le (fun _ ⟨M, _, hr⟩ => hr.symm ▸ gainOnSubspace_le_norm S M)
      (norm_nonneg _)) ?_
  -- For each `v` with `‖v‖ ≠ 0`, the 1-dim subspace `span {v}` realises
  -- the gain `‖S v‖/‖v‖`, which is therefore `≤ b_0 S`.
  refine opNorm_le_bound' _ (bernsteinNumber_nonneg S 0) fun v hv_norm => ?_
  have hv_ne : v ≠ 0 := norm_ne_zero_iff.mp hv_norm
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hM_rank : Module.rank 𝕜 (Submodule.span 𝕜 ({v} : Set X)) = ((0 + 1 : ℕ) : Cardinal) := by
    rw [rank_span_set (LinearIndepOn.singleton hv_ne), Cardinal.mk_singleton]; norm_cast
  have h_le : gainOnSubspace S (Submodule.span 𝕜 ({v} : Set X)) ≤ bernsteinNumber S 0 :=
    le_csSup (bddAbove_bernsteinSet S 0) ⟨_, hM_rank, rfl⟩
  rw [gainOnSubspace_span_singleton hv_ne, div_le_iff₀ hv_pos] at h_le
  linarith

/-! ## (S1b) Antitone in `n` -/

/-- Restricting the gain to a subspace `M' ⊆ M` only increases it (smaller
inf-domain). -/
lemma gainOnSubspace_anti {S : X →L[𝕜] Y} {M M' : Submodule 𝕜 X}
    (h_le : M' ≤ M) (hM' : M' ≠ ⊥) :
    gainOnSubspace S M ≤ gainOnSubspace S M' := by
  refine csInf_le_csInf (gainSet_bddBelow S M)
    (gainSet_nonempty_of_ne_bot S hM') ?_
  rintro _ ⟨x, hx_mem', hx_ne, rfl⟩
  exact ⟨x, h_le hx_mem', hx_ne, rfl⟩

lemma bernsteinNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S (n + 1) ≤ bernsteinNumber S n := by
  refine Real.sSup_le ?_ (bernsteinNumber_nonneg S n)
  rintro _ ⟨M, hM_rank, rfl⟩
  -- `M` has rank `n + 2`. Pick an `(n+1)`-dim subspace `M' ⊆ M`.
  have hM_rank' : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 M := by
    rw [hM_rank]; exact_mod_cast Nat.le_succ _
  obtain ⟨f, hf_li⟩ := exists_linearIndependent_of_le_rank hM_rank'
  set g : Fin (n + 1) → X := fun i => (f i : X) with hg_def
  have hg_li : LinearIndependent 𝕜 g :=
    (M.subtype.linearIndependent_iff (Submodule.ker_subtype M)).mpr hf_li
  set M' : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range g) with hM'_def
  have hM'_rank : Module.rank 𝕜 M' = ((n + 1 : ℕ) : Cardinal) :=
    rank_span_range_fin hg_li
  have hM'_le : M' ≤ M := by
    rw [hM'_def]
    exact Submodule.span_le.mpr <| by rintro _ ⟨i, rfl⟩; exact (f i).2
  calc gainOnSubspace S M
      ≤ gainOnSubspace S M' :=
        gainOnSubspace_anti hM'_le (rank_eq_succ_implies_ne_bot hM'_rank)
    _ ≤ bernsteinNumber S n := le_csSup (bddAbove_bernsteinSet S n) ⟨M', hM'_rank, rfl⟩

/-- Upper bound by the operator norm: `b_n S ≤ ‖S‖`, since `b_n S ≤ b_0 S = ‖S‖`. -/
lemma bernsteinNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (bernsteinNumber_antitone S) (Nat.zero_le n)).trans_eq
    (bernsteinNumber_zero_eq_norm S)

/-! ## (S2) Subadditivity -/

private lemma gainOnSubspace_add_le (S T : X →L[𝕜] Y) {M : Submodule 𝕜 X}
    (hM : M ≠ ⊥) :
    gainOnSubspace (S + T) M ≤ gainOnSubspace S M + ‖T‖ := by
  rw [← sub_le_iff_le_add]
  refine le_gainOnSubspace hM ?_
  intro x hx_mem hx_ne
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  -- `‖(S+T) x‖ / ‖x‖ ≤ ‖S x‖/‖x‖ + ‖T‖`, then chain through `gain (S+T) M`.
  have h_div : ‖(S + T) x‖ / ‖x‖ ≤ ‖S x‖ / ‖x‖ + ‖T‖ := by
    rw [show ‖S x‖ / ‖x‖ + ‖T‖ = (‖S x‖ + ‖T‖ * ‖x‖) / ‖x‖ from by
          rw [add_div, mul_div_cancel_right₀ _ hx_pos.ne'],
        div_le_div_iff_of_pos_right hx_pos]
    calc ‖(S + T) x‖
        = ‖S x + T x‖ := by rw [add_apply]
      _ ≤ ‖S x‖ + ‖T x‖ := norm_add_le _ _
      _ ≤ ‖S x‖ + ‖T‖ * ‖x‖ := by linarith [T.le_opNorm x]
  linarith [gainOnSubspace_le_div (S := S + T) hx_mem hx_ne]

lemma bernsteinNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber (S + T) n ≤ bernsteinNumber S n + ‖T‖ := by
  refine Real.sSup_le ?_
    (add_nonneg (bernsteinNumber_nonneg S n) (norm_nonneg _))
  rintro _ ⟨M, hM_rank, rfl⟩
  have h1 : gainOnSubspace (S + T) M ≤ gainOnSubspace S M + ‖T‖ :=
    gainOnSubspace_add_le S T (rank_eq_succ_implies_ne_bot hM_rank)
  have h2 : gainOnSubspace S M ≤ bernsteinNumber S n :=
    le_csSup (bddAbove_bernsteinSet S n) ⟨M, hM_rank, rfl⟩
  linarith

/-! ## (S4) Vanishing on operators of rank at most `n`

If `rank S ≤ n`, then for every `M ⊆ X` with `dim M = n + 1`, the
restriction `S|_M` has rank `≤ rank S ≤ n < n + 1 = dim M`, so by
rank-nullity `S` has a nontrivial kernel inside `M`. Picking
`x ∈ M ∩ ker S` with `x ≠ 0` gives `‖S x‖/‖x‖ = 0` in the gain set,
hence `gainOnSubspace S M = 0`. The supremum over `M` is then `0`. -/

lemma bernsteinNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    bernsteinNumber S n = 0 := by
  refine le_antisymm ?_ (bernsteinNumber_nonneg S n)
  refine Real.sSup_le ?_ le_rfl
  rintro _ ⟨M, hM_rank, rfl⟩
  -- We claim `gainOnSubspace S M ≤ 0`. Find `x ∈ M ∩ ker S` with `x ≠ 0`
  -- via rank-nullity on `f := S.domRestrict M : M →ₗ Y`.
  set f : M →ₗ[𝕜] Y := (S : X →ₗ[𝕜] Y).domRestrict M
  have h_rank_f_le : Module.rank 𝕜 (LinearMap.range f) ≤ (n : Cardinal) :=
    (Submodule.rank_mono <| by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩).trans hS
  have h_split :
      Module.rank 𝕜 (LinearMap.range f) + Module.rank 𝕜 (LinearMap.ker f)
        = Module.rank 𝕜 M := LinearMap.rank_range_add_rank_ker f
  -- `dim ker f ≥ 1` from the rank decomposition.
  have h_ker_pos : 0 < Module.rank 𝕜 (LinearMap.ker f) := by
    rw [hM_rank] at h_split
    by_contra h_le
    have h_zero : Module.rank 𝕜 (LinearMap.ker f) = 0 :=
      le_antisymm (not_lt.mp h_le) bot_le
    rw [h_zero, add_zero] at h_split
    have : (n + 1 : ℕ) ≤ (n : ℕ) := by
      exact_mod_cast h_split.symm.trans_le h_rank_f_le
    omega
  have h_ker_ne_bot : LinearMap.ker f ≠ ⊥ := fun h => by
    rw [h, rank_bot] at h_ker_pos; exact lt_irrefl _ h_ker_pos
  obtain ⟨⟨x, hx_mem⟩, hx_ker, hx_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot h_ker_ne_bot
  have hx_ne_zero : x ≠ 0 := fun h => hx_ne (by ext; exact h)
  have hSx : S x = 0 := hx_ker
  have h_zero_in :
      (0 : ℝ) ∈ {r : ℝ | ∃ y, y ∈ M ∧ y ≠ 0 ∧ r = ‖S y‖ / ‖y‖} :=
    ⟨x, hx_mem, hx_ne_zero, by rw [hSx, norm_zero, zero_div]⟩
  exact csInf_le (gainSet_bddBelow S M) h_zero_in

/-! ## (S5') Strict normalisation `b_n (id_X) = 1` whenever `dim X > n`

For `id_X`, every nonzero `x` satisfies `‖x‖ / ‖x‖ = 1`. Hence
`gainOnSubspace id_X M = 1` for every `M ≠ ⊥`. The supremum over
`(n+1)`-dim subspaces is then `1`, provided at least one such subspace
exists (which holds iff `dim X > n`). -/

private lemma gainOnSubspace_id_eq_one {M : Submodule 𝕜 X} (hM : M ≠ ⊥) :
    gainOnSubspace (ContinuousLinearMap.id 𝕜 X) M = 1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    refine (gainOnSubspace_le_div (S := ContinuousLinearMap.id 𝕜 X)
      hx_mem hx_ne).trans_eq ?_
    rw [ContinuousLinearMap.id_apply, div_self hx_pos.ne']
  · refine le_gainOnSubspace hM ?_
    intro x _ hx_ne
    rw [ContinuousLinearMap.id_apply, div_self (norm_pos_iff.mpr hx_ne).ne']

/-- (S5') Strict normalisation: `bernsteinNumber (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma bernsteinNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    bernsteinNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have : FiniteDimensional 𝕜 X :=
    .of_finrank_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h)
  -- Construct an `(n+1)`-dim subspace `M ⊆ X`.
  obtain ⟨g, hg_li⟩ := exists_linearIndependent_of_le_finrank (h : n + 1 ≤ _)
  set M : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range g)
  have hM_rank : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal) :=
    rank_span_range_fin hg_li
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: every gain in `bSet` is `1`.
    refine Real.sSup_le ?_ zero_le_one
    rintro _ ⟨M', hM'_rank, rfl⟩
    rw [gainOnSubspace_id_eq_one (rank_eq_succ_implies_ne_bot hM'_rank)]
  · -- `≥ 1`: `M` is a witness with gain `= 1`.
    refine (le_of_eq (gainOnSubspace_id_eq_one
      (rank_eq_succ_implies_ne_bot hM_rank)).symm).trans ?_
    exact le_csSup (bddAbove_bernsteinSet _ n) ⟨M, hM_rank, rfl⟩

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma bernsteinNumber_id_euclidean (n : ℕ) :
    bernsteinNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin' (n + 1)]; exact Nat.lt_succ_self n
  exact bernsteinNumber_strict n h

/-! ## (S3) Ideal property

For `M ⊆ W` with `dim M = n+1`, split on whether `A : W →L X` is
injective on `M`:

* If not, some nonzero `x ∈ M` has `A x = 0`, hence `(BSA) x = 0`, so
  `gainOnSubspace (BSA) M = 0` and the bound is trivial.
* If yes, `M' := A.M ⊆ X` has `dim M' = n+1`, and the per-vector
  inequality
    `‖B(S(A x))‖ / ‖x‖ ≤ ‖B‖ · ‖A‖ · ‖S(A x)‖ / ‖A x‖`
  taken against the bijection `M ≃ M'` gives
  `gainOnSubspace (BSA) M ≤ ‖B‖ · ‖A‖ · gainOnSubspace S M'`. -/

/-- Per-subspace bound in the injective case. -/
private lemma gainOnSubspace_comp_comp_le_of_injective
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) {M : Submodule 𝕜 W}
    (hM : M ≠ ⊥) (h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0) :
    gainOnSubspace (B.comp (S.comp A)) M ≤
      ‖B‖ * ‖A‖ * gainOnSubspace S (M.map (A : W →ₗ[𝕜] X)) := by
  by_cases hBA : ‖B‖ * ‖A‖ = 0
  · -- `‖B‖ * ‖A‖ = 0`. Either `‖B‖ = 0` (so `B = 0` and `BSA = 0`), or
    -- `‖A‖ = 0` (which is incompatible with `M ≠ ⊥` and `h_inj`).
    rw [hBA, zero_mul]
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    rcases mul_eq_zero.mp hBA with hB | hA
    · have hB_zero : B = 0 := norm_eq_zero.mp hB
      have h_zero : B.comp (S.comp A) = 0 := by rw [hB_zero, zero_comp]
      rw [h_zero]
      refine (gainOnSubspace_le_div (S := (0 : W →L[𝕜] Z)) hx_mem hx_ne).trans ?_
      rw [zero_apply, norm_zero, zero_div]
    · exfalso
      apply h_inj x hx_mem hx_ne
      rw [norm_eq_zero.mp hA, zero_apply]
  · -- `‖B‖ * ‖A‖ > 0`. The main case.
    have hBA_pos : 0 < ‖B‖ * ‖A‖ :=
      lt_of_le_of_ne (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm hBA)
    set M' : Submodule 𝕜 X := M.map (A : W →ₗ[𝕜] X)
    have hM'_ne_bot : M' ≠ ⊥ := by
      obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
      intro hM'_bot
      have : A x ∈ M' := ⟨x, hx_mem, rfl⟩
      rw [hM'_bot, Submodule.mem_bot] at this
      exact h_inj x hx_mem hx_ne this
    -- Show `gain (BSA) M / (‖B‖‖A‖) ≤ gain S M'`.
    suffices h_div :
        gainOnSubspace (B.comp (S.comp A)) M / (‖B‖ * ‖A‖) ≤
          gainOnSubspace S M' by
      rw [div_le_iff₀ hBA_pos] at h_div
      linarith [mul_comm (‖B‖ * ‖A‖) (gainOnSubspace S M')]
    refine le_gainOnSubspace hM'_ne_bot ?_
    rintro _ ⟨x, hx_mem, rfl⟩ hAx_ne
    -- `A x ≠ 0` ⇒ `x ≠ 0` (since `A 0 = 0`).
    have hx_ne : x ≠ 0 := fun h => hAx_ne (by rw [h, map_zero])
    have hAx_pos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx_ne
    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    -- `‖(BSA) x‖/‖x‖ ≤ ‖B‖‖A‖ * ‖S(A x)‖/‖A x‖`.
    have h_per_vec :
        ‖(B.comp (S.comp A)) x‖ / ‖x‖ ≤
          ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) := by
      rw [div_le_iff₀ hx_pos]
      calc ‖(B.comp (S.comp A)) x‖
          = ‖B (S (A x))‖ := rfl
        _ ≤ ‖B‖ * ‖S (A x)‖ := B.le_opNorm _
        _ = ‖B‖ * (‖S (A x)‖ / ‖A x‖) * ‖A x‖ := by
            rw [mul_assoc, div_mul_cancel₀ _ hAx_pos.ne']
        _ ≤ ‖B‖ * (‖S (A x)‖ / ‖A x‖) * (‖A‖ * ‖x‖) := by
            gcongr; exact A.le_opNorm x
        _ = ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) * ‖x‖ := by ring
    rw [div_le_iff₀ hBA_pos]
    calc gainOnSubspace (B.comp (S.comp A)) M
        ≤ ‖(B.comp (S.comp A)) x‖ / ‖x‖ := gainOnSubspace_le_div hx_mem hx_ne
      _ ≤ ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) := h_per_vec
      _ = ‖S (A x)‖ / ‖A x‖ * (‖B‖ * ‖A‖) := by ring

/-- Rank of `M.map A` equals rank of `M` when `A` is injective on `M`. -/
private lemma rank_map_of_injective_on
    (A : W →L[𝕜] X) {M : Submodule 𝕜 W}
    (h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0) :
    Module.rank 𝕜 (M.map (A : W →ₗ[𝕜] X)) = Module.rank 𝕜 M := by
  -- `f := A.domRestrict M : M →ₗ X` has range `M.map A` and trivial kernel.
  set f : M →ₗ[𝕜] X := (A : W →ₗ[𝕜] X).domRestrict M with hf_def
  have h_inj_f : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx_mem⟩ hx_ker
    by_contra hx_ne_zero
    exact h_inj x hx_mem (fun h => hx_ne_zero (by ext; exact h)) hx_ker
  rw [← LinearMap.range_domRestrict M (A : W →ₗ[𝕜] X)]
  exact (LinearEquiv.ofInjective f h_inj_f).rank_eq.symm

lemma bernsteinNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    bernsteinNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * bernsteinNumber S n * ‖A‖ := by
  refine Real.sSup_le ?_
    (mul_nonneg (mul_nonneg (norm_nonneg _) (bernsteinNumber_nonneg _ _))
      (norm_nonneg _))
  rintro _ ⟨M, hM_rank, rfl⟩
  have hM_ne_bot : M ≠ ⊥ := rank_eq_succ_implies_ne_bot hM_rank
  by_cases h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0
  · -- Injective case.
    set M' : Submodule 𝕜 X := M.map (A : W →ₗ[𝕜] X)
    have hM'_rank : Module.rank 𝕜 M' = ((n + 1 : ℕ) : Cardinal) := by
      rw [rank_map_of_injective_on A h_inj, hM_rank]
    calc gainOnSubspace (B.comp (S.comp A)) M
        ≤ ‖B‖ * ‖A‖ * gainOnSubspace S M' :=
          gainOnSubspace_comp_comp_le_of_injective A S B hM_ne_bot h_inj
      _ ≤ ‖B‖ * ‖A‖ * bernsteinNumber S n :=
          mul_le_mul_of_nonneg_left
            (le_csSup (bddAbove_bernsteinSet S n) ⟨M', hM'_rank, rfl⟩)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖B‖ * bernsteinNumber S n * ‖A‖ := by ring
  · -- Non-injective case: some nonzero `x ∈ M` has `A x = 0`, so `(BSA) x = 0`.
    simp only [not_forall, Classical.not_not, ne_eq] at h_inj
    obtain ⟨x, hx_mem, hx_ne, hAx_zero⟩ := h_inj
    have h_zero : ‖B.comp (S.comp A) x‖ / ‖x‖ = 0 := by
      change ‖B (S (A x))‖ / ‖x‖ = 0
      rw [hAx_zero, map_zero, map_zero, norm_zero, zero_div]
    linarith [(gainOnSubspace_le_div hx_mem hx_ne).trans (le_of_eq h_zero),
      mul_nonneg (mul_nonneg (norm_nonneg B) (bernsteinNumber_nonneg S n))
        (norm_nonneg A)]

/-! ## Summary: Bernstein numbers form a strict s-number sequence -/

theorem isSNumberSequence_bernsteinNumber :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) where
  nonneg := fun S n => bernsteinNumber_nonneg S n
  norm_at_zero := fun S => bernsteinNumber_zero_eq_norm S
  antitone := fun S n => bernsteinNumber_antitone S n
  subadditive := fun S T n => bernsteinNumber_add_le S T n
  ideal := fun A S B n => bernsteinNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => bernsteinNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => bernsteinNumber_id_euclidean n

theorem isStrictSNumberSequence_bernsteinNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) where
  toIsSNumberSequence := isSNumberSequence_bernsteinNumber
  strictly_normalised_at_id := fun n h => bernsteinNumber_strict n h

/-! ## Bernstein numbers are the smallest injective strict
`s`-number sequence

For **every** injective strict `s`-number sequence `s`, one has
`bₙ(S) ≤ sₙ(S)`.

The proof is the classical Pietsch argument, elementary and self-contained. Fix
an `(n+1)`-dimensional subspace `M ⊆ X` and
let `c := gainOnSubspace S M`, so `S` is bounded below by `c` on `M`. Corestrict
`f := S|_M` to its range `V ⊆ Y`: there it becomes a continuous linear
*isomorphism* `f₀ : M ≃ V` with `‖f₀⁻¹‖ ≤ 1/c`. **Injectivity** of `s` discards
the isometric inclusion `V ↪ Y` (`sₙ(f) = sₙ(f₀)`); the ideal property against
`f₀⁻¹` together with **strict normalisation** `sₙ(id_M) = 1` (valid because
`dim M = n+1 > n`) forces `sₙ(f₀) ≥ c`. Finally `f = S ∘ ι_M` with `‖ι_M‖ ≤ 1`,
so `c ≤ sₙ(f) ≤ sₙ(S)`. Taking the supremum over `M` gives `bₙ(S) ≤ sₙ(S)`. -/

/-- **Core lower bound.** If `f : E →L[𝕜] F` is bounded below by `c > 0` on a
space `E` with `n < dim E`, then every injective strict `s`-number sequence `s`
satisfies `c ≤ sₙ(f)`.

This isolates the heart of the extremality theorem: `f` is corestricted to its
range `V` (an isometric copy inside `F`), where it is a continuous linear
isomorphism `f₀` with `‖f₀⁻¹‖ ≤ 1/c`. Injectivity of `s` removes the inclusion
`V ↪ F`, and the ideal property plus strict normalisation `sₙ(id_E) = 1` give the
bound. -/
lemma le_sn_of_boundedBelow_strict {s : Family 𝕜}
    (hs : IsStrictSNumberSequence s) (hinj : Injective s)
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (hE : n < Module.finrank 𝕜 E) {c : ℝ} (hc : 0 < c)
    (f : E →L[𝕜] F) (hf : ∀ x, c * ‖x‖ ≤ ‖f x‖) :
    c ≤ s f n := by
  -- `f` is injective, being bounded below by `c > 0`.
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h := hf (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h
    exact absurd h (not_le.2 (mul_pos hc hpos))
  -- Corestrict `f` to its range `V := range f ⊆ F`.
  set V : Submodule 𝕜 F := LinearMap.range (f : E →ₗ[𝕜] F) with hV
  have hmem : ∀ x, f x ∈ V := fun x => ⟨x, rfl⟩
  set f₀ : E →L[𝕜] V := f.codRestrict V hmem with hf₀_def
  -- `f₀` is a linear bijection onto `V`.
  have hf₀_inj : Function.Injective f₀ := fun a b hab =>
    hf_inj (congrArg Subtype.val hab)
  have hf₀_surj : Function.Surjective f₀ := by
    rintro ⟨z, x, rfl⟩
    exact ⟨x, Subtype.ext rfl⟩
  have hbij : Function.Bijective (f₀ : E →ₗ[𝕜] V) := ⟨hf₀_inj, hf₀_surj⟩
  set e : E ≃ₗ[𝕜] V := LinearEquiv.ofBijective (f₀ : E →ₗ[𝕜] V) hbij with he_def
  have he_apply : ∀ x, e x = f₀ x := fun x => rfl
  -- The algebraic inverse `e.symm` is bounded by `1/c`; upgrade it to a CLM `g`.
  have hbound : ∀ v : V, ‖e.symm v‖ ≤ (1 / c) * ‖v‖ := by
    intro v
    have hfx : f (e.symm v) = (v : F) := by
      have h2 : f₀ (e.symm v) = v := by rw [← he_apply]; exact e.apply_symm_apply v
      exact congrArg Subtype.val h2
    have h3 := hf (e.symm v)
    rw [hfx] at h3
    have hnorm : ‖(v : F)‖ = ‖v‖ := rfl
    rw [hnorm] at h3
    rw [show (1 / c) * ‖v‖ = ‖v‖ / c from by ring, le_div_iff₀ hc, mul_comm]
    exact h3
  set g : V →L[𝕜] E := (e.symm : V →ₗ[𝕜] E).mkContinuous (1 / c) hbound with hg_def
  have hg_norm : ‖g‖ ≤ 1 / c := by
    rw [hg_def]; exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  -- `g ∘ f₀ = id_E`.
  have hgf : g.comp f₀ = ContinuousLinearMap.id 𝕜 E := by
    ext x
    have : g (f₀ x) = x := by
      rw [hg_def, LinearMap.mkContinuous_apply]; exact e.symm_apply_apply x
    simpa using this
  -- `f = ι_V ∘ f₀` with `ι_V` a metric injection ⟹ `sₙ(f) = sₙ(f₀)`.
  have hmetric : IsMetricInjection (V.subtypeL) := fun v => rfl
  have hcomp : V.subtypeL.comp f₀ = f := by ext x; rfl
  have h_inj_eq : s f n = s f₀ n := by
    rw [← hcomp]; exact hinj f₀ V.subtypeL hmetric n
  -- Ideal property against `g = f₀⁻¹` and strict normalisation `sₙ(id_E) = 1`.
  have h_ideal := hs.ideal (ContinuousLinearMap.id 𝕜 E) f₀ g n
  rw [ContinuousLinearMap.comp_id, hgf, hs.strictly_normalised_at_id n hE] at h_ideal
  have hsn : 0 ≤ s f₀ n := hs.nonneg f₀ n
  have hidle : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := norm_id_le
  have h1 : (1 : ℝ) ≤ ‖g‖ * s f₀ n := by
    nlinarith [h_ideal,
      mul_nonneg (mul_nonneg (norm_nonneg g) hsn) (sub_nonneg.mpr hidle)]
  have h2 : c * ‖g‖ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hg_norm hc.le
    rwa [mul_one_div, div_self hc.ne'] at hh
  have key : c ≤ s f₀ n := by
    nlinarith [h1, h2, hsn, hc.le, mul_nonneg hc.le (norm_nonneg g)]
  rw [h_inj_eq]; exact key

/-- **The Bernstein numbers are the smallest injective strict `s`-number
sequence.** For every injective strict `s`-number sequence `s`,
`bₙ(S) ≤ sₙ(S)`. -/
theorem bernsteinNumber_le_of_injective_strict {s : Family 𝕜}
    (hs : IsStrictSNumberSequence s) (hinj : Injective s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n ≤ s S n := by
  refine Real.sSup_le ?_ (hs.nonneg S n)
  rintro _ ⟨M, hM_rank, rfl⟩
  -- Goal: `gainOnSubspace S M ≤ s S n`.
  set c := gainOnSubspace S M with hc_def
  rcases lt_or_ge 0 c with hcpos | hc0
  · -- `dim M = n+1`, so `n < finrank M`.
    have hfin : n < Module.finrank 𝕜 (M : Submodule 𝕜 X) := by
      rw [Module.finrank_eq_of_rank_eq hM_rank]; exact Nat.lt_succ_self n
    -- `S|_M = S ∘ M.subtypeL` is bounded below by `c` on `M`.
    have hf : ∀ x : M, c * ‖x‖ ≤ ‖(S.comp M.subtypeL) x‖ := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · have hx' : (x : X) ≠ 0 := fun h => hx (Subtype.ext h)
        have hpos : 0 < ‖(x : X)‖ := norm_pos_iff.mpr hx'
        have hle : c ≤ ‖S (x : X)‖ / ‖(x : X)‖ :=
          gainOnSubspace_le_div x.2 hx'
        have hmul : c * ‖(x : X)‖ ≤ ‖S (x : X)‖ := (le_div_iff₀ hpos).mp hle
        simpa using hmul
    -- Core bound and the (S3) step back to `S`.
    have hcore : c ≤ s (S.comp M.subtypeL) n :=
      le_sn_of_boundedBelow_strict hs hinj hfin hcpos (S.comp M.subtypeL) hf
    have hback : s (S.comp M.subtypeL) n ≤ s S n := by
      have h_ideal := hs.ideal M.subtypeL S (ContinuousLinearMap.id 𝕜 Y) n
      rw [ContinuousLinearMap.id_comp] at h_ideal
      have hsn : 0 ≤ s S n := hs.nonneg S n
      have hidY : ‖ContinuousLinearMap.id 𝕜 Y‖ ≤ 1 := norm_id_le
      have hsub : ‖M.subtypeL‖ ≤ 1 := M.norm_subtypeL_le
      have t1 : ‖ContinuousLinearMap.id 𝕜 Y‖ * s S n ≤ 1 * s S n :=
        mul_le_mul_of_nonneg_right hidY hsn
      have t2 := mul_le_mul t1 hsub (norm_nonneg M.subtypeL)
        (by rw [one_mul]; exact hsn)
      calc s (S.comp M.subtypeL) n
          ≤ ‖ContinuousLinearMap.id 𝕜 Y‖ * s S n * ‖M.subtypeL‖ := h_ideal
        _ ≤ 1 * s S n * 1 := t2
        _ = s S n := by ring
    exact hcore.trans hback
  · exact hc0.trans (hs.nonneg S n)

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
