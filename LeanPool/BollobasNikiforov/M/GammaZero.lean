/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.CP.Closed
import LeanPool.BollobasNikiforov.M.Schur
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Order.Basic

/-!
# The `γ = 0` perturbation

If `configγ s t ρ x = 0`, enlarge the configuration by a new vector
`y* = √ε • (x*, 1)` with `x*` strictly to the right of every `t i` and
`ε > 0`. Every new `H i` is then positive, hence the enlarged `γ` is
positive (SC19). The principal submatrix of `M` on the original indices
differs from the original `M` only by diagonal `O(ε)` Laplacian terms
coming from edges to `y*`, and therefore converges as `ε ↓ 0` (SC20).
Closedness of the CP cone upgrades SC18 on the enlargements to CP of the
original `M`, including the case `p = 0` (SC21).
-/

namespace BollobasNikiforov

open Matrix Finset Function Filter
open scoped Matrix Topology

variable {k p : ℕ}


noncomputable section

/-! ### SC19 — vanishing `H i` when `γ = 0` -/

/-- Original `γ = 0` forces each summand `s i * H i / d i` to vanish. -/
lemma configH_eq_zero_of_configγ_eq_zero {s t : Fin k → ℝ} {ρ x : Fin p → ℝ}
    (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j)
    (hγ : configγ s t ρ x = 0) (i : Fin k) :
    configH t ρ x i = 0 := by
  have hsum : ∑ i, s i * configH t ρ x i / configD t ρ x i = 0 := by
    simpa [configγ_eq_sum s t hρ x] using hγ
  have hterm : s i * configH t ρ x i / configD t ρ x i = 0 :=
    (sum_eq_zero_iff_of_nonneg fun j _ =>
      div_nonneg (mul_nonneg (hs j).le (configH_nonneg t hρ x j))
        (configD_pos t hρ x j).le).1 hsum _ (mem_univ i)
  have hd : configD t ρ x i ≠ 0 := (configD_pos t hρ x i).ne'
  have hprod : s i * configH t ρ x i = 0 :=
    (div_eq_zero_iff.mp hterm).resolve_right hd
  exact (mul_eq_zero.mp hprod).resolve_left (hs i).ne'

/-! ### Canonical abscissa `x*` -/

/-- If `k = 0`, take `x* = 0`; if `k ≥ 1`, take `x* = (max t i) + 1`. -/
noncomputable def configXstar (t : Fin k → ℝ) : ℝ :=
  match k, t with
  | 0, _ => 0
  | _ + 1, t => univ.sup' univ_nonempty t + 1

lemma configXstar_zero (t : Fin 0 → ℝ) : configXstar t = 0 := rfl

lemma configXstar_succ {n : ℕ} (t : Fin (n + 1) → ℝ) :
    configXstar t = univ.sup' univ_nonempty t + 1 := rfl

lemma configXstar_nonneg {t : Fin k → ℝ} (ht : ∀ i, 0 < t i) :
    0 ≤ configXstar t := by
  cases k with
  | zero => simp [configXstar]
  | succ n =>
    rw [configXstar_succ]
    have hle : 0 ≤ univ.sup' univ_nonempty t := by
      rw [le_sup'_iff]
      exact ⟨0, mem_univ 0, (ht 0).le⟩
    linarith

lemma lt_configXstar (t : Fin k → ℝ) (i : Fin k) : t i < configXstar t := by
  cases k with
  | zero => exact i.elim0
  | succ n =>
    rw [configXstar_succ]
    have hle : t i ≤ univ.sup' univ_nonempty t := by
      rw [le_sup'_iff]
      exact ⟨i, mem_univ i, le_rfl⟩
    exact lt_add_of_le_of_pos hle zero_lt_one

/-! ### Enlarged weights and abscissae -/

/-- Extend `ρ` by a last coordinate `ε`. -/
def configExtendρ (ρ : Fin p → ℝ) (ε : ℝ) : Fin (p + 1) → ℝ :=
  Fin.snoc ρ ε

/-- Extend `x` by a last coordinate `x*`. -/
def configExtendx (x : Fin p → ℝ) (xstar : ℝ) : Fin (p + 1) → ℝ :=
  Fin.snoc x xstar

@[simp] lemma configExtendρ_castSucc (ρ : Fin p → ℝ) (ε : ℝ) (j : Fin p) :
    configExtendρ ρ ε j.castSucc = ρ j := by
  simp [configExtendρ]

@[simp] lemma configExtendρ_last (ρ : Fin p → ℝ) (ε : ℝ) :
    configExtendρ ρ ε (Fin.last p) = ε := by
  simp [configExtendρ]

@[simp] lemma configExtendx_castSucc (x : Fin p → ℝ) (xstar : ℝ) (j : Fin p) :
    configExtendx x xstar j.castSucc = x j := by
  simp [configExtendx]

@[simp] lemma configExtendx_last (x : Fin p → ℝ) (xstar : ℝ) :
    configExtendx x xstar (Fin.last p) = xstar := by
  simp [configExtendx]

lemma configExtendρ_pos {ρ : Fin p → ℝ} (hρ : ∀ j, 0 < ρ j) {ε : ℝ}
    (hε : 0 < ε) : ∀ j : Fin (p + 1), 0 < configExtendρ ρ ε j := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa using hε
  | cast j => simpa using hρ j

lemma configExtendx_nonneg {x : Fin p → ℝ} (hx : ∀ j, 0 ≤ x j) {xstar : ℝ}
    (hxstar : 0 ≤ xstar) : ∀ j : Fin (p + 1), 0 ≤ configExtendx x xstar j := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa using hxstar
  | cast j => simpa using hx j

/-! ### Embedding `ConfigIdx k p ↪ ConfigIdx k (p + 1)` -/

/-- Keep `z₀`, each `z i`, and the original `y j` (the latter via `Fin.castSucc`). -/
def configIdxEmbed {k p : ℕ} (α : ConfigIdx k p) : ConfigIdx k (p + 1) :=
  (configIdxEquiv k (p + 1)).symm <|
    match configIdxEquiv k p α with
    | Sum.inl o => Sum.inl o
    | Sum.inr j => Sum.inr j.castSucc

lemma configIdxEmbed_z0 :
    configIdxEmbed (idxZ0 : ConfigIdx k p) = (idxZ0 : ConfigIdx k (p + 1)) := by
  simp [configIdxEmbed, idxZ0]

lemma configIdxEmbed_z (i : Fin k) :
    configIdxEmbed (idxZ (p := p) i) = idxZ (p := p + 1) i := by
  simp [configIdxEmbed, idxZ]

lemma configIdxEmbed_y (j : Fin p) :
    configIdxEmbed (idxY (k := k) j) = idxY (k := k) j.castSucc := by
  simp [configIdxEmbed, idxY]

lemma configIdxEmbed_val (α : ConfigIdx k p) :
    (configIdxEmbed α).val = α.val := by
  refine configIdx_cases (P := fun β => (configIdxEmbed β).val = β.val) α ?_ ?_ ?_
  · rw [configIdxEmbed_z0]
    simp [idxZ0_eq]
  · intro i
    simp [configIdxEmbed_z, idxZ_val]
  · intro j
    simp [configIdxEmbed_y, idxY_val]

lemma configIdxEmbed_lt_iff {α β : ConfigIdx k p} :
    configIdxEmbed α < configIdxEmbed β ↔ α < β := by
  rw [Fin.lt_def, Fin.lt_def, configIdxEmbed_val, configIdxEmbed_val]

lemma configIdxEmbed_injective :
    Injective (configIdxEmbed (k := k) (p := p)) := by
  intro α β h
  exact Fin.eq_of_val_eq ((configIdxEmbed_val α).symm.trans
    ((congrArg Fin.val h).trans (configIdxEmbed_val β)))

lemma configIdxEmbed_lt_idxY_last (α : ConfigIdx k p) :
    configIdxEmbed α < idxY (k := k) (Fin.last p) := by
  rw [Fin.lt_def, configIdxEmbed_val, idxY_val]
  have := α.isLt
  simp only [Fin.val_last]
  omega

/-! ### Original vectors are unchanged -/

lemma yVec_extend_castSucc (ρ : Fin p → ℝ) (x : Fin p → ℝ) (ε xstar : ℝ)
    (j : Fin p) :
    yVec (configExtendρ ρ ε) (configExtendx x xstar) j.castSucc = yVec ρ x j := by
  simp [yVec]

lemma configVec_extend_embed (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (ε xstar : ℝ)
    (α : ConfigIdx k p) :
    configVec s t (configExtendρ ρ ε) (configExtendx x xstar) (configIdxEmbed α) =
      configVec s t ρ x α := by
  refine configIdx_cases
    (P := fun β =>
      configVec s t (configExtendρ ρ ε) (configExtendx x xstar) (configIdxEmbed β) =
        configVec s t ρ x β) α ?_ ?_ ?_
  · rw [configIdxEmbed_z0, configVec_z0, configVec_z0]
  · intro i
    rw [configIdxEmbed_z, configVec_z, configVec_z]
  · intro j
    rw [configIdxEmbed_y, configVec_y, configVec_y, yVec_extend_castSucc]

/-- The Gram matrix among original indices is independent of `ε`. -/
lemma Xconfig_extend_submatrix (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (ε xstar : ℝ) :
    (Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar)).submatrix
        configIdxEmbed configIdxEmbed =
      Xconfig s t ρ x := by
  ext α β
  simp [submatrix_apply, Xconfig_apply, configVec_extend_embed]

lemma Xconfig_embed_ystar (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (ε xstar : ℝ)
    (α : ConfigIdx k p) :
    Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar)
        (configIdxEmbed α) (idxY (Fin.last p)) =
      Real.sqrt ε *
        (configVec s t ρ x α 0 * xstar + configVec s t ρ x α 1) := by
  rw [Xconfig_apply, configVec_extend_embed, configVec_y]
  simp [yVec, dotProduct, Fin.sum_univ_two]
  ring

/-! ### SC19 — positivity of the enlarged `H i` and `γ` -/

lemma configH_extend (t : Fin k → ℝ) (ρ x : Fin p → ℝ) (ε xstar : ℝ)
    (i : Fin k) :
    configH t (configExtendρ ρ ε) (configExtendx x xstar) i =
      configH t ρ x i + ε * (max (xstar - t i) 0) ^ 2 := by
  unfold configH
  rw [Fin.sum_univ_castSucc]
  simp

/-- Each new `H i` is strictly positive: `(x* - t i)_+ > 0` and `ε > 0`. -/
lemma configH_extend_pos (t : Fin k → ℝ) {ρ : Fin p → ℝ} (hρ : ∀ j, 0 < ρ j)
    (x : Fin p → ℝ) {ε : ℝ} (hε : 0 < ε) {xstar : ℝ}
    (hxstar : ∀ i, t i < xstar) (i : Fin k) :
    0 < configH t (configExtendρ ρ ε) (configExtendx x xstar) i := by
  rw [configH_extend]
  have hH : 0 ≤ configH t ρ x i := configH_nonneg t hρ x i
  have hdiff : 0 < xstar - t i := sub_pos.mpr (hxstar i)
  have hmax : max (xstar - t i) 0 = xstar - t i := max_eq_left hdiff.le
  have hsq : 0 < (max (xstar - t i) 0) ^ 2 := by
    rw [hmax]
    exact sq_pos_iff.mpr hdiff.ne'
  exact add_pos_of_nonneg_of_pos hH (mul_pos hε hsq)

/-- The enlarged configuration has `γ > 0` (needs at least one `z`-index). -/
lemma configγ_extend_pos [NeZero k] (s t : Fin k → ℝ) {ρ : Fin p → ℝ}
    (hρ : ∀ j, 0 < ρ j) (x : Fin p → ℝ) (hs : ∀ i, 0 < s i) {ε : ℝ}
    (hε : 0 < ε) {xstar : ℝ} (hxstar : ∀ i, t i < xstar) :
    0 < configγ s t (configExtendρ ρ ε) (configExtendx x xstar) := by
  have hρε := configExtendρ_pos hρ hε
  rw [configγ_eq_sum s t hρε]
  have : Nonempty (Fin k) := ⟨0⟩
  refine sum_pos (fun i _ => ?_) univ_nonempty
  exact div_pos (mul_pos (hs i) (configH_extend_pos t hρ x hε hxstar i))
    (configD_pos t hρε _ i)

lemma configH_extend_configXstar_pos (t : Fin k → ℝ) {ρ : Fin p → ℝ}
    (hρ : ∀ j, 0 < ρ j) (x : Fin p → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin k) :
    0 < configH t (configExtendρ ρ ε) (configExtendx x (configXstar t)) i :=
  configH_extend_pos t hρ x hε (lt_configXstar t) i

lemma configγ_extend_configXstar_pos [NeZero k] (s t : Fin k → ℝ)
    {ρ : Fin p → ℝ} (hρ : ∀ j, 0 < ρ j) (x : Fin p → ℝ) (hs : ∀ i, 0 < s i)
    {ε : ℝ} (hε : 0 < ε) :
    0 < configγ s t (configExtendρ ρ ε) (configExtendx x (configXstar t)) :=
  configγ_extend_pos s t hρ x hs hε (lt_configXstar t)

/-! ### SC20 — principal submatrices of `M` -/

lemma sum_configIdx_extend (f : ConfigIdx k (p + 1) → ℝ) :
    ∑ α : ConfigIdx k (p + 1), f α =
      ∑ α : ConfigIdx k p, f (configIdxEmbed α) +
        f (idxY (Fin.last p)) := by
  rw [sum_configIdx f, sum_configIdx (fun α => f (configIdxEmbed α)),
    Fin.sum_univ_castSucc (fun j => f (idxY j))]
  simp only [configIdxEmbed_z0, configIdxEmbed_z, configIdxEmbed_y]
  ac_rfl

/-- Off-diagonals of `M` among original indices ignore the new vertex. -/
lemma MX_extend_submatrix_of_ne (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (ε xstar : ℝ) {α β : ConfigIdx k p} (hne : α ≠ β) :
    M (Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar))
        (configIdxEmbed α) (configIdxEmbed β) =
      M (Xconfig s t ρ x) α β := by
  have hembed : configIdxEmbed α ≠ configIdxEmbed β :=
    fun h => hne (configIdxEmbed_injective h)
  rw [M_apply_of_ne _ (Xconfig_isSymm _ _ _ _) hembed,
    M_apply_of_ne _ (Xconfig_isSymm _ _ _ _) hne]
  simp [posPart_apply, Xconfig_apply, configVec_extend_embed]

/-- Diagonals pick up one extra Laplacian weight from the edge to `y*`. -/
lemma MX_extend_submatrix_diag_add (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (ε xstar : ℝ) (α : ConfigIdx k p) :
    M (Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar))
        (configIdxEmbed α) (configIdxEmbed α) =
      M (Xconfig s t ρ x) α α +
        if Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar)
            (configIdxEmbed α) (idxY (Fin.last p)) < 0 then
          Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar)
            (configIdxEmbed α) (idxY (Fin.last p)) ^ 2
        else 0 := by
  set Xe := Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar)
  set X0 := Xconfig s t ρ x
  set e := configIdxEmbed (k := k) (p := p)
  set ystar := idxY (k := k) (Fin.last p)
  have hX : ∀ β, Xe (e α) (e β) = X0 α β := fun β => by
    simp [Xe, X0, e, Xconfig_apply, configVec_extend_embed]
  have hXt : ∀ β, Xe (e β) (e α) = X0 β α := fun β => by
    simp [Xe, X0, e, Xconfig_apply, configVec_extend_embed]
  rw [M_diag, M_diag, hX α]
  have hUp :
      ∑ q : ConfigIdx k (p + 1),
          (if e α < q ∧ Xe (e α) q < 0 then Xe (e α) q ^ 2 else 0) =
        ∑ β : ConfigIdx k p,
            (if α < β ∧ X0 α β < 0 then X0 α β ^ 2 else 0) +
          (if Xe (e α) ystar < 0 then Xe (e α) ystar ^ 2 else 0) := by
    rw [sum_configIdx_extend]
    congr 1
    · refine Fintype.sum_congr _ _ fun β => ?_
      simp only [e, configIdxEmbed_lt_iff, hX]
    · simp only [ystar, e, configIdxEmbed_lt_idxY_last, true_and]
  have hLow :
      ∑ u : ConfigIdx k (p + 1),
          (if u < e α ∧ Xe u (e α) < 0 then Xe u (e α) ^ 2 else 0) =
        ∑ β : ConfigIdx k p,
            (if β < α ∧ X0 β α < 0 then X0 β α ^ 2 else 0) := by
    rw [sum_configIdx_extend]
    have hlast :
        (if idxY (k := k) (Fin.last p) < e α ∧
            Xe (idxY (Fin.last p)) (e α) < 0 then
          Xe (idxY (Fin.last p)) (e α) ^ 2 else 0) = 0 := by
      simp [e, not_lt.mpr (configIdxEmbed_lt_idxY_last α).le]
    rw [hlast, add_zero]
    refine Fintype.sum_congr _ _ fun β => ?_
    simp only [e, configIdxEmbed_lt_iff, hXt]
  rw [hUp, hLow]
  ac_rfl

/-- For `ε > 0` the extra diagonal term is `ε` times a constant (hence `O(ε)`). -/
lemma MX_extend_submatrix_diag (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {ε : ℝ} (hε : 0 < ε) (xstar : ℝ) (α : ConfigIdx k p) :
    M (Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar))
        (configIdxEmbed α) (configIdxEmbed α) =
      M (Xconfig s t ρ x) α α +
        if configVec s t ρ x α 0 * xstar + configVec s t ρ x α 1 < 0 then
          ε * (configVec s t ρ x α 0 * xstar + configVec s t ρ x α 1) ^ 2
        else 0 := by
  rw [MX_extend_submatrix_diag_add]
  set c := configVec s t ρ x α 0 * xstar + configVec s t ρ x α 1
  have hinner := Xconfig_embed_ystar s t ρ x ε xstar α
  have hpos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hneg :
      Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar)
          (configIdxEmbed α) (idxY (Fin.last p)) < 0 ↔ c < 0 := by
    rw [hinner]
    constructor
    · intro h
      nlinarith
    · intro h
      exact mul_neg_of_pos_of_neg hpos h
  by_cases hc : c < 0
  · simp only [hneg, hc, ite_true]
    rw [hinner, mul_pow, Real.sq_sqrt hε.le]
  · simp only [hneg, hc, ite_false]

/-- `M` of the enlargement, restricted to original indices, is the original
`M` plus a diagonal of order `ε`. (`M` of the large matrix then submatrix is
not `M` of the Gram submatrix, because Laplacian edges to `y*` affect
diagonals; `continuous_M` would only recover `M` of that submatrix.) -/
lemma MX_extend_submatrix (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {ε : ℝ} (hε : 0 < ε) (xstar : ℝ) :
    (M (Xconfig s t (configExtendρ ρ ε) (configExtendx x xstar))).submatrix
        configIdxEmbed configIdxEmbed =
      M (Xconfig s t ρ x) +
        diagonal fun α =>
          if configVec s t ρ x α 0 * xstar + configVec s t ρ x α 1 < 0 then
            ε * (configVec s t ρ x α 0 * xstar + configVec s t ρ x α 1) ^ 2
          else 0 := by
  ext α β
  rcases eq_or_ne α β with rfl | hne
  · simp [submatrix_apply, MX_extend_submatrix_diag s t ρ x hε xstar α,
      Matrix.diagonal]
  · simp [submatrix_apply, MX_extend_submatrix_of_ne s t ρ x ε xstar hne,
      Matrix.diagonal, hne]

/-- As `ε ↓ 0`, the principal submatrix of `M(X_ε)` converges to `M(X)`. -/
lemma tendsto_MX_extend_submatrix (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (xstar : ℝ) :
    Tendsto (fun ε : ℝ =>
        (M (Xconfig s t (configExtendρ ρ ε)
            (configExtendx x xstar))).submatrix
          configIdxEmbed configIdxEmbed)
      (𝓝[>] 0) (𝓝 (M (Xconfig s t ρ x))) := by
  refine tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => ?_
  rcases eq_or_ne α β with rfl | hne
  · set c := configVec s t ρ x α 0 * xstar + configVec s t ρ x α 1
    have hform :
        Tendsto (fun ε : ℝ =>
            M (Xconfig s t ρ x) α α +
              if c < 0 then ε * c ^ 2 else 0)
          (𝓝[>] 0) (𝓝 (M (Xconfig s t ρ x) α α)) := by
      by_cases hc : c < 0
      · simp only [hc, ite_true]
        have hlim :
            Tendsto (fun ε : ℝ => M (Xconfig s t ρ x) α α + ε * c ^ 2)
              (𝓝[>] 0) (𝓝 (M (Xconfig s t ρ x) α α + 0 * c ^ 2)) :=
          tendsto_const_nhds.add
            ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul
              tendsto_const_nhds)
        simpa using hlim
      · simp only [hc, ite_false, add_zero]
        exact tendsto_const_nhds
    have heq :
        (fun ε : ℝ =>
          (M (Xconfig s t (configExtendρ ρ ε)
              (configExtendx x xstar))).submatrix configIdxEmbed
              configIdxEmbed α α) =ᶠ[𝓝[>] (0 : ℝ)]
          fun ε => M (Xconfig s t ρ x) α α +
            if c < 0 then ε * c ^ 2 else 0 :=
      eventually_of_mem self_mem_nhdsWithin fun ε hε => by
        have hε' : 0 < ε := hε
        simp [submatrix_apply, MX_extend_submatrix_diag s t ρ x hε' xstar α, c]
    exact hform.congr' heq.symm
  · refine tendsto_const_nhds.congr fun ε => ?_
    simp [submatrix_apply, MX_extend_submatrix_of_ne s t ρ x ε xstar hne]

lemma tendsto_MX_extend_submatrix_configXstar (s t : Fin k → ℝ)
    (ρ x : Fin p → ℝ) :
    Tendsto (fun ε : ℝ =>
        (M (Xconfig s t (configExtendρ ρ ε)
            (configExtendx x (configXstar t)))).submatrix
          configIdxEmbed configIdxEmbed)
      (𝓝[>] 0) (𝓝 (M (Xconfig s t ρ x))) :=
  tendsto_MX_extend_submatrix s t ρ x (configXstar t)

/-! ### SC21 — `γ = 0` and `p = 0` by closedness -/

lemma isCompletelyPositive_MX_extend [NeZero k] (s t : Fin k → ℝ)
    (ρ x : Fin p → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hmono : Monotone t) (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j)
    {ε : ℝ} (hε : 0 < ε) :
    IsCompletelyPositive
      (M (Xconfig s t (configExtendρ ρ ε)
          (configExtendx x (configXstar t)))) :=
  isCompletelyPositive_M_Xconfig s t
    (configExtendρ ρ ε) (configExtendx x (configXstar t))
    hs ht hmono (configExtendρ_pos hρ hε)
    (configExtendx_nonneg hx (configXstar_nonneg ht))
    (configγ_extend_configXstar_pos s t hρ x hs hε)

lemma isCompletelyPositive_MX_extend_submatrix [NeZero k]
    (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (hs : ∀ i, 0 < s i)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) {ε : ℝ} (hε : 0 < ε) :
    IsCompletelyPositive
      ((M (Xconfig s t (configExtendρ ρ ε)
          (configExtendx x (configXstar t)))).submatrix
        configIdxEmbed configIdxEmbed) :=
  (isCompletelyPositive_MX_extend s t ρ x hs ht hmono hρ hx hε).submatrix
    configIdxEmbed

/-- If `γ = 0`, the original `M` is completely positive: enlarge, apply SC18,
restrict to original indices, and pass to the limit by closedness of CP. -/
lemma isCompletelyPositive_M_Xconfig_of_configγ_eq_zero [NeZero k]
    (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (hs : ∀ i, 0 < s i)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (_hγ : configγ s t ρ x = 0) :
    IsCompletelyPositive (M (Xconfig s t ρ x)) := by
  have hmem :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsCompletelyPositive
          ((M (Xconfig s t (configExtendρ ρ ε)
              (configExtendx x (configXstar t)))).submatrix
            configIdxEmbed configIdxEmbed) :=
    eventually_of_mem self_mem_nhdsWithin fun ε hε =>
      isCompletelyPositive_MX_extend_submatrix s t ρ x hs ht hmono hρ hx hε
  exact isClosed_isCompletelyPositive.mem_of_tendsto
    (tendsto_MX_extend_submatrix_configXstar s t ρ x) hmem

lemma configH_eq_zero_of_p_eq_zero (t : Fin k → ℝ) (ρ x : Fin 0 → ℝ)
    (i : Fin k) : configH t ρ x i = 0 := by
  simp [configH]

lemma configγ_eq_zero_of_p_eq_zero (s t : Fin k → ℝ) (ρ x : Fin 0 → ℝ) :
    configγ s t ρ x = 0 := by
  rw [configγ_eq_sum s t (fun j => j.elim0) x]
  exact Fintype.sum_eq_zero _ fun i => by simp [configH]

/-- The case `p = 0` has `H i = 0` for every `i`, hence `γ = 0`. -/
lemma isCompletelyPositive_M_Xconfig_of_p_eq_zero [NeZero k]
    (s t : Fin k → ℝ) (ρ x : Fin 0 → ℝ) (hs : ∀ i, 0 < s i)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t) :
    IsCompletelyPositive (M (Xconfig s t ρ x)) :=
  isCompletelyPositive_M_Xconfig_of_configγ_eq_zero s t ρ x hs ht hmono
    (fun j => j.elim0) (fun j => j.elim0)
    (configγ_eq_zero_of_p_eq_zero s t ρ x)

end

end BollobasNikiforov
