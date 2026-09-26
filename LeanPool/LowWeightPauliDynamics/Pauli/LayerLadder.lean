/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Pauli.LayerFlow
public import LeanPool.LowWeightPauliDynamics.Pauli.Truncate
public import LeanPool.LowWeightPauliDynamics.Constants.Entry
public import LeanPool.LowWeightPauliDynamics.Ladder.MultiJump

/-!
# The Pauli-layer inhabitant of the multi-jump ladder

This file instantiates the abstract `MultiLadder` of `Ladder/MultiJump.lean` with Pauli dynamics,
which formalizes the recurrence of `apd:rmk:multijump`. A trajectory `layerTraj` alternates
conjugation by a disjoint-support layer of Pauli rotations with truncation to an arbitrary
retained set of Paulis, and `layerN` records its high-weight norms above the rungs
`w_m = k_o + (m - 1) (k_h - 1)`. The layer-inflow bound `apd:thm:layer_inflow` of
`LayerFlow.lean` yields the multi-jump recurrence with the jump factors
`ε_j^{(m)} = (w_{m+j} a)^j / j!` (`epsJump`) and the entry factor
`E_m = ∑_{j ≥ m} ε_j^{(m)}` (`entryFactor`), where `a` bounds the absolute sines of all rotation
angles. The abstract first-passage majorant `apd:eq:composition_majorant` then applies.

## Main definitions

* `layerTraj Ls S O`: the trajectory `O_{T+1} = truncOp (S T) (layerConj (Ls T) O_T)`, `O_0 = O`.
* `layerN`: the rung masses of `layerTraj`: the Pauli norm at rung `0` (the reservoir) and the
  high-weight norm above `rungWeight ko kh m` at rung `m ≥ 1`.
* `pauliMultiLadder`: the resulting
  `MultiLadder (epsJump ..) (entryFactor ..) (pauliNorm O)`.

## Main results

* `summable_epsJump_tail`, `sum_Ico_epsJump_le_entryFactor`: for `β < 1` the entry series
  converges and dominates each of its finite partial sums.
* `highNorm_layerConj_le_multi`: the multi-jump inflow inequality of one layer, for an arbitrary
  operator.
* `layerN_step`: the recurrence of `apd:rmk:multijump` along `layerTraj`.
* `layerN_le_majorant`: the first-passage majorant `apd:eq:composition_majorant` for `layerTraj`.

## Implementation notes

The hypotheses of `pauliMultiLadder` are: every layer has pairwise disjoint supports and
Hermitian generators of weight at most `k_h`, with `2 ≤ k_h`; `|sin θ| ≤ a` for every angle;
`betaOf < 1`, which makes the entry series converge by comparison with a geometric series; and
the input observable is `k_o`-local. The fields `nonneg`, `init` and `step` of `MultiLadder` are
then theorems about `layerTraj`. The retained sets `S T` are arbitrary, so the construction covers
truncation after every layer as well as truncation only at step boundaries (`S T = univ` in
between).

`layerN` measures the operator that is *kept* along the trajectory. The operator discarded at a
step boundary, `Õ^{(d)}_{≥w*+1}` of `apd:eq:step_component`, is a different object: its norm is a
high-weight
norm before the cut. The two are related in `LayerError.lean`.
-/

public section

namespace Lean4LPD

open Finset

/-- The entry series `∑_i ε_{m+i}^{(m)}` of `apd:eq:composition_majorant` converges when
`β < 1`: by `epsJump_ratio` each term is at most `β` times the previous one, so the series is
dominated by a geometric series. -/
theorem summable_epsJump_tail {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {m : ℕ} (hm : 1 ≤ m) (hb : betaOf kh1 c a < 1) :
    Summable (fun i : ℕ => epsJump kh1 c a (m + i) m) := by
  have hb0 : 0 ≤ betaOf kh1 c a := by
    have hw := rungW_nonneg hkh hc (m := 2) (by omega)
    unfold betaOf
    positivity
  have hgeom : ∀ i : ℕ, epsJump kh1 c a (m + i) m ≤
      betaOf kh1 c a ^ i * epsJump kh1 c a m m := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        epsJump kh1 c a (m + (i + 1)) m ≤
            betaOf kh1 c a * epsJump kh1 c a (m + i) m := by
          simpa only [Nat.add_assoc] using epsJump_ratio hkh hc ha hm (Nat.le_add_right m i)
        _ ≤ betaOf kh1 c a * (betaOf kh1 c a ^ i * epsJump kh1 c a m m) :=
          mul_le_mul_of_nonneg_left ih hb0
        _ = betaOf kh1 c a ^ (i + 1) * epsJump kh1 c a m m := by rw [pow_succ]; ring
  exact Summable.of_nonneg_of_le
    (fun i => epsJump_nonneg hkh hc ha _ _ (by omega)) hgeom
    ((summable_geometric_of_lt_one hb0 hb).mul_right _)

/-- Every finite partial sum `∑_{m ≤ j < K} ε_j^{(m)}` is at most the entry factor `E_m` of
`apd:eq:composition_majorant`, which is defined as the infinite sum. -/
theorem sum_Ico_epsJump_le_entryFactor {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) {m : ℕ} (hm : 1 ≤ m)
    (hb : betaOf kh1 c a < 1) (K : ℕ) :
    (∑ j ∈ Ico m K, epsJump kh1 c a j m) ≤ entryFactor kh1 c a m := by
  rw [Finset.sum_Ico_eq_sum_range, entryFactor]
  exact (summable_epsJump_tail hkh hc ha hm hb).sum_le_tsum _
    (fun i _ => epsJump_nonneg hkh hc ha _ _ (by omega))

/-- The jump factors `ε_j^{(m)}` of `apd:rmk:multijump` are nonnegative for all indices. The
ladder recurrence only sums over `j ≥ 1`; the case `j = 0`, where the formula gives
`ε_0^{(m)} = 1`, is included because `MultiLadder.le_majorant` asks for nonnegativity at all
indices. -/
theorem epsJump_nonneg_all {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (j m : ℕ) : 0 ≤ epsJump kh1 c a j m := by
  cases j with
  | zero => simp [epsJump]
  | succ j => exact epsJump_nonneg hkh hc ha _ _ (by omega)

/-- The entry factors `E_m` of `apd:eq:composition_majorant` are nonnegative. -/
theorem entryFactor_nonneg_all {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (m : ℕ) : 0 ≤ entryFactor kh1 c a m :=
  tsum_nonneg fun i => epsJump_nonneg_all hkh hc ha (m + i) m

namespace PauliString

variable {n : ℕ}

/-- The natural-number rung threshold `rungWeight ko kh m = k_o + (m - 1) (k_h - 1)` equals the
real-valued rung `rungW (k_h - 1) (k_o / (k_h - 1)) m` that enters `epsJump`
(`apd:rmk:multijump`). Under `2 ≤ k_h` and `1 ≤ m` the natural subtractions `k_h - 1` and
`m - 1` are exact, so they agree with the real ones. -/
theorem rungWeight_cast_eq_rungW {ko kh m : ℕ} (hkh : 2 ≤ kh) (hm : 1 ≤ m) :
    (rungWeight ko kh m : ℝ) = rungW (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) m := by
  have hd : ((kh - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : kh - 1 ≠ 0)
  simp only [rungWeight, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hm, Nat.cast_one, rungW]
  field_simp
  ring

/-- Adding `j` rung spacings `k_h - 1` to rung `m ≥ 1` gives rung `m + j`, the index that
appears in the coefficient `ε_j^{(m)}` of `apd:rmk:multijump`. -/
theorem rungWeight_add_jump (ko kh m j : ℕ) (hm : 1 ≤ m) :
    rungWeight ko kh m + j * (kh - 1) = rungWeight ko kh (m + j) := by
  have h : m + j - 1 = (m - 1) + j := by omega
  simp only [rungWeight, h, Nat.add_mul, Nat.add_assoc]

/-- A `j`-jump with `j < m` enters rung `m` from the positive rung `m - j`
(`apd:rmk:multijump`). Since `j < m`, the natural subtraction `m - j` is exact. -/
theorem rungWeight_sub_jump (ko kh m j : ℕ) (hj : j < m) :
    rungWeight ko kh (m - j) + j * (kh - 1) = rungWeight ko kh m := by
  have h := rungWeight_add_jump ko kh (m - j) j (by omega)
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt hj)] using h

/-- The factorial coefficient of the layer-inflow bound `norm_layerInflowMatrix_le_factorial`
at the threshold `w_m` is exactly the jump factor `ε_j^{(m)}`
(`apd:eq:layer_inflow`; `apd:rmk:multijump`). -/
theorem layer_factor_eq_epsJump {ko kh m : ℕ} (hkh : 2 ≤ kh) (hm : 1 ≤ m)
    (a : ℝ) (j : ℕ) :
    ((((rungWeight ko kh m + j * (kh - 1) : ℕ) : ℝ) * a) ^ j / (Nat.factorial j : ℝ)) =
      epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m := by
  rw [rungWeight_add_jump ko kh m j hm, rungWeight_cast_eq_rungW hkh (by omega), epsJump]

/-- The truncated layer trajectory of `apd:rmk:multijump`: at time `T`, conjugate by the layer
`Ls T` and then project onto the retained set `S T`. The trajectory is defined at operator
level; its rung masses `layerN` are computed from it, and their recurrence is a theorem
(`layerN_step`). -/
@[expose]
noncomputable def layerTraj (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | T + 1 => truncOp (S T) (layerConj (Ls T) (layerTraj Ls S O T))

/-- The trajectory of `apd:rmk:multijump` starts at the input observable itself: no
truncation is applied at time `0`. -/
@[simp] theorem layerTraj_zero (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    layerTraj Ls S O 0 = O := rfl

/-- One step of the trajectory of `apd:rmk:multijump`: evolve through a layer, then cut. -/
theorem layerTraj_succ (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (T : ℕ) :
    layerTraj Ls S O (T + 1) = truncOp (S T) (layerConj (Ls T) (layerTraj Ls S O T)) := rfl

/-- Conjugation by a whole layer of Hermitian generators preserves the Pauli norm, by the
coefficient isometry `norm_layerAct`. This is one half of the reservoir bound in
`apd:rmk:multijump`. -/
theorem pauliNorm_layerConj (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (layerConj L O) = pauliNorm O := by
  rw [← norm_coeffVec, coeffVec_layerConj L hL, norm_layerAct L hL, norm_coeffVec]

/-- The Pauli norm along the truncated trajectory never exceeds that of the input, since layers
preserve it and truncation cannot increase it. This is the reservoir bound of
`apd:rmk:multijump`. -/
theorem pauliNorm_layerTraj_le (Ls : ℕ → List (PauliString n × ℝ))
    (hL : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) (S : ℕ → Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) (T : ℕ) :
    pauliNorm (layerTraj Ls S O T) ≤ pauliNorm O := by
  induction T with
  | zero => exact le_rfl
  | succ T ih =>
    rw [layerTraj_succ]
    exact (pauliNorm_truncOp_le _ _).trans ((pauliNorm_layerConj _ (hL T) _).le.trans ih)

/-- The rung masses of the truncated trajectory: the total Pauli norm at rung `0`, and the
high-weight norm above `rungWeight ko kh m` at rung `m ≥ 1`. This is the field `N` of the
`MultiLadder` for `apd:rmk:multijump`. -/
noncomputable def layerN (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh : ℕ) :
    ℕ → ℕ → ℝ
  | 0, T => pauliNorm (layerTraj Ls S O T)
  | m + 1, T => highNorm (rungWeight ko kh (m + 1)) (layerTraj Ls S O T)

/-- At every positive rung, `layerN` is the high-weight norm of the truncated trajectory
(`apd:rmk:multijump`). -/
theorem layerN_eq_highNorm (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh m T : ℕ)
    (hm : 1 ≤ m) :
    layerN Ls S O ko kh m T = highNorm (rungWeight ko kh m) (layerTraj Ls S O T) := by
  cases m with
  | zero => omega
  | succ m => rfl

/-- The rung masses of the truncated trajectory are nonnegative (`apd:rmk:multijump`). -/
theorem layerN_nonneg (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh m T : ℕ) :
    0 ≤ layerN Ls S O ko kh m T := by
  cases m with
  | zero => exact pauliNorm_nonneg _
  | succ m => exact highNorm_nonneg _ _

/-- A `k_o`-local input observable has no mass above any positive rung, since
`k_o ≤ rungWeight ko kh m`. This is the initial condition in `apd:rmk:multijump`. -/
theorem layerN_init (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ}
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (m : ℕ) (hm : 1 ≤ m) :
    layerN Ls S O ko kh m 0 = 0 := by
  rw [layerN_eq_highNorm _ _ _ _ _ _ _ hm, layerTraj_zero]
  refine highNorm_eq_zero _ fun p hp => hloc p (lt_of_le_of_lt ?_ hp)
  exact Nat.le_add_right ko ((m - 1) * (kh - 1))

/-- **Multi-jump flow through one layer.** For an arbitrary operator `O`, the high-weight norm
above rung `m` after a disjoint-support layer is at most its value before the layer, plus the
`j`-jump inflows `ε_j^{(m)}` from the positive rungs `m - j`, plus the entry factor `E_m` times
the Pauli norm of `O`. This derives the recurrence of `apd:rmk:multijump` from
`apd:thm:layer_inflow`: jumps with `j < m` are localized on rung `m - j`, and the finitely many
jumps with `j ≥ m` are bounded by the full norm and then by the infinite sum `E_m`. -/
theorem highNorm_layerConj_le_multi (L : List (PauliString n × ℝ)) {ko kh m : ℕ}
    (hkh : 2 ≤ kh) (hL : IsLayer kh (L.map Prod.fst))
    (hherm : ∀ g ∈ L, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm (rungWeight ko kh m) (layerConj L O) ≤
      highNorm (rungWeight ko kh m) O +
        (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
          highNorm (rungWeight ko kh (m - j)) O) +
        entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  let f : ℕ → ℝ := fun j =>
    ‖Lean4LPD.clm (layerInflowMatrix L (rungWeight ko kh m) j) (coeffVec O)‖
  have hf0 : f 0 = 0 := by
    simp [f, layerInflowMatrix_zero, Lean4LPD.clm]
  have hfnonneg (j : ℕ) : 0 ≤ f j := norm_nonneg _
  have hsmall (j : ℕ) (hj : j ∈ Ico 1 m) :
      f j ≤ epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        highNorm (rungWeight ko kh (m - j)) O := by
    have hj' := Finset.mem_Ico.1 hj
    have h := norm_layerInflowMatrix_clm_le_restr L hL ha hsin
      (rungWeight_sub_jump ko kh m j hj'.2).le (coeffVec O)
    rw [layer_factor_eq_epsJump hkh hm] at h
    exact h
  have hlarge (j : ℕ) :
      f j ≤ epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m * pauliNorm O := by
    have h := norm_layerInflowMatrix_clm_le L hL ha hsin
      (rungWeight ko kh m) j (coeffVec O)
    rw [layer_factor_eq_epsJump hkh hm, norm_coeffVec] at h
    exact h
  let K := max m (L.length + 1)
  have hmK : m ≤ K := le_max_left _ _
  have hlenK : L.length + 1 ≤ K := le_max_right _ _
  have hsum : (∑ j ∈ range (L.length + 1), f j) ≤
      (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        highNorm (rungWeight ko kh (m - j)) O) +
      entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by
    calc
      (∑ j ∈ range (L.length + 1), f j) ≤ ∑ j ∈ range K, f j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hlenK)
          (fun j _ _ => hfnonneg j)
      _ = (∑ j ∈ Ico 1 m, f j) + ∑ j ∈ Ico m K, f j := by
        rw [Finset.sum_range_eq_add_Ico f (by omega), hf0, zero_add,
          ← Finset.sum_Ico_consecutive f hm hmK]
      _ ≤ (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
          highNorm (rungWeight ko kh (m - j)) O) +
          ∑ j ∈ Ico m K, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
            pauliNorm O :=
        add_le_add (Finset.sum_le_sum hsmall) (Finset.sum_le_sum fun j _ => hlarge j)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (sum_Ico_epsJump_le_entryFactor hkh1 hc ha hm hb K) (pauliNorm_nonneg O))
  calc
    highNorm (rungWeight ko kh m) (layerConj L O) =
        ‖restr (highSet n (rungWeight ko kh m)) (layerAct L (coeffVec O))‖ := by
      rw [highNorm, coeffVec_layerConj L hherm]
    _ ≤ highNorm (rungWeight ko kh m) O + ∑ j ∈ range (L.length + 1), f j :=
      norm_restr_layerAct_le_sum_inflow L hherm _ _
    _ ≤ _ := by
      have h := add_le_add (le_refl (highNorm (rungWeight ko kh m) O)) hsum
      simpa only [add_assoc] using h

/-- **The multi-jump recurrence along the truncated layer trajectory.** This is the `step`
field of `MultiLadder` for `apd:rmk:multijump`, with the factorial jump factors `epsJump` and the
infinite-sum entry factor `entryFactor`. It combines `highNorm_layerConj_le_multi` with the
facts that truncation does not increase high-weight norms and that the Pauli norm along the
trajectory is at most that of the input. -/
theorem layerN_step (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((Ls T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ Ls T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (m T : ℕ) (hm : 1 ≤ m) :
    layerN Ls S O ko kh m (T + 1) ≤ layerN Ls S O ko kh m T +
      (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        layerN Ls S O ko kh (m - j) T) +
      entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  have hE : 0 ≤ entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m :=
    tsum_nonneg fun i => epsJump_nonneg hkh1 hc ha _ _ (by omega)
  rw [layerN_eq_highNorm _ _ _ _ _ _ _ hm, layerTraj_succ]
  have hflow := (highNorm_truncOp_le (rungWeight ko kh m) (S T) _).trans
    (highNorm_layerConj_le_multi (Ls T) hkh (hL T) (hherm T) ha (hsin T) hm hb
      (layerTraj Ls S O T))
  have hsum : (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
      highNorm (rungWeight ko kh (m - j)) (layerTraj Ls S O T)) =
      ∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        layerN Ls S O ko kh (m - j) T := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [layerN_eq_highNorm _ _ _ _ _ _ _ (by have := Finset.mem_Ico.1 hj; omega)]
  rw [hsum, ← layerN_eq_highNorm _ _ _ _ _ _ _ hm] at hflow
  exact hflow.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (pauliNorm_layerTraj_le Ls hherm S O T) hE))

/-- **The Pauli-layer `MultiLadder`**, with the jump factors `epsJump` and the entry factors
`entryFactor` of `apd:rmk:multijump`. It formalizes the recurrence underlying
`apd:eq:composition_majorant`. The fields `nonneg`, `init` and `step` are theorems about
`layerTraj`; the hypotheses are only the layer structure, Hermiticity of the generators, the sine
bound, `betaOf < 1` and `k_o`-locality of `O`.
The ladder controls the rung masses of the kept operator; the discarded operator `Õ^{(d)}_{≥w*+1}`
is
treated in `LayerError.lean`. -/
noncomputable def pauliMultiLadder (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((Ls T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ Ls T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    MultiLadder (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
      (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (pauliNorm O) where
  N := layerN Ls S O ko kh
  nonneg := layerN_nonneg Ls S O ko kh
  init := layerN_init Ls S hloc
  step := layerN_step Ls S O hkh hL hherm ha hsin hb

/-- The Pauli ladder records the rung masses of the kept layer trajectory. -/
@[simp] theorem pauliMultiLadder_N (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((Ls T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ Ls T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    (pauliMultiLadder Ls S O hkh hL hherm ha hsin hb hloc).N = layerN Ls S O ko kh := by rfl

/-- **The first-passage majorant for truncated Pauli layers.** The abstract bound
`MultiLadder.le_majorant` (`apd:eq:composition_majorant`) applied to `pauliMultiLadder`: the
mass of `layerTraj` above every rung `m ≥ 1` is at most the majorant built from `epsJump` and
`entryFactor`. -/
theorem layerN_le_majorant (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((Ls T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ Ls T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (T m : ℕ) (hm : 1 ≤ m) :
    layerN Ls S O ko kh m T ≤ MultiLadder.majorant
      (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
      (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (pauliNorm O) m T := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  exact (pauliMultiLadder Ls S O hkh hL hherm ha hsin hb hloc).le_majorant
    (epsJump_nonneg_all hkh1 (div_nonneg (Nat.cast_nonneg _) hkh1.le) ha) T m hm

end PauliString
end Lean4LPD
