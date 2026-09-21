/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Grid.OmittedConditions
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Gap
import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Vanishing
import LeanPool.Nikodym.Nikodym.LowerBound.PrivateFamily

/-!
# A proper low-degree polynomial containing a private family

This file implements blueprint node **C04** of the lower-bound side of the sharp finite-field
Nikodym exponent.

Let `F ⊆ K`, `q = |F|`, let `I` be a prime ideal of `P_d = MvPolynomial (Fin d) K` of quotient
dimension `k = quotDim I ≥ 1` and degree `Δ = degree I`, and let `P : PrivateFamily F d E` be a
private family of `L = Fintype.card E > 0` lines whose line ideals all contain `I`. If
`8 d² ≤ r ≤ q` and `8 d² Δ q^k < r L`, then `PrivateFamily.exists_cut` produces a polynomial
`g ∉ I` of total degree at most `T = r (q - 1) - 1` lying in every line ideal `λ_e` of the family,
and such that `I + (g) ≠ P_d`.

The proof is the blueprint's. Each anchor `b e` lies on `I` (`I ≤ λ_e ≤ 𝔪_{ι(b e)}`), so by J02
it saves at least `c = (r + k - 1).choose k` jet conditions
(`PrivateFamily.card_mul_choose_le_sum_jetDim`). The Hilbert gap C03,
`r H_I(U) ≤ r H_I(T) + 4 d² Δ q^k c`, together with `8 d² Δ q^k < r L` makes the omitted-condition
inequality `H_I(U) < H_I(T) + ∑_{b ∈ B₀} j_{I, ι b}(r)` of G04 strict, which yields `g`. Since
`b e + a • v e ∉ B₀` for `a ≠ 0` (`PrivateFamily.add_smul_notMem_anchors`), L02 puts `g` in every
`λ_e`, and `I + (g) ≤ λ_e ≠ P_d` for any index `e`.

The blueprint hypothesis `k ≤ d` is automatic (`quotDim_le`) and `2 ≤ q` follows from
`32 ≤ 8 d² ≤ r ≤ q`; neither is assumed.
-/

namespace Nikodym.LowerBound

open Finset

variable {K : Type*} [Field K] {d : ℕ} {F : Type*} [Field F] [Fintype F] [Algebra F K]
variable {E : Type*} [Fintype E]

namespace PrivateFamily

omit [Fintype F] [Algebra F K] in
/-- Blueprint C04: the points `b e + a • v e` with `a ≠ 0` of the `e`-th line are not anchors of
the family. -/
theorem add_smul_notMem_anchors (P : PrivateFamily F d E) (e : E) {a : F} (ha : a ≠ 0) :
    P.b e + a • P.v e ∉ P.anchors := by
  intro h
  obtain ⟨f, hf⟩ := P.mem_anchors.mp h
  obtain rfl : f = e := P.anchor_private e f a hf
  have hv : P.v f = 0 := by simpa [ha] using hf
  exact P.v_ne_zero f hv

omit [Fintype F] in
/-- Blueprint C04: each anchor of a private family on the prime `I` saves at least
`c = (r + k - 1).choose k` jet conditions, so `L * c ≤ ∑_{b ∈ B₀} j_{I, ι b}(r)`. -/
theorem card_mul_choose_le_sum_jetDim (H : AlgebraInterface K d) (P : PrivateFamily F d E)
    {I : Ideal (MvPolynomial (Fin d) K)} (hI : I.IsPrime)
    (hIP : ∀ e, I ≤ P.lineIdeal (K := K) e) {r : ℕ} (hr : 1 ≤ r) :
    Fintype.card E * (r + quotDim I - 1).choose (quotDim I) ≤
      ∑ b ∈ P.anchors, jetDim I (liftPt b) r := by
  rw [← P.card_anchors, ← smul_eq_mul]
  refine card_nsmul_le_sum _ _ _ fun x hx ↦ ?_
  obtain ⟨e, rfl⟩ := P.mem_anchors.mp hx
  exact H.choose_le_jetDim I hI _ ((hIP e).trans (P.lineIdeal_le_pointIdeal_b e)) r hr

/-- Blueprint C04: a proper low-degree polynomial containing the family. Let `I` be prime of
quotient dimension `k ≥ 1` and degree `Δ`, contained in every line ideal of the private family
`P` of `L = Fintype.card E > 0` lines, and let `8 d² ≤ r ≤ q` with `8 d² Δ q^k < r L`. Then there
is `g ∉ I` of total degree at most `T = r (q - 1) - 1` lying in every `λ_e`, with
`I + (g) ≠ P_d`. -/
theorem exists_cut (H : AlgebraInterface K d) (P : PrivateFamily F d E)
    {I : Ideal (MvPolynomial (Fin d) K)} (hI : I.IsPrime) (hd : 2 ≤ d) (hk : 1 ≤ quotDim I)
    (hIP : ∀ e, I ≤ P.lineIdeal (K := K) e) [Nonempty E] {r : ℕ}
    (hr : 8 * d ^ 2 ≤ r) (hrq : r ≤ Fintype.card F)
    (hL : 8 * d ^ 2 * (degree I * Fintype.card F ^ quotDim I) < r * Fintype.card E) :
    ∃ g : MvPolynomial (Fin d) K, g ∉ I ∧ g.totalDegree ≤ r * (Fintype.card F - 1) - 1 ∧
      (∀ e, g ∈ P.lineIdeal (K := K) e) ∧ I ⊔ Ideal.span {g} ≠ ⊤ := by
  set q := Fintype.card F
  have hdd : 4 ≤ d ^ 2 := by nlinarith
  have hr1 : 1 ≤ r := by omega
  have hq : 2 ≤ q := by omega
  set k := quotDim I
  set c := (r + k - 1).choose k
  set M := degree I * q ^ k
  set L := Fintype.card E
  have hc : 0 < c := Nat.choose_pos (by omega)
  have hsum : L * c ≤ ∑ b ∈ P.anchors, jetDim I (liftPt b) r :=
    P.card_mul_choose_le_sum_jetDim H hI hIP hr1
  have hgap := hilbert_gap H hI hd hk hq hr hrq
  have h4 : 4 * d ^ 2 * M < r * L :=
    lt_of_le_of_lt (Nat.mul_le_mul_right M (Nat.mul_le_mul_right _ (by norm_num))) hL
  have hlt : hilbert I (q * (r - 1) + d * (q - 1)) <
      hilbert I (r * (q - 1) - 1) + ∑ b ∈ P.anchors, jetDim I (liftPt b) r := by
    refine Nat.lt_of_mul_lt_mul_left (a := r) ?_
    rw [mul_add]
    refine hgap.trans_lt (Nat.add_lt_add_left ?_ _)
    calc 4 * d ^ 2 * M * c < r * L * c := Nat.mul_lt_mul_of_pos_right h4 hc
      _ = r * (L * c) := mul_assoc _ _ _
      _ ≤ r * ∑ b ∈ P.anchors, jetDim I (liftPt b) r := Nat.mul_le_mul_left r hsum
  obtain ⟨g, hgT, hgI, hgjet⟩ :=
    exists_omitted_conditions I r P.anchors (r * (q - 1) - 1) hlt
  have hrq1 : 1 ≤ r * (q - 1) := Nat.mul_pos hr1 (by omega)
  have hline : ∀ e, g ∈ P.lineIdeal (K := K) e := fun e ↦
    mem_lineIdeal_of_jets_restrictTotalDegree (P.b e) (P.v e) (hIP e) r hgT hrq1
      fun a ha ↦ hgjet _ (P.add_smul_notMem_anchors e ha)
  refine ⟨g, hgI, mem_restrictTotalDegree_iff.mp hgT, hline, fun htop ↦ ?_⟩
  obtain ⟨e⟩ := ‹Nonempty E›
  refine P.lineIdeal_ne_top (K := K) e (top_le_iff.mp ?_)
  rw [← htop]
  exact sup_le (hIP e) ((Ideal.span_le).mpr (Set.singleton_subset_iff.mpr (hline e)))

/-- Blueprint C04: `PrivateFamily.exists_cut` with the nonemptiness of the family stated as
`0 < L = Fintype.card E`. -/
theorem exists_cut_of_card_pos (H : AlgebraInterface K d) (P : PrivateFamily F d E)
    {I : Ideal (MvPolynomial (Fin d) K)} (hI : I.IsPrime) (hd : 2 ≤ d) (hk : 1 ≤ quotDim I)
    (hIP : ∀ e, I ≤ P.lineIdeal (K := K) e) (hE : 0 < Fintype.card E) {r : ℕ}
    (hr : 8 * d ^ 2 ≤ r) (hrq : r ≤ Fintype.card F)
    (hL : 8 * d ^ 2 * (degree I * Fintype.card F ^ quotDim I) < r * Fintype.card E) :
    ∃ g : MvPolynomial (Fin d) K, g ∉ I ∧ g.totalDegree ≤ r * (Fintype.card F - 1) - 1 ∧
      (∀ e, g ∈ P.lineIdeal (K := K) e) ∧ I ⊔ Ideal.span {g} ≠ ⊤ :=
  haveI : Nonempty E := Fintype.card_pos_iff.mp hE
  P.exists_cut H hI hd hk hIP hr hrq hL

end PrivateFamily

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
