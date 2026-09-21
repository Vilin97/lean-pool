/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weighted-parity combinatorics ([WP] §6.1)

The exponent-level layer of the weighted-parity example of
[WP] = `refs/AdicSpaces/uniform_sheafy_domains_with_reduced_example.tex` §6.

Monomials of the ambient restricted power-series ring are indexed by `t : ℕ →₀ ℕ`,
with index `0` playing the paper's `W` and index `n ≥ 1` playing `U_n`.  For a weight
function `w : ℕ → ℕ` (the paper's example is `w = id`; Tate extensions use a shifted
weight vanishing on finitely many indices) we define the parity weight

  `wpWeight w t = ∑_{n ≥ 1, t n odd} w n`      ([WP] eq:parity-weight, ω(ν))

and the support monoid

  `WPMem w t ↔ wpWeight w t ≤ t 0`             ([WP] eq:parity-monoid, S)

together with the head submonoids (tail support bounded by `N`) and the head/tail
splitting of exponents that underlies the `c₀`-decomposition of [WP] §6.4.
-/

@[expose] public section

namespace WeightedParity

open Finset

/-! ### The parity weight -/

/-- The parity weight `ω(ν) = ∑_{n ≥ 1, ν_n odd} w n` of an exponent `t : ℕ →₀ ℕ`
([WP] eq:parity-weight, with the generalized weight `w`; the paper's example is
`w = id`).  Index `0` (the `W`-variable) never contributes. -/
def wpWeight (w : ℕ → ℕ) (t : ℕ →₀ ℕ) : ℕ :=
  ∑ n ∈ t.support, if t n % 2 = 1 ∧ n ≠ 0 then w n else 0

/-- The parity weight can be computed over any finite superset of the support
(the extra terms vanish). -/
theorem wpWeight_eq_sum_subset (w : ℕ → ℕ) {t : ℕ →₀ ℕ} {S : Finset ℕ}
    (hS : t.support ⊆ S) :
    wpWeight w t = ∑ n ∈ S, if t n % 2 = 1 ∧ n ≠ 0 then w n else 0 := by
  refine Finset.sum_subset hS fun n _ hn => ?_
  have ht : t n = 0 := Finsupp.notMem_support_iff.mp hn
  simp [ht]

@[simp] theorem wpWeight_zero (w : ℕ → ℕ) : wpWeight w 0 = 0 := by
  simp [wpWeight]

/-- The weight only sees parity: it is unchanged by adding an even exponent vector.
Key computational form of [WP] eq:parity-weight. -/
theorem wpWeight_add_two_nsmul (w : ℕ → ℕ) (t s : ℕ →₀ ℕ) :
    wpWeight w (t + 2 • s) = wpWeight w t := by
  classical
  rw [two_nsmul]
  rw [wpWeight_eq_sum_subset w
      (Finsupp.support_add : (t + (s + s)).support ⊆ t.support ∪ (s + s).support),
    wpWeight_eq_sum_subset w
      (Finset.subset_union_left : t.support ⊆ t.support ∪ (s + s).support)]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmod : (t + (s + s)) n % 2 = t n % 2 := by
    simp only [Finsupp.add_apply]
    omega
  rw [hmod]

/-- Subadditivity `ω(ν+μ) ≤ ω(ν) + ω(μ)` ([WP] eq:omega-subadditive): `(ν+μ)_n` is odd
iff exactly one of `ν_n, μ_n` is odd. -/
theorem wpWeight_add_le (w : ℕ → ℕ) (s t : ℕ →₀ ℕ) :
    wpWeight w (s + t) ≤ wpWeight w s + wpWeight w t := by
  classical
  have hsub : (s + t).support ⊆ s.support ∪ t.support := Finsupp.support_add
  rw [wpWeight_eq_sum_subset w hsub,
    wpWeight_eq_sum_subset w (Finset.subset_union_left :
      s.support ⊆ s.support ∪ t.support),
    wpWeight_eq_sum_subset w (Finset.subset_union_right :
      t.support ⊆ s.support ∪ t.support), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases h0 : n = 0
  · simp [h0]
  · have hmod : (s + t) n = s n + t n := Finsupp.add_apply s t n
    have hs := Nat.mod_two_eq_zero_or_one (s n)
    have ht' := Nat.mod_two_eq_zero_or_one (t n)
    rcases hs with hs | hs <;> rcases ht' with ht' | ht' <;>
      simp only [hmod, h0, ne_eq, not_false_iff, and_true] <;>
      split_ifs <;> subst_vars <;> omega

/-- Disjoint-support additivity of the parity weight (used silently by
[WP] eq:parity-factorization and eq:tail-multiplication). -/
theorem wpWeight_add_of_disjoint (w : ℕ → ℕ) {s t : ℕ →₀ ℕ}
    (h : Disjoint s.support t.support) :
    wpWeight w (s + t) = wpWeight w s + wpWeight w t := by
  classical
  rw [wpWeight_eq_sum_subset w (Finsupp.support_add :
      (s + t).support ⊆ s.support ∪ t.support),
    Finset.sum_union h]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    have ht : t n = 0 := Finsupp.notMem_support_iff.mp
      (Finset.disjoint_left.mp h hn)
    simp [Finsupp.add_apply, ht]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hs : s n = 0 := Finsupp.notMem_support_iff.mp
      (Finset.disjoint_right.mp h hn)
    simp [Finsupp.add_apply, hs]

@[simp] theorem wpWeight_single (w : ℕ → ℕ) (n : ℕ) (k : ℕ) :
    wpWeight w (Finsupp.single n k) = if k % 2 = 1 ∧ n ≠ 0 then w n else 0 := by
  classical
  by_cases hk : k = 0
  · simp [hk]
  · rw [wpWeight, Finsupp.support_single_ne_zero n hk, Finset.sum_singleton,
      Finsupp.single_eq_same]

/-- The parity weight ignores the value at index `0`. -/
theorem wpWeight_update_zero (w : ℕ → ℕ) (t : ℕ →₀ ℕ) (k : ℕ) :
    wpWeight w (t.update 0 k) = wpWeight w t := by
  classical
  rw [wpWeight_eq_sum_subset w (Finset.subset_union_left :
      (t.update 0 k).support ⊆ (t.update 0 k).support ∪ t.support),
    wpWeight_eq_sum_subset w (Finset.subset_union_right :
      t.support ⊆ (t.update 0 k).support ∪ t.support)]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h0 : n = 0
  · simp [h0]
  · rw [Finsupp.update_apply, if_neg h0]

/-! ### The support monoid `S` -/

/-- Membership in the weighted-parity support monoid
`S = {(a,ν) : a ≥ ω(ν)}` ([WP] eq:parity-monoid): the `W`-exponent `t 0` dominates the
parity weight of the `U`-part. -/
def WPMem (w : ℕ → ℕ) (t : ℕ →₀ ℕ) : Prop :=
  wpWeight w t ≤ t 0

@[simp] theorem wpMem_zero (w : ℕ → ℕ) : WPMem w 0 := by
  simp [WPMem]

/-- `S` is closed under addition ([WP] line "The inequality (eq:omega-subadditive) shows
that `S` is closed under addition"). -/
theorem WPMem.add {w : ℕ → ℕ} {s t : ℕ →₀ ℕ} (hs : WPMem w s) (ht : WPMem w t) :
    WPMem w (s + t) := by
  refine (wpWeight_add_le w s t).trans ?_
  simpa [Finsupp.add_apply] using Nat.add_le_add hs ht

/-- The `W`-monomial exponents are in `S`. -/
theorem wpMem_single_zero (w : ℕ → ℕ) (k : ℕ) : WPMem w (Finsupp.single 0 k) := by
  simp [WPMem]

/-- The allowed `U_n`-monomial `W^{w n}·U_n` ([WP] `Y_n = W^n U_n` at `w = id`,
eq:finite-stage-substitution). -/
theorem wpMem_single_add_single (w : ℕ → ℕ) (n : ℕ) :
    WPMem w (Finsupp.single 0 (w n) + Finsupp.single n 1) := by
  classical
  by_cases h0 : n = 0
  · subst h0
    simpa [WPMem] using wpMem_single_zero w (w 0 + 1)
  · have hdisj : Disjoint (Finsupp.single 0 (w n)).support
        (Finsupp.single n 1).support := by
      by_cases hw0 : w n = 0
      · simp [hw0]
      · rw [Finsupp.support_single_ne_zero _ hw0,
          Finsupp.support_single_ne_zero _ (one_ne_zero)]
        simpa using fun h => h0 h.symm
    unfold WPMem
    rw [wpWeight_add_of_disjoint w hdisj]
    simp [Finsupp.add_apply, Finsupp.single_apply, h0, Ne.symm h0]

/-- Even pure-`U` exponents are in `S` ([WP] `Z_n = U_n²`). -/
theorem wpMem_two_nsmul_single (w : ℕ → ℕ) (n : ℕ) (k : ℕ) :
    WPMem w (2 • Finsupp.single n k) := by
  have h := wpWeight_add_two_nsmul w 0 (Finsupp.single n k)
  unfold WPMem
  rw [zero_add] at h
  simp [h]

/-! ### Heads ([WP] §6.1, finite stages) -/

/-- Membership in the `N`-th head: in `S`, with `U`-support contained in `{1,…,N}`
([WP] lem:finite-stage-normal-form — "the monomials in (eq:parity-monoid) involving
only `U_1,…,U_N`"). -/
def HeadMem (w : ℕ → ℕ) (N : ℕ) (t : ℕ →₀ ℕ) : Prop :=
  WPMem w t ∧ ∀ n, N < n → t n = 0

theorem HeadMem.wpMem {w : ℕ → ℕ} {N : ℕ} {t : ℕ →₀ ℕ} (h : HeadMem w N t) :
    WPMem w t := h.1

theorem HeadMem.add {w : ℕ → ℕ} {N : ℕ} {s t : ℕ →₀ ℕ}
    (hs : HeadMem w N s) (ht : HeadMem w N t) : HeadMem w N (s + t) :=
  ⟨hs.1.add ht.1, fun n hn => by
    rw [Finsupp.add_apply, hs.2 n hn, ht.2 n hn]⟩

theorem HeadMem.mono {w : ℕ → ℕ} {N M : ℕ} (hNM : N ≤ M) {t : ℕ →₀ ℕ}
    (h : HeadMem w N t) : HeadMem w M t :=
  ⟨h.1, fun n hn => h.2 n (lt_of_le_of_lt hNM hn)⟩

/-! ### Tails and the head/tail splitting ([WP] §6.4) -/

/-- A tail multi-index for the `N`-th head: supported on `{n : n > N}`
([WP] §6.4, `μ = (μ_n)_{n>N}`). -/
def IsTailIdx (N : ℕ) (μ : ℕ →₀ ℕ) : Prop :=
  ∀ n, n ≤ N → μ n = 0

/-- Tail multi-indices form an additive submonoid of the exponent monoid. -/
noncomputable def tailIdxSubmonoid (N : ℕ) : AddSubmonoid (ℕ →₀ ℕ) where
  carrier := {μ | IsTailIdx N μ}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {μ} {ν} hμ hν n hn => by
    rw [Finsupp.add_apply, hμ n hn, hν n hn]

/-- The type of tail multi-indices ([WP] §6.4). -/
def TailIdx (N : ℕ) : Type :=
  ↥(tailIdxSubmonoid N)

namespace TailIdx

noncomputable instance (N : ℕ) : AddCommMonoid (TailIdx N) :=
  inferInstanceAs (AddCommMonoid ↥(tailIdxSubmonoid N))

@[simp] theorem add_val {N : ℕ} (μ ν : TailIdx N) : (μ + ν).1 = μ.1 + ν.1 := rfl

@[simp] theorem zero_val {N : ℕ} : (0 : TailIdx N).1 = 0 := rfl

noncomputable instance (N : ℕ) : DecidableEq (TailIdx N) := Classical.decEq _

theorem prop {N : ℕ} (μ : TailIdx N) : IsTailIdx N μ.1 := μ.2

end TailIdx

/-- The exponent of the tail basis monomial `e_μ = W^{ω(μ)} U^μ`
([WP] eq:tail-basis, under the substitution eq:finite-stage-substitution). -/
noncomputable def tailShift (w : ℕ → ℕ) {N : ℕ} (μ : TailIdx N) : ℕ →₀ ℕ :=
  Finsupp.single 0 (wpWeight w μ.1) + μ.1

theorem wpMem_tailShift (w : ℕ → ℕ) {N : ℕ} (μ : TailIdx N) :
    WPMem w (tailShift w μ) := by
  classical
  have hμ0 : μ.1 0 = 0 := μ.prop 0 (Nat.zero_le N)
  have hdisj : Disjoint (Finsupp.single 0 (wpWeight w μ.1)).support μ.1.support := by
    by_cases hw0 : wpWeight w μ.1 = 0
    · simp [hw0]
    · rw [Finsupp.support_single_ne_zero _ hw0]
      simp [Finsupp.notMem_support_iff, hμ0]
  unfold WPMem tailShift
  rw [wpWeight_add_of_disjoint w hdisj]
  simp [Finsupp.add_apply, hμ0]

/-- The head part of an allowed exponent: restrict to indices `≤ N` and subtract the
tail weight from the `W`-exponent.  This is the exponent-level content of
[WP] eq:tail-decomposition. -/
noncomputable def headPart (w : ℕ → ℕ) (N : ℕ) (t : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  (t.filter fun n => n ≤ N).update 0 (t 0 - wpWeight w (t.filter fun n => N < n))

/-- The tail part of an exponent: restrict to indices `> N`. -/
noncomputable def tailPart (N : ℕ) (t : ℕ →₀ ℕ) : TailIdx N :=
  ⟨t.filter fun n => N < n, fun n hn => by
    classical
    rw [Finsupp.filter_apply, if_neg (by omega)]⟩

/-- The filter split of the parity weight:
`ω(t) = ω(t restricted to [0,N]) + ω(t restricted to (N,∞))`. -/
theorem wpWeight_filter_split (w : ℕ → ℕ) (N : ℕ) (t : ℕ →₀ ℕ) :
    wpWeight w t =
      wpWeight w (t.filter fun n => n ≤ N) +
        wpWeight w (t.filter fun n => N < n) := by
  classical
  have hrec : (t.filter fun n => n ≤ N) + (t.filter fun n => N < n) = t := by
    have := Finsupp.filter_add_filter_not t (fun n => n ≤ N)
    simpa [Nat.not_le] using this
  have hdisj : Disjoint (t.filter fun n => n ≤ N).support
      (t.filter fun n => N < n).support := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    rw [Finsupp.support_filter, Finset.mem_filter] at hn hn'
    omega
  rw [← hrec, wpWeight_add_of_disjoint w hdisj, hrec]

theorem headMem_headPart {w : ℕ → ℕ} {N : ℕ} {t : ℕ →₀ ℕ} (ht : WPMem w t) :
    HeadMem w N (headPart w N t) := by
  classical
  constructor
  · unfold WPMem headPart
    rw [wpWeight_update_zero, Finsupp.update_apply, if_pos rfl]
    have hsplit := wpWeight_filter_split w N t
    have := ht
    unfold WPMem at this
    omega
  · intro n hn
    unfold headPart
    rw [Finsupp.update_apply, if_neg (by omega), Finsupp.filter_apply,
      if_neg (by omega)]

/-- The head/tail reconstruction: every allowed exponent splits uniquely as
(head exponent) + (tail-basis exponent) ([WP] eq:tail-decomposition at the level of
monomials; uses disjoint-support additivity of `ω`). -/
theorem headPart_add_tailShift {w : ℕ → ℕ} {N : ℕ} {t : ℕ →₀ ℕ} (ht : WPMem w t) :
    headPart w N t + tailShift w (tailPart N t) = t := by
  classical
  have hsplit := wpWeight_filter_split w N t
  have hle : wpWeight w (t.filter fun n => N < n) ≤ t 0 := by
    have := ht; unfold WPMem at this; omega
  ext n
  simp only [Finsupp.add_apply, headPart, tailShift, tailPart, Finsupp.update_apply,
    Finsupp.filter_apply, Finsupp.single_apply]
  split_ifs <;> subst_vars <;> omega

/-- Uniqueness half of the splitting: a head exponent plus a tail-basis exponent
recovers its parts. -/
theorem tailPart_of_headMem_add {w : ℕ → ℕ} {N : ℕ} {h : ℕ →₀ ℕ} (hh : HeadMem w N h)
    (μ : TailIdx N) : tailPart N (h + tailShift w μ) = μ := by
  classical
  apply Subtype.ext
  ext n
  show ((h + tailShift w μ).filter fun n => N < n) n = μ.1 n
  by_cases hN : N < n
  · have hh0 : h n = 0 := hh.2 n hN
    simp only [Finsupp.filter_apply, Finsupp.add_apply, tailShift,
      Finsupp.single_apply, hh0]
    split_ifs <;> subst_vars <;> omega
  · have hμ0 : μ.1 n = 0 := μ.prop n (by omega)
    simp only [Finsupp.filter_apply, hμ0]
    split_ifs <;> subst_vars <;> omega

theorem headPart_of_headMem_add {w : ℕ → ℕ} {N : ℕ} {h : ℕ →₀ ℕ} (hh : HeadMem w N h)
    (μ : TailIdx N) : headPart w N (h + tailShift w μ) = h := by
  classical
  have htail : tailPart N (h + tailShift w μ) = μ := tailPart_of_headMem_add hh μ
  have hfil : (h + tailShift w μ).filter (fun n => N < n) = μ.1 := by
    have := congrArg Subtype.val htail
    simpa [tailPart] using this
  have hwfil : wpWeight w ((h + tailShift w μ).filter fun n => N < n) =
      wpWeight w μ.1 := by rw [hfil]
  simp only [tailShift] at hwfil
  have hμ0 : μ.1 0 = 0 := μ.prop 0 (Nat.zero_le N)
  ext n
  unfold headPart
  by_cases hN : N < n
  · have hh0 : h n = 0 := hh.2 n hN
    simp only [Finsupp.update_apply, Finsupp.filter_apply, Finsupp.add_apply,
      tailShift, Finsupp.single_apply, hh0]
    split_ifs <;> subst_vars <;> omega
  · have hμn : μ.1 n = 0 := μ.prop n (by omega)
    simp only [Finsupp.update_apply, Finsupp.filter_apply, Finsupp.add_apply,
      tailShift, Finsupp.single_apply, hμn, hμ0]
    split_ifs <;> subst_vars <;> omega

/-! ### The shifted weight (Tate extensions, [WP] §6.5 eq:strong-sheafy-decomposition) -/

/-- The weight for the Tate extension `𝒜⟨V_1,…,V_s⟩`: the first `s` `U`-variables are
freed (weight `0`, i.e. they become the auxiliary Tate variables `V_i`), the rest carry
the shifted original weight.  [WP] §6.5: "for auxiliary Tate variables `V_1,…,V_s` one
has, isometrically, `𝒜⟨V⟩ ≅ ⊕̂ 𝒜_N⟨V⟩ e_μ`" — in this formalization the Tate extension
is the same weighted-parity construction at the shifted weight. -/
def shiftWeight (w : ℕ → ℕ) (s : ℕ) : ℕ → ℕ :=
  fun n => if n ≤ s then 0 else w (n - s)

/-- Shifting by `0` does not change the parity weight (the two weight functions differ
only at index `0`, which `wpWeight` ignores). -/
@[simp] theorem wpWeight_shiftWeight_zero (w : ℕ → ℕ) (t : ℕ →₀ ℕ) :
    wpWeight (shiftWeight w 0) t = wpWeight w t := by
  classical
  unfold wpWeight
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h0 : n = 0
  · simp [h0]
  · have : ¬ n ≤ 0 := by omega
    simp only [shiftWeight, if_neg this, Nat.sub_zero]

end WeightedParity
