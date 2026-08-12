/-
Copyright (c) 2026 Dirk Kunert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dirk Kunert
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Period lengths of rational cut-and-project gap sequences

For coprime `α, β : ℕ` and a window parameter `ω ≥ 0`, the accepted lattice
points `(x, y) ∈ ℤ²` with `y ∈ [(α/β)(x-ω), (α/β)x + ω]` project onto the
line `f(x) = (α/β)x`; sorting the projections yields a periodic sequence of
consecutive gaps. Writing `N = ⌊ωα⌋ + ⌊ωβ⌋ + 1` and `D = α² + β²`, this file
proves the closed-form minimal periods for the residue model of that
construction: the paper's strip-to-residue reduction — enumerate `N`
consecutive residue classes modulo `D` under the multiplier `m = -α·β⁻¹` and
sort the hits — is taken here as the definition of the gap sequence
(`differenceSequenceUnit`), not derived from the lattice points. For it,
counting with multiplicity the period is `N` if `D ∤ N` and `N / D` if
`D ∣ N` (`main_theorem_geometric_concrete`), while discarding multiplicities
it is `N` if `N < D` and `1` otherwise (`set_main_theorem_geometric_concrete`).

The geometric data is threaded through the `GeometricProjection` typeclass,
whose concrete instance `GeometricProjectionConcrete` discharges its four
hypotheses; the identification of the residue model with the sorted lattice
projections is not formalised here. The irrational-slope case
(`LeanPool.CutAndProject.Irrational`) is built from the lattice directly.
-/

open Nat

namespace CutAndProject

/--
Lemma 4.1 from the paper.
Given α, β ∈ ℕ with gcd(α, β) = 1, we have gcd(α, α ^ 2 + β ^ 2) = 1.
-/
theorem coprime_alpha_D (α β : ℕ) (h : Nat.Coprime α β) : Nat.Coprime α (α ^ 2 + β ^ 2) := by
  have h1 : Nat.Coprime α (β ^ 2) := Nat.Coprime.pow_right 2 h
  have h2 : α ^ 2 + β ^ 2 = β ^ 2 + α * α := by ring
  rw [h2]
  exact (Nat.coprime_add_mul_right_right α (β ^ 2) α).mpr h1

/--
Symmetric part of Lemma 4.1.
-/
theorem coprime_beta_D (α β : ℕ) (h : Nat.Coprime α β) : Nat.Coprime β (α ^ 2 + β ^ 2) := by
  have h1 : Nat.Coprime β (α ^ 2) := Nat.Coprime.pow_right 2 h.symm
  have h2 : α ^ 2 + β ^ 2 = α ^ 2 + β * β := by ring
  rw [h2]
  exact (Nat.coprime_add_mul_right_right β (α ^ 2) β).mpr h1

lemma D_pos (α β : ℕ) (h : Nat.Coprime α β) : 0 < α ^ 2 + β ^ 2 := by
  rcases Nat.eq_zero_or_pos α with rfl | hα
  · rw [Nat.coprime_zero_left] at h
    rw [h]
    decide
  · have h1 : 0 < α ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero 2 (Nat.ne_of_gt hα))
    omega

/-- The image of `β` as a unit of `ZMod (α ^ 2 + β ^ 2)`; well-defined because `β` is coprime to
`α ^ 2 + β ^ 2`. -/
def betaUnit (α β : ℕ) (h : Nat.Coprime α β) : (ZMod (α ^ 2 + β ^ 2))ˣ :=
  ZMod.unitOfCoprime β (coprime_beta_D α β h)

/-- The image of `α` as a unit of `ZMod (α ^ 2 + β ^ 2)`; well-defined because `α` is coprime to
`α ^ 2 + β ^ 2`. -/
def alphaUnit (α β : ℕ) (h : Nat.Coprime α β) : (ZMod (α ^ 2 + β ^ 2))ˣ :=
  ZMod.unitOfCoprime α (coprime_alpha_D α β h)

/-- The geometric multiplier `m = -α · β⁻¹`, as a unit of `ZMod (α ^ 2 + β ^ 2)`. -/
def multiplier (α β : ℕ) (h : Nat.Coprime α β) : (ZMod (α ^ 2 + β ^ 2))ˣ :=
  (-1 : (ZMod (α ^ 2 + β ^ 2))ˣ) * (alphaUnit α β h) * (betaUnit α β h)⁻¹

/-- Multiplication by `multiplier` as a permutation of `ZMod (α ^ 2 + β ^ 2)`. -/
def residueBijection (α β : ℕ) (h : Nat.Coprime α β) :
    Equiv (ZMod (α ^ 2 + β ^ 2)) (ZMod (α ^ 2 + β ^ 2)) where
  toFun x := (multiplier α β h).val * x
  invFun x := (multiplier α β h)⁻¹.val * x
  left_inv x := by
    dsimp
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    dsimp
    rw [← mul_assoc, Units.mul_inv, one_mul]

section ResidueDistribution

/--
`countHits D r0 N x` counts the number of times the residue `x` (modulo `D`) is hit
by the arithmetic progression `r0, r0+1, ..., r0+N-1` of length `N`.
The residue distribution theorem (`residue_distribution`, Lemma 4.3 in the
paper) describes the multiset of multiplicities.
-/
def countHits (D : ℕ) (r0 N : ℕ) (x : ZMod D) : ℕ :=
  (Finset.range N).filter (fun (i : ℕ) => (r0 + i : ZMod D) = x) |>.card

lemma count_hits_D (D : ℕ) [NeZero D] (r0 : ℕ) (x : ZMod D) :
    countHits D r0 D x = 1 := by
  dsimp [countHits]
  have h_unique :
      (Finset.range D).filter (fun (i : ℕ) => (r0 + i : ZMod D) = x)
        = {(x - (r0 : ZMod D)).val} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hi_lt, hi_eq⟩
      have h1 : (i : ZMod D) = x - (r0 : ZMod D) := by
        calc (i : ZMod D) = (r0 : ZMod D) + i - (r0 : ZMod D) := by ring
             _ = x - (r0 : ZMod D) := by rw [hi_eq]
      have h2 : i = (i : ZMod D).val := by
        have h_mod : (i : ZMod D).val = i % D := ZMod.val_natCast D i
        rw [h_mod, Nat.mod_eq_of_lt hi_lt]
      rw [h2, h1]
    · rintro rfl
      have h_lt : (x - (r0 : ZMod D)).val < D := ZMod.val_lt (x - (r0 : ZMod D))
      refine ⟨h_lt, ?_⟩
      have h_cast : ((x - (r0 : ZMod D)).val : ZMod D) = x - (r0 : ZMod D) :=
        ZMod.natCast_zmod_val (x - (r0 : ZMod D))
      rw [h_cast]
      ring
  rw [h_unique, Finset.card_singleton]

lemma count_hits_lt_D (D : ℕ) (r0 N : ℕ) (h : N < D) (x : ZMod D) :
    countHits D r0 N x ≤ 1 := by
  dsimp [countHits]
  rw [Finset.card_le_one]
  intro i hi j hj
  rw [Finset.mem_filter, Finset.mem_range] at hi hj
  have h_eq : (r0 + i : ZMod D) = (r0 + j : ZMod D) := by rw [hi.2, hj.2]
  have h_eq2 : (i : ZMod D) = (j : ZMod D) := add_left_cancel h_eq
  have hi_lt : i < D := lt_trans hi.1 h
  have hj_lt : j < D := lt_trans hj.1 h
  have h_mod : i ≡ j [MOD D] := (ZMod.natCast_eq_natCast_iff i j D).mp h_eq2
  exact Nat.ModEq.eq_of_lt_of_lt h_mod hi_lt hj_lt
lemma sum_count_hits (D : ℕ) [NeZero D] (r0 N : ℕ) :
    ∑ x : ZMod D, countHits D r0 N x = N := by
  dsimp [countHits]
  have h := @Finset.card_eq_sum_card_fiberwise ℕ (ZMod D) _
    (fun i => (r0 + i : ZMod D)) (Finset.range N) Finset.univ (fun x _ => Finset.mem_univ _)
  rw [← h]
  exact Finset.card_range N

lemma count_hits_succ (D : ℕ) (r0 N : ℕ) (x : ZMod D) :
    countHits D r0 (N + 1) x = countHits D r0 N x + if (r0 + N : ZMod D) = x then 1 else 0 := by
  dsimp [countHits]
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · rfl

lemma count_hits_add (D : ℕ) (r0 N M : ℕ) (x : ZMod D) :
    countHits D r0 (N + M) x = countHits D r0 N x + countHits D (r0 + N) M x := by
  induction M with
  | zero =>
    dsimp [countHits]
    simp
  | succ k ih =>
    rw [Nat.add_succ, count_hits_succ, ih, count_hits_succ, ← add_assoc]
    congr 2
    congr 1
    push_cast
    ring

lemma count_hits_mul_D (D : ℕ) [NeZero D] (r0 q : ℕ) (x : ZMod D) :
    countHits D r0 (q * D) x = q := by
  induction q with
  | zero =>
    dsimp [countHits]
    simp
  | succ k ih =>
    rw [Nat.succ_mul, count_hits_add, ih, count_hits_D]

lemma count_hits_eq (D : ℕ) [NeZero D] (r0 N : ℕ) (x : ZMod D) :
    countHits D r0 N x = (N / D) + countHits D (r0 + (N / D) * D) (N % D) x := by
  have h_div : N = (N / D) * D + (N % D) := Nat.div_add_mod' N D |>.symm
  nth_rw 1 [h_div]
  rw [count_hits_add, count_hits_mul_D]

theorem residue_distribution (D : ℕ) [NeZero D] (r0 N : ℕ) :
    let q := N / D
    let s := N % D
    (Finset.univ.filter (fun x : ZMod D => countHits D r0 N x = q + 1)).card = s ∧
    (Finset.univ.filter (fun x : ZMod D => countHits D r0 N x = q)).card = D - s := by
  intro q s
  have h_s_lt : s < D := Nat.mod_lt N (NeZero.pos D)
  have hc_le : ∀ x, countHits D (r0 + q * D) s x ≤ 1 :=
    fun x => count_hits_lt_D D (r0 + q * D) s h_s_lt x
  have h_sum : ∑ x : ZMod D, countHits D (r0 + q * D) s x = s := sum_count_hits D (r0 + q * D) s
  have heq : ∀ x, countHits D r0 N x = q + countHits D (r0 + q * D) s x :=
    fun x => count_hits_eq D r0 N x
  have h_card1 :
      (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 1)).card = s := by
    calc (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 1)).card
      _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 1), 1 := by
        symm
        exact Finset.sum_const_nat (fun _ _ => rfl) |>.trans (mul_one _)
      _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 1),
            countHits D (r0 + q * D) s x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [hx.2]
      _ = ∑ x ∈ Finset.univ, countHits D (r0 + q * D) s x := by
        apply Finset.sum_subset
        · exact Finset.filter_subset _ _
        · intro x _ hx
          rw [Finset.mem_filter, not_and] at hx
          have h1 := hx (Finset.mem_univ x)
          have h2 := hc_le x
          omega
      _ = s := h_sum
  -- Cardinality of the count-0 set: complement of the count-1 set in ZMod D.
  have h_card0 :
      (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0)).card = D - s := by
    have h_union : Finset.univ =
        Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0)
          ∪ Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 1) := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
      have h2 := hc_le x
      omega
    have h_disj : Disjoint
        (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0))
        (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 1)) := by
      simp only [Finset.disjoint_filter]
      intro x _ h0 h1
      omega
    have h_card_univ := Finset.card_union_of_disjoint h_disj
    rw [← h_union] at h_card_univ
    have hd : (Finset.univ : Finset (ZMod D)).card = D := ZMod.card D
    have h_eq_card : D =
        (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0)).card + s := by
      calc D = (Finset.univ : Finset (ZMod D)).card := hd.symm
           _ = (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0)).card
               + (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 1)).card :=
             h_card_univ
           _ = (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0)).card
                 + s := by rw [h_card1]
    calc (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0)).card
      _ = (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0)).card + s - s :=
        by rw [Nat.add_sub_cancel]
      _ = D - s := by rw [← h_eq_card]
  -- Lift the count-(r0+qD,s) cardinalities back to count-(r0,N) via heq.
  constructor
  · have h_eq_set1 :
        (Finset.univ.filter (fun x : ZMod D => countHits D r0 N x = q + 1))
          = (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq x]
      omega
    rw [h_eq_set1, h_card1]
  · have h_eq_set0 :
        (Finset.univ.filter (fun x : ZMod D => countHits D r0 N x = q))
          = (Finset.univ.filter (fun x : ZMod D => countHits D (r0 + q * D) s x = 0)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq x]
      omega
    rw [h_eq_set0, h_card0]

/--
Specialisation of `residue_distribution` to the genuinely non-uniform
case `D ∤ N`: here `s = N % D` is positive, so the heavy classes form a
non-empty proper subset of `ZMod D`.
-/
theorem non_uniform_residue_distribution_of_not_dvd
    (D : ℕ) [NeZero D] (r0 N : ℕ) (h : ¬ D ∣ N) :
    let q := N / D
    let s := N % D
    0 < s ∧
    (Finset.univ.filter (fun x : ZMod D => countHits D r0 N x = q + 1)).card = s ∧
    (Finset.univ.filter (fun x : ZMod D => countHits D r0 N x = q)).card = D - s := by
  have h_pos : 0 < N % D :=
    Nat.pos_of_ne_zero (fun h_eq => h (Nat.dvd_of_mod_eq_zero h_eq))
  exact ⟨h_pos, (residue_distribution D r0 N).1, (residue_distribution D r0 N).2⟩

lemma count_hits_zero (D : ℕ) (r0 : ℕ) (x : ZMod D) :
    countHits D r0 0 x = 0 := by
  dsimp [countHits]
  rw [Finset.filter_empty, Finset.card_empty]

/--
Lemma (Degenerate Case): Uniform residue distribution.
If `D ∣ N`, then every residue class is hit exactly `N / D` times.
-/
theorem uniform_residue_distribution (D : ℕ) [NeZero D] (r0 N : ℕ) (h : D ∣ N) (x : ZMod D) :
    countHits D r0 N x = N / D := by
  have h_eq := count_hits_eq D r0 N x
  have h_mod : N % D = 0 := Nat.mod_eq_zero_of_dvd h
  rw [h_mod, count_hits_zero] at h_eq
  exact h_eq

/--
`countHitsUnit D u r0 N x` is the unit-aware variant of `countHits`:
it counts how many `i ∈ Finset.range N` satisfy `(u : ZMod D) * (r0 + i) = x`.

This corresponds to the geometric residue map `r ↦ m * r (mod D)` from the
paper, where `m = -α · β⁻¹ ∈ (ZMod D)ˣ` is the multiplier introduced via
`multiplier`. For `u = 1` it reduces to `countHits` (`count_hits_unit_one`);
in general it reduces to `countHits` after applying `u⁻¹` to the target
residue (`count_hits_unit_eq_count_hits`).
-/
def countHitsUnit (D : ℕ) (u : (ZMod D)ˣ) (r0 N : ℕ) (x : ZMod D) : ℕ :=
  (Finset.range N).filter (fun (i : ℕ) => (u : ZMod D) * (r0 + i : ZMod D) = x) |>.card

/--
Transfer lemma: counting hits of the multiplier-twisted progression
`u * (r0 + i)` against the target `x` equals counting hits of the plain
progression `r0 + i` against `u⁻¹ * x`. Multiplication by a unit is a
bijection of `ZMod D`, so the two counts agree pointwise.
-/
lemma count_hits_unit_eq_count_hits
    (D : ℕ) (u : (ZMod D)ˣ) (r0 N : ℕ) (x : ZMod D) :
    countHitsUnit D u r0 N x = countHits D r0 N ((u⁻¹ : (ZMod D)ˣ) * x) := by
  unfold countHitsUnit countHits
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
  intro _
  constructor
  · intro h
    rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    rw [h, ← mul_assoc, Units.mul_inv, one_mul]

/--
Specialisation of `count_hits_unit_eq_count_hits` to `u = 1`:
the unit-aware count with trivial multiplier reduces to `countHits`.
-/
lemma count_hits_unit_one (D : ℕ) (r0 N : ℕ) (x : ZMod D) :
    countHitsUnit D 1 r0 N x = countHits D r0 N x := by
  rw [count_hits_unit_eq_count_hits]
  simp

/--
Unit-aware analogue of `residue_distribution` (Lemma 4.3): the multiset of
multiplicities of `countHitsUnit D u r0 N` agrees with that of
`countHits D r0 N`. Multiplication by `u : (ZMod D)ˣ` is a bijection of
`ZMod D`, so the cardinalities of the level sets `{x | count = k}` are
preserved.
-/
theorem residue_distribution_unit (D : ℕ) [NeZero D] (u : (ZMod D)ˣ) (r0 N : ℕ) :
    let q := N / D
    let s := N % D
    (Finset.univ.filter (fun x : ZMod D => countHitsUnit D u r0 N x = q + 1)).card = s ∧
    (Finset.univ.filter (fun x : ZMod D => countHitsUnit D u r0 N x = q)).card = D - s := by
  intro q s
  have h_inj : Function.Injective (fun y : ZMod D => (u : ZMod D) * y) := by
    intro a b hab
    change (u : ZMod D) * a = (u : ZMod D) * b at hab
    have hcancel := congrArg (fun z : ZMod D => (u⁻¹ : (ZMod D)ˣ) * z) hab
    simp only [← mul_assoc, Units.inv_mul, one_mul] at hcancel
    exact hcancel
  have h_card : ∀ k,
      (Finset.univ.filter (fun x : ZMod D => countHitsUnit D u r0 N x = k)).card =
      (Finset.univ.filter (fun x : ZMod D => countHits D r0 N x = k)).card := by
    intro k
    have h_set :
        (Finset.univ.filter (fun x : ZMod D => countHitsUnit D u r0 N x = k)) =
        (Finset.univ.filter (fun y : ZMod D => countHits D r0 N y = k)).image
          (fun y : ZMod D => (u : ZMod D) * y) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_image, true_and]
      constructor
      · intro h
        rw [count_hits_unit_eq_count_hits] at h
        exact ⟨(u⁻¹ : (ZMod D)ˣ) * x, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
      · rintro ⟨y, hy, rfl⟩
        rw [count_hits_unit_eq_count_hits, ← mul_assoc, Units.inv_mul, one_mul]
        exact hy
    rw [h_set, Finset.card_image_of_injective _ h_inj]
  refine ⟨?_, ?_⟩
  · rw [h_card]; exact (residue_distribution D r0 N).1
  · rw [h_card]; exact (residue_distribution D r0 N).2

/--
Unit-aware analogue of `uniform_residue_distribution`: in the degenerate
case `D ∣ N`, every residue class is hit exactly `N / D` times under the
multiplier-twisted progression `u * (r0 + i)`.
-/
theorem uniform_residue_distribution_unit
    (D : ℕ) [NeZero D] (u : (ZMod D)ˣ) (r0 N : ℕ) (h : D ∣ N) (x : ZMod D) :
    countHitsUnit D u r0 N x = N / D := by
  rw [count_hits_unit_eq_count_hits]
  exact uniform_residue_distribution D r0 N h _

end ResidueDistribution

section Minimality

/-- The cyclic interval of length `s` based at `x0`: the image of `{0, …, s - 1}` under `i ↦ x0
+ i` in `ZMod D`. -/
def cyclicInterval (D s : ℕ) (x0 : ZMod D) : Finset (ZMod D) :=
  (Finset.range s).image (fun (i : ℕ) => x0 + (i : ZMod D))

lemma cyclic_interval_mem (D s : ℕ) (x0 : ZMod D) (x : ZMod D) :
    x ∈ cyclicInterval D s x0 ↔ ∃ (i : ℕ), i < s ∧ x = x0 + (i : ZMod D) := by
  dsimp [cyclicInterval]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

lemma count_hits_lt_D_eq_one (D s : ℕ) (r0 : ℕ) (h_s_lt : s < D) (x : ZMod D) :
    countHits D r0 s x = 1 ↔ x ∈ cyclicInterval D s (r0 : ZMod D) := by
  dsimp [countHits]
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩
    have h_a_in : a ∈ (Finset.range s).filter (fun (i : ℕ) => (r0 + i : ZMod D) = x) := by
      rw [ha]
      exact Finset.mem_singleton_self a
    rw [Finset.mem_filter, Finset.mem_range] at h_a_in
    rw [cyclic_interval_mem]
    use a
    constructor
    · exact h_a_in.1
    · exact h_a_in.2.symm
  · intro h_in
    rw [cyclic_interval_mem] at h_in
    rcases h_in with ⟨i, hi, rfl⟩
    use i
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, h_eq⟩
      have h_eq2 : ((r0 : ZMod D) + (j : ZMod D) : ZMod D)
          = ((r0 : ZMod D) + (i : ZMod D) : ZMod D) := h_eq
      have h_eq3 : (j : ZMod D) = (i : ZMod D) := add_left_cancel h_eq2
      have h_mod : j ≡ i [MOD D] := (ZMod.natCast_eq_natCast_iff j i D).mp h_eq3
      exact Nat.ModEq.eq_of_lt_of_lt h_mod (lt_trans hj h_s_lt) (lt_trans hi h_s_lt)
    · rintro rfl
      exact ⟨hi, rfl⟩

lemma heavy_set_is_cyclic_interval (D : ℕ) [NeZero D] (r0 N : ℕ) :
    let q := N / D
    let s := N % D
    ∀ x : ZMod D, countHits D r0 N x = q + 1
      ↔ x ∈ cyclicInterval D s ((r0 + q * D : ℕ) : ZMod D) := by
  intro q s x
  have h_s_lt : s < D := Nat.mod_lt N (NeZero.pos D)
  have h_eq := count_hits_eq D r0 N x
  constructor
  · intro h
    have h2 : q + countHits D (r0 + q * D) s x = q + 1 := by
      calc q + countHits D (r0 + q * D) s x = countHits D r0 N x := h_eq.symm
           _ = q + 1 := h
    have h3 : countHits D (r0 + q * D) s x = 1 := add_left_cancel h2
    exact (count_hits_lt_D_eq_one D s (r0 + q * D) h_s_lt x).mp h3
  · intro h
    have h3 : countHits D (r0 + q * D) s x = 1 :=
      (count_hits_lt_D_eq_one D s (r0 + q * D) h_s_lt x).mpr h
    rw [h_eq, h3]

/--
Unit-aware analogue of `heavy_set_is_cyclic_interval`: under the unit-twisted
count `countHitsUnit D u r0 N`, the heavy residues are precisely those `x`
for which `u⁻¹ * x` lies in the cyclic interval describing the heavy residues
of the untwisted `countHits D r0 N`. Equivalently, the unit-twisted heavy
set is the image of the untwisted heavy cyclic interval under multiplication
by `u`.

Proof: direct corollary of the transfer lemma `count_hits_unit_eq_count_hits`
and `heavy_set_is_cyclic_interval`.
-/
lemma heavy_set_unit_is_cyclic_interval (D : ℕ) [NeZero D] (u : (ZMod D)ˣ) (r0 N : ℕ) :
    let q := N / D
    let s := N % D
    ∀ x : ZMod D, countHitsUnit D u r0 N x = q + 1 ↔
      ((u⁻¹ : (ZMod D)ˣ) : ZMod D) * x ∈ cyclicInterval D s ((r0 + q * D : ℕ) : ZMod D) := by
  intro q s x
  rw [count_hits_unit_eq_count_hits]
  exact heavy_set_is_cyclic_interval D r0 N ((u⁻¹ : (ZMod D)ˣ) * x)


lemma right_boundary_exists (D s : ℕ) (x0 : ZMod D) (h_s_pos : 0 < s) (h_s_lt : s < D) :
    (x0 + (s - 1 : ℕ) : ZMod D) ∈ cyclicInterval D s x0 ∧
    (x0 + (s - 1 : ℕ) + 1 : ZMod D) ∉ cyclicInterval D s x0 := by
  constructor
  · rw [cyclic_interval_mem]
    use s - 1
    constructor
    · omega
    · rfl
  · intro h_in
    rw [cyclic_interval_mem] at h_in
    rcases h_in with ⟨i, hi, h_eq⟩
    have h_add : (x0 + (s - 1 : ℕ) + 1 : ZMod D) = x0 + s := by
      calc x0 + (s - 1 : ℕ) + 1 = x0 + ((s - 1 : ℕ) + 1 : ZMod D) := by ring
           _ = x0 + (((s - 1 + 1 : ℕ) : ZMod D)) := by push_cast; rfl
           _ = x0 + (s : ZMod D) := by
             congr 2
             have : s - 1 + 1 = s := Nat.sub_add_cancel h_s_pos
             rw [this]
    rw [h_add] at h_eq
    have h_eq2 : (s : ZMod D) = (i : ZMod D) := add_left_cancel h_eq
    have h_mod : s ≡ i [MOD D] := (ZMod.natCast_eq_natCast_iff s i D).mp h_eq2
    have h_eq3 : s = i := Nat.ModEq.eq_of_lt_of_lt h_mod h_s_lt (lt_trans hi h_s_lt)
    omega

lemma right_boundary_unique (D s : ℕ) (x0 : ZMod D) (h_s_pos : 0 < s)
    (_h_s_lt : s < D) (y : ZMod D)
    (hy_in : y ∈ cyclicInterval D s x0) (hy_next_notin : y + 1 ∉ cyclicInterval D s x0) :
    y = x0 + (s - 1 : ℕ) := by
  rw [cyclic_interval_mem] at hy_in
  rcases hy_in with ⟨i, hi, rfl⟩
  have h_eq : i = s - 1 := by
    by_contra h_neq
    have h_i_lt : i < s - 1 := by omega
    have h_next_in : x0 + (i : ZMod D) + 1 ∈ cyclicInterval D s x0 := by
      rw [cyclic_interval_mem]
      use i + 1
      constructor
      · omega
      · push_cast; ring
    exact hy_next_notin h_next_in
  rw [h_eq]

/--
Lemma (Minimality): A cyclic interval of length `s` with `0 < s < D`
cannot be invariant under any non-zero translation `τ`.
-/
lemma cyclic_interval_stabilizer_trivial (D s : ℕ) (x0 : ZMod D) (τ : ZMod D)
    (h_s_pos : 0 < s) (h_s_lt : s < D)
    (h_inv : ∀ x, x ∈ cyclicInterval D s x0 ↔ (x + τ) ∈ cyclicInterval D s x0) :
    τ = 0 := by
  let y := x0 + (s - 1 : ℕ)
  have hy_bound := right_boundary_exists D s x0 h_s_pos h_s_lt
  have h_y_sub_tau_in : y - τ ∈ cyclicInterval D s x0 := by
    have h1 := h_inv (y - τ)
    have h2 : y - τ + τ = y := sub_add_cancel y τ
    rw [h2] at h1
    exact h1.mpr hy_bound.1
  have h_y_sub_tau_next_notin : (y - τ) + 1 ∉ cyclicInterval D s x0 := by
    intro h_in
    have h1 := h_inv ((y - τ) + 1)
    have h2 : (y - τ) + 1 + τ = y + 1 := by
      calc (y - τ) + 1 + τ = y - τ + τ + 1 := by ring
           _ = y + 1 := by rw [sub_add_cancel]
    rw [h2] at h1
    have h_y_next_in := h1.mp h_in
    exact hy_bound.2 h_y_next_in
  have h_eq :=
    right_boundary_unique D s x0 h_s_pos h_s_lt (y - τ) h_y_sub_tau_in h_y_sub_tau_next_notin
  have h_eq2 : y - τ = y := h_eq
  exact sub_eq_self.mp h_eq2

end Minimality



/--
Definition of a sequence having a period L.
-/
def IsPeriod (s : ℤ → ℤ) (L : ℕ) : Prop :=
  L > 0 ∧ ∀ i : ℤ, s (i + (L : ℤ)) = s i

/-- `HasPeriodLength s L` states that `L` is the least positive period of the sequence `s`. -/
def HasPeriodLength (s : ℤ → ℤ) (L : ℕ) : Prop :=
  IsPeriod s L ∧ ∀ L' > 0, IsPeriod s L' → L ≤ L'

/--
Abstract interface for the combinatorial residue model obtained by reducing
the cut-and-project geometry to the distribution of `N` consecutive residue
classes modulo `D = α² + β²`. The four axioms are periodic-combinatorial
in nature; the geometric construction is not formalised from first
principles. Concrete instances are built from the geometric data via
`GeometricProjectionConcrete`.
-/
class GeometricProjection (α β : ℕ) (ω : ℝ) (s : ℤ → ℤ) [NeZero (α ^ 2 + β ^ 2)] where
  N_pos : 0 < (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  period_N : IsPeriod s (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  period_degenerate : (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat →
    HasPeriodLength s ((⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat / (α ^ 2 + β ^ 2))
  sigma_of_period : ∀ L > 0, IsPeriod s L →
    ∃ σ : ℕ, σ * (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat = L * (α ^ 2 + β ^ 2) ∧
    ∃ r0 : ℕ, ∀ x : ZMod (α ^ 2 + β ^ 2),
      countHits (α ^ 2 + β ^ 2) r0 (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
          (x + (σ : ZMod (α ^ 2 + β ^ 2)))
        = countHits (α ^ 2 + β ^ 2) r0 (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat x

open GeometricProjection

lemma generic_minimality (α β : ℕ) (ω : ℝ) (seq : ℤ → ℤ) [NeZero (α ^ 2 + β ^ 2)]
    [GeometricProjection α β ω seq] :
    let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    ¬ (D ∣ N) → ∀ L > 0, IsPeriod seq L → N ≤ L := by
  intro N D hdvd L hL_pos hL_period
  have hD : NeZero D := inferInstance
  have h_sigma := sigma_of_period (α:=α) (β:=β) (ω:=ω) (s:=seq) L hL_pos hL_period
  rcases h_sigma with ⟨σ, h_sigma_eq, r0, h_inv_count⟩
  let q := N / D
  let s := N % D
  have h_s_pos : 0 < s := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
  have h_s_lt : s < D := Nat.mod_lt N (Nat.pos_of_ne_zero (NeZero.ne D))
  have h_heavy_eq : ∀ x : ZMod D,
      countHits D r0 N x = q + 1 ↔ x ∈ cyclicInterval D s ((r0 + q * D : ℕ) : ZMod D) :=
    @heavy_set_is_cyclic_interval D hD r0 N
  have h_inv : ∀ x : ZMod D, x ∈ cyclicInterval D s ((r0 + q * D : ℕ) : ZMod D) ↔
                            (x + (σ : ZMod D))
                              ∈ cyclicInterval D s ((r0 + q * D : ℕ) : ZMod D) := by
    intro x
    rw [← h_heavy_eq x, ← h_heavy_eq (x + (σ : ZMod D))]
    rw [h_inv_count x]
  have h_sigma_mod : (σ : ZMod D) = 0 :=
    @cyclic_interval_stabilizer_trivial D s ((r0 + q * D : ℕ) : ZMod D) (σ : ZMod D)
      h_s_pos h_s_lt h_inv
  have h_sigma_dvd : D ∣ σ := by
    have h_cast : (σ : ZMod D) = 0 := h_sigma_mod
    exact (ZMod.natCast_eq_zero_iff σ D).mp h_cast
  rcases h_sigma_dvd with ⟨k, rfl⟩
  have h_eq : D * k * N = L * D := h_sigma_eq
  have h_eq2 : k * N * D = L * D := by
    calc k * N * D = D * k * N := by ring
         _ = L * D := h_eq
  have h_eq3 : k * N = L := mul_right_cancel₀ (NeZero.ne D) h_eq2
  have h_k_pos : 0 < k := by
    by_contra h_k
    have h_k0 : k = 0 := by omega
    rw [h_k0, zero_mul] at h_eq3
    omega
  have hN_pos : 0 < N := GeometricProjection.N_pos (s := seq)
  have h_N_le : N ≤ k * N := Nat.le_mul_of_pos_left N h_k_pos
  omega

open Classical in
/-- Running total of `countHits` over `Finset.range (x + 1)`: the number of projected points
with index in `[0, x]`. -/
noncomputable def cumulativeHits (α β : ℕ) (ω : ℝ) (x : ℕ) : ℕ :=
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  (Finset.range (x + 1)).sum (fun y => countHits D r0 N (y : ZMod D))

open Classical in
/-- The `k`-th sorted index: the least `x` whose cumulative hit count exceeds `k`. -/
noncomputable def V (α β : ℕ) (ω : ℝ) (k : ℕ) : ℕ :=
  if h : ∃ x, k < cumulativeHits α β ω x then
    Nat.find h
  else
    0

/-- The `i`-th value of the sorted multiset of projected residues, extended `D`-periodically to
all of `ℤ`. -/
noncomputable def sortedMultiset (α β : ℕ) (ω : ℝ) (i : ℤ) : ℤ :=
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  let D := α ^ 2 + β ^ 2
  let r := (i % (N : ℤ)).toNat
  let q := i / (N : ℤ)
  (V α β ω r : ℤ) + q * D

/--
The concrete difference sequence of the normalized residue model (`u = 1`).
`differenceSequenceUnit` with `u = multiplier α β h` is the residue-model
counterpart of the geometric gap sequence in the paper (the identification is
the paper's strip-to-residue reduction, stated as a definition here, not
proved); the two have the same period length but differ as sequences in
general.
-/
noncomputable def differenceSequence (α β : ℕ) (ω : ℝ) (i : ℤ) : ℤ :=
  sortedMultiset α β ω (i + 1) - sortedMultiset α β ω i

open Classical in
/--
Unit-aware concrete construction. `cumulativeHitsUnit α β ω u x` is the
total number of hits in the integer range `[0, x]` of the multiplier-twisted
arithmetic progression `u * (r0 + i)` for `i ∈ [0, N)`. With `u = 1` it
reduces to `cumulativeHits` (`cumulative_hits_unit_one`); with
`u = multiplier α β h` it realises the geometric residue map
`c_{r0+i} ≡ -αβ⁻¹·(r0 + i) (mod D)`, `i ∈ [0, N)`, from the paper.
-/
noncomputable def cumulativeHitsUnit (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (x : ℕ) : ℕ :=
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  (Finset.range (x + 1)).sum (fun y => countHitsUnit D u r0 N (y : ZMod D))

open Classical in
/-- Unit-twisted analogue of `V`, built from `cumulativeHitsUnit`. -/
noncomputable def VUnit (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (k : ℕ) : ℕ :=
  if h : ∃ x, k < cumulativeHitsUnit α β ω u x then
    Nat.find h
  else
    0

/-- Unit-twisted analogue of `sortedMultiset`, built from `VUnit`. -/
noncomputable def sortedMultisetUnit (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (i : ℤ) : ℤ :=
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  let D := α ^ 2 + β ^ 2
  let r := (i % (N : ℤ)).toNat
  let q := i / (N : ℤ)
  (VUnit α β ω u r : ℤ) + q * D

/--
Unit-aware concrete difference sequence. With `u = multiplier α β h_coprime`
this is the residue-model counterpart of the geometric gap sequence in the
paper (the strip-to-residue identification is definitional, not proved).
-/
noncomputable def differenceSequenceUnit (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (i : ℤ) : ℤ :=
  sortedMultisetUnit α β ω u (i + 1) - sortedMultisetUnit α β ω u i

/-- `u = 1` specialisation: the unit-aware cumulative count agrees with `cumulativeHits`. -/
lemma cumulative_hits_unit_one (α β : ℕ) (ω : ℝ) (x : ℕ) :
    cumulativeHitsUnit α β ω 1 x = cumulativeHits α β ω x := by
  unfold cumulativeHitsUnit cumulativeHits
  apply Finset.sum_congr rfl
  intro y _
  exact count_hits_unit_one _ _ _ _

lemma N_pos_concrete (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω) : 0 < (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat := by
  have h1 : 0 ≤ ⌊ω * α⌋ := Int.floor_nonneg.mpr (mul_nonneg h_ω (Nat.cast_nonneg α))
  have h2 : 0 ≤ ⌊ω * β⌋ := Int.floor_nonneg.mpr (mul_nonneg h_ω (Nat.cast_nonneg β))
  omega

lemma period_N_concrete (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω) :
    let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
    IsPeriod (differenceSequence α β ω) N := by
  intro N
  unfold IsPeriod
  constructor
  · exact N_pos_concrete α β ω h_ω
  · intro i
    dsimp only [differenceSequence, sortedMultiset]
    have hN : 0 < N := N_pos_concrete α β ω h_ω
    have hN_ne : (N : ℤ) ≠ 0 := by omega
    have h_mod1 : (i + (N : ℤ) + 1) % (N : ℤ) = (i + 1) % (N : ℤ) := by
      have h_eq : i + (N : ℤ) + 1 = i + 1 + (N : ℤ) := by omega
      rw [h_eq]
      have hm1 : (i + 1 + (N : ℤ)) % (N : ℤ)
          = ((i + 1) % (N : ℤ) + (N : ℤ) % (N : ℤ)) % (N : ℤ) :=
        Int.add_emod (i + 1) (N : ℤ) (N : ℤ)
      have hm2 : (N : ℤ) % (N : ℤ) = 0 := Int.emod_self
      have hm3 : ((i + 1) % (N : ℤ)) % (N : ℤ) = (i + 1) % (N : ℤ) := Int.emod_emod (i + 1) (N : ℤ)
      rw [hm2, add_zero, hm3] at hm1
      exact hm1
    have h_mod2 : (i + (N : ℤ)) % (N : ℤ) = i % (N : ℤ) := by
      have hm1 : (i + (N : ℤ)) % (N : ℤ) = (i % (N : ℤ) + (N : ℤ) % (N : ℤ)) % (N : ℤ) :=
        Int.add_emod i (N : ℤ) (N : ℤ)
      have hm2 : (N : ℤ) % (N : ℤ) = 0 := Int.emod_self
      have hm3 : (i % (N : ℤ)) % (N : ℤ) = i % (N : ℤ) := Int.emod_emod i (N : ℤ)
      rw [hm2, add_zero, hm3] at hm1
      exact hm1
    have h_div1 : (i + (N : ℤ) + 1) / (N : ℤ) = (i + 1) / (N : ℤ) + 1 := by
      have h_eq : i + (N : ℤ) + 1 = i + 1 + (N : ℤ) := by omega
      rw [h_eq]
      have hd1 : (i + 1 + (N : ℤ)) / (N : ℤ) = (i + 1) / (N : ℤ) + (N : ℤ) / (N : ℤ) :=
        Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ))
      have hd2 : (N : ℤ) / (N : ℤ) = 1 := Int.ediv_self hN_ne
      rw [hd2] at hd1
      exact hd1
    have h_div2 : (i + (N : ℤ)) / (N : ℤ) = i / (N : ℤ) + 1 := by
      have hd1 : (i + (N : ℤ)) / (N : ℤ) = i / (N : ℤ) + (N : ℤ) / (N : ℤ) :=
        Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ))
      have hd2 : (N : ℤ) / (N : ℤ) = 1 := Int.ediv_self hN_ne
      rw [hd2] at hd1
      exact hd1
    rw [h_mod1, h_mod2, h_div1, h_div2]
    ring

/--
Helper: sortedMultiset shifts by D when index shifts by N.
-/
lemma sorted_multiset_add_N (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω) (i : ℤ) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    sortedMultiset α β ω (i + ↑N) = sortedMultiset α β ω i + ↑D := by
  intro N D
  -- sortedMultiset(i + N) = V((i+N) % N) + ((i+N)/N) * D
  --                        = V(i % N) + (i/N + 1) * D
  --                        = V(i % N) + (i/N) * D + D
  --                        = sortedMultiset(i) + D
  dsimp only [sortedMultiset]
  have hN : 0 < N := N_pos_concrete α β ω h_ω
  have hN_ne : (N : ℤ) ≠ 0 := by omega
  have h_mod : (i + (N : ℤ)) % (N : ℤ) = i % (N : ℤ) := by
    have hm1 : (i + (N : ℤ)) % (N : ℤ) =
        (i % (N : ℤ) + (N : ℤ) % (N : ℤ)) % (N : ℤ) :=
      Int.add_emod i (N : ℤ) (N : ℤ)
    have hm2 : (N : ℤ) % (N : ℤ) = 0 := Int.emod_self
    have hm3 : (i % (N : ℤ)) % (N : ℤ) = i % (N : ℤ) :=
      Int.emod_emod i (N : ℤ)
    rw [hm2, add_zero, hm3] at hm1; exact hm1
  have h_div : (i + (N : ℤ)) / (N : ℤ) = i / (N : ℤ) + 1 := by
    have hd1 : (i + (N : ℤ)) / (N : ℤ) =
        i / (N : ℤ) + (N : ℤ) / (N : ℤ) :=
      Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ))
    have hd2 : (N : ℤ) / (N : ℤ) = 1 := Int.ediv_self hN_ne
    rw [hd2] at hd1; exact hd1
  rw [h_mod, h_div]; ring

/--
Unit-aware analogue of `sorted_multiset_add_N`. Purely structural — only
uses the `q*N + r` decomposition that defines `sortedMultisetUnit`.
-/
lemma sorted_multiset_unit_add_N (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (i : ℤ) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    sortedMultisetUnit α β ω u (i + ↑N) = sortedMultisetUnit α β ω u i + ↑D := by
  intro N D
  dsimp only [sortedMultisetUnit]
  have hN : 0 < N := N_pos_concrete α β ω h_ω
  have hN_ne : (N : ℤ) ≠ 0 := by omega
  have h_mod : (i + (N : ℤ)) % (N : ℤ) = i % (N : ℤ) := by
    have hm1 : (i + (N : ℤ)) % (N : ℤ) =
        (i % (N : ℤ) + (N : ℤ) % (N : ℤ)) % (N : ℤ) :=
      Int.add_emod i (N : ℤ) (N : ℤ)
    have hm2 : (N : ℤ) % (N : ℤ) = 0 := Int.emod_self
    have hm3 : (i % (N : ℤ)) % (N : ℤ) = i % (N : ℤ) :=
      Int.emod_emod i (N : ℤ)
    rw [hm2, add_zero, hm3] at hm1; exact hm1
  have h_div : (i + (N : ℤ)) / (N : ℤ) = i / (N : ℤ) + 1 := by
    have hd1 : (i + (N : ℤ)) / (N : ℤ) =
        i / (N : ℤ) + (N : ℤ) / (N : ℤ) :=
      Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ))
    have hd2 : (N : ℤ) / (N : ℤ) = 1 := Int.ediv_self hN_ne
    rw [hd2] at hd1; exact hd1
  rw [h_mod, h_div]; ring

/--
Helper: If the difference sequence has period L, the sortedMultiset shift
by L is constant (independent of i).

Proof idea: Define f(i) = sortedMultiset(i+L) - sortedMultiset(i).
Then f(i+1) - f(i) = differenceSequence(i+L) - differenceSequence(i) = 0
by periodicity. So f is constant = f(0).
-/
lemma sorted_shift_constant (α β : ℕ) (ω : ℝ)
    (L : ℕ) (hL : IsPeriod (differenceSequence α β ω) L) (i : ℤ) :
    sortedMultiset α β ω (i + ↑L) - sortedMultiset α β ω i =
    sortedMultiset α β ω ↑L - sortedMultiset α β ω 0 := by
  -- f(i) := sortedMultiset(i + L) - sortedMultiset(i) is constant
  -- because f(i+1) - f(i) = diff_seq(i+L) - diff_seq(i) = 0.
  -- Step lemma: f(j+1) = f(j) where f(j) = sorted(j+L) - sorted(j)
  have h_step : ∀ j : ℤ,
      sortedMultiset α β ω (j + 1 + ↑L) - sortedMultiset α β ω (j + 1) =
      sortedMultiset α β ω (j + ↑L) - sortedMultiset α β ω j := by
    intro j
    have hper := hL.2 j
    simp only [differenceSequence] at hper
    have h1 : j + 1 + ↑L = j + ↑L + 1 := by ring
    rw [h1]; linarith
  -- Forward: f(n) = f(0) for n : ℕ
  have h_nat : ∀ n : ℕ, sortedMultiset α β ω (↑n + ↑L) - sortedMultiset α β ω ↑n =
      sortedMultiset α β ω ↑L - sortedMultiset α β ω 0 := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      have := h_step ↑k
      have h1 : (↑k : ℤ) + 1 + ↑L = ↑(k + 1) + ↑L := by push_cast; ring
      have h2 : (↑k : ℤ) + 1 = ↑(k + 1) := by push_cast; ring
      rw [h1, h2] at this; linarith
  -- Backward: f(-n) = f(0) for n : ℕ
  have h_neg : ∀ n : ℕ, sortedMultiset α β ω (-↑n + ↑L) - sortedMultiset α β ω (-↑n) =
      sortedMultiset α β ω ↑L - sortedMultiset α β ω 0 := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      -- h_step at j = -↑k - 1 gives:
      -- sorted(-↑k - 1 + 1 + L) - sorted(-↑k - 1 + 1) = sorted(-↑k - 1 + L) - sorted(-↑k - 1)
      -- i.e., sorted(-↑k + L) - sorted(-↑k) = sorted(-↑(k+1) + L) - sorted(-↑(k+1))
      have h_eq : sortedMultiset α β ω (-↑k + ↑L) - sortedMultiset α β ω (-↑k) =
          sortedMultiset α β ω (-↑(k + 1) + ↑L) - sortedMultiset α β ω (-↑(k + 1)) := by
        have := h_step (-↑(k + 1))
        have ha : (-↑(k + 1) : ℤ) + 1 + ↑L = -↑k + ↑L := by push_cast; omega
        have hb : (-↑(k + 1) : ℤ) + 1 = -↑k := by push_cast; omega
        simp only [hb] at this; linarith
      linarith
  -- Case split on i
  cases i with
  | ofNat n => exact h_nat n
  | negSucc n =>
    have : (Int.negSucc n : ℤ) = -↑(n + 1) := by omega
    simp only [this]
    exact h_neg (n + 1)

/--
Helper: N * shift = L * D.
From sortedMultiset(i+N) = sortedMultiset(i) + D and
sortedMultiset(i+L) = sortedMultiset(i) + σ, applied NL times both ways.
-/
lemma shift_times_N_eq (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (L : ℕ) (hL : IsPeriod (differenceSequence α β ω) L) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    let σ := sortedMultiset α β ω ↑L - sortedMultiset α β ω 0
    ↑N * σ = ↑L * ↑D := by
  intro N D σ
  -- Iterate the L-shift N times: sorted(N*L) = sorted(0) + N*σ
  have h_shift_L : ∀ n : ℕ, sortedMultiset α β ω (↑n * ↑L) =
      sortedMultiset α β ω 0 + ↑n * σ := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      have hsc := sorted_shift_constant α β ω L hL (↑k * ↑L)
      -- hsc : sorted(k*L + L) - sorted(k*L) = σ
      -- Goal: sorted((k+1)*L) = sorted(0) + (k+1)*σ
      -- Since (k+1)*L = k*L + L and sorted(k*L) = sorted(0) + k*σ:
      have h_eq : (↑(k + 1) : ℤ) * ↑L = ↑k * ↑L + ↑L := by push_cast; ring
      rw [h_eq]; push_cast at ih ⊢; linarith
  -- Iterate the N-shift L times: sorted(L*N) = sorted(0) + L*D
  have h_shift_N : ∀ n : ℕ, sortedMultiset α β ω (↑n * ↑N) =
      sortedMultiset α β ω 0 + ↑n * ↑D := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      have hsa : sortedMultiset α β ω (↑k * ↑N + ↑N) =
          sortedMultiset α β ω (↑k * ↑N) + ↑D :=
        sorted_multiset_add_N α β ω h_ω (↑k * (↑N : ℤ))
      have h_eq : (↑(k + 1) : ℤ) * ↑N = ↑k * ↑N + ↑N := by push_cast; ring
      have h_eq2 : (↑(k + 1) : ℤ) * ↑D = ↑k * ↑D + ↑D := by push_cast; ring
      rw [h_eq]; linarith
  -- N*L = L*N, so sorted(N*L) = sorted(L*N), giving N*σ = L*D
  have h1 := h_shift_L N
  have h2 := h_shift_N L
  have h3 : (↑N : ℤ) * ↑L = ↑L * ↑N := by ring
  rw [h3] at h1; linarith

/--
Helper: the shift σ is nonneg (sortedMultiset is non-decreasing).
-/
lemma shift_nonneg (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (L : ℕ) (hL_pos : 0 < L) (hL : IsPeriod (differenceSequence α β ω) L) :
    0 ≤ sortedMultiset α β ω ↑L - sortedMultiset α β ω 0 := by
  -- N * σ = L * D with L, D, N > 0, so σ ≥ 0.
  set σ := sortedMultiset α β ω ↑L - sortedMultiset α β ω 0
  have hN_pos : (0 : ℤ) < ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by
    exact_mod_cast N_pos_concrete α β ω h_ω
  have h_eq : ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat * σ =
      ↑L * ↑(α ^ 2 + β ^ 2) :=
    shift_times_N_eq α β ω h_ω L hL
  have h_rhs : 0 ≤ ↑L * ↑(α ^ 2 + β ^ 2) := by positivity
  nlinarith

/--
Generalization of sorted_multiset_add_N to multiple N-steps:
sortedMultiset(i + m*N) = sortedMultiset(i) + m*D.
-/
lemma sorted_multiset_add_mul_N (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (i : ℤ) (m : ℕ) :
    sortedMultiset α β ω (i + ↑m * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) =
      sortedMultiset α β ω i + ↑m * ↑(α ^ 2 + β ^ 2) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have ha : sortedMultiset α β ω
        (i + ↑k * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat +
          ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) =
        sortedMultiset α β ω
          (i + ↑k * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) +
          ↑(α ^ 2 + β ^ 2) :=
      sorted_multiset_add_N α β ω h_ω _
    have h_eq : i + ↑(k + 1) * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat =
        i + ↑k * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat +
        ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by push_cast; ring
    rw [h_eq, ha, ih]; push_cast; ring

/--
sortedMultiset mod D depends only on the index mod N.
-/
lemma sorted_multiset_mod_D_eq (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (k L : ℕ) :
    (sortedMultiset α β ω ↑(k + L) : ZMod (α ^ 2 + β ^ 2)) =
    (sortedMultiset α β ω ↑((k + L) %
      (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) :
      ZMod (α ^ 2 + β ^ 2)) := by
  set N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
  set D := α ^ 2 + β ^ 2
  have hN := N_pos_concrete α β ω h_ω
  have h_decomp : (↑(k + L) : ℤ) =
      ↑((k + L) % N) + ↑((k + L) / N) * ↑N := by
    have := Nat.div_add_mod (k + L) N
    push_cast; linarith
  conv_lhs => rw [h_decomp]
  rw [sorted_multiset_add_mul_N α β ω h_ω _ ((k + L) / N)]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have : (↑D : ZMod D) = 0 := ZMod.natCast_self D
  rw [this, mul_zero, add_zero]

/-- Unit-aware analogue of `sorted_shift_constant`. Structural — identical
to the untwisted proof with `differenceSequenceUnit`/`sortedMultisetUnit`
substituted. -/
lemma sorted_shift_constant_unit (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (L : ℕ) (hL : IsPeriod (differenceSequenceUnit α β ω u) L) (i : ℤ) :
    sortedMultisetUnit α β ω u (i + ↑L) - sortedMultisetUnit α β ω u i =
    sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0 := by
  have h_step : ∀ j : ℤ,
      sortedMultisetUnit α β ω u (j + 1 + ↑L) - sortedMultisetUnit α β ω u (j + 1) =
      sortedMultisetUnit α β ω u (j + ↑L) - sortedMultisetUnit α β ω u j := by
    intro j
    have hper := hL.2 j
    simp only [differenceSequenceUnit] at hper
    have h1 : j + 1 + ↑L = j + ↑L + 1 := by ring
    rw [h1]; linarith
  have h_nat : ∀ n : ℕ,
      sortedMultisetUnit α β ω u (↑n + ↑L) - sortedMultisetUnit α β ω u ↑n =
      sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0 := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      have := h_step ↑k
      have h1 : (↑k : ℤ) + 1 + ↑L = ↑(k + 1) + ↑L := by push_cast; ring
      have h2 : (↑k : ℤ) + 1 = ↑(k + 1) := by push_cast; ring
      rw [h1, h2] at this; linarith
  have h_neg : ∀ n : ℕ,
      sortedMultisetUnit α β ω u (-↑n + ↑L) - sortedMultisetUnit α β ω u (-↑n) =
      sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0 := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      have h_eq : sortedMultisetUnit α β ω u (-↑k + ↑L) - sortedMultisetUnit α β ω u (-↑k) =
          sortedMultisetUnit α β ω u (-↑(k + 1) + ↑L)
            - sortedMultisetUnit α β ω u (-↑(k + 1)) := by
        have := h_step (-↑(k + 1))
        have ha : (-↑(k + 1) : ℤ) + 1 + ↑L = -↑k + ↑L := by push_cast; omega
        have hb : (-↑(k + 1) : ℤ) + 1 = -↑k := by push_cast; omega
        simp only [hb] at this; linarith
      linarith
  cases i with
  | ofNat n => exact h_nat n
  | negSucc n =>
    have : (Int.negSucc n : ℤ) = -↑(n + 1) := by omega
    simp only [this]
    exact h_neg (n + 1)

/-- Unit-aware analogue of `shift_times_N_eq`. -/
lemma shift_times_N_eq_unit (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (L : ℕ) (hL : IsPeriod (differenceSequenceUnit α β ω u) L) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    let σ := sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0
    ↑N * σ = ↑L * ↑D := by
  intro N D σ
  have h_shift_L : ∀ n : ℕ, sortedMultisetUnit α β ω u (↑n * ↑L) =
      sortedMultisetUnit α β ω u 0 + ↑n * σ := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      have hsc := sorted_shift_constant_unit α β ω u L hL (↑k * ↑L)
      have h_eq : (↑(k + 1) : ℤ) * ↑L = ↑k * ↑L + ↑L := by push_cast; ring
      rw [h_eq]; push_cast at ih ⊢; linarith
  have h_shift_N : ∀ n : ℕ, sortedMultisetUnit α β ω u (↑n * ↑N) =
      sortedMultisetUnit α β ω u 0 + ↑n * ↑D := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      have hsa : sortedMultisetUnit α β ω u (↑k * ↑N + ↑N) =
          sortedMultisetUnit α β ω u (↑k * ↑N) + ↑D :=
        sorted_multiset_unit_add_N α β ω h_ω u (↑k * (↑N : ℤ))
      have h_eq : (↑(k + 1) : ℤ) * ↑N = ↑k * ↑N + ↑N := by push_cast; ring
      have h_eq2 : (↑(k + 1) : ℤ) * ↑D = ↑k * ↑D + ↑D := by push_cast; ring
      rw [h_eq]; linarith
  have h1 := h_shift_L N
  have h2 := h_shift_N L
  have h3 : (↑N : ℤ) * ↑L = ↑L * ↑N := by ring
  rw [h3] at h1; linarith

/-- Unit-aware analogue of `shift_nonneg`. -/
lemma shift_nonneg_unit (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (L : ℕ) (hL_pos : 0 < L) (hL : IsPeriod (differenceSequenceUnit α β ω u) L) :
    0 ≤ sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0 := by
  set σ := sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0
  have hN_pos : (0 : ℤ) < ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by
    exact_mod_cast N_pos_concrete α β ω h_ω
  have h_eq : ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat * σ =
      ↑L * ↑(α ^ 2 + β ^ 2) :=
    shift_times_N_eq_unit α β ω h_ω u L hL
  have h_rhs : 0 ≤ ↑L * ↑(α ^ 2 + β ^ 2) := by positivity
  nlinarith

/-- Unit-aware analogue of `sorted_multiset_add_mul_N`. -/
lemma sorted_multiset_unit_add_mul_N (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (i : ℤ) (m : ℕ) :
    sortedMultisetUnit α β ω u (i + ↑m * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) =
      sortedMultisetUnit α β ω u i + ↑m * ↑(α ^ 2 + β ^ 2) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have ha : sortedMultisetUnit α β ω u
        (i + ↑k * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat +
          ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) =
        sortedMultisetUnit α β ω u
          (i + ↑k * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) +
          ↑(α ^ 2 + β ^ 2) :=
      sorted_multiset_unit_add_N α β ω h_ω u _
    have h_eq : i + ↑(k + 1) * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat =
        i + ↑k * ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat +
        ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by push_cast; ring
    rw [h_eq, ha, ih]; push_cast; ring

/-- Unit-aware analogue of `sorted_multiset_mod_D_eq`. -/
lemma sorted_multiset_unit_mod_D_eq (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (k L : ℕ) :
    (sortedMultisetUnit α β ω u ↑(k + L) : ZMod (α ^ 2 + β ^ 2)) =
    (sortedMultisetUnit α β ω u ↑((k + L) %
      (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) :
      ZMod (α ^ 2 + β ^ 2)) := by
  have hN := N_pos_concrete α β ω h_ω
  have h_decomp : (↑(k + L) : ℤ) =
      ↑((k + L) % (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) +
        ↑((k + L) / (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) *
        ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by
    have := Nat.div_add_mod (k + L) (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    push_cast; linarith
  conv_lhs => rw [h_decomp]
  rw [sorted_multiset_unit_add_mul_N α β ω h_ω u _
        ((k + L) / (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat)]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have : (↑(α ^ 2 + β ^ 2) : ZMod (α ^ 2 + β ^ 2)) = 0 :=
    ZMod.natCast_self (α ^ 2 + β ^ 2)
  rw [this, mul_zero, add_zero]

/--
Key residue shift: sortedMultiset((j+L)%N) ≡ sortedMultiset(j) + σ (mod D).
-/
lemma sorted_residue_shift (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (L : ℕ) (hL : IsPeriod (differenceSequence α β ω) L) (j : ℕ) :
    let D := α ^ 2 + β ^ 2
    let σ_ℤ := sortedMultiset α β ω ↑L - sortedMultiset α β ω 0
    (sortedMultiset α β ω ↑((j + L) %
      (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) : ZMod D) =
    (sortedMultiset α β ω ↑j : ZMod D) + (σ_ℤ : ZMod D) := by
  intro D σ_ℤ
  have h1 := sorted_multiset_mod_D_eq α β ω h_ω j L
  have h2 : sortedMultiset α β ω (↑j + ↑L) =
      sortedMultiset α β ω ↑j + σ_ℤ := by
    have := sorted_shift_constant α β ω L hL ↑j; linarith
  have h3 : (↑(j + L) : ℤ) = ↑j + ↑L := by push_cast; ring
  rw [← h1, h3]; simp only [h2, Int.cast_add]

/--
For k < N, sortedMultiset at (↑k : ℤ) simplifies to ↑(V α β ω k).
-/
private lemma sorted_multiset_of_lt_N (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (k : ℕ) (hk : k < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) :
    sortedMultiset α β ω (↑k : ℤ) = ↑(V α β ω k) := by
  have hN_pos : (0 : ℤ) < ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by
    exact_mod_cast (show 0 < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat from by omega)
  have h_mod : (↑k : ℤ) % ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat = ↑k :=
    Int.emod_eq_of_lt (Int.natCast_nonneg k) (by exact_mod_cast hk)
  have h_div : (↑k : ℤ) / ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat = 0 :=
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg k) (by exact_mod_cast hk)
  -- sortedMultiset unfolds to V((...%N).toNat) + (.../N) * D
  -- After substituting h_mod and h_div: V((↑k).toNat) + 0 * D = V(k)
  simp only [sortedMultiset, h_mod, h_div, Int.toNat_natCast, zero_mul,
             add_zero]

/--
cumulativeHits is monotone (non-decreasing).
-/
private lemma cumulative_hits_mono (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)] :
    Monotone (cumulativeHits α β ω) := by
  intro a b hab
  dsimp [cumulativeHits]
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono (Nat.add_le_add_right hab 1)

/--
Sum over range D of countHits composed with ZMod cast equals sum over ZMod D.
-/
private lemma sum_range_eq_sum_zmod (D : ℕ) [NeZero D] (r0 N : ℕ) :
    ∑ y ∈ Finset.range D, countHits D r0 N (↑y : ZMod D) =
    ∑ x : ZMod D, countHits D r0 N x := by
  symm
  apply Finset.sum_bij (fun (x : ZMod D) _ => x.val)
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro x₁ _ x₂ _ h
    rw [← ZMod.natCast_zmod_val x₁, ← ZMod.natCast_zmod_val x₂, h]
  · intro y hy
    exact ⟨(↑y : ZMod D), Finset.mem_univ _,
      by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hy)]⟩
  · intro x _; congr 1; exact (ZMod.natCast_zmod_val x).symm

/--
cumulativeHits at D - 1 equals N.
-/
private lemma cumulative_hits_eq_N (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)] :
    cumulativeHits α β ω (α ^ 2 + β ^ 2 - 1) =
    (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by
  set D := α ^ 2 + β ^ 2
  set N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
  set r0 := ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
  dsimp [cumulativeHits]
  rw [show D - 1 + 1 = D from Nat.succ_pred_eq_of_pos (NeZero.pos D)]
  rw [sum_range_eq_sum_zmod D r0 N, sum_count_hits D r0 N]

/--
V(k) < D for k < N (the quantile stays within one period).
-/
private lemma V_lt_D (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (k : ℕ) (hk : k < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) :
    V α β ω k < α ^ 2 + β ^ 2 := by
  set D := α ^ 2 + β ^ 2
  have h_exists : ∃ x, k < cumulativeHits α β ω x :=
    ⟨D - 1, (cumulative_hits_eq_N α β ω).symm ▸ hk⟩
  simp only [V, dite_eq_left h_exists]
  calc Nat.find h_exists
      ≤ D - 1 := Nat.find_min' h_exists ((cumulative_hits_eq_N α β ω).symm ▸ hk)
    _ < D := Nat.sub_lt (NeZero.pos D) Nat.one_pos

/--
Characterization of V: V(k) = v iff k is in the v-th interval of cumulativeHits.
-/
private lemma V_eq_iff (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (k : ℕ) (hk : k < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) (v : ℕ) :
    V α β ω k = v ↔
    (v = 0 ∨ cumulativeHits α β ω (v - 1) ≤ k) ∧
    k < cumulativeHits α β ω v := by
  set D := α ^ 2 + β ^ 2
  have h_exists : ∃ x, k < cumulativeHits α β ω x :=
    ⟨D - 1, (cumulative_hits_eq_N α β ω).symm ▸ hk⟩
  simp only [V, dite_eq_left h_exists]
  constructor
  · -- Forward: Nat.find = v → interval condition
    intro h_eq
    refine ⟨?_, h_eq ▸ Nat.find_spec h_exists⟩
    rcases Nat.eq_zero_or_pos v with hv | hv
    · left; exact hv
    · right
      have h_lt_find : v - 1 < Nat.find h_exists := by
        rw [h_eq]; exact Nat.sub_lt hv Nat.one_pos
      exact Nat.not_lt.mp (Nat.find_min h_exists h_lt_find)
  · -- Backward: interval condition → Nat.find = v
    intro ⟨h_left, h_right⟩
    apply le_antisymm
    · exact Nat.find_min' h_exists h_right
    · by_contra h_lt
      push Not at h_lt
      rcases h_left with hv | h_ge
      · subst hv; omega
      · have h_mono := cumulative_hits_mono α β ω (show Nat.find h_exists ≤ v - 1 by omega)
        linarith [Nat.find_spec h_exists]

/--
The fiber of V at v has exactly countHits many elements.
-/
private lemma V_fiber_card (α β : ℕ) (ω : ℝ) (_h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)]
    (v : ℕ) (hv : v < α ^ 2 + β ^ 2) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    let r0 := ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
    ((Finset.range N).filter (fun k => V α β ω k = v)).card =
    countHits D r0 N (↑v : ZMod D) := by
  intro N D r0
  set prev := if v = 0 then 0 else cumulativeHits α β ω (v - 1) with h_prev_def
  -- The filter equals Finset.Ico prev (cumulativeHits α β ω v)
  have h_filter_eq : (Finset.range N).filter (fun k => V α β ω k = v) =
      Finset.Ico prev (cumulativeHits α β ω v) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro ⟨hk, hV⟩
      have h_iff := (V_eq_iff α β ω k hk v).mp hV
      refine ⟨?_, h_iff.2⟩
      simp only [prev]
      split_ifs with hv0
      · omega
      · rcases h_iff.1 with h | h
        · omega
        · exact h
    · intro ⟨h_ge, h_lt⟩
      have hk_lt_N : k < N := by
        calc k < cumulativeHits α β ω v := h_lt
          _ ≤ cumulativeHits α β ω (D - 1) :=
              cumulative_hits_mono α β ω (by omega : v ≤ D - 1)
          _ = N := cumulative_hits_eq_N α β ω
      refine ⟨hk_lt_N, (V_eq_iff α β ω k hk_lt_N v).mpr ⟨?_, h_lt⟩⟩
      simp only [prev] at h_ge
      split_ifs at h_ge with hv0
      · left; exact hv0
      · right; exact h_ge
  rw [h_filter_eq, Nat.card_Ico]
  -- Goal: cumulativeHits α β ω v - prev = countHits D r0 N (↑v : ZMod D)
  -- Use the step formula for cumulativeHits
  have h_step : ∀ n, cumulativeHits α β ω (n + 1) =
      cumulativeHits α β ω n + countHits D r0 N (↑(n + 1) : ZMod D) := by
    intro n; dsimp [cumulativeHits]; rw [Finset.sum_range_succ]
  rcases Nat.eq_zero_or_pos v with hv0 | hv0
  · -- v = 0: prev = 0, cumulativeHits 0 = countHits 0
    subst hv0; simp only [prev, ite_true, Nat.sub_zero]
    have : cumulativeHits α β ω 0 =
        (Finset.range 1).sum
          (fun y => countHits D r0 N (↑y : ZMod D)) := by rfl
    rw [this, Finset.sum_range_one]
  · -- v > 0: prev = cumulativeHits(v-1)
    simp only [prev, show v = 0 ↔ False from ⟨by omega, False.elim⟩, ite_false]
    have h_eq : cumulativeHits α β ω v =
        cumulativeHits α β ω (v - 1) + countHits D r0 N (↑v : ZMod D) := by
      have := h_step (v - 1)
      rwa [show v - 1 + 1 = v from Nat.succ_pred_eq_of_pos hv0] at this
    omega

/--
Bridge lemma: countHits via the arithmetic progression equals
counting sortedMultiset residues over one period.
-/
lemma count_hits_eq_sorted_count (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    let r0 := ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
    ∀ x : ZMod D, countHits D r0 N x =
      ((Finset.range N).filter
        (fun (k : ℕ) => (sortedMultiset α β ω (↑k : ℤ) : ZMod D) = x)).card := by
  intro N D r0 x
  -- sortedMultiset(k) = V(k) for k < N
  have h_filter_eq : (Finset.range N).filter
      (fun (k : ℕ) => (sortedMultiset α β ω (↑k : ℤ) : ZMod D) = x) =
      (Finset.range N).filter
      (fun (k : ℕ) => (↑(V α β ω k) : ZMod D) = x) := by
    apply Finset.filter_congr
    intro k hk; rw [Finset.mem_range] at hk
    constructor
    · intro h; rw [sorted_multiset_of_lt_N α β ω k hk] at h; exact_mod_cast h
    · intro h; rw [sorted_multiset_of_lt_N α β ω k hk]; exact_mod_cast h
  rw [h_filter_eq]
  -- (V(k) : ZMod D) = x iff V(k) = x.val (since V(k) < D)
  have h_filter_eq2 : (Finset.range N).filter
      (fun (k : ℕ) => (↑(V α β ω k) : ZMod D) = x) =
      (Finset.range N).filter (fun k => V α β ω k = x.val) := by
    apply Finset.filter_congr
    intro k hk; rw [Finset.mem_range] at hk
    have hV := V_lt_D α β ω k hk
    constructor
    · intro heq
      have := congrArg ZMod.val heq
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hV] at this
    · intro heq; rw [heq, ZMod.natCast_zmod_val]
  rw [h_filter_eq2, V_fiber_card α β ω h_ω x.val (ZMod.val_lt x)]
  congr 1; exact (ZMod.natCast_zmod_val x).symm

/--
Injectivity of `j ↦ (j + L) % N` on `[0, N)`: a cancellation lemma used in the minimality argument.
-/
private lemma mod_add_inj (N L j₁ j₂ : ℕ) (hN : 0 < N)
    (hj₁ : j₁ < N) (hj₂ : j₂ < N)
    (h : (j₁ + L) % N = (j₂ + L) % N) : j₁ = j₂ := by
  have hLN := Nat.mod_lt L hN
  have ha := Nat.add_mod j₁ L N
  have hb := Nat.add_mod j₂ L N
  rw [Nat.mod_eq_of_lt hj₁] at ha
  rw [Nat.mod_eq_of_lt hj₂] at hb
  rw [ha, hb] at h
  -- h : (j₁ + L % N) % N = (j₂ + L % N) % N
  -- In each case, reduce (x + L%N) % N in h and conclude with omega
  have reduce : ∀ x, x < N → x + L % N ≥ N →
      (x + L % N) % N = x + L % N - N := by
    intro x hx hge
    have h_lt : x + L % N - N < N := by omega
    have h_eq : x + L % N = N + (x + L % N - N) := by omega
    conv_lhs => rw [h_eq]
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt h_lt]
  rcases Nat.lt_or_ge (j₁ + L % N) N with h1 | h1 <;>
    rcases Nat.lt_or_ge (j₂ + L % N) N with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, reduce j₂ hj₂ h2] at h; omega
  · rw [reduce j₁ hj₁ h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [reduce j₁ hj₁ h1, reduce j₂ hj₂ h2] at h; omega

private lemma mod_add_inv (N L k : ℕ) (hN : 0 < N) (hk : k < N) :
    ((k + N - L % N) % N + L) % N = k := by
  have hLN := Nat.mod_lt L hN
  -- Step 1: (a%N + L) % N = (a + L) % N for a = k + N - L%N
  have step1 : ((k + N - L % N) % N + L) % N =
      (k + N - L % N + L) % N := by
    set a := k + N - L % N
    conv_rhs => rw [show a = a % N + N * (a / N) from (Nat.mod_add_div a N).symm]
    rw [show a % N + N * (a / N) + L = a % N + L + N * (a / N) from by ring]
    rw [Nat.add_mul_mod_self_left]
  -- Step 2: (k + N - L%N + L) % N = k
  have step2 : k + N - L % N + L = k + (1 + L / N) * N := by
    have h_le : L % N ≤ k + N := by omega
    have h_decomp : L = N * (L / N) + L % N := (Nat.div_add_mod L N).symm
    have h1 : k + N - L % N + L = k + N + N * (L / N) := by omega
    rw [h1]; ring
  rw [step1, step2, show k + (1 + L / N) * N = k + N * (1 + L / N) from by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

lemma count_hits_shift_invariant (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)]
    (L : ℕ) (hL_pos : 0 < L) (hL : IsPeriod (differenceSequence α β ω) L) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    let σ := (sortedMultiset α β ω ↑L - sortedMultiset α β ω 0).toNat
    let r0 := ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
    ∀ x : ZMod D, countHits D r0 N (x + ↑σ) = countHits D r0 N x := by
  intro N D σ r0 x
  have hN := N_pos_concrete α β ω h_ω
  set σ_ℤ := sortedMultiset α β ω ↑L - sortedMultiset α β ω 0
    with hσ_def
  have h_nn : 0 ≤ σ_ℤ := shift_nonneg α β ω h_ω L hL_pos hL
  have h_σ_cast : (↑σ : ZMod D) = (σ_ℤ : ZMod D) := by
    have h_eq : (σ_ℤ.toNat : ℤ) = σ_ℤ := Int.toNat_of_nonneg h_nn
    have : (↑σ : ZMod D) = ((σ_ℤ.toNat : ℤ) : ZMod D) := by push_cast; rfl
    rw [this, h_eq]
  rw [count_hits_eq_sorted_count α β ω h_ω x,
      count_hits_eq_sorted_count α β ω h_ω (x + ↑σ)]
  -- Goal: (x+σ)-filter.card = x-filter.card
  -- Flip to x-filter.card = (x+σ)-filter.card, then use π(j) = (j+L)%N
  symm
  apply Finset.card_bij (fun (j : ℕ) (_ : j ∈ _) => (j + L) % N)
  · -- π(j) maps x-filter into (x+σ)-filter
    intro j hj
    have hjf := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hN), ?_⟩
    rw [sorted_residue_shift α β ω h_ω L hL j, hjf.2, h_σ_cast]
  · -- π injective on the x-filter
    intro j₁ hj₁ j₂ hj₂ h_eq
    have hj₁' := Finset.mem_range.mp (Finset.mem_filter.mp hj₁).1
    have hj₂' := Finset.mem_range.mp (Finset.mem_filter.mp hj₂).1
    exact mod_add_inj N L j₁ j₂ hN hj₁' hj₂' h_eq
  · -- π surjective onto the (x+σ)-filter
    intro k hk
    have hkf := Finset.mem_filter.mp hk
    have hk_range := Finset.mem_range.mp hkf.1
    -- Inverse: j = (k + N - L % N) % N
    refine ⟨(k + N - L % N) % N, ?_, ?_⟩
    · -- preimage is in the x-filter
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hN), ?_⟩
      -- sorted_residue_shift at preimage:
      -- sortedMultiset(((k+N-L%N)%N + L) % N) = sortedMultiset((k+N-L%N)%N) + σ
      -- And ((k+N-L%N)%N + L) % N = k
      have h_inv : ((k + N - L % N) % N + L) % N = k :=
        mod_add_inv N L k hN hk_range
      have h_shift := sorted_residue_shift α β ω h_ω L hL
          ((k + N - L % N) % N)
      simp only at h_shift; rw [h_inv] at h_shift
      -- h_shift: sorted(k) = sorted(preimage) + σ_ℤ in ZMod D
      -- hkf.2: sorted(k) = x + σ in ZMod D
      -- So sorted(preimage) + σ_ℤ = x + σ_ℤ, hence sorted(preimage) = x
      have h_eq : (sortedMultiset α β ω
          ↑((k + N - L % N) % N) : ZMod D) +
          (σ_ℤ : ZMod D) = x + (σ_ℤ : ZMod D) := by
        rw [← h_shift, hkf.2, h_σ_cast]
      exact add_right_cancel h_eq
    · -- ((k + N - L%N) % N + L) % N = k
      exact mod_add_inv N L k hN hk_range

-- =====================================================================
-- Unit-aware parallel infrastructure (Phase 2 step 3d).
-- =====================================================================

/-- Unit-aware analogue of `sorted_residue_shift`. -/
lemma sorted_residue_shift_unit (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (L : ℕ) (hL : IsPeriod (differenceSequenceUnit α β ω u) L) (j : ℕ) :
    let D := α ^ 2 + β ^ 2
    let σ_ℤ := sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0
    (sortedMultisetUnit α β ω u ↑((j + L) %
      (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) : ZMod D) =
    (sortedMultisetUnit α β ω u ↑j : ZMod D) + (σ_ℤ : ZMod D) := by
  intro D σ_ℤ
  have h1 := sorted_multiset_unit_mod_D_eq α β ω h_ω u j L
  have h2 : sortedMultisetUnit α β ω u (↑j + ↑L) =
      sortedMultisetUnit α β ω u ↑j + σ_ℤ := by
    have := sorted_shift_constant_unit α β ω u L hL ↑j; linarith
  have h3 : (↑(j + L) : ℤ) = ↑j + ↑L := by push_cast; ring
  rw [← h1, h3]; simp only [h2, Int.cast_add]

/-- For k < N, sortedMultisetUnit at (↑k : ℤ) simplifies to ↑(VUnit α β ω u k). -/
private lemma sorted_multiset_unit_of_lt_N (α β : ℕ) (ω : ℝ)
    [NeZero (α ^ 2 + β ^ 2)] (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (k : ℕ) (hk : k < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) :
    sortedMultisetUnit α β ω u (↑k : ℤ) = ↑(VUnit α β ω u k) := by
  have hN_pos : (0 : ℤ) < ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by
    exact_mod_cast (show 0 < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat from by omega)
  have h_mod : (↑k : ℤ) % ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat = ↑k :=
    Int.emod_eq_of_lt (Int.natCast_nonneg k) (by exact_mod_cast hk)
  have h_div : (↑k : ℤ) / ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat = 0 :=
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg k) (by exact_mod_cast hk)
  simp only [sortedMultisetUnit, h_mod, h_div, Int.toNat_natCast, zero_mul,
             add_zero]

private lemma cumulative_hits_unit_mono (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) :
    Monotone (cumulativeHitsUnit α β ω u) := by
  intro a b hab
  dsimp [cumulativeHitsUnit]
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono (Nat.add_le_add_right hab 1)

/-- Unit-aware version of `sum_count_hits`. Total hits over all D residues equals N. -/
private lemma sum_count_hits_unit (D : ℕ) [NeZero D] (u : (ZMod D)ˣ) (r0 N : ℕ) :
    ∑ x : ZMod D, countHitsUnit D u r0 N x = N := by
  have h_eq : ∀ x : ZMod D,
      countHitsUnit D u r0 N x = countHits D r0 N ((u⁻¹ : (ZMod D)ˣ) * x) :=
    count_hits_unit_eq_count_hits D u r0 N
  rw [Finset.sum_congr rfl (fun x _ => h_eq x)]
  -- ∑ x, countHits D r0 N (u⁻¹ * x) = ∑ y, countHits D r0 N y via bijection x ↦ u⁻¹ * x
  rw [show (∑ x : ZMod D, countHits D r0 N ((u⁻¹ : (ZMod D)ˣ) * x)) =
        ∑ y : ZMod D, countHits D r0 N y from ?_]
  · exact sum_count_hits D r0 N
  · apply Finset.sum_bij (fun (x : ZMod D) _ => (u⁻¹ : (ZMod D)ˣ) * x)
    · intro a _; exact Finset.mem_univ _
    · intro a _ b _ h
      have := congrArg (fun z => (u : ZMod D) * z) h
      simp only [← mul_assoc, Units.mul_inv, one_mul] at this
      exact this
    · intro b _; refine ⟨(u : ZMod D) * b, Finset.mem_univ _, ?_⟩
      rw [← mul_assoc, Units.inv_mul, one_mul]
    · intros; rfl

private lemma sum_range_eq_sum_zmod_unit (D : ℕ) [NeZero D] (u : (ZMod D)ˣ) (r0 N : ℕ) :
    ∑ y ∈ Finset.range D, countHitsUnit D u r0 N (↑y : ZMod D) =
    ∑ x : ZMod D, countHitsUnit D u r0 N x := by
  symm
  apply Finset.sum_bij (fun (x : ZMod D) _ => x.val)
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro x₁ _ x₂ _ h
    rw [← ZMod.natCast_zmod_val x₁, ← ZMod.natCast_zmod_val x₂, h]
  · intro y hy
    exact ⟨(↑y : ZMod D), Finset.mem_univ _,
      by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hy)]⟩
  · intro x _; congr 1; exact (ZMod.natCast_zmod_val x).symm

private lemma cumulative_hits_unit_eq_N (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) :
    cumulativeHitsUnit α β ω u (α ^ 2 + β ^ 2 - 1) =
    (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat := by
  dsimp [cumulativeHitsUnit]
  rw [show α ^ 2 + β ^ 2 - 1 + 1 = α ^ 2 + β ^ 2 from
        Nat.succ_pred_eq_of_pos (NeZero.pos (α ^ 2 + β ^ 2))]
  rw [sum_range_eq_sum_zmod_unit (α ^ 2 + β ^ 2) u
        (((-⌊ω * ↑β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val)
        (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat,
      sum_count_hits_unit (α ^ 2 + β ^ 2) u
        (((-⌊ω * ↑β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val)
        (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat]

private lemma V_unit_lt_D (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (k : ℕ) (hk : k < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) :
    VUnit α β ω u k < α ^ 2 + β ^ 2 := by
  have h_exists : ∃ x, k < cumulativeHitsUnit α β ω u x :=
    ⟨α ^ 2 + β ^ 2 - 1, (cumulative_hits_unit_eq_N α β ω u).symm ▸ hk⟩
  have h_eq : VUnit α β ω u k = Nat.find h_exists := by
    unfold VUnit; exact dite_eq_left h_exists
  rw [h_eq]
  calc Nat.find h_exists
      ≤ α ^ 2 + β ^ 2 - 1 :=
        Nat.find_min' h_exists ((cumulative_hits_unit_eq_N α β ω u).symm ▸ hk)
    _ < α ^ 2 + β ^ 2 := Nat.sub_lt (NeZero.pos _) Nat.one_pos

private lemma V_unit_eq_iff (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (k : ℕ) (hk : k < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) (v : ℕ) :
    VUnit α β ω u k = v ↔
    (v = 0 ∨ cumulativeHitsUnit α β ω u (v - 1) ≤ k) ∧
    k < cumulativeHitsUnit α β ω u v := by
  have h_exists : ∃ x, k < cumulativeHitsUnit α β ω u x :=
    ⟨α ^ 2 + β ^ 2 - 1, (cumulative_hits_unit_eq_N α β ω u).symm ▸ hk⟩
  have h_V : VUnit α β ω u k = Nat.find h_exists := by
    unfold VUnit; exact dite_eq_left h_exists
  rw [h_V]
  constructor
  · intro h_eq
    refine ⟨?_, h_eq ▸ Nat.find_spec h_exists⟩
    rcases Nat.eq_zero_or_pos v with hv | hv
    · left; exact hv
    · right
      have h_lt_find : v - 1 < Nat.find h_exists := by
        rw [h_eq]; exact Nat.sub_lt hv Nat.one_pos
      exact Nat.not_lt.mp (Nat.find_min h_exists h_lt_find)
  · intro ⟨h_left, h_right⟩
    apply le_antisymm
    · exact Nat.find_min' h_exists h_right
    · by_contra h_lt
      push Not at h_lt
      rcases h_left with hv | h_ge
      · subst hv; omega
      · have h_mono := cumulative_hits_unit_mono α β ω u
            (show Nat.find h_exists ≤ v - 1 by omega)
        linarith [Nat.find_spec h_exists]

private lemma V_unit_fiber_card (α β : ℕ) (ω : ℝ) (_h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (v : ℕ) (hv : v < α ^ 2 + β ^ 2) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    let r0 := ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
    ((Finset.range N).filter (fun k => VUnit α β ω u k = v)).card =
    countHitsUnit D u r0 N (↑v : ZMod D) := by
  intro N D r0
  set prev := if v = 0 then 0 else cumulativeHitsUnit α β ω u (v - 1) with h_prev_def
  have h_filter_eq : (Finset.range N).filter (fun k => VUnit α β ω u k = v) =
      Finset.Ico prev (cumulativeHitsUnit α β ω u v) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro ⟨hk, hV⟩
      have h_iff := (V_unit_eq_iff α β ω u k hk v).mp hV
      refine ⟨?_, h_iff.2⟩
      simp only [prev]
      split_ifs with hv0
      · omega
      · rcases h_iff.1 with h | h
        · omega
        · exact h
    · intro ⟨h_ge, h_lt⟩
      have hk_lt_N : k < N := by
        calc k < cumulativeHitsUnit α β ω u v := h_lt
          _ ≤ cumulativeHitsUnit α β ω u (D - 1) :=
              cumulative_hits_unit_mono α β ω u (by omega : v ≤ D - 1)
          _ = N := cumulative_hits_unit_eq_N α β ω u
      refine ⟨hk_lt_N, (V_unit_eq_iff α β ω u k hk_lt_N v).mpr ⟨?_, h_lt⟩⟩
      simp only [prev] at h_ge
      split_ifs at h_ge with hv0
      · left; exact hv0
      · right; exact h_ge
  rw [h_filter_eq, Nat.card_Ico]
  have h_step : ∀ n, cumulativeHitsUnit α β ω u (n + 1) =
      cumulativeHitsUnit α β ω u n + countHitsUnit D u r0 N (↑(n + 1) : ZMod D) := by
    intro n; dsimp [cumulativeHitsUnit]; rw [Finset.sum_range_succ]
  rcases Nat.eq_zero_or_pos v with hv0 | hv0
  · subst hv0; simp only [prev, ite_true, Nat.sub_zero]
    have : cumulativeHitsUnit α β ω u 0 =
        (Finset.range 1).sum
          (fun y => countHitsUnit D u r0 N (↑y : ZMod D)) := by rfl
    rw [this, Finset.sum_range_one]
  · simp only [prev, show v = 0 ↔ False from ⟨by omega, False.elim⟩, ite_false]
    have h_eq : cumulativeHitsUnit α β ω u v =
        cumulativeHitsUnit α β ω u (v - 1) + countHitsUnit D u r0 N (↑v : ZMod D) := by
      have := h_step (v - 1)
      rwa [show v - 1 + 1 = v from Nat.succ_pred_eq_of_pos hv0] at this
    omega

/-- Unit-aware analogue of `count_hits_eq_sorted_count`. -/
lemma count_hits_eq_sorted_count_unit (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] (u : (ZMod (α ^ 2 + β ^ 2))ˣ) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    let r0 := ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
    ∀ x : ZMod D, countHitsUnit D u r0 N x =
      ((Finset.range N).filter
        (fun (k : ℕ) => (sortedMultisetUnit α β ω u (↑k : ℤ) : ZMod D) = x)).card := by
  intro N D r0 x
  have h_filter_eq : (Finset.range N).filter
      (fun (k : ℕ) => (sortedMultisetUnit α β ω u (↑k : ℤ) : ZMod D) = x) =
      (Finset.range N).filter
      (fun (k : ℕ) => (↑(VUnit α β ω u k) : ZMod D) = x) := by
    apply Finset.filter_congr
    intro k hk; rw [Finset.mem_range] at hk
    constructor
    · intro h; rw [sorted_multiset_unit_of_lt_N α β ω u k hk] at h; exact_mod_cast h
    · intro h; rw [sorted_multiset_unit_of_lt_N α β ω u k hk]; exact_mod_cast h
  rw [h_filter_eq]
  have h_filter_eq2 : (Finset.range N).filter
      (fun (k : ℕ) => (↑(VUnit α β ω u k) : ZMod D) = x) =
      (Finset.range N).filter (fun k => VUnit α β ω u k = x.val) := by
    apply Finset.filter_congr
    intro k hk; rw [Finset.mem_range] at hk
    have hV := V_unit_lt_D α β ω u k hk
    constructor
    · intro heq
      have := congrArg ZMod.val heq
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hV] at this
    · intro heq; rw [heq, ZMod.natCast_zmod_val]
  rw [h_filter_eq2, V_unit_fiber_card α β ω h_ω u x.val (ZMod.val_lt x)]
  congr 1; exact (ZMod.natCast_zmod_val x).symm

/-- Unit-aware analogue of `count_hits_shift_invariant`. -/
lemma count_hits_shift_invariant_unit (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (L : ℕ) (hL_pos : 0 < L) (hL : IsPeriod (differenceSequenceUnit α β ω u) L) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    let σ := (sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0).toNat
    let r0 := ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
    ∀ x : ZMod D, countHitsUnit D u r0 N (x + ↑σ) = countHitsUnit D u r0 N x := by
  intro N D σ r0 x
  have hN := N_pos_concrete α β ω h_ω
  set σ_ℤ := sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0
    with hσ_def
  have h_nn : 0 ≤ σ_ℤ := shift_nonneg_unit α β ω h_ω u L hL_pos hL
  have h_σ_cast : (↑σ : ZMod D) = (σ_ℤ : ZMod D) := by
    have h_eq : (σ_ℤ.toNat : ℤ) = σ_ℤ := Int.toNat_of_nonneg h_nn
    have : (↑σ : ZMod D) = ((σ_ℤ.toNat : ℤ) : ZMod D) := by push_cast; rfl
    rw [this, h_eq]
  rw [count_hits_eq_sorted_count_unit α β ω h_ω u x,
      count_hits_eq_sorted_count_unit α β ω h_ω u (x + ↑σ)]
  symm
  apply Finset.card_bij (fun (j : ℕ) (_ : j ∈ _) => (j + L) % N)
  · intro j hj
    have hjf := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hN), ?_⟩
    rw [sorted_residue_shift_unit α β ω h_ω u L hL j, hjf.2, h_σ_cast]
  · intro j₁ hj₁ j₂ hj₂ h_eq
    have hj₁' := Finset.mem_range.mp (Finset.mem_filter.mp hj₁).1
    have hj₂' := Finset.mem_range.mp (Finset.mem_filter.mp hj₂).1
    exact mod_add_inj N L j₁ j₂ hN hj₁' hj₂' h_eq
  · intro k hk
    have hkf := Finset.mem_filter.mp hk
    have hk_range := Finset.mem_range.mp hkf.1
    refine ⟨(k + N - L % N) % N, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hN), ?_⟩
      have h_inv : ((k + N - L % N) % N + L) % N = k :=
        mod_add_inv N L k hN hk_range
      have h_shift := sorted_residue_shift_unit α β ω h_ω u L hL
          ((k + N - L % N) % N)
      simp only at h_shift; rw [h_inv] at h_shift
      have h_eq : (sortedMultisetUnit α β ω u
          ↑((k + N - L % N) % N) : ZMod D) +
          (σ_ℤ : ZMod D) = x + (σ_ℤ : ZMod D) := by
        rw [← h_shift, hkf.2, h_σ_cast]
      exact add_right_cancel h_eq
    · exact mod_add_inv N L k hN hk_range

private lemma cumulative_hits_uniform (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h_dvd : (α ^ 2 + β ^ 2) ∣ (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) (v : ℕ)
    (_hv : v < α ^ 2 + β ^ 2) :
    cumulativeHits α β ω v = (v + 1) * ((⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat / (α ^ 2 + β ^ 2)) := by
  set D := α ^ 2 + β ^ 2
  set N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
  set q := N / D
  set r0 := ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
  have h_unif : ∀ x : ZMod D, countHits D r0 N x = q :=
    uniform_residue_distribution D r0 N h_dvd
  have : cumulativeHits α β ω v =
      (Finset.range (v + 1)).sum (fun y => countHits D r0 N (↑y : ZMod D)) := rfl
  rw [this]
  simp [h_unif, Finset.sum_const, Finset.card_range]

private lemma V_uniform (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)]
    (h_dvd : (α ^ 2 + β ^ 2) ∣ (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat)
    (k : ℕ) (hk : k < (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) :
    V α β ω k = k / ((⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat / (α ^ 2 + β ^ 2)) := by
  set D := α ^ 2 + β ^ 2
  set N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
  set q := N / D
  have hD_pos : 0 < D := NeZero.pos D
  have hN_pos : 0 < N := N_pos_concrete α β ω h_ω
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hN_pos h_dvd) hD_pos
  have hN_eq : N = q * D := (Nat.div_mul_cancel h_dvd).symm
  -- V(k) = Nat.find (∃ x, k < cumulativeHits x)
  -- cumulativeHits(v) = (v+1)*q, so k < (v+1)*q iff v ≥ k/q
  -- Therefore V(k) = k/q
  set v := k / q
  have hv_lt_D : v < D := by
    rw [Nat.div_lt_iff_lt_mul hq_pos]; rw [hN_eq] at hk; linarith
  have h_find : V α β ω k = v := by
    have h_exists : ∃ x, k < cumulativeHits α β ω x := by
      use D - 1
      rw [cumulative_hits_eq_N α β ω]; exact hk
    unfold V; rw [dite_eq_left h_exists]
    apply le_antisymm
    · apply Nat.find_min'
      rw [cumulative_hits_uniform α β ω h_dvd v hv_lt_D]
      calc k = q * v + k % q := (Nat.div_add_mod k q).symm
        _ < q * v + q := by have := Nat.mod_lt k hq_pos; omega
        _ = (v + 1) * q := by ring
    · by_contra h_lt; push Not at h_lt
      have h_prev := Nat.find_spec h_exists
      have h_find_lt : Nat.find h_exists < v := h_lt
      have h_find_lt_D : Nat.find h_exists < D := lt_trans h_find_lt hv_lt_D
      rw [cumulative_hits_uniform α β ω h_dvd _ h_find_lt_D] at h_prev
      have : k < (Nat.find h_exists + 1) * q := h_prev
      have : v ≤ Nat.find h_exists := by
        have : k / q < Nat.find h_exists + 1 :=
          (Nat.div_lt_iff_lt_mul hq_pos).mpr this
        omega
      omega
  exact h_find

private lemma sorted_multiset_add_q (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)]
    (h_dvd : (α ^ 2 + β ^ 2) ∣ (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) (i : ℤ) :
    let q := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat / (α ^ 2 + β ^ 2)
    sortedMultiset α β ω (i + ↑q) = sortedMultiset α β ω i + 1 := by
  intro q
  set N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat with hN_def
  set D := α ^ 2 + β ^ 2 with hD_def
  have hD_pos : 0 < D := NeZero.pos D
  have hN_pos : 0 < N := N_pos_concrete α β ω h_ω
  have hN_ne : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hN_pos h_dvd) hD_pos
  have hN_eq : N = q * D := (Nat.div_mul_cancel h_dvd).symm
  -- r is the remainder of i modulo N
  set r := (i % (N : ℤ)).toNat with hr_def
  have hr_nonneg : 0 ≤ i % (N : ℤ) := Int.emod_nonneg i hN_ne
  have hr_lt : r < N := by
    rw [hr_def]; exact Int.toNat_lt hr_nonneg |>.mpr (Int.emod_lt_of_pos i (by omega))
  have hr_cast : (r : ℤ) = i % (N : ℤ) := Int.toNat_of_nonneg hr_nonneg
  have h_decomp : i = ↑N * (i / ↑N) + ↑r := by
    rw [hr_cast]; exact (Int.mul_ediv_add_emod i ↑N).symm
  -- Key helper: rewrite (i + q) as N * quot + remainder
  -- We split into two cases depending on whether r + q < N
  by_cases h_case : r + q < N
  · -- Case 1: r + q < N, so the N-quotient doesn't change
    -- i + q = N * (i/N) + (r + q), with r + q < N
    have h_iq : (i + ↑q : ℤ) = ↑N * (i / ↑N) + (↑r + ↑q) := by linarith [h_decomp]
    have h_rq_nonneg : (0 : ℤ) ≤ ↑r + ↑q := by positivity
    have h_rq_lt : (↑r + ↑q : ℤ) < ↑N := by exact_mod_cast h_case
    have h_mod : (i + ↑q) % (↑N : ℤ) = ↑(r + q) := by
      conv_lhs => rw [h_iq]
      rw [show ↑N * (i / ↑N) + (↑r + ↑q) = (↑r + ↑q) + ↑N * (i / ↑N) from by ring]
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt h_rq_nonneg h_rq_lt
    have h_div : (i + ↑q) / (↑N : ℤ) = i / ↑N := by
      conv_lhs => rw [h_iq]
      rw [show ↑N * (i / ↑N) + (↑r + ↑q) = (↑r + ↑q) + ↑N * (i / ↑N) from by ring]
      rw [Int.add_mul_ediv_left _ _ hN_ne]
      have : (↑r + ↑q : ℤ) / ↑N = 0 :=
        Int.ediv_eq_zero_of_lt h_rq_nonneg h_rq_lt
      omega
    -- Now compute both sides
    change (V α β ω ((i + ↑q) % ↑N).toNat : ℤ) + (i + ↑q) / ↑N * ↑D =
         (V α β ω (i % ↑N).toNat : ℤ) + i / ↑N * ↑D + 1
    -- fold (i % ↑N).toNat back to r
    rw [show (i % (↑N : ℤ)).toNat = r from rfl]
    rw [h_mod, h_div, Int.toNat_natCast]
    -- V_uniform gives V(k) = k / q for k < N
    have hV_rq := V_uniform α β ω h_ω h_dvd (r + q) h_case
    have hV_r := V_uniform α β ω h_ω h_dvd r hr_lt
    -- q = N / D by definition
    have hq_fold : N / D = q := rfl
    rw [hq_fold] at hV_rq hV_r
    rw [hV_rq, hV_r]
    have h_div_q : (r + q) / q = r / q + 1 := Nat.add_div_right r hq_pos
    rw [h_div_q]; push_cast; ring
  · -- Case 2: r + q ≥ N, so the N-quotient increases by 1
    push Not at h_case
    -- In this case, r ≥ N - q = q * (D - 1)
    have hD_ge_one : D ≥ 1 := by omega
    have h_r_large : (D - 1) * q ≤ r := by
      have h1 : (D - 1) * q = D * q - q := Nat.sub_one_mul D q
      rw [h1, show D * q = q * D from Nat.mul_comm D q, hN_eq.symm]; omega
    have h_r_div : r / q = D - 1 := by
      apply Nat.div_eq_of_lt_le h_r_large
      have h1 : D - 1 + 1 = D := Nat.succ_pred_eq_of_pos hD_pos
      rw [h1, show D * q = N from by rw [hN_eq]; ring]; exact hr_lt
    -- r + q - N is a natural number since r + q ≥ N
    have h_rqN_ge : r + q ≥ N := h_case
    have hq_le_N : q ≤ N := Nat.div_le_self N D
    have h_rqN_lt_N : r + q - N < N := by omega
    -- i + q = N * (i/N + 1) + (r + q - N)
    have h_iq : (i + ↑q : ℤ) = ↑N * (i / ↑N + 1) + ↑(r + q - N) := by
      have h_cast : (↑(r + q - N) : ℤ) = ↑r + ↑q - ↑N := by
        rw [Nat.cast_sub h_rqN_ge]; push_cast; ring
      rw [h_cast]; linarith [h_decomp]
    have h_rem_nonneg : (0 : ℤ) ≤ ↑(r + q - N) := Int.natCast_nonneg _
    have h_rem_lt : (↑(r + q - N) : ℤ) < ↑N := by exact_mod_cast h_rqN_lt_N
    have h_mod : (i + ↑q) % (↑N : ℤ) = ↑(r + q - N) := by
      conv_lhs => rw [h_iq]
      rw [show ↑N * (i / ↑N + 1) + ↑(r + q - N) =
          ↑(r + q - N) + ↑N * (i / ↑N + 1) from by ring]
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt h_rem_nonneg h_rem_lt
    have h_div : (i + ↑q) / (↑N : ℤ) = i / ↑N + 1 := by
      conv_lhs => rw [h_iq]
      rw [show ↑N * (i / ↑N + 1) + ↑(r + q - N) =
          ↑(r + q - N) + ↑N * (i / ↑N + 1) from by ring]
      rw [Int.add_mul_ediv_left _ _ hN_ne]
      have : (↑(r + q - N) : ℤ) / ↑N = 0 :=
        Int.ediv_eq_zero_of_lt h_rem_nonneg h_rem_lt
      omega
    -- r + q - N = r mod q (since r/q = D-1 and N = q*D)
    have h_rqN : r + q - N = r % q := by
      have h1 := Nat.div_add_mod r q
      rw [h_r_div] at h1
      -- h1 : q * (D - 1) + r % q = r
      -- Need: r + q - N = r % q, with N = q * D
      rw [hN_eq]
      -- r + q - q * D = r % q
      -- From h1: r = q * (D - 1) + r % q
      -- q * (D - 1) + r % q + q - q * D = r % q
      -- q * (D - 1) + q = q * D, so this simplifies
      have h2 : q * (D - 1) + q = q * D := by
        rw [Nat.mul_sub_one]; omega
      omega
    change (V α β ω ((i + ↑q) % ↑N).toNat : ℤ) + (i + ↑q) / ↑N * ↑D =
         (V α β ω (i % ↑N).toNat : ℤ) + i / ↑N * ↑D + 1
    -- fold (i % ↑N).toNat back to r
    rw [show (i % (↑N : ℤ)).toNat = r from rfl]
    rw [h_mod, h_div, Int.toNat_natCast]
    have hV_rqN := V_uniform α β ω h_ω h_dvd (r + q - N) h_rqN_lt_N
    have hV_r := V_uniform α β ω h_ω h_dvd r hr_lt
    have hq_fold : N / D = q := rfl
    rw [hq_fold] at hV_rqN hV_r
    rw [hV_rqN, hV_r, h_rqN]
    have h_zero : r % q / q = 0 := Nat.div_eq_of_lt (Nat.mod_lt r hq_pos)
    rw [h_zero, h_r_div]
    have hD_sub_cast : (↑(D - 1) : ℤ) = ↑D - 1 := Nat.cast_sub hD_ge_one
    rw [hD_sub_cast]; push_cast; ring

lemma sigma_of_period_concrete (α β : ℕ) (_h_coprime : Nat.Coprime α β) (ω : ℝ)
    (h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)] :
    ∀ L > 0, IsPeriod (differenceSequence α β ω) L →
    ∃ σ : ℕ, σ * (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat = L * (α ^ 2 + β ^ 2) ∧
    ∃ r0 : ℕ, ∀ x : ZMod (α ^ 2 + β ^ 2),
      countHits (α ^ 2 + β ^ 2) r0 (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
          (x + (σ : ZMod (α ^ 2 + β ^ 2)))
        = countHits (α ^ 2 + β ^ 2) r0 (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat x := by
  intro L hL_pos hL_period
  set N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
  set D := α ^ 2 + β ^ 2
  set σ_ℤ := sortedMultiset α β ω ↑L - sortedMultiset α β ω 0
  have h_nonneg : 0 ≤ σ_ℤ := shift_nonneg α β ω h_ω L hL_pos hL_period
  set σ := σ_ℤ.toNat
  use σ
  constructor
  · -- σ * N = L * D
    have h_eq : ↑N * σ_ℤ = ↑L * ↑D := shift_times_N_eq α β ω h_ω L hL_period
    have h_cast : (↑σ : ℤ) = σ_ℤ := by
      simp only [σ]
      exact Int.toNat_of_nonneg h_nonneg
    have h_eq_int : (↑(σ * N) : ℤ) = ↑(L * D) := by
      push_cast
      rw [h_cast]
      linarith
    exact_mod_cast h_eq_int
  · -- countHits invariance
    use ((-⌊ω * ↑β⌋ : ℤ) : ZMod D).val
    exact count_hits_shift_invariant α β ω h_ω L hL_pos hL_period

lemma period_degenerate_concrete (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ)
    (h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)] :
    let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    D ∣ N → HasPeriodLength (differenceSequence α β ω) (N / D) := by
  intro N D h_dvd
  set q := N / D
  have hD_pos : 0 < D := NeZero.pos D
  have hN_pos : 0 < N := N_pos_concrete α β ω h_ω
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hN_pos h_dvd) hD_pos
  constructor
  · -- IsPeriod (differenceSequence α β ω) q
    constructor
    · exact hq_pos
    · intro i
      simp only [differenceSequence]
      have h1 := sorted_multiset_add_q α β ω h_ω h_dvd (i + 1)
      have h2 := sorted_multiset_add_q α β ω h_ω h_dvd i
      dsimp only at h1 h2
      have h3 : i + 1 + ↑q = i + ↑q + 1 := by ring
      rw [h3] at h1; linarith
  · -- Minimality: ∀ L' > 0, IsPeriod → q ≤ L'
    intro L' hL'_pos hL'_period
    have h_sigma := sigma_of_period_concrete α β h_coprime ω h_ω L' hL'_pos hL'_period
    rcases h_sigma with ⟨σ, h_eq, _⟩
    have hN_eq : N = q * D := (Nat.div_mul_cancel h_dvd).symm
    have h2 : σ * (q * D) = L' * D := by rw [← hN_eq]; exact h_eq
    have h3 : σ * q = L' := by
      have : σ * q * D = L' * D := by linarith [mul_assoc σ q D]
      exact Nat.eq_of_mul_eq_mul_right hD_pos this
    have hσ_pos : 0 < σ := by
      by_contra h; push Not at h
      have : σ = 0 := by omega
      rw [this, zero_mul] at h3; omega
    -- L' = σ * q ≥ 1 * q = q
    calc q = 1 * q := (one_mul q).symm
      _ ≤ σ * q := Nat.mul_le_mul_right q hσ_pos
      _ = L' := h3


/-- The concrete residue-model instance built from the difference sequence:
discharges the four hypotheses of `GeometricProjection` for coprime `α, β`
and window parameter `ω ≥ 0`. Supplied explicitly at each use site (the
coprimality and nonnegativity hypotheses cannot be found by synthesis). -/
theorem GeometricProjectionConcrete (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ)
    (h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)] :
    GeometricProjection α β ω (differenceSequence α β ω) :=
  { N_pos := N_pos_concrete α β ω h_ω
    period_N := period_N_concrete α β ω h_ω
    period_degenerate := period_degenerate_concrete α β h_coprime ω h_ω
    sigma_of_period := sigma_of_period_concrete α β h_coprime ω h_ω }


/--
Theorem 3.1: Period length formula.
-/
theorem main_theorem (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (_h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] [GeometricProjection α β ω (differenceSequence α β ω)] :
    let N_int := ⌊ω * α⌋ + ⌊ω * β⌋ + 1
    let N := N_int.toNat
    let D := α ^ 2 + β ^ 2
    let L := if D ∣ N then N / D else N
    HasPeriodLength (differenceSequence α β ω) L := by
  intro N_int N D L
  have h_D_pos : 0 < D := by
    change 0 < α ^ 2 + β ^ 2
    rcases Nat.eq_zero_or_pos α with rfl | h_pos
    · have h_beta : β = 1 := by simpa using h_coprime
      rw [h_beta]
      norm_num
    · have : 0 < α ^ 2 := by positivity
      omega
  have hD : NeZero D := ⟨_root_.ne_of_gt h_D_pos⟩
  by_cases h_dvd : D ∣ N
  · have h_L : L = N / D := ite_eq_left h_dvd
    rw [h_L]
    exact GeometricProjection.period_degenerate h_dvd
  · have h_L : L = N := ite_eq_right h_dvd
    rw [h_L]
    constructor
    · exact GeometricProjection.period_N
    · intro L' hL_pos hL_period
      exact generic_minimality α β ω (differenceSequence α β ω) h_dvd L' hL_pos hL_period

/-! ## Set-valued period (Phase A: `countHits` dichotomy)

The two lemmas `count_hits_lt_D` (already proved above) and `count_hits_ge_D`
(below) furnish the structural dichotomy underlying the set-valued period
theorem: under `N < D` the multiplicity function takes values in `{0,1}`
(so the gap multiset coincides with the gap set), while under `N ≥ D` every
residue class is hit (so the underlying set is all of ℤ and the set-valued
period collapses to 1).
-/

/--
Lower bound on `countHits`: if `N ≥ D`, every residue class is hit at least
once. Structural complement to `count_hits_lt_D`.
-/
lemma count_hits_ge_D (D : ℕ) [NeZero D] (r0 N : ℕ) (h : D ≤ N) (x : ZMod D) :
    1 ≤ countHits D r0 N x := by
  rw [count_hits_eq D r0 N x]
  have h_pos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have h_div : 1 ≤ N / D := (Nat.one_le_div_iff h_pos).mpr h
  omega

/-! ## Set-valued period (Phase B: dichotomy theorem, abstract form)

Together with `count_hits_lt_D` and `count_hits_ge_D` (Phase A), this section
gives the abstract version of the set-valued period theorem:
`λ_set = N` if `N < D`, else `1`. The dichotomy is reduced to two hypotheses
on the candidate set sequence — pointwise agreement with the multiset gap
sequence (when `N < D`), respectively constancy at `1` (when `N ≥ D`) —
which a concrete construction would discharge.
-/

/-- A sequence that is identically `1` has minimal period `1`. -/
lemma HasPeriodLength_const_one (s : ℤ → ℤ) (h : ∀ i, s i = 1) :
    HasPeriodLength s 1 := by
  refine ⟨⟨Nat.one_pos, fun i => ?_⟩, ?_⟩
  · rw [h, h]
  · intro L' hL_pos _
    exact hL_pos

/--
Set-valued period theorem (abstract form).

If `set_seq : ℤ → ℤ` agrees pointwise with `differenceSequence` whenever
`N < D`, and is constantly `1` whenever `N ≥ D`, then its minimal period is
`N` in the first case and `1` in the second.

The two hypotheses are exactly what the structural dichotomy
(`count_hits_lt_D` / `count_hits_ge_D`) lets a concrete enumeration of the
underlying point set verify.
-/
theorem set_main_theorem
    (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (h_ω : 0 ≤ ω)
    (set_seq : ℤ → ℤ)
    [NeZero (α ^ 2 + β ^ 2)]
    [GeometricProjection α β ω (differenceSequence α β ω)]
    (h_lt : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2 →
            ∀ i, set_seq i = differenceSequence α β ω i)
    (h_ge : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat →
            ∀ i, set_seq i = 1) :
    HasPeriodLength set_seq
      (if (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2 then
        (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
       else 1) := by
  by_cases h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2
  · -- Case N < D: set_seq = differenceSequence, period N (since N > 0 and ¬ D ∣ N).
    rw [ite_eq_left h]
    have h_eq : set_seq = differenceSequence α β ω := funext (h_lt h)
    rw [h_eq]
    have hN_pos : 0 < (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat := N_pos_concrete α β ω h_ω
    have hND : ¬ (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat := by
      intro hd
      have := Nat.le_of_dvd hN_pos hd
      omega
    have h_main : HasPeriodLength (differenceSequence α β ω)
        (if (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
         then (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat / (α ^ 2 + β ^ 2)
         else (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) := main_theorem α β h_coprime ω h_ω
    rw [ite_eq_right hND] at h_main
    exact h_main
  · -- Case ¬ (N < D), i.e., N ≥ D: set_seq ≡ 1, period 1.
    rw [ite_eq_right h]
    exact HasPeriodLength_const_one set_seq (h_ge (not_lt.mp h))

/-! ## Set-valued period (Phase C: concrete construction)

Concrete enumeration of the underlying set
`{ z ∈ ℤ | countHits D r0 N (z mod D) ≥ 1 }`,
mirroring the multiset's `V` / `sortedMultiset` machinery but with
multiplicities flattened to `{0,1}` via the indicator. The resulting
`setDifferenceSequence` discharges the abstract hypotheses `h_lt`
and `h_ge` of `set_main_theorem`.
-/

/-- Set indicator: `1` if residue `(y : ZMod D)` is hit at least once,
else `0`. Flattens multiplicities of the multiset to `{0,1}`. -/
noncomputable def setIndicator (α β : ℕ) (ω : ℝ)
    (y : ℕ) : ℕ :=
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  if 1 ≤ countHits D r0 N (y : ZMod D) then 1 else 0

/-- Cumulative count of hit residues over `[0, x]`. Set analogue of
`cumulativeHits`. -/
noncomputable def setCumulativeHits (α β : ℕ) (ω : ℝ)
    (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sum (setIndicator α β ω)

-- The `k`-th hit position: least `x` such that `[0, x]` contains
-- strictly more than `k` hits. Set analogue of `V`.
open Classical in
/-- Set-convention analogue of `V`: the least `x` whose set-cumulative hit count exceeds `k`. -/
noncomputable def setV (α β : ℕ) (ω : ℝ)
    (k : ℕ) : ℕ :=
  if h : ∃ x, k < setCumulativeHits α β ω x then
    Nat.find h
  else
    0

/-- Number of distinct residues hit, i.e. `|set ∩ [0, D)|`. -/
noncomputable def setSize (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)] : ℕ :=
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  (Finset.univ.filter (fun x : ZMod D => 1 ≤ countHits D r0 N x)).card

/-- Bi-infinite enumeration of the underlying set, lifted via `setSize`. -/
noncomputable def setSorted (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (i : ℤ) : ℤ :=
  let M := (setSize α β ω : ℤ)
  let D := α ^ 2 + β ^ 2
  let r := (i % M).toNat
  let q := i / M
  (setV α β ω r : ℤ) + q * D

/-- Concrete set-valued gap sequence. -/
noncomputable def setDifferenceSequence (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (i : ℤ) : ℤ :=
  setSorted α β ω (i + 1) - setSorted α β ω i

/-! ### Phase C, branch `N < D`: agreement with `differenceSequence` -/

/-- Under `N < D`, the indicator and the multiplicity coincide pointwise. -/
lemma set_indicator_eq_count_hits_of_lt
    (α β : ℕ) (ω : ℝ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (y : ℕ) :
    setIndicator α β ω y =
      countHits (α ^ 2 + β ^ 2)
        (((-⌊ω * β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val)
        ((⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (y : ZMod (α ^ 2 + β ^ 2)) := by
  have h_le := count_hits_lt_D (α ^ 2 + β ^ 2)
      (((-⌊ω * β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val)
      (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat h (y : ZMod (α ^ 2 + β ^ 2))
  change (if 1 ≤ countHits _ _ _ _ then 1 else 0) = _
  split_ifs with hge
  · omega
  · push Not at hge; omega

/-- Under `N < D`, `setCumulativeHits` and `cumulativeHits` agree. -/
lemma set_cumulative_hits_eq_of_lt
    (α β : ℕ) (ω : ℝ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (x : ℕ) :
    setCumulativeHits α β ω x = cumulativeHits α β ω x := by
  change (Finset.range (x + 1)).sum (setIndicator α β ω) = _
  apply Finset.sum_congr rfl
  intro y _
  exact set_indicator_eq_count_hits_of_lt α β ω h y

/-- Under `N < D`, `setV` and `V` agree. -/
lemma set_V_eq_V_of_lt
    (α β : ℕ) (ω : ℝ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (k : ℕ) :
    setV α β ω k = V α β ω k := by
  have h_funeq : setCumulativeHits α β ω = cumulativeHits α β ω :=
    funext (set_cumulative_hits_eq_of_lt α β ω h)
  unfold setV V
  rw [h_funeq]

/-- Under `N < D`, `setSize = N`. -/
lemma set_size_eq_N_of_lt
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) :
    setSize α β ω = (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat := by
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  have h_div : N / D = 0 := Nat.div_eq_of_lt h
  have h_mod : N % D = N := Nat.mod_eq_of_lt h
  have h_dist := (residue_distribution D r0 N).1
  simp only [h_div, h_mod, zero_add] at h_dist
  have h_le : ∀ x : ZMod D, countHits D r0 N x ≤ 1 :=
    fun x => count_hits_lt_D D r0 N h x
  change (Finset.univ.filter (fun x : ZMod D => 1 ≤ countHits D r0 N x)).card = N
  have h_filter_eq :
      (Finset.univ.filter (fun x : ZMod D => 1 ≤ countHits D r0 N x)) =
      (Finset.univ.filter (fun x : ZMod D => countHits D r0 N x = 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hge; have := h_le x; omega
    · intro heq; omega
  rw [h_filter_eq]
  exact h_dist

/-- Under `N < D`, `setSorted = sortedMultiset` pointwise. -/
lemma set_sorted_eq_of_lt
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (i : ℤ) :
    setSorted α β ω i = sortedMultiset α β ω i := by
  change (setV α β ω (i % ((setSize α β ω : ℤ))).toNat : ℤ) +
       (i / (setSize α β ω : ℤ)) * (α ^ 2 + β ^ 2 : ℕ) =
       (V α β ω (i % ((⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat : ℤ)).toNat : ℤ) +
       (i / ((⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat : ℤ)) * (α ^ 2 + β ^ 2 : ℕ)
  rw [set_size_eq_N_of_lt α β ω h, set_V_eq_V_of_lt α β ω h]

/-- **Discharge of `h_lt`**: under `N < D`, the concrete set sequence
agrees pointwise with `differenceSequence`. -/
lemma set_difference_sequence_eq_of_lt
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (i : ℤ) :
    setDifferenceSequence α β ω i = differenceSequence α β ω i := by
  change setSorted α β ω (i + 1) - setSorted α β ω i =
       sortedMultiset α β ω (i + 1) - sortedMultiset α β ω i
  rw [set_sorted_eq_of_lt α β ω h (i + 1), set_sorted_eq_of_lt α β ω h i]

/-! ### Phase C, branch `D ≤ N`: constant-`1` set sequence -/

/-- Under `D ≤ N`, every residue is hit, so the indicator is constantly `1`. -/
lemma set_indicator_eq_one_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (y : ℕ) :
    setIndicator α β ω y = 1 := by
  have h_ge := count_hits_ge_D (α ^ 2 + β ^ 2)
      (((-⌊ω * β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val)
      (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat h (y : ZMod (α ^ 2 + β ^ 2))
  change (if 1 ≤ countHits _ _ _ _ then 1 else 0) = 1
  rw [ite_eq_left h_ge]

/-- Under `D ≤ N`, the cumulative count is just `x + 1`. -/
lemma set_cumulative_hits_eq_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (x : ℕ) :
    setCumulativeHits α β ω x = x + 1 := by
  change (Finset.range (x + 1)).sum (setIndicator α β ω) = x + 1
  calc (Finset.range (x + 1)).sum (setIndicator α β ω)
      = (Finset.range (x + 1)).sum (fun _ : ℕ => 1) :=
        Finset.sum_congr rfl (fun y _ => set_indicator_eq_one_of_ge α β ω h y)
    _ = x + 1 := by simp

/-- Under `D ≤ N`, `setV k = k`. -/
lemma set_V_eq_id_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (k : ℕ) :
    setV α β ω k = k := by
  have h_cum : ∀ x, setCumulativeHits α β ω x = x + 1 :=
    set_cumulative_hits_eq_of_ge α β ω h
  have hex : ∃ x, k < setCumulativeHits α β ω x := ⟨k, by rw [h_cum]; omega⟩
  unfold setV
  rw [dite_eq_left hex]
  apply Nat.find_eq_iff _ |>.mpr
  refine ⟨?_, ?_⟩
  · rw [h_cum]; omega
  · intro m hm
    rw [h_cum]; omega

/-- Under `D ≤ N`, `setSize = D` (every residue is hit). -/
lemma set_size_eq_D_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) :
    setSize α β ω = α ^ 2 + β ^ 2 := by
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  have h_ge : ∀ x : ZMod D, 1 ≤ countHits D r0 N x :=
    fun x => count_hits_ge_D D r0 N h x
  change (Finset.univ.filter (fun x : ZMod D => 1 ≤ countHits D r0 N x)).card = D
  have h_filter_eq :
      Finset.univ.filter (fun x : ZMod D => 1 ≤ countHits D r0 N x) =
      (Finset.univ : Finset (ZMod D)) := by
    ext x; simp [h_ge x]
  rw [h_filter_eq, Finset.card_univ, ZMod.card]

/--
The set size is positive in either branch of the dichotomy: it equals `N`
when `N < D` (and `N ≥ 1` from `N_pos_concrete`), and equals `D` when
`N ≥ D` (and `D ≥ 1` from `NeZero`). Hence the modulo arithmetic in
`setSorted` is well-defined as a period-block enumeration.
-/
lemma set_size_pos (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)] :
    0 < setSize α β ω := by
  by_cases h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2
  · rw [set_size_eq_N_of_lt α β ω h]
    exact N_pos_concrete α β ω h_ω
  · rw [set_size_eq_D_of_ge α β ω (Nat.le_of_not_lt h)]
    exact NeZero.pos _

/-- Under `D ≤ N`, `setSorted i = i`. -/
lemma set_sorted_eq_id_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (i : ℤ) :
    setSorted α β ω i = i := by
  have hD_pos : 0 < α ^ 2 + β ^ 2 := by
    have : NeZero (α ^ 2 + β ^ 2) := inferInstance
    exact Nat.pos_of_ne_zero this.out
  have hD_ne : ((α ^ 2 + β ^ 2 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hD_pos.ne'
  change (setV α β ω (i % ((setSize α β ω : ℤ))).toNat : ℤ) +
       (i / (setSize α β ω : ℤ)) * (α ^ 2 + β ^ 2 : ℕ) = i
  rw [set_size_eq_D_of_ge α β ω h]
  have hmod_nn : 0 ≤ i % ((α ^ 2 + β ^ 2 : ℕ) : ℤ) := Int.emod_nonneg i hD_ne
  have hmod_lt : i % ((α ^ 2 + β ^ 2 : ℕ) : ℤ) < ((α ^ 2 + β ^ 2 : ℕ) : ℤ) :=
    Int.emod_lt_of_pos i (by exact_mod_cast hD_pos)
  set r : ℕ := (i % ((α ^ 2 + β ^ 2 : ℕ) : ℤ)).toNat with hr_def
  have hr_lt : r < α ^ 2 + β ^ 2 := by
    have : (r : ℤ) < ((α ^ 2 + β ^ 2 : ℕ) : ℤ) := by
      rw [hr_def, Int.toNat_of_nonneg hmod_nn]; exact hmod_lt
    exact_mod_cast this
  rw [set_V_eq_id_of_ge α β ω h r]
  have h_r_int : (r : ℤ) = i % ((α ^ 2 + β ^ 2 : ℕ) : ℤ) := by
    rw [hr_def, Int.toNat_of_nonneg hmod_nn]
  rw [h_r_int]
  have := Int.emod_add_mul_ediv i ((α ^ 2 + β ^ 2 : ℕ) : ℤ)
  linarith

/-- **Discharge of `h_ge`**: under `D ≤ N`, the concrete set sequence
is constantly `1`. -/
lemma set_difference_sequence_eq_one_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (i : ℤ) :
    setDifferenceSequence α β ω i = 1 := by
  change setSorted α β ω (i + 1) - setSorted α β ω i = 1
  rw [set_sorted_eq_id_of_ge α β ω h (i + 1), set_sorted_eq_id_of_ge α β ω h i]
  ring

/-! ### Phase C, concrete instantiation of both period theorems

For symmetry between the two branches: each wrapper internally discharges
the `[GeometricProjection ...]` instance via `GeometricProjectionConcrete`,
so neither requires its caller to provide it. -/

/--
Concrete multiset-valued period theorem. Wrapper around `main_theorem`
(line 1903) that internalises the `GeometricProjectionConcrete` instance,
so callers only need `h_coprime` and `h_ω`. -/
theorem main_theorem_concrete
    (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] :
    HasPeriodLength (differenceSequence α β ω)
      (if (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat then
        (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat / (α ^ 2 + β ^ 2)
       else (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) := by
  have : GeometricProjection α β ω (differenceSequence α β ω) :=
    GeometricProjectionConcrete α β h_coprime ω h_ω
  exact main_theorem α β h_coprime ω h_ω

-- =====================================================================
-- Unit-aware concrete period theorems (Phase 2 step 3e–3g).
-- The geometric `cR ≡ -αβ⁻¹ · (r0 + r) (mod D)` enumeration is realised
-- by `differenceSequenceUnit α β ω (multiplier α β h_coprime)`. Below we
-- prove that this sequence has the same period structure as the
-- normalised `differenceSequence`.
-- =====================================================================

/-- In the degenerate case `D ∣ N`, the countHitsUnit and countHits at any
residue both equal `N / D` (uniform residue distribution), hence the
unit-aware cumulative count agrees pointwise with the untwisted one. -/
private lemma cumulative_hits_unit_eq_cumulative_hits_of_dvd
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h_dvd : (α ^ 2 + β ^ 2) ∣ (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) (v : ℕ) :
    cumulativeHitsUnit α β ω u v = cumulativeHits α β ω v := by
  unfold cumulativeHitsUnit cumulativeHits
  apply Finset.sum_congr rfl
  intro y _
  rw [count_hits_unit_eq_count_hits]
  rw [uniform_residue_distribution _ _ _ h_dvd, uniform_residue_distribution _ _ _ h_dvd]

/-- In the degenerate case, `VUnit` agrees with `V` (both invert the same
cumulative function). -/
private lemma V_unit_eq_V_of_dvd (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h_dvd : (α ^ 2 + β ^ 2) ∣ (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) (k : ℕ) :
    VUnit α β ω u k = V α β ω k := by
  unfold VUnit V
  have h_eq : ∀ x, k < cumulativeHitsUnit α β ω u x ↔ k < cumulativeHits α β ω x := fun x => by
    rw [cumulative_hits_unit_eq_cumulative_hits_of_dvd α β ω u h_dvd]
  by_cases h : ∃ x, k < cumulativeHits α β ω x
  · have h' : ∃ x, k < cumulativeHitsUnit α β ω u x := by
      rcases h with ⟨x, hx⟩; exact ⟨x, (h_eq x).mpr hx⟩
    rw [dite_eq_left h, dite_eq_left h']
    apply le_antisymm
    · exact Nat.find_min' h' ((h_eq _).mpr (Nat.find_spec h))
    · exact Nat.find_min' h ((h_eq _).mp (Nat.find_spec h'))
  · have h' : ¬ ∃ x, k < cumulativeHitsUnit α β ω u x := by
      rintro ⟨x, hx⟩; exact h ⟨x, (h_eq x).mp hx⟩
    rw [dite_eq_right h, dite_eq_right h']

/-- In the degenerate case, sortedMultisetUnit agrees with sortedMultiset. -/
private lemma sorted_multiset_unit_eq_sorted_multiset_of_dvd
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h_dvd : (α ^ 2 + β ^ 2) ∣ (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) (i : ℤ) :
    sortedMultisetUnit α β ω u i = sortedMultiset α β ω i := by
  change ((VUnit α β ω u (i % ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat).toNat : ℤ) +
        (i / ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) * ↑(α ^ 2 + β ^ 2)) =
       ((V α β ω (i % ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat).toNat : ℤ) +
        (i / ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) * ↑(α ^ 2 + β ^ 2))
  rw [V_unit_eq_V_of_dvd α β ω u h_dvd]

/-- In the degenerate case, differenceSequenceUnit agrees with differenceSequence. -/
private lemma difference_sequence_unit_eq_difference_sequence_of_dvd
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h_dvd : (α ^ 2 + β ^ 2) ∣ (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) :
    differenceSequenceUnit α β ω u = differenceSequence α β ω := by
  funext i
  unfold differenceSequenceUnit differenceSequence
  rw [sorted_multiset_unit_eq_sorted_multiset_of_dvd α β ω u h_dvd,
      sorted_multiset_unit_eq_sorted_multiset_of_dvd α β ω u h_dvd]

/-- Unit-aware analogue of `period_N_concrete`. -/
lemma period_N_unit_concrete (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) :
    let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
    IsPeriod (differenceSequenceUnit α β ω u) N := by
  intro N
  refine ⟨N_pos_concrete α β ω h_ω, ?_⟩
  intro i
  show differenceSequenceUnit α β ω u (i + ↑N) = differenceSequenceUnit α β ω u i
  unfold differenceSequenceUnit
  have h1 := sorted_multiset_unit_add_N α β ω h_ω u (i + 1)
  have h2 := sorted_multiset_unit_add_N α β ω h_ω u i
  have h3 : i + ↑N + 1 = (i + 1) + ↑N := by ring
  rw [h3]; linarith

/-- Unit-aware analogue of `sigma_of_period_concrete`. -/
lemma sigma_of_period_unit_concrete (α β : ℕ) (_h_coprime : Nat.Coprime α β)
    (ω : ℝ) (h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) :
    ∀ L > 0, IsPeriod (differenceSequenceUnit α β ω u) L →
    ∃ σ : ℕ, σ * (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat = L * (α ^ 2 + β ^ 2) ∧
    ∃ r0 : ℕ, ∀ x : ZMod (α ^ 2 + β ^ 2),
      countHitsUnit (α ^ 2 + β ^ 2) u r0 (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
        (x + (σ : ZMod (α ^ 2 + β ^ 2))) =
      countHitsUnit (α ^ 2 + β ^ 2) u r0 (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat x := by
  intro L hL_pos hL_period
  let σ_ℤ := sortedMultisetUnit α β ω u ↑L - sortedMultisetUnit α β ω u 0
  have h_nonneg : 0 ≤ σ_ℤ := shift_nonneg_unit α β ω h_ω u L hL_pos hL_period
  refine ⟨σ_ℤ.toNat, ?_, ?_⟩
  · have h_eq : ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat * σ_ℤ = ↑L * ↑(α ^ 2 + β ^ 2) :=
      shift_times_N_eq_unit α β ω h_ω u L hL_period
    have h_cast : (↑(σ_ℤ.toNat) : ℤ) = σ_ℤ := Int.toNat_of_nonneg h_nonneg
    have h_eq_int : (↑(σ_ℤ.toNat * (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat) : ℤ) =
        ↑(L * (α ^ 2 + β ^ 2)) := by
      push_cast; rw [h_cast]
      have h2 : ↑(⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat * σ_ℤ =
          ↑L * ↑(α ^ 2 + β ^ 2) := h_eq
      push_cast at h2
      linarith
    exact_mod_cast h_eq_int
  · refine ⟨((-⌊ω * ↑β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val, ?_⟩
    exact count_hits_shift_invariant_unit α β ω h_ω u L hL_pos hL_period

/-- Unit-aware analogue of `period_degenerate_concrete`. In the degenerate
case the unit-twisted sequence equals the untwisted one
(`difference_sequence_unit_eq_difference_sequence_of_dvd`), so the period
result transfers directly from `period_degenerate_concrete`. -/
lemma period_degenerate_unit_concrete (α β : ℕ) (h_coprime : Nat.Coprime α β)
    (ω : ℝ) (h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) :
    let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    D ∣ N → HasPeriodLength (differenceSequenceUnit α β ω u) (N / D) := by
  intro N D h_dvd
  rw [difference_sequence_unit_eq_difference_sequence_of_dvd α β ω u h_dvd]
  exact period_degenerate_concrete α β h_coprime ω h_ω h_dvd

/-- Unit-aware concrete main theorem. Combines the period-N and degenerate
cases plus the minimality argument from `heavy_set_unit_is_cyclic_interval`.
For `u = multiplier α β h_coprime`, this is the geometric main theorem
(`main_theorem_geometric_concrete` below). -/
theorem main_theorem_unit_concrete (α β : ℕ) (h_coprime : Nat.Coprime α β)
    (ω : ℝ) (h_ω : 0 ≤ ω) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) :
    HasPeriodLength (differenceSequenceUnit α β ω u)
      (if (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat then
        (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat / (α ^ 2 + β ^ 2)
       else (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) := by
  by_cases h_dvd : (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  · simp only [ite_eq_left h_dvd]
    exact period_degenerate_unit_concrete α β h_coprime ω h_ω u h_dvd
  · simp only [ite_eq_right h_dvd]
    refine ⟨period_N_unit_concrete α β ω h_ω u, ?_⟩
    intro L hL_pos hL_period
    have h_sigma := sigma_of_period_unit_concrete α β h_coprime ω h_ω u L hL_pos hL_period
    rcases h_sigma with ⟨σ, h_sigma_eq, r0, h_inv_count⟩
    let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
    let q := N / (α ^ 2 + β ^ 2)
    let s := N % (α ^ 2 + β ^ 2)
    have h_s_pos : 0 < s :=
      Nat.pos_of_ne_zero (fun h => h_dvd (Nat.dvd_of_mod_eq_zero h))
    have h_s_lt : s < α ^ 2 + β ^ 2 :=
      Nat.mod_lt N (Nat.pos_of_ne_zero (NeZero.ne (α ^ 2 + β ^ 2)))
    have h_heavy_eq := heavy_set_unit_is_cyclic_interval (α ^ 2 + β ^ 2) u r0 N
    have h_inv : ∀ y : ZMod (α ^ 2 + β ^ 2),
        y ∈ cyclicInterval (α ^ 2 + β ^ 2) s
              ((r0 + q * (α ^ 2 + β ^ 2) : ℕ) : ZMod (α ^ 2 + β ^ 2)) ↔
        y + ((u⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
            (σ : ZMod (α ^ 2 + β ^ 2)) ∈
          cyclicInterval (α ^ 2 + β ^ 2) s
            ((r0 + q * (α ^ 2 + β ^ 2) : ℕ) : ZMod (α ^ 2 + β ^ 2)) := by
      intro y
      have hx := h_heavy_eq ((u : ZMod (α ^ 2 + β ^ 2)) * y)
      have hx' := h_heavy_eq
        ((u : ZMod (α ^ 2 + β ^ 2)) * y + (σ : ZMod (α ^ 2 + β ^ 2)))
      have h_inv_y :
          ((u⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
            ((u : ZMod (α ^ 2 + β ^ 2)) * y) = y := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      have h_inv_yσ :
          ((u⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
            ((u : ZMod (α ^ 2 + β ^ 2)) * y + (σ : ZMod (α ^ 2 + β ^ 2))) =
          y + ((u⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
            (σ : ZMod (α ^ 2 + β ^ 2)) := by
        rw [mul_add, ← mul_assoc, Units.inv_mul, one_mul]
      rw [h_inv_y] at hx
      rw [h_inv_yσ] at hx'
      rw [← hx, ← hx', h_inv_count ((u : ZMod (α ^ 2 + β ^ 2)) * y)]
    have h_zero : ((u⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
        (σ : ZMod (α ^ 2 + β ^ 2)) = 0 :=
      cyclic_interval_stabilizer_trivial (α ^ 2 + β ^ 2) s
        ((r0 + q * (α ^ 2 + β ^ 2) : ℕ) : ZMod (α ^ 2 + β ^ 2))
        (((u⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
          (σ : ZMod (α ^ 2 + β ^ 2))) h_s_pos h_s_lt h_inv
    have h_sigma_zero : (σ : ZMod (α ^ 2 + β ^ 2)) = 0 := by
      have := congrArg (fun z => (u : ZMod (α ^ 2 + β ^ 2)) * z) h_zero
      simp only [mul_zero, ← mul_assoc, Units.mul_inv, one_mul] at this
      exact this
    have h_sigma_dvd : (α ^ 2 + β ^ 2) ∣ σ :=
      (ZMod.natCast_eq_zero_iff σ (α ^ 2 + β ^ 2)).mp h_sigma_zero
    rcases h_sigma_dvd with ⟨k, rfl⟩
    have h_eq : (α ^ 2 + β ^ 2) * k * N = L * (α ^ 2 + β ^ 2) := h_sigma_eq
    have h_eq2 : k * N * (α ^ 2 + β ^ 2) = L * (α ^ 2 + β ^ 2) := by
      calc k * N * (α ^ 2 + β ^ 2) = (α ^ 2 + β ^ 2) * k * N := by ring
        _ = L * (α ^ 2 + β ^ 2) := h_eq
    have h_eq3 : k * N = L :=
      mul_right_cancel₀ (NeZero.ne (α ^ 2 + β ^ 2)) h_eq2
    have h_k_pos : 0 < k := by
      by_contra h_k
      have h_k0 : k = 0 := by omega
      rw [h_k0, zero_mul] at h_eq3
      omega
    have hN_pos : 0 < N := N_pos_concrete α β ω h_ω
    have h_N_le : N ≤ k * N := Nat.le_mul_of_pos_left N h_k_pos
    omega

/-- Geometric concrete main theorem. Specialises `main_theorem_unit_concrete`
to the geometric multiplier `u = multiplier α β h_coprime`, so the period
result holds for the residue-model enumeration carrying the geometric
residues `c_{r0+r} ≡ -αβ⁻¹ · (r0 + r) (mod D)` (paper §9.3, Layer 2; the
reduction from the lattice strip is not formalised — see the module
docstring). -/
theorem main_theorem_geometric_concrete
    (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] :
    HasPeriodLength
      (differenceSequenceUnit α β ω (multiplier α β h_coprime))
      (if (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat then
        (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat / (α ^ 2 + β ^ 2)
       else (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) :=
  main_theorem_unit_concrete α β h_coprime ω h_ω (multiplier α β h_coprime)

/--
The geometric residue of the integer point indexed by `r`, as defined in
equation `eq:residue` of the paper:
`cR ≡ -α · β⁻¹ · r (mod D)`.

This formalises the residue-class formula used by Section 3 of the paper
(strip-to-residue reduction). The function below is just `multiplier · r`
in `ZMod D`; the bridge lemma `c_r_eq_multiplier_mul_r` makes the equation
to the paper explicit, and `count_hits_unit_multiplier_eq_c_r_count`
shows that the unit-twisted hit-counter used in
`differenceSequenceUnit α β ω (multiplier α β h_coprime)` precisely
counts integer indices `i ∈ [0, N)` with `c_{r0 + i} ≡ x (mod D)`.
-/
def cR (α β : ℕ) (h_coprime : Nat.Coprime α β)
    (r : ℤ) : ZMod (α ^ 2 + β ^ 2) :=
  ((multiplier α β h_coprime : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
    (r : ZMod (α ^ 2 + β ^ 2))

/--
Bridge lemma to the paper's cR formula. The Lean `multiplier` equals
`-α · β⁻¹` as a unit in `ZMod D`, so `cR α β h r = -α · β⁻¹ · r (mod D)`
matches equation `eq:residue` of the paper verbatim.
-/
lemma c_r_eq_multiplier_mul_r (α β : ℕ) (h_coprime : Nat.Coprime α β)
    (r : ℤ) :
    cR α β h_coprime r =
      -((alphaUnit α β h_coprime : (ZMod (α ^ 2 + β ^ 2))ˣ) :
          ZMod (α ^ 2 + β ^ 2)) *
       (((betaUnit α β h_coprime)⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) :
          ZMod (α ^ 2 + β ^ 2)) *
       (r : ZMod (α ^ 2 + β ^ 2)) := by
  unfold cR multiplier
  push_cast
  ring

/--
Bridge from the paper's residue map to the unit-twisted hit counter.
`countHitsUnit (α^2+β^2) (multiplier α β h_coprime) r0 N x` is exactly
the cardinality of `{i ∈ [0, N) : c_{r0+i} ≡ x (mod D)}`, where
`c_{r0+i}` is the geometric residue from the paper. This makes the
formalisation of `main_theorem_geometric_concrete` an honest statement
about the geometric cR enumeration.
-/
lemma count_hits_unit_multiplier_eq_c_r_count
    (α β : ℕ) (h_coprime : Nat.Coprime α β)
    (r0 N : ℕ) (x : ZMod (α ^ 2 + β ^ 2)) :
    countHitsUnit (α ^ 2 + β ^ 2) (multiplier α β h_coprime) r0 N x =
    ((Finset.range N).filter
      (fun i => cR α β h_coprime ((r0 + i : ℕ) : ℤ) = x)).card := by
  unfold countHitsUnit cR
  congr 1
  apply Finset.filter_congr
  intro i _
  have h_cast : (((r0 + i : ℕ) : ℤ) : ZMod (α ^ 2 + β ^ 2)) =
      ((r0 : ZMod (α ^ 2 + β ^ 2)) + (i : ZMod (α ^ 2 + β ^ 2))) := by push_cast; ring
  rw [h_cast]

/--
Concrete set-valued period theorem. The `setDifferenceSequence` defined
above realises the abstract `set_main_theorem`, closing the asymmetry
between the multiset side (`main_theorem`, line 1903 — instantiated via
`GeometricProjectionConcrete`) and the set side. -/
theorem set_main_theorem_concrete
    (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] :
    HasPeriodLength (setDifferenceSequence α β ω)
      (if (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2 then
        (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
       else 1) := by
  have : GeometricProjection α β ω (differenceSequence α β ω) :=
    GeometricProjectionConcrete α β h_coprime ω h_ω
  exact set_main_theorem α β h_coprime ω h_ω (setDifferenceSequence α β ω)
    (set_difference_sequence_eq_of_lt α β ω)
    (set_difference_sequence_eq_one_of_ge α β ω)

-- =====================================================================
-- Unit-aware set-valued construction (Phase 2 step 3 — set side).
-- =====================================================================

/-- Unit-aware set indicator: `1` if residue `(y : ZMod D)` is hit at least once
under the multiplier-twisted progression, else `0`. -/
noncomputable def setIndicatorUnit (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (y : ℕ) : ℕ :=
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  if 1 ≤ countHitsUnit D u r0 N (y : ZMod D) then 1 else 0

/-- Unit-twisted set-convention analogue of `cumulativeHits`. -/
noncomputable def setCumulativeHitsUnit (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sum (setIndicatorUnit α β ω u)

open Classical in
/-- Unit-twisted set-convention analogue of `setV`. -/
noncomputable def setVUnit (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (k : ℕ) : ℕ :=
  if h : ∃ x, k < setCumulativeHitsUnit α β ω u x then
    Nat.find h
  else
    0

/-- Unit-twisted set-convention analogue of `setSize` (number of distinct residues hit). -/
noncomputable def setSizeUnit (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) : ℕ :=
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  (Finset.univ.filter (fun x : ZMod D => 1 ≤ countHitsUnit D u r0 N x)).card

/-- Unit-twisted set-convention analogue of `setSorted`. -/
noncomputable def setSortedUnit (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (i : ℤ) : ℤ :=
  let M := (setSizeUnit α β ω u : ℤ)
  let D := α ^ 2 + β ^ 2
  let r := (i % M).toNat
  let q := i / M
  (setVUnit α β ω u r : ℤ) + q * D

/-- Unit-aware concrete set-valued gap sequence. With
`u = multiplier α β h_coprime` this is the residue-model counterpart of the
geometric set enumeration (identification definitional, not proved). -/
noncomputable def setDifferenceSequenceUnit (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (i : ℤ) : ℤ :=
  setSortedUnit α β ω u (i + 1) - setSortedUnit α β ω u i

/-! ### Unit-aware Phase C, branch `N < D`: agreement with `differenceSequenceUnit` -/

lemma set_indicator_unit_eq_count_hits_unit_of_lt
    (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (y : ℕ) :
    setIndicatorUnit α β ω u y =
      countHitsUnit (α ^ 2 + β ^ 2) u
        (((-⌊ω * β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val)
        ((⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (y : ZMod (α ^ 2 + β ^ 2)) := by
  rw [count_hits_unit_eq_count_hits]
  have h_le := count_hits_lt_D (α ^ 2 + β ^ 2)
      (((-⌊ω * β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val)
      (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat h
      (((u⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
        ((y : ℕ) : ZMod (α ^ 2 + β ^ 2)))
  change (if 1 ≤ countHitsUnit _ _ _ _ _ then 1 else 0) = _
  rw [count_hits_unit_eq_count_hits]
  split_ifs with hge
  · omega
  · push Not at hge; omega

lemma set_cumulative_hits_unit_eq_of_lt
    (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (x : ℕ) :
    setCumulativeHitsUnit α β ω u x = cumulativeHitsUnit α β ω u x := by
  change (Finset.range (x + 1)).sum (setIndicatorUnit α β ω u) = _
  apply Finset.sum_congr rfl
  intro y _
  exact set_indicator_unit_eq_count_hits_unit_of_lt α β ω u h y

lemma set_V_unit_eq_V_unit_of_lt
    (α β : ℕ) (ω : ℝ)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (k : ℕ) :
    setVUnit α β ω u k = VUnit α β ω u k := by
  have h_funeq : setCumulativeHitsUnit α β ω u = cumulativeHitsUnit α β ω u :=
    funext (set_cumulative_hits_unit_eq_of_lt α β ω u h)
  unfold setVUnit VUnit
  rw [h_funeq]

lemma set_size_unit_eq_N_of_lt
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) :
    setSizeUnit α β ω u = (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat := by
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  have h_div : N / D = 0 := Nat.div_eq_of_lt h
  have h_mod : N % D = N := Nat.mod_eq_of_lt h
  have h_dist := (residue_distribution_unit D u r0 N).1
  simp only [h_div, h_mod, zero_add] at h_dist
  have h_le : ∀ x : ZMod D, countHitsUnit D u r0 N x ≤ 1 := fun x => by
    rw [count_hits_unit_eq_count_hits]
    exact count_hits_lt_D D r0 N h _
  change (Finset.univ.filter (fun x : ZMod D => 1 ≤ countHitsUnit D u r0 N x)).card = N
  have h_filter_eq :
      (Finset.univ.filter (fun x : ZMod D => 1 ≤ countHitsUnit D u r0 N x)) =
      (Finset.univ.filter (fun x : ZMod D => countHitsUnit D u r0 N x = 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hge; have := h_le x; omega
    · intro heq; omega
  rw [h_filter_eq]
  exact h_dist

lemma set_sorted_unit_eq_of_lt
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (i : ℤ) :
    setSortedUnit α β ω u i = sortedMultisetUnit α β ω u i := by
  change (setVUnit α β ω u (i % ((setSizeUnit α β ω u : ℤ))).toNat : ℤ) +
       (i / (setSizeUnit α β ω u : ℤ)) * (α ^ 2 + β ^ 2 : ℕ) =
       (VUnit α β ω u (i % ((⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat : ℤ)).toNat : ℤ) +
       (i / ((⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat : ℤ)) * (α ^ 2 + β ^ 2 : ℕ)
  rw [set_size_unit_eq_N_of_lt α β ω u h, set_V_unit_eq_V_unit_of_lt α β ω u h]

/-- **Discharge of `h_lt`** for the unit case: under `N < D`, the unit
set sequence agrees pointwise with `differenceSequenceUnit`. -/
lemma set_difference_sequence_unit_eq_of_lt
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2) (i : ℤ) :
    setDifferenceSequenceUnit α β ω u i = differenceSequenceUnit α β ω u i := by
  change setSortedUnit α β ω u (i + 1) - setSortedUnit α β ω u i =
       sortedMultisetUnit α β ω u (i + 1) - sortedMultisetUnit α β ω u i
  rw [set_sorted_unit_eq_of_lt α β ω u h (i + 1),
      set_sorted_unit_eq_of_lt α β ω u h i]

/-! ### Unit-aware Phase C, branch `D ≤ N`: constant-`1` set sequence -/

lemma set_indicator_unit_eq_one_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (y : ℕ) :
    setIndicatorUnit α β ω u y = 1 := by
  have h_ge := count_hits_ge_D (α ^ 2 + β ^ 2)
      (((-⌊ω * β⌋ : ℤ) : ZMod (α ^ 2 + β ^ 2)).val)
      (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat h
      (((u⁻¹ : (ZMod (α ^ 2 + β ^ 2))ˣ) : ZMod (α ^ 2 + β ^ 2)) *
        ((y : ℕ) : ZMod (α ^ 2 + β ^ 2)))
  change (if 1 ≤ countHitsUnit _ _ _ _ _ then 1 else 0) = 1
  rw [count_hits_unit_eq_count_hits]
  rw [ite_eq_left h_ge]

lemma set_cumulative_hits_unit_eq_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (x : ℕ) :
    setCumulativeHitsUnit α β ω u x = x + 1 := by
  change (Finset.range (x + 1)).sum (setIndicatorUnit α β ω u) = x + 1
  calc (Finset.range (x + 1)).sum (setIndicatorUnit α β ω u)
      = (Finset.range (x + 1)).sum (fun _ : ℕ => 1) :=
        Finset.sum_congr rfl (fun y _ => set_indicator_unit_eq_one_of_ge α β ω u h y)
    _ = x + 1 := by simp

lemma set_V_unit_eq_id_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (k : ℕ) :
    setVUnit α β ω u k = k := by
  have h_cum : ∀ x, setCumulativeHitsUnit α β ω u x = x + 1 :=
    set_cumulative_hits_unit_eq_of_ge α β ω u h
  have hex : ∃ x, k < setCumulativeHitsUnit α β ω u x := ⟨k, by rw [h_cum]; omega⟩
  unfold setVUnit
  rw [dite_eq_left hex]
  apply Nat.find_eq_iff _ |>.mpr
  refine ⟨?_, ?_⟩
  · rw [h_cum]; omega
  · intro m hm; rw [h_cum]; omega

lemma set_size_unit_eq_D_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) :
    setSizeUnit α β ω u = α ^ 2 + β ^ 2 := by
  let D := α ^ 2 + β ^ 2
  let r0 := ((-⌊ω * β⌋ : ℤ) : ZMod D).val
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  have h_ge : ∀ x : ZMod D, 1 ≤ countHitsUnit D u r0 N x := fun x => by
    rw [count_hits_unit_eq_count_hits]
    exact count_hits_ge_D D r0 N h _
  change (Finset.univ.filter (fun x : ZMod D => 1 ≤ countHitsUnit D u r0 N x)).card = D
  have h_filter_eq :
      Finset.univ.filter (fun x : ZMod D => 1 ≤ countHitsUnit D u r0 N x) =
      (Finset.univ : Finset (ZMod D)) := by
    ext x; simp [h_ge x]
  rw [h_filter_eq, Finset.card_univ, ZMod.card]

lemma set_sorted_unit_eq_id_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (i : ℤ) :
    setSortedUnit α β ω u i = i := by
  have hD_pos : 0 < α ^ 2 + β ^ 2 := by
    have : NeZero (α ^ 2 + β ^ 2) := inferInstance
    exact Nat.pos_of_ne_zero this.out
  have hD_ne : ((α ^ 2 + β ^ 2 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hD_pos.ne'
  change (setVUnit α β ω u (i % ((setSizeUnit α β ω u : ℤ))).toNat : ℤ) +
       (i / (setSizeUnit α β ω u : ℤ)) * (α ^ 2 + β ^ 2 : ℕ) = i
  rw [set_size_unit_eq_D_of_ge α β ω u h]
  have hmod_nn : 0 ≤ i % ((α ^ 2 + β ^ 2 : ℕ) : ℤ) := Int.emod_nonneg i hD_ne
  have hmod_lt : i % ((α ^ 2 + β ^ 2 : ℕ) : ℤ) < ((α ^ 2 + β ^ 2 : ℕ) : ℤ) :=
    Int.emod_lt_of_pos i (by exact_mod_cast hD_pos)
  set r : ℕ := (i % ((α ^ 2 + β ^ 2 : ℕ) : ℤ)).toNat with hr_def
  have hr_lt : r < α ^ 2 + β ^ 2 := by
    have : (r : ℤ) < ((α ^ 2 + β ^ 2 : ℕ) : ℤ) := by
      rw [hr_def, Int.toNat_of_nonneg hmod_nn]; exact hmod_lt
    exact_mod_cast this
  rw [set_V_unit_eq_id_of_ge α β ω u h r]
  have h_r_int : (r : ℤ) = i % ((α ^ 2 + β ^ 2 : ℕ) : ℤ) := by
    rw [hr_def, Int.toNat_of_nonneg hmod_nn]
  rw [h_r_int]
  have := Int.emod_add_mul_ediv i ((α ^ 2 + β ^ 2 : ℕ) : ℤ)
  linarith

/-- **Discharge of `h_ge`** for the unit case: under `D ≤ N`, the unit
set sequence is constantly `1`. -/
lemma set_difference_sequence_unit_eq_one_of_ge
    (α β : ℕ) (ω : ℝ) [NeZero (α ^ 2 + β ^ 2)]
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ)
    (h : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) (i : ℤ) :
    setDifferenceSequenceUnit α β ω u i = 1 := by
  change setSortedUnit α β ω u (i + 1) - setSortedUnit α β ω u i = 1
  rw [set_sorted_unit_eq_id_of_ge α β ω u h (i + 1),
      set_sorted_unit_eq_id_of_ge α β ω u h i]
  ring

/-- Unit-aware abstract set-valued period theorem. Parallel to
`set_main_theorem` but uses `main_theorem_unit_concrete` (the unit-aware
multiset main theorem) for the `N < D` branch. -/
theorem set_main_theorem_unit
    (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (set_seq : ℤ → ℤ)
    [NeZero (α ^ 2 + β ^ 2)]
    (h_lt : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2 →
            ∀ i, set_seq i = differenceSequenceUnit α β ω u i)
    (h_ge : α ^ 2 + β ^ 2 ≤ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat →
            ∀ i, set_seq i = 1) :
    HasPeriodLength set_seq
      (if (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2 then
        (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
       else 1) := by
  by_cases h : (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2
  · rw [ite_eq_left h]
    have h_eq : set_seq = differenceSequenceUnit α β ω u := funext (h_lt h)
    rw [h_eq]
    have hN_pos : 0 < (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat := N_pos_concrete α β ω h_ω
    have hND : ¬ (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat := by
      intro hd
      have := Nat.le_of_dvd hN_pos hd
      omega
    have h_main : HasPeriodLength (differenceSequenceUnit α β ω u)
        (if (α ^ 2 + β ^ 2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
         then (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat / (α ^ 2 + β ^ 2)
         else (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat) :=
      main_theorem_unit_concrete α β h_coprime ω h_ω u
    rw [ite_eq_right hND] at h_main
    exact h_main
  · rw [ite_eq_right h]
    exact HasPeriodLength_const_one set_seq (h_ge (not_lt.mp h))

/-- Geometric concrete set-valued main theorem. Specialises
`set_main_theorem_unit` to `u = multiplier α β h_coprime` and discharges
the dichotomy axioms via the unit-aware Phase C lemmas. -/
theorem set_main_theorem_geometric_concrete
    (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α ^ 2 + β ^ 2)] :
    HasPeriodLength
      (setDifferenceSequenceUnit α β ω (multiplier α β h_coprime))
      (if (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat < α ^ 2 + β ^ 2 then
        (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
       else 1) :=
  set_main_theorem_unit α β h_coprime ω h_ω (multiplier α β h_coprime)
    (setDifferenceSequenceUnit α β ω (multiplier α β h_coprime))
    (set_difference_sequence_unit_eq_of_lt α β ω (multiplier α β h_coprime))
    (set_difference_sequence_unit_eq_one_of_ge α β ω (multiplier α β h_coprime))

end CutAndProject
