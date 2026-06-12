/-
Copyright (c) 2026 Antoine de Saint Germain, Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine de Saint Germain, Ambrose Tang
-/

import Mathlib.Order.Interval.Finset.Fin
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Aesop
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-!
# Type-Aₙ root systems

Explicit construction of the type-`Aₙ` root pairing on the weight lattice `Fin n → ℤ`,
exhibited as a crystallographic, reduced Mathlib `RootPairing`.
-/

namespace An

/-- The integral weight lattice `Fin n → ℤ` underlying the type-Aₙ root pairing. -/
abbrev Zn (n : ℕ) := Fin n → ℤ
/-- The `ℤ`-linear dual of `Zn n`, carrying the coroots. -/
abbrev ZnDual (n : ℕ) := Module.Dual ℤ (Zn n)

/-- The covector extracting the `k`-th coordinate of a vector in `Zn n`. -/
def eTranspose {n : ℕ} (k : Fin n) : ZnDual n :=
  { toFun := fun t => t k
    map_add' := by intro t s; rfl
    map_smul' := by intro a t; rfl }

/-- The `k`-th column vector: `2` at index `k`, `-1` at the neighbours of `k`, and `0` elsewhere. -/
def Ae {n : ℕ} (k : Fin n) : Zn n :=
  fun t =>
    if t = k then 2
    else if (k : ℕ) + 1 = (t : ℕ) ∨ (t : ℕ) + 1 = (k : ℕ) then -1
    else 0

/-- A signed interval `[i, j]` in `Fin n` with a sign `ε`; indexes the roots of type Aₙ. -/
structure SignedInterval (n : ℕ) where
  /-- The left endpoint of the interval. -/
  i : Fin n
  /-- The right endpoint of the interval. -/
  j : Fin n
  hij : i ≤ j
  /-- The Boolean sign attached to the interval. -/
  ε : Bool

/-- The integer sign of a signed interval: `1` when `ε` is true, otherwise `-1`. -/
def SignedInterval.sign {n : ℕ} (J : SignedInterval n) : ℤ :=
  if J.ε then 1 else -1

/-- The root of type Aₙ associated to a signed interval. -/
def α {n : ℕ} (J : SignedInterval n) : Zn n :=
  J.sign • Finset.sum (Finset.Icc J.i J.j) (fun k => Ae k)

/-- The coroot of type Aₙ associated to a signed interval. -/
def αDual {n : ℕ} (J : SignedInterval n) : ZnDual n :=
  J.sign • Finset.sum (Finset.Icc J.i J.j) (fun k => eTranspose k)

/-- The reflection permutation for signed intervals.
    For positive intervals J = [i,j] and K = [k,l]:
    - If (i,j) = (k,l): returns -[k,l]
    - If i = l+1: returns [k,j]   (merge: K then J)
    - If k = j+1: returns [i,l]   (merge: J then K)
    - If i = k, j > l: returns -[l+1, j]
    - If i = k, j < l: returns [j+1, l]
    - If i < k, j = l: returns -[i, k-1]
    - If i > k, j = l: returns [k, i-1]
    - Otherwise: returns [k,l]
    Then s_{-J} = s_J and s_J(-K) = -s_J(K). -/
def s {n : ℕ} (J K : SignedInterval n) : SignedInterval n :=
  -- The sign of the output: if K is negative, flip the unsigned result sign
  let signAdj (b : Bool) : Bool := if K.ε then b else !b
  if h₀ : J.i = K.i ∧ J.j = K.j then
    { i := K.i, j := K.j, hij := K.hij, ε := signAdj false }
  else if h₁ : (J.i : ℕ) = (K.j : ℕ) + 1 then
    { i := K.i
      j := J.j
      hij := by
        have hKi : (K.i : ℕ) ≤ K.j := Fin.le_iff_val_le_val.mp K.hij
        have hJi : (J.i : ℕ) ≤ J.j := Fin.le_iff_val_le_val.mp J.hij
        exact Fin.le_iff_val_le_val.mpr (by omega)
      ε := signAdj true }
  else if h₂ : (K.i : ℕ) = (J.j : ℕ) + 1 then
    { i := J.i
      j := K.j
      hij := by
        have hJi : (J.i : ℕ) ≤ J.j := Fin.le_iff_val_le_val.mp J.hij
        have hKj : (K.i : ℕ) ≤ K.j := Fin.le_iff_val_le_val.mp K.hij
        exact Fin.le_iff_val_le_val.mpr (by omega)
      ε := signAdj true }
  else if h₃ : J.i = K.i ∧ (J.j : ℕ) > (K.j : ℕ) then
    { i := ⟨(K.j : ℕ) + 1, by have := J.j.isLt; omega⟩
      j := J.j
      hij := by simp only [Fin.le_iff_val_le_val]; omega
      ε := signAdj false }
  else if h₄ : J.i = K.i ∧ (J.j : ℕ) < (K.j : ℕ) then
    { i := ⟨(J.j : ℕ) + 1, by have := K.j.isLt; omega⟩
      j := K.j
      hij := by simp only [Fin.le_iff_val_le_val]; omega
      ε := signAdj true }
  else if h₅ : (J.i : ℕ) < (K.i : ℕ) ∧ J.j = K.j then
    { i := J.i
      j := ⟨(K.i : ℕ) - 1, by have := K.i.isLt; omega⟩
      hij := by simp only [Fin.le_iff_val_le_val]; omega
      ε := signAdj false }
  else if h₆ : (J.i : ℕ) > (K.i : ℕ) ∧ J.j = K.j then
    { i := K.i
      j := ⟨(J.i : ℕ) - 1, by have := J.i.isLt; omega⟩
      hij := by simp only [Fin.le_iff_val_le_val]; omega
      ε := signAdj true }
  else
    { i := K.i, j := K.j, hij := K.hij, ε := signAdj true }

/-- The canonical evaluation pairing between `Zn n` and its dual `ZnDual n`. -/
noncomputable abbrev ZnPairing (n : ℕ) : Zn n →ₗ[ℤ] ZnDual n →ₗ[ℤ] ℤ :=
  Module.Dual.eval ℤ (Zn n)

-- Helper: SignedInterval extensional equality
@[ext]
theorem SignedInterval.ext' {n : ℕ} {J K : SignedInterval n}
    (hi : J.i = K.i) (hj : J.j = K.j) (hε : J.ε = K.ε) : J = K := by
  cases J; cases K; simp_all

/-
s is involutive
-/
theorem s_involutive {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    s J (s J K) = K := by
  cases J; cases K; simp +decide only [s, Bool.not_false, Bool.if_true_right, Bool.decide_eq_true,
    Bool.or_false, Bool.not_true, Bool.if_false_right, Bool.and_true, gt_iff_lt, Fin.val_fin_lt,
    dite_eq_ite];
  rename_i k l hk hl;
  rename_i i j hij ε;
  by_cases hi : i.val = l.val + 1 <;>
    by_cases hj : k.val = j.val + 1 <;>
    simp +decide only [hi, hj, ↓reduceDIte, Nat.add_right_cancel_iff,
      add_tsub_cancel_right, Fin.eta];
  · grind;
  · grind +locals;
  · grind;
  · by_cases hi : i = k <;> by_cases hj : j = l <;>
      simp +decide only [hi, hj, and_self, ↓reduceIte, Bool.not_not, not_false_eq_true, and_false,
        true_and, lt_self_iff_false, ↓reduceDIte, and_true, false_and] at *;
    · by_cases h : l < j <;> by_cases h' : j < l <;>
        simp +decide only [h, h', ↓reduceDIte, and_true, Bool.not_not, Nat.add_right_cancel_iff,
          lt_self_iff_false, and_false, add_tsub_cancel_right, Fin.eta, not_false_eq_true,
          true_and, false_and] at *;
      · grind;
      · grind;
      · grind;
      · grind;
    · by_cases h : i < k <;>
        simp +decide only [h, ↓reduceDIte, true_and, Bool.not_not, lt_self_iff_false, false_and,
          not_false_eq_true] at *;
      · grind;
      · grind;
    · aesop

/-
The key formula: sum of Ae columns over an interval [p,q] evaluated at t
    gives δ_{t,p} + δ_{t,q} - δ_{t+1,p} - δ_{q+1,t} (using ℕ comparisons).
-/
theorem Ae_sum_eq {n : ℕ} [NeZero n] (p q : Fin n) (hpq : p ≤ q) (t : Fin n) :
    (∑ u ∈ Finset.Icc p q, Ae u) t =
    (if t = p then 1 else 0) + (if t = q then 1 else 0)
    - (if (t : ℕ) + 1 = (p : ℕ) then 1 else 0)
    - (if (q : ℕ) + 1 = (t : ℕ) then 1 else 0) := by
  induction q with
  | mk q hq =>
  induction q generalizing p t with
  | zero => rcases t with ⟨ _ | _ | t, ht ⟩ <;> simp_all +decide [ Ae ];
  | succ q ih =>
    by_cases hpq' : p = ⟨ q + 1, hq ⟩ <;>
      simp_all +decide only [Finset.sum_apply, Std.le_refl, Finset.Icc_self, Finset.sum_singleton,
        Nat.add_right_cancel_iff];
    · unfold Ae; split_ifs <;> simp_all +decide [ Fin.ext_iff ];
      linarith;
    · rw [show (Finset.Icc p ⟨ q + 1, hq ⟩ : Finset (Fin n)) =
          Finset.Icc p ⟨ q, by linarith ⟩ ∪ {⟨q + 1, hq⟩} from ?_,
        Finset.sum_union] <;> norm_num;
      · rw [ ih p t ( by linarith ) ( Nat.le_of_lt_succ ( hpq.lt_of_ne hpq' ) ) ];
        unfold Ae; simp +decide [ Fin.ext_iff ];
        grind;
      · grind

/-
Key consequence of Ae_sum_eq: α(J)(t) expressed in terms of Kronecker deltas
-/
theorem α_eval {n : ℕ} [NeZero n] (J : SignedInterval n) (t : Fin n) :
    α J t = J.sign * ((if t = J.i then 1 else 0) + (if t = J.j then 1 else 0)
    - (if (t : ℕ) + 1 = (J.i : ℕ) then 1 else 0)
    - (if (J.j : ℕ) + 1 = (t : ℕ) then 1 else 0)) := by
  have := @Ae_sum_eq;
  convert congr_arg ( fun x : ℤ => J.sign * x ) ( this J.i J.j J.hij t ) using 1

/-
Key consequence: αDual(J) evaluated on a test function
-/
theorem α_dual_eval {n : ℕ} [NeZero n] (J : SignedInterval n) (f : Zn n) :
    αDual J f = J.sign * ∑ v ∈ Finset.Icc J.i J.j, f v := by
  unfold αDual; simp +decide [Finset.mul_sum _ _ _]; ring_nf;
  rfl

/-
Pairing computation: L(α K, α^v J) in terms of interval endpoints
-/
theorem pairing_formula {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    (ZnPairing n (α K)) (αDual J) = J.sign * K.sign *
    ((if J.i = K.i then 1 else 0) + (if J.j = K.j then 1 else 0)
    - (if (J.i : ℕ) = (K.j : ℕ) + 1 then 1 else 0)
    - (if (K.i : ℕ) = (J.j : ℕ) + 1 then 1 else 0)) := by
  -- By definition, `αDual J (α K)` is a signed sum over the interval `J`.
  have h_dual :
      (ZnPairing n (α K)) (αDual J) =
        J.sign * ∑ v ∈ Finset.Icc J.i J.j, (α K) v := by
    convert α_dual_eval J ( α K ) using 1;
  simp_all +decide only [Module.Dual.eval_apply, α_eval, mul_assoc, mul_eq_mul_left_iff];
  have h_simplify3 :
      ∑ x ∈ Finset.Icc J.i J.j,
          (if (x : ℕ) + 1 = (K.i : ℕ) then 1 else 0) =
        if (J.i : ℕ) + 1 ≤ (K.i : ℕ) ∧ (K.i : ℕ) ≤ (J.j : ℕ) + 1
        then 1 else 0 := by
    split_ifs <;>
      simp_all +decide only [Order.add_one_le_iff, Fin.val_fin_lt, Finset.sum_boole, Nat.cast_id,
        not_and, not_le, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_Icc, and_imp];
    · rw [ Finset.card_eq_one ];
      use ⟨ K.i - 1, by
        exact lt_of_le_of_lt ( Nat.pred_le _ ) ( Fin.is_lt _ ) ⟩
      generalize_proofs at *;
      grind +locals;
    · grind;
  have h_simplify4 :
      ∑ x ∈ Finset.Icc J.i J.j,
          (if (K.j : ℕ) + 1 = (x : ℕ) then 1 else 0) =
        if (K.j : ℕ) + 1 ≥ (J.i : ℕ) ∧ (K.j : ℕ) + 1 ≤ (J.j : ℕ)
        then 1 else 0 := by
    split_ifs <;>
      simp_all +decide only [Finset.sum_boole, Nat.cast_id, Order.add_one_le_iff, Fin.val_fin_lt,
        ge_iff_le, not_and, not_lt, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_Icc,
        and_imp];
    · rw [ Finset.card_eq_one ];
      use ⟨ K.j + 1, by
        linarith [Fin.is_lt K.j, Fin.is_lt J.j, show (K.j : ℕ) < J.j from by tauto] ⟩
      ext
      aesop;
    · lia;
  rw [← Finset.mul_sum _ _ _]
  simp_all +decide [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  grind +suggestions

theorem pairing_self {n : ℕ} [NeZero n] (J : SignedInterval n) :
    (ZnPairing n (α J)) (αDual J) = 2 := by
  rw [pairing_formula J J]
  obtain ⟨i, j, hij, ε⟩ := J
  cases ε <;> simp +decide [SignedInterval.sign] <;> omega

theorem pairing_eq_two_iff_eq {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    (ZnPairing n (α K)) (αDual J) = 2 ↔ K = J := by
  constructor
  · intro h
    rw [pairing_formula J K] at h
    obtain ⟨Ji, Jj, Jh, Jε⟩ := J
    obtain ⟨Ki, Kj, Kh, Kε⟩ := K
    cases Jε <;> cases Kε <;> simp +decide [SignedInterval.sign] at h ⊢
    all_goals
      split_ifs at h <;> simp_all +decide <;> omega
  · intro h
    subst K
    exact pairing_self J

-- α is injective
theorem α_injective {n : ℕ} [NeZero n] : Function.Injective (α (n := n)) := by
  intro J K h
  exact ((pairing_eq_two_iff_eq J K).mp (by
    rw [← h]
    exact pairing_self J)).symm

/-
αDual is injective
-/
theorem α_dual_injective {n : ℕ} [NeZero n] : Function.Injective (αDual (n := n)) := by
  intro J K h
  exact (pairing_eq_two_iff_eq K J).mp (by
    rw [← h]
    exact pairing_self J)

/-
root_coroot_two
-/
theorem root_coroot_two' {n : ℕ} [NeZero n] (J : SignedInterval n) :
    (ZnPairing n) (α J) (αDual J) = 2 :=
  pairing_self J

-- reflection formula for roots
-- Proof sketch: ext t, rewrite using α_eval and pairing_formula on both sides,
-- then unfold s, case-split on signs and s-conditions.
-- The normalized endpoint identity creates many Boolean cases for `grind`.
theorem reflectionPerm_root_eval {n : ℕ} [NeZero n] (J K : SignedInterval n) (t : Fin n) :
    (α K - (ZnPairing n (α K)) (αDual J) • α J) t = α (s J K) t := by
  change (α K) t - ((ZnPairing n (α K)) (αDual J)) * (α J) t = α (s J K) t
  rw [pairing_formula J K]
  cases J
  cases K
  simp +decide [s, α_eval, SignedInterval.sign, Fin.ext_iff]
  grind (splits := 80)

theorem reflectionPerm_root' {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    α K - (ZnPairing n (α K)) (αDual J) • α J = α (s J K) := by
  ext t
  exact reflectionPerm_root_eval J K t

-- Pairing symmetry: L(α J, α^v K) = L(α K, α^v J)
theorem pairing_symm {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    (ZnPairing n (α J)) (αDual K) = (ZnPairing n (α K)) (αDual J) := by
  rw [pairing_formula J K, pairing_formula K J]
  obtain ⟨Ji, Jj, _, Jε⟩ := J
  obtain ⟨Ki, Kj, _, Kε⟩ := K
  unfold SignedInterval.sign
  cases Jε <;> cases Kε <;> simp only [ite_true] <;> split_ifs <;> omega

-- reflection formula for coroots
-- Proof sketch: use dual extensionality, so it suffices to evaluate on the coordinate
-- basis vector `LinearMap.single ... t 1`; then rewrite by α_dual_eval and pairing_formula.
-- The coordinate-basis reduction has the same endpoint case split as `reflectionPerm_root_eval`.
theorem reflectionPerm_coroot_single {n : ℕ} [NeZero n] (J K : SignedInterval n) (t : Fin n) :
    ((αDual K - (ZnPairing n (α J)) (αDual K) • αDual J) ∘ₗ
        LinearMap.single ℤ (fun _ : Fin n => ℤ) t) 1 =
      (αDual (s J K) ∘ₗ LinearMap.single ℤ (fun _ : Fin n => ℤ) t) 1 := by
  change αDual K (LinearMap.single ℤ (fun _ : Fin n => ℤ) t 1) -
      ((ZnPairing n (α J)) (αDual K)) *
      αDual J (LinearMap.single ℤ (fun _ : Fin n => ℤ) t 1) =
      αDual (s J K) (LinearMap.single ℤ (fun _ : Fin n => ℤ) t 1)
  rw [pairing_formula K J]
  cases J
  cases K
  simp +decide [s, α_dual_eval, SignedInterval.sign, Fin.ext_iff]
  grind (splits := 80)

theorem reflectionPerm_coroot' {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    αDual K - (ZnPairing n (α J)) (αDual K) • αDual J = αDual (s J K) := by
  ext t
  exact reflectionPerm_coroot_single J K t

/-- The type-Aₙ root pairing over `ℤ`, built from signed intervals on `Fin n`. -/
noncomputable def rootPairing (n : ℕ) [NeZero n] :
    RootPairing (SignedInterval n) ℤ (Zn n) (ZnDual n) where
  toLinearMap := ZnPairing n
  root :=
    { toFun := α
      inj' := α_injective
    }
  coroot :=
    { toFun := αDual
      inj' := α_dual_injective
    }
  root_coroot_two := root_coroot_two'
  reflectionPerm := fun J =>
    { toFun := s J
      invFun := s J
      left_inv := s_involutive J
      right_inv := s_involutive J }
  reflectionPerm_root := reflectionPerm_root'
  reflectionPerm_coroot := reflectionPerm_coroot'



instance finite (n : ℕ) : Fintype (SignedInterval n) := by
  exact Fintype.ofEquiv {x : (Fin n × Fin n) × Bool // x.1.1 ≤ x.1.2}
    { toFun := fun x =>
        { i := x.1.1.1
          j := x.1.1.2
          hij := x.2
          ε := x.1.2 }
      invFun := fun J => ⟨((J.i, J.j), J.ε), J.hij⟩
      left_inv := by
        intro x
        rcases x with ⟨⟨⟨i, j⟩, ε⟩, hij⟩
        rfl
      right_inv := by
        intro J
        cases J
        rfl }

lemma An_is_finite (n : ℕ) [NeZero n] : Finite (SignedInterval n) := by
  infer_instance

-- Proof that the root pairing is reduced
lemma An_is_reduced (n : ℕ) [NeZero n] : (rootPairing n).IsReduced := by
  rw [RootPairing.isReduced_iff]
  intro J K hlin
  have hcw : (rootPairing n).coxeterWeight J K = 4 := by
    exact (RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent (rootPairing n)).2 hlin
  change ((ZnPairing n (α J)) (αDual K) * (ZnPairing n (α K)) (αDual J) = 4) at hcw
  rw [pairing_formula K J, pairing_formula J K] at hcw
  obtain ⟨Ji, Jj, Jh, Jε⟩ := J
  obtain ⟨Ki, Kj, Kh, Kε⟩ := K
  cases Jε <;> cases Kε
  · simp +decide only [SignedInterval.sign] at hcw
    have hends : Ji = Ki ∧ Jj = Kj := by
      split_ifs at hcw <;> constructor <;> apply Fin.ext <;> omega
    rcases hends with ⟨hi, hj⟩
    subst Ki
    subst Kj
    left
    rfl
  · simp +decide only [SignedInterval.sign] at hcw
    have hends : Ji = Ki ∧ Jj = Kj := by
      split_ifs at hcw <;> constructor <;> apply Fin.ext <;> omega
    rcases hends with ⟨hi, hj⟩
    subst Ki
    subst Kj
    right
    ext t
    change α ({ i := Ji, j := Jj, hij := Jh, ε := false } : SignedInterval n) t =
      - α ({ i := Ji, j := Jj, hij := Kh, ε := true } : SignedInterval n) t
    rw [α_eval, α_eval]
    simp [SignedInterval.sign]
  · simp +decide only [SignedInterval.sign] at hcw
    have hends : Ji = Ki ∧ Jj = Kj := by
      split_ifs at hcw <;> constructor <;> apply Fin.ext <;> omega
    rcases hends with ⟨hi, hj⟩
    subst Ki
    subst Kj
    right
    ext t
    change α ({ i := Ji, j := Jj, hij := Jh, ε := true } : SignedInterval n) t =
      - α ({ i := Ji, j := Jj, hij := Kh, ε := false } : SignedInterval n) t
    rw [α_eval, α_eval]
    simp [SignedInterval.sign]
  · simp +decide only [SignedInterval.sign] at hcw
    have hends : Ji = Ki ∧ Jj = Kj := by
      split_ifs at hcw <;> constructor <;> apply Fin.ext <;> omega
    rcases hends with ⟨hi, hj⟩
    subst Ki
    subst Kj
    left
    rfl

lemma An_is_crystallographic (n : ℕ) [NeZero n] : (rootPairing n).IsCrystallographic :=
  ⟨fun i j => ⟨(rootPairing n).pairing i j, by simp⟩⟩



-- Note that the root pairing is not irreducible. Indeed, the set of roots for A1 is {2e1, -2e1},
-- whose ℤ-span is a proper sub-module of M which remains invariant under the s_i's.
-- Similarly, the root pairing is not a root system.

-- To fix this, we must base change to ℚ or ℝ

end An
