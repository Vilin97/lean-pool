/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic

open Module

variable {α β γ : Type*}

lemma lambda_comp (f : α → β) (g : β → γ) :
    (fun b ↦ g b) ∘ (fun a ↦ f a) = g ∘ f :=
  rfl

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

lemma exp_le_exp_of_pow_le_pow (a : Γ₀) (hlt : a < 1) (h₀ : a ≠ 0) {n m : ℤ} (hle : a ^ n ≤ a ^ m) :
    m ≤ n := by
  rwa [zpow_le_zpow_iff_right_of_lt_one₀ (zero_lt_iff.mpr h₀) hlt] at hle

lemma exp_zero_of_pow_eq_one_aux {n : ℕ} (ha : (0 : Γ₀) ^ n = 1) : n = 0 := by
  induction n with
  | zero => rfl
  | succ n _ => simp at ha

lemma exp_zero_of_zpow_eq_one' {n : ℤ} (ha : (0 : Γ₀) ^ n = 1) : n = 0 := by
  have haux (n : ℤ) (ha : (0 : Γ₀) ^ n = 1) (hn : n ≥ 0) : n = 0 := by
    have : n.toNat = 0 := by
      apply exp_zero_of_pow_eq_one_aux (Γ₀ := Γ₀)
      rwa [← zpow_natCast, Int.toNat_of_nonneg hn]
    rw [← Int.toNat_of_nonneg hn]
    simpa
  by_cases hn : n ≥ 0
  · exact haux n ha hn
  · apply Int.neg_eq_zero.mp
    apply haux
    · simpa
    · simp only [ge_iff_le, Left.nonneg_neg_iff]
      exact Int.le_of_not_le hn

lemma exp_zero_of_zpow_eq_one {a : Γ₀} (h : a < 1) {n : ℤ} (han : a ^ n = 1) : n = 0 := by
  by_cases ha : a = 0
  · subst ha
    exact exp_zero_of_zpow_eq_one' han
  · apply le_antisymm
    · apply exp_le_exp_of_pow_le_pow a h ha
      simp [han]
    · apply exp_le_exp_of_pow_le_pow a h ha
      simp [han]

lemma Pi.basisFun_eq_single {ι : Type*} [Finite ι] [DecidableEq ι] {R : Type*}
    [Semiring R] (i : ι) : Pi.basisFun R ι i = Pi.single i 1 := by
  simp only [Pi.basisFun_apply]

@[simp]
lemma Matrix.GeneralLinearGroup.toLinear_symm_ofLinearEquiv_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*} [CommRing R]
    (e : (ι → R) ≃ₗ[R] ι → R) (i j : ι) :
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e) i j =
      e (Pi.single j 1) i :=
  rfl

lemma Fin.rev_antitone (n : ℕ) : Antitone (Fin.rev (n := n)) := by match n with
  | 0 => intro j; simp
  | n + 1 =>
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      simp only [Fin.rev_le_rev]
      exact Fin.le_of_lt i.castSucc_lt_succ

namespace Finset

variable {ι α β : Type*} [CommGroupWithZero β]

--@[to_additive sum_zsmul_assoc]
lemma prod_zpow_eq_zpow_sum (s : Finset ι) (f : ι → ℤ) (a : β) (ha : a ≠ 0) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i :=
  cons_induction (by simp) (fun _ _ _ h ↦ by simp [h, zpow_add₀ ha]) s

end Finset

theorem IsLocalRing.exists_isUnit_of_isUnit_sum {ι R : Type*} [CommRing R] [IsLocalRing R]
    {s : Finset ι} {f : ι → R} (h : IsUnit (∑ i ∈ s, f i)) : ∃ i ∈ s, IsUnit (f i) := by
  contrapose! h
  simp_rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal] at h ⊢
  exact Ideal.sum_mem (maximalIdeal R) h

/-- `Fin (n + 1)` is equivalent to `Fin n ⊕ Unit`. -/
@[simps]
def Fin.succ_equiv_unit (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit where
  toFun j := if h : (j : ℕ) < n then Sum.inl ⟨j, h⟩ else Sum.inr ()
  invFun := Sum.elim (fun j ↦ j.castSucc) (fun _ ↦ Fin.last n)
  left_inv j := by
    simp only
    split_ifs with h
    · ext
      simp
    · ext
      simp only [Sum.elim_inr, Fin.val_last]
      omega
  right_inv
    | Sum.inl i => by
        simp only [Sum.elim_inl, Fin.val_castSucc]
        split_ifs with h
        · rw [Sum.inl.injEq]
        · omega
    | Sum.inr () => by simp

lemma MulAction.stabilizer_fun_const {α : Type*} (ι G : Type*) [Nonempty ι] [Group G]
    [MulAction G α] (x : α) :
    MulAction.stabilizer G (fun _ : ι ↦ x) = MulAction.stabilizer G x := by
  ext g
  simp [funext_iff]

lemma MulAction.stabilizer_pi {ι : Type*} {α : ι → Type*} (G : Type*) [Group G]
    [∀ i, MulAction G (α i)] (x : ∀ i, α i) :
    MulAction.stabilizer G x = ⨅ i, MulAction.stabilizer G (x i) := by
  ext g
  simp [funext_iff, Subgroup.mem_iInf]

lemma MulAction.mem_stabilizer_pi {ι : Type*} {α : ι → Type*} {G : Type*} [Group G]
    [∀ i, MulAction G (α i)] (x : ∀ i, α i) (g : G) :
    g ∈ MulAction.stabilizer G x ↔ ∀ i, g ∈ MulAction.stabilizer G (x i) := by
  simp [funext_iff]
