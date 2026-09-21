/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ThinDirections
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Mass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift

/-!
# Restricting a weight to selected thin slabs

A finite union bound controls the mass removed by intersecting thin slabs.
The stage errors form a geometric sum, leaving enough thickness outside the
maximal space of selected directions. Retained points also have bounded
integer coordinates in the selected directions.
-/

open scoped BigOperators

namespace EGZ

section Restriction

variable {α I : Type*} [Fintype α] [Fintype I]

/-- Delete all mass outside a set. -/
noncomputable def restrictWeight (w : α → ℕ) (S : Set α) : α → ℕ := by
  classical
  exact fun v ↦ if v ∈ S then w v else 0

omit [Fintype α] in
theorem restrictWeight_le (w : α → ℕ) (S : Set α) : restrictWeight w S ≤ w := by
  classical
  intro v
  change (if v ∈ S then w v else 0) ≤ w v
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

omit [Fintype α] in
@[simp]
theorem restrictWeight_ne_zero_iff (w : α → ℕ) (S : Set α) (v : α) :
    restrictWeight w S v ≠ 0 ↔ v ∈ S ∧ w v ≠ 0 := by
  classical
  by_cases hv : v ∈ S <;> simp [restrictWeight, hv]

@[simp]
theorem natMass_restrictWeight (w : α → ℕ) (S : Set α) :
    natMass (restrictWeight w S) = natMassOn w S := rfl

theorem restrictWeight_loss_eq_compl (w : α → ℕ) (S : Set α) :
    (natMass w : ℝ) - natMass (restrictWeight w S) = (natMassOn w Sᶜ : ℝ) := by
  have h : (natMassOn w S : ℝ) + natMassOn w Sᶜ = natMass w := by
    exact_mod_cast natMassOn_add_compl w S
  rw [natMass_restrictWeight]
  linarith

/-- Finite union bound for the mass outside an intersection. -/
theorem natMassOn_compl_intersection_le (w : α → ℕ) (S : I → Set α) :
    natMassOn w {v | ∀ i, v ∈ S i}ᶜ ≤ ∑ i, natMassOn w (S i)ᶜ := by
  classical
  unfold natMassOn
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : ∀ i, v ∈ S i
  · simp [hv]
  · obtain ⟨i, hi⟩ := not_forall.mp hv
    have hle := Finset.single_le_sum
      (f := fun i ↦ if v ∈ (S i)ᶜ then w v else 0)
      (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, hv, not_false_eq_true,
      ite_true, hi] using hle

/-- Relative complement bounds add when the retained sets are intersected. -/
theorem restrictWeight_intersection_loss_le (w : α → ℕ) (S : I → Set α)
    (ε : I → ℝ)
    (hS : ∀ i, (natMassOn w (S i)ᶜ : ℝ) ≤ ε i * natMass w) :
    (natMass w : ℝ) - natMass (restrictWeight w {v | ∀ i, v ∈ S i}) ≤
      (∑ i, ε i) * natMass w := by
  rw [restrictWeight_loss_eq_compl]
  calc
    (natMassOn w {v | ∀ i, v ∈ S i}ᶜ : ℝ) ≤ ∑ i, (natMassOn w (S i)ᶜ : ℝ) := by
      exact_mod_cast natMassOn_compl_intersection_le w S
    _ ≤ ∑ i, ε i * natMass w := Finset.sum_le_sum (fun i _ ↦ hS i)
    _ = (∑ i, ε i) * natMass w := (Finset.sum_mul _ _ _).symm

theorem restrictWeight_retainedMass_ge (w : α → ℕ) (S : Set α) (ε : ℝ)
    (hloss : (natMass w : ℝ) - natMass (restrictWeight w S) ≤ ε * natMass w) :
    (1 - ε) * (natMass w : ℝ) ≤ natMass (restrictWeight w S) := by
  linarith

theorem restrictWeight_nonzero_of_loss_lt_one (w : α → ℕ) (S : Set α) (ε : ℝ)
    (hw : ∃ v, w v ≠ 0) (hε : ε < 1)
    (hloss : (natMass w : ℝ) - natMass (restrictWeight w S) ≤ ε * natMass w) :
    ∃ v, restrictWeight w S v ≠ 0 := by
  obtain ⟨v, hv⟩ := hw
  have hmass : 0 < natMass w := (Nat.pos_of_ne_zero hv).trans_le
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v))
  have hmass' : (0 : ℝ) < natMass w := by exact_mod_cast hmass
  have hret := restrictWeight_retainedMass_ge w S ε hloss
  have hpos : (0 : ℝ) < natMass (restrictWeight w S) :=
    (mul_pos (sub_pos.mpr hε) hmass').trans_le hret
  have hn : natMass (restrictWeight w S) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨v, hv⟩

end Restriction

theorem IsThinAlong.compl_mass_le {p d : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    {t : ℕ} {ε : ℝ} (h : IsThinAlong w ξ t ε) :
    (natMassOn w (slab ξ t)ᶜ : ℝ) ≤ ε * natMass w := by
  have hthin := (isThinAlong_iff_natMass w ξ t ε).mp h
  have htotal : (natMassOn w (slab ξ t) : ℝ) + natMassOn w (slab ξ t)ᶜ = natMass w := by
    exact_mod_cast natMassOn_add_compl w (slab ξ t)
  linarith

/-- The intersection of the first `k` stage-indexed slabs. -/
def slabIntersection {p d : ℕ} (k : ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (t : ℕ → ℕ) : Set (FpCoord p d) :=
  {v | ∀ i : Fin k, v ∈ slab (ξ i) (t (i + 1))}

theorem sum_three_pow_succ_le (k : ℕ) :
    (∑ i : Fin k, (3 : ℝ) ^ (i.val + 1)) ≤ 3 ^ (k + 1) - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hpow : (0 : ℝ) ≤ 3 ^ (k + 1) := by positivity
    rw [show (3 : ℝ) ^ (k + 1 + 1) = 3 ^ (k + 1) * 3 from pow_succ _ _]
    nlinarith

namespace DirectionChain

variable {p d k : ℕ} [Fact p.Prime]
    {W : Submodule (ZMod p) (FpCoord p d →ᵃ[ZMod p] ZMod p)}
    {w : FpCoord p d → ℕ} {t : ℕ → ℕ} {δ : ℝ}
    (D : DirectionChain W
      (fun i ξ ↦ IsThinAlong w ξ (t (i + 1)) ((3 : ℝ) ^ (i + 1) * δ)) k)

theorem slabIntersection_loss_le_sum :
    (natMass w : ℝ) - natMass (restrictWeight w (slabIntersection k D.direction t)) ≤
      (∑ i : Fin k, (3 : ℝ) ^ (i.val + 1) * δ) * natMass w :=
  restrictWeight_intersection_loss_le w (fun i : Fin k ↦ slab (D.direction i) (t (i + 1)))
    (fun i ↦ (3 : ℝ) ^ (i.val + 1) * δ)
    (fun i ↦ (D.selected i i.isLt).compl_mass_le)

theorem slabIntersection_loss_le (hδ : 0 ≤ δ) :
    (natMass w : ℝ) - natMass (restrictWeight w (slabIntersection k D.direction t)) ≤
      ((3 : ℝ) ^ (k + 1) - 1) * δ * natMass w := by
  apply D.slabIntersection_loss_le_sum.trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sum_three_pow_succ_le k) hδ) (Nat.cast_nonneg _)

theorem slabIntersection_loss_le_dimension (hδ : 0 ≤ δ) (hkd : k ≤ d) :
    (natMass w : ℝ) - natMass (restrictWeight w (slabIntersection k D.direction t)) ≤
      (3 : ℝ) ^ (d + 1) * δ * natMass w := by
  apply (D.slabIntersection_loss_le hδ).trans
  have hpow : (3 : ℝ) ^ (k + 1) ≤ 3 ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hkd 1)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (by linarith) hδ

theorem slabIntersection_retainedMass_ge (hδ : 0 ≤ δ) (hkd : k ≤ d) :
    (1 - (3 : ℝ) ^ (d + 1) * δ) * natMass w ≤
      (natMass (restrictWeight w (slabIntersection k D.direction t)) : ℝ) :=
  restrictWeight_retainedMass_ge _ _ _ (D.slabIntersection_loss_le_dimension hδ hkd)

theorem slabIntersection_nonzero (hδ : 0 ≤ δ) (hkd : k ≤ d)
    (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1) (hw : ∃ v, w v ≠ 0) :
    ∃ v, restrictWeight w (slabIntersection k D.direction t) v ≠ 0 :=
  restrictWeight_nonzero_of_loss_lt_one _ _ _ hw hsmall
    (D.slabIntersection_loss_le_dimension hδ hkd)

/-- The geometric error budget leaves thickness `δ` after intersecting all
chosen slabs. No monotonicity assumptions on the widths are needed. -/
theorem thick_slabIntersection (hδ : 0 ≤ δ)
    {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    (hthick : IsThickAlong w ξ (t (k + 1)) ((3 : ℝ) ^ (k + 1) * δ)) :
    IsThickAlong (restrictWeight w (slabIntersection k D.direction t)) ξ (t (k + 1)) δ := by
  have hpow : (1 : ℝ) ≤ 3 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have heq : (3 : ℝ) ^ (k + 1) * δ - ((3 : ℝ) ^ (k + 1) - 1) * δ / 1 = δ := by ring
  have h := hthick.of_pruning (restrictWeight_le _ _) (ε := 1) (M := natMass w)
    (by norm_num) (mul_nonneg (sub_nonneg.mpr hpow) hδ) (by simp)
    (D.slabIntersection_loss_le hδ) (by rw [heq]; exact hδ)
  rwa [heq] at h

theorem thick_slabIntersection_of_maximal (hδ : 0 ≤ δ)
    (hmax : ∀ ξ, ξ ∉ D.space k → IsThickAlong w ξ (t (k + 1)) ((3 : ℝ) ^ (k + 1) * δ))
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) (hξ : ξ ∉ D.space k) :
    IsThickAlong (restrictWeight w (slabIntersection k D.direction t)) ξ (t (k + 1)) δ :=
  D.thick_slabIntersection hδ (hmax ξ hξ)

end DirectionChain

/-- A small bounded representative agrees with the centered representative. -/
theorem HasBoundedRepresentative.valMinAbs_natAbs_le {p K : ℕ} [NeZero p]
    {a : ZMod p} (ha : HasBoundedRepresentative p K a) (hK : 2 * K < p) :
    a.valMinAbs.natAbs ≤ K := by
  obtain ⟨z, hz, hza⟩ := ha
  have hval : a.valMinAbs = z := (ZMod.valMinAbs_spec a z).mpr ⟨hza.symm, by
    constructor <;> omega⟩
  rwa [hval]

/-- Integer coordinates supplied by the selected affine functionals. -/
def slabCoordinates {p d : ℕ} (k : ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (v : FpCoord p d) : IntCoord k :=
  fun i ↦ (ξ i v).valMinAbs

@[simp]
theorem slabCoordinates_mod {p d k : ℕ}
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (v : FpCoord p d) :
    (slabCoordinates k ξ v).mod p = fun i : Fin k ↦ ξ i v := by
  funext i
  exact ZMod.coe_valMinAbs _

theorem slabCoordinates_apply_bound {p d k : ℕ} [NeZero p]
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (t : ℕ → ℕ)
    {v : FpCoord p d} (hv : v ∈ slabIntersection k ξ t)
    (i : Fin k) (hsmall : 2 * t (i + 1) < p) :
    (slabCoordinates k ξ v i).natAbs ≤ t (i + 1) :=
  (hv i).valMinAbs_natAbs_le hsmall

theorem slabCoordinates_bound {p d k : ℕ} [NeZero p]
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (t : ℕ → ℕ)
    (ht : Monotone t) (hsmall : ∀ i : Fin k, 2 * t (i + 1) < p)
    {v : FpCoord p d} (hv : v ∈ slabIntersection k ξ t) :
    latticeSupNorm (slabCoordinates k ξ v) ≤ t k := by
  rw [latticeSupNorm_le_iff]
  intro i
  exact (slabCoordinates_apply_bound ξ t hv i (hsmall i)).trans (ht (by omega))

end EGZ
