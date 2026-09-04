/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import LeanPool.FltRegular.NumberTheory.CyclotomicRing

/-!
# Systems of units

This file develops linearly independent systems of units in cyclotomic modules.
-/

@[expose] public section

open FiniteDimensional
open NumberField

variable (p : ℕ) (hp : Nat.Prime p)

open Module Finset
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))

local notation "A" => (CyclotomicIntegers p)

section

variable [Module (CyclotomicIntegers p) G]

/-- A system of `s` units represented by a linearly independent family over cyclotomic integers. -/
structure systemOfUnits (s : ℕ) where
  /-- The family of units in the system. -/
  units : Fin s → G
  /-- The linear independence of the family over cyclotomic integers. -/
  linearIndependent : LinearIndependent A units

namespace systemOfUnits

lemma existence0 : Nonempty (systemOfUnits p G 0) :=
  ⟨⟨fun _ ↦ 0, linearIndependent_empty_type⟩⟩

include hp

lemma finrank_spanA {R : ℕ} (f : Fin R → G) (hf : LinearIndependent A f) :
    finrank ℤ (Submodule.span A (Set.range f)) = (p - 1) * R := by
  classical
  have := Fact.mk hp
  have := finrank_span_set_eq_card (R := A) (s := Set.range f)
    ((linearIndepOn_id_range_iff hf.injective).mpr hf)
  simp only [Set.toFinset_range, Finset.card_image_of_injective _ hf.injective, card_fin] at this
  rw [← CyclotomicIntegers.powerBasis_dim, ← PowerBasis.finrank]
  conv_rhs => rw [← this]
  have := Module.Free.of_basis (Basis.span hf)
  have := Module.Finite.of_basis (Basis.span hf)
  rw [finrank_mul_finrank]

include hf

lemma ex_not_mem [Module.Free ℤ G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    ∃ g, ∀ (k : ℤ), k ≠ 0 → ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
  have := Fact.mk hp
  have : Module.Finite ℤ G := Module.finite_of_finrank_pos
    (by simp [hf, R.zero_le.trans_lt hR, hp.one_lt])
  refine Submodule.exists_of_finrank_lt
    ((Submodule.span A (Set.range S.units)).restrictScalars ℤ) ?_
  have hfinrank :
      finrank ℤ ((Submodule.span A (Set.range S.units)).restrictScalars ℤ) =
        finrank ℤ (Submodule.span A (Set.range S.units)) := by
    with_unfolding_all rfl
  rw [hfinrank, finrank_spanA p hp G S.units S.linearIndependent, hf, mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le hR rfl.le hp.pred_pos

end systemOfUnits

end

namespace systemOfUnits

include hp hf

variable [Module.Free ℤ G]

lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    Nonempty (systemOfUnits p G (R + 1)) := by
  obtain ⟨g, hg⟩ := ex_not_mem p hp G s hf S hR
  refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
  refine LinearIndependent.finCons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
  by_contra! ha
  have := Fact.mk hp
  obtain ⟨n, h0, f, Hf⟩ := CyclotomicIntegers.exists_dvd_int p _ ha.2
  have hy' := congr_arg (f • ·) ha.1
  rw [smul_zero, smul_add, smul_smul, mul_comm f,
    ← Hf, ← eq_neg_iff_add_eq_zero, Int.cast_smul_eq_zsmul] at hy'
  apply hg _ h0
  rw [hy']
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)

lemma existence'' [Module A G] {R : ℕ} (hR : R ≤ s) : Nonempty (systemOfUnits p G R) := by
  induction R with
  | zero => exact existence0 p G
  | succ n ih =>
      obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
      exact existence' p hp G s hf S (lt_of_lt_of_le (Nat.lt_add_one n) hR)

lemma existence [Module A G] : Nonempty (systemOfUnits p G s) := existence'' p hp G s hf rfl.le

end systemOfUnits
