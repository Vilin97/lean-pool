/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SampleAvailability
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FibreSlots
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ResourceCompletion
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.PrescribedCounts

/-!
# Relative expansion

The thresholds are first chosen for a fixed finite lattice support, then
made uniform over every support in the prescribed box. All sampling and
deletion arguments retain the positions of repeated vectors.
-/

@[expose] public section

open scoped BigOperators Matrix
open Module

namespace EGZ.Expansion

/-- For one fixed support, the analytic parameters are independent of the
prime, the fibre multiplicities and the prescribed coefficients. -/
theorem relative_expansion_fixed_support {r t : ℕ} (ht : 0 < t)
    (S : Finset (IntCoord r)) (hS : S.Nonempty) (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ p₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → ∀ p : ℕ,
      ∀ (_ : Fact p.Prime) (_ : NeZero p), p₀ ≤ p →
      Function.Injective (fun q : S ↦ q.val.mod p) →
      ∀ (w : FpCoord p (r + t) → ℕ) (α : S → ℤ),
      (∀ v, w v ≠ 0 → ∃ q : S, Coord.first r t v = q.val.mod p) →
      (∑ q : S, α q • q.val) = 0 → (∑ q : S, α q) = (p : ℤ) →
      (∀ q : S, δ * p ≤ (α q : ℝ) ∧
        (α q : ℝ) ≤ pushWeight (Coord.first r t) w (q.val.mod p) - δ * p) →
      IsThickRelative w (Coord.first r t) T δ → HasZeroSumMultiplicity w := by
  classical
  let : Nonempty S := hS.to_subtype
  obtain ⟨N, M, Q, hN, hQ, hAQ⟩ := exists_affine_relations S
  let B := max 2 (Finset.univ.sup (fun q : S ↦ ∑ z, (Q z q).natAbs))
  have hB : 2 ≤ B := le_max_left _ _
  have hsize (q : S) : (∑ z, (Q z q).natAbs) ≤ B :=
    (Finset.le_sup (f := fun q : S ↦ ∑ z, (Q z q).natAbs)
      (Finset.mem_univ q)).trans (le_max_right _ _)
  let η : ℝ := min (δ / 2) (1 / (2 * (B + 1 : ℝ)))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  have hηsmall : η ≤ 1 / (2 * (B + 1 : ℝ)) := min_le_right _ _
  have hdenB : 0 < (B : ℝ) + 1 := by positivity
  have hsmall : ((B : ℝ) + 1) * η < 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (B + 1 : ℝ))).mp hηsmall
    nlinarith
  have hηone : η ≤ 1 := by nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B]
  let γ : ℝ := η / (4 * S.card)
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨a, p₁, ha, hgrow⟩ := exists_binarySums_cover_uniform t B ht (δ / 2) (by positivity)
  let W : ℕ := ⌈20 * a / γ⌉₊ + 1
  have hW : 0 < W := by dsimp [W]; omega
  have haW : 20 * a ≤ W * γ := by
    have hh : 20 * a / γ ≤ (W : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_succ _))
    exact (div_le_iff₀ hγ).mp hh
  let p₂ : ℕ := ⌈2 * (B : ℝ) ^ 2 / (δ * η)⌉₊
  let p₀ := max p₁ (max W (max (N + 1) p₂))
  refine ⟨(N + B + 1) * W, p₀, ?_⟩
  intro T hT p hpprime hpzero hp hmod w α hs hz hm hα hthick
  have hp₁ : p₁ ≤ p := (le_max_left _ _).trans hp
  have hWp : W ≤ p := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hp
  have hNp : N < p := by
    have hh : N + 1 ≤ p :=
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hp
    omega
  have hp₂ : p₂ ≤ p :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hmpos : 0 < δ * (p : ℝ) := mul_pos hδ hpR
  have hcollision : (B : ℝ) ^ 2 / (δ * p) ≤ η / 2 := by
    have hh : 2 * (B : ℝ) ^ 2 / (δ * η) ≤ (p : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hp₂)
    have hmul := (div_le_iff₀ (mul_pos hδ hη)).mp hh
    apply (div_le_iff₀ hmpos).mpr
    nlinarith
  have hαpos (q : S) : 0 ≤ α q := by exact_mod_cast hmpos.le.trans (hα q).1
  have hfibre (q : S) : 2 * δ * p ≤
      (pushWeight (Coord.first r t) w (q.val.mod p) : ℝ) := by
    have hh := hα q
    linarith
  -- The prescribed quotient multiplicities retain a uniform margin.
  obtain ⟨counts, hcounts, hcountsmass, hcountszero, hmargin⟩ :=
    prescribed_quotient_counts_with_margin S w α hmod
      (fun v hv ↦ by obtain ⟨q, hq⟩ := hs v hv; exact ⟨q.val, q.property, hq⟩)
      hz hm (R := δ * p / 2)
      (by positivity) (by intro q; have hh := hα q; constructor <;> linarith)
  have hmass : p ≤ natMass w := by
    have hh := natMass_mono hcounts
    simpa only [hcountsmass, natMass_pushWeight] using hh
  let A := FibreSlots.Atom w
  let : DecidableEq A := fun x y ↦ Classical.propDecidable (x = y)
  let point : A → FpCoord p (r + t) := Sigma.fst
  have havailable (U : Finset A) (hU : (U.card : ℝ) ≤ (δ / 2) * p) :
      ∃ ν : FpCoord p t → ℝ, (∀ v, 0 ≤ ν v) ∧ 0 < ∑ v, ν v ∧
        IsCentrallyThick ν W γ ∧
        ∀ v, 0 < ν v → ∃ e : Exchange point B, Disjoint e.support U ∧ e.shift = v := by
    let X : S → Type := fun q ↦ FibreSlots.Fibre w U (Coord.first r t) (q.val.mod p)
    have hcard (q : S) : δ * (p : ℝ) ≤ Fintype.card (X q) := by
      have hh := FibreSlots.card_fibre_lower w U (Coord.first r t) (q.val.mod p)
      have hh' := Nat.sub_le_iff_le_add.mp hh
      have hc : (pushWeight (Coord.first r t) w (q.val.mod p) : ℝ) ≤
          Fintype.card (X q) + U.card := by exact_mod_cast hh'
      have hf := hfibre q
      nlinarith
    let : ∀ q, Nonempty (X q) := fun q ↦ Fintype.card_pos_iff.mp (by
      have hh : (0 : ℝ) < Fintype.card (X q) := hmpos.trans_le (hcard q)
      exact_mod_cast hh)
    let encode : ∀ q, X q → A := fun _ x ↦ x.val
    have hreassemble := FibreSlots.reassemble_remaining w U (Coord.first r t)
      (fun q : S ↦ q.val.mod p) hmod hs
    have hremain := FibreSlots.remaining_isThickRelative w U (Coord.first r t)
      hδ.le hmass (by nlinarith) hthick
    have hremainsmall := hremain.mono hT le_rfl
    have hthin : IsThickRelative
        (pushWeight (fun z : Σ q, X q ↦ point (encode z.1 z.2)) (fun _ ↦ 1))
        (Coord.first r t) ((N + B + 1) * W) (δ / 2) := by
      rw [hreassemble]
      exact hremainsmall
    exact exists_thick_exchange_weight S X point encode (fun _ ↦ Subtype.val_injective)
      (fun q x ↦ x.property.1) U (fun q x ↦ x.property.2) M Q hQ hAQ hsize hB hN hNp
      hη hηone hηδ hsmall hmpos hcard hcollision hthin
  obtain ⟨F, hF, hused, hcover⟩ := hgrow p hpzero hpprime hp₁ (Exchange point B) A
    inferInstance inferInstance Exchange.support Exchange.shift
    Exchange.support_card_le Exchange.shift_eq_zero_of_support_eq_empty
    (by
      intro U hU
      obtain ⟨ν, hν, hνmass, hνthick, hνex⟩ := havailable U hU
      obtain ⟨basis, hbasis⟩ := hνthick.exists_basis hν hνmass hγ
      exact ⟨basis, fun i ↦ hνex _ (hbasis i)⟩)
    (by
      intro U hU Y hY
      obtain ⟨ν, hν, hνmass, hνthick, hνex⟩ := havailable U hU
      obtain ⟨v, hv, hb⟩ := exists_boundary_of_central_thickness hW hWp ν hν hνmass
        hγ.le hνthick Y hY
      obtain ⟨e, heU, hev⟩ := hνex v hv
      refine ⟨e, heU, ?_⟩
      rw [hev]
      have hh := mul_le_mul_of_nonneg_right haW (Nat.cast_nonneg Y.card)
      nlinarith)
  have hused' : ((usedAtoms Exchange.support F).card : ℝ) ≤ δ * (p : ℝ) / 2 := by
    calc
      _ ≤ (δ / 2) * (p : ℝ) := hused
      _ = δ * (p : ℝ) / 2 := by ring
  exact complete_exchange_resources point w (by
    simpa only [point] using (FibreSlots.pushWeight_atoms w).le) F hF hcover
    counts hcounts hcountsmass hcountszero (R := δ * p / 2) hused' hmargin

/-- The relative expansion theorem, with uniform thresholds for all
supports in a fixed integer box. -/
theorem relative_expansion_theorem : RelativeExpansionStatement := by
  classical
  intro r t K _hK δ hδ
  by_cases htzero : t = 0
  · subst t
    refine ⟨0, 0, ?_⟩
    intro T _ p _ _ _ hKp
    exact relativeExpansionAt_zero_fibre hδ hKp
  have ht : 0 < t := Nat.pos_of_ne_zero htzero
  let supports := (latticeBox r K).powerset
  let Family := {s : supports // s.val.Nonempty}
  let : Fintype Family := Fintype.ofFinite Family
  have hfixed (s : Family) := relative_expansion_fixed_support ht s.val.val s.property δ hδ
  choose Tbound pbound hbound using hfixed
  refine ⟨Finset.univ.sup Tbound, Finset.univ.sup pbound, ?_⟩
  intro T hT p hpprime hpzero hp hKp S w α hbox hs hz hm hα hthick
  by_cases hS : S.Nonempty
  · have hsub : S ⊆ latticeBox r K := by
      intro q hq
      exact mem_latticeBox.mpr (hbox q hq)
    let s : Family := ⟨⟨S, Finset.mem_powerset.mpr hsub⟩, hS⟩
    exact hbound s T ((Finset.le_sup (Finset.mem_univ s)).trans hT) p hpprime hpzero
      ((Finset.le_sup (Finset.mem_univ s)).trans hp)
      (mod_injective_on_support S hbox hKp) w α
      (fun v hv ↦ by obtain ⟨q, hq, hmod⟩ := hs v hv; exact ⟨⟨q, hq⟩, hmod⟩)
      hz hm hα hthick
  · have hpz : (p : ℤ) = 0 := hm.symm.trans (by
      apply Finset.sum_eq_zero
      intro q _
      exact (hS ⟨q.val, q.property⟩).elim)
    exact False.elim (NeZero.ne p (by exact_mod_cast hpz))

end EGZ.Expansion
