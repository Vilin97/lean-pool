/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTOrtho
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CharEquiv
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CharClass

/-!
# Norm one forces a single simple

A `±1`-signed combination of native characters with norm one is
`±` a single native character: group the index set by equivalence
of the underlying simples, express the norm as a sum of integer
squares over the classes, and conclude a unique class with
coefficient `±1`.
-/

namespace RS

open Finset Equiv

/-- A finite sum of integer squares equal to one has exactly one
nonzero term, of value `±1`. -/
theorem sum_sq_eq_one {Q : Type*} [Fintype Q] (Z : Q → ℤ)
    (h : ∑ q : Q, Z q * Z q = 1) :
    ∃ q₀ : Q, (Z q₀ = 1 ∨ Z q₀ = -1) ∧
      ∀ q : Q, q ≠ q₀ → Z q = 0 := by
  classical
  have hnn : ∀ q : Q, 0 ≤ Z q * Z q := fun q => mul_self_nonneg _
  have hex : ∃ q₀ : Q, Z q₀ ≠ 0 := by
    by_contra hc
    rw [not_exists] at hc
    have h0 : (∑ q : Q, Z q * Z q) = 0 :=
      Finset.sum_eq_zero fun q _ => by
        rw [not_not.mp (hc q), mul_zero]
    omega
  obtain ⟨q₀, hq₀⟩ := hex
  have h1 : 1 ≤ Z q₀ * Z q₀ := by
    rcases lt_trichotomy (Z q₀) 0 with hlt | heq | hgt
    · nlinarith
    · exact absurd heq hq₀
    · nlinarith
  have hsplit : (∑ q : Q, Z q * Z q) =
      Z q₀ * Z q₀ + ∑ q ∈ Finset.univ.erase q₀, Z q * Z q := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ q₀)]
  have hrest : (∑ q ∈ Finset.univ.erase q₀, Z q * Z q) = 0 := by
    have hnn2 : 0 ≤ ∑ q ∈ Finset.univ.erase q₀, Z q * Z q :=
      Finset.sum_nonneg fun q _ => hnn q
    omega
  have hz : ∀ q : Q, q ≠ q₀ → Z q = 0 := by
    intro q hq
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q _ => hnn q)).mp hrest q
      (Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩)
    nlinarith [mul_self_nonneg (Z q)]
  have hsq : Z q₀ * Z q₀ = 1 := by omega
  exact ⟨q₀, mul_self_eq_one_iff.mp hsq, hz⟩

open scoped Classical in
/-- **Norm one forces a single simple.** -/
theorem jt_pm_nChar (μ : YoungDiagram) {J : Type} [Fintype J]
    (ε : J → ℤ)
    (T : J → Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))))
    (hT : ∀ j, IsSimpleModule
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) (T j))
    (hchar : ∀ π : Equiv.Perm (Fin μ.card),
      jtChar μ π = ∑ j, ((ε j : ℤ) : ℂ) * nChar (T j) π) :
    ∃ S₀ : Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))),
      IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
        S₀ ∧
      ((∀ π, jtChar μ π = nChar S₀ π) ∨
        (∀ π, jtChar μ π = - nChar S₀ π)) := by
  classical
  -- ═══════ SETUP: THE CLASSES OF EQUAL CHARACTERS ═══════
  -- Irreducible constituents with equal characters are identified,
  -- and `Z` records the common multiplicity of a class.
  have hip : ∀ j j' : J,
      ((μ.card.factorial : ℂ))⁻¹ *
        ∑ π : Equiv.Perm (Fin μ.card),
          nChar (T j) π * nChar (T j') π⁻¹ =
      (if Nonempty ((rhoS (T j')).Equiv (rhoS (T j)))
        then (1 : ℂ) else 0) := by
    intro j j'
    have := rhoS_isIrreducible (T j) (hT j)
    have := rhoS_isIrreducible (T j') (hT j')
    have : Invertible ((Nat.card (Equiv.Perm (Fin μ.card)) : ℂ)) :=
      invertibleOfNonzero (by
        rw [Nat.card_eq_fintype_card]
        exact_mod_cast Fintype.card_ne_zero)
    have horth := Representation.char_orthonormal
      (rhoS (T j)) (rhoS (T j'))
    rw [show (Nat.card (Equiv.Perm (Fin μ.card)) : ℂ) =
        (μ.card.factorial : ℂ) from by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]] at horth
    exact horth
  let sd : Setoid J :=
    ⟨fun j j' => Nonempty ((rhoS (T j)).Equiv (rhoS (T j'))),
      fun _ => ⟨Representation.Equiv.refl _⟩,
      fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩
  let g : J → Quotient sd := Quotient.mk sd
  have hgr : ∀ j j' : J, g j = g j' ↔
      Nonempty ((rhoS (T j)).Equiv (rhoS (T j'))) := by
    intro j j'
    exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  let Z : Quotient sd → ℤ := fun q =>
    ∑ j ∈ Finset.univ.filter (fun j => g j = q), ε j
  have hZc : ∀ q : Quotient sd, ((Z q : ℤ) : ℂ) =
      ∑ j ∈ Finset.univ.filter (fun j => g j = q),
        ((ε j : ℤ) : ℂ) := by
    intro q
    rw [show Z q = ∑ j ∈ Finset.univ.filter
      (fun j => g j = q), ε j from rfl]
    push_cast
    rfl
  -- ═══════ STAGE 1: THE NORM AS A SUM OF SQUARES ═══════
  have hkey : ((μ.card.factorial : ℂ))⁻¹ *
      (∑ π : Equiv.Perm (Fin μ.card), jtChar μ π * jtChar μ π) =
      ∑ j : J, ∑ j' : J, ((ε j : ℤ) : ℂ) * ((ε j' : ℤ) : ℂ) *
        (if g j = g j' then (1 : ℂ) else 0) := by
    rw [Finset.sum_congr rfl (fun π (_ : π ∈ Finset.univ) => show
      jtChar μ π * jtChar μ π =
        ∑ j : J, ∑ j' : J,
          (((ε j : ℤ) : ℂ) * nChar (T j) π) *
            (((ε j' : ℤ) : ℂ) * nChar (T j') π⁻¹) from by
      rw [show jtChar μ π * jtChar μ π =
        jtChar μ π * jtChar μ π⁻¹ from by rw [jtChar_inv]]
      rw [hchar π, hchar π⁻¹, Finset.sum_mul_sum])]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl
      (fun j (_ : j ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [show (if g j = g j' then (1 : ℂ) else 0) =
      (if Nonempty ((rhoS (T j')).Equiv (rhoS (T j)))
        then (1 : ℂ) else 0) from by
      by_cases hc : Nonempty ((rhoS (T j')).Equiv (rhoS (T j)))
      · rw [ite_eq_left hc, ite_eq_left ((hgr j j').mpr ⟨hc.some.symm⟩)]
      · rw [ite_eq_right hc, ite_eq_right (fun hgj => hc
          ⟨((hgr j j').mp hgj).some.symm⟩)]]
    rw [← hip j j']
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
    refine Finset.sum_congr rfl fun π _ => ?_
    ring
  have hnorm : (∑ q : Quotient sd,
      ((Z q : ℤ) : ℂ) * ((Z q : ℤ) : ℂ)) = 1 := by
    have h0 := jtChar_orthonormal μ
    rw [hkey] at h0
    rw [← h0]
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => show
      (∑ j' : J, ((ε j : ℤ) : ℂ) * ((ε j' : ℤ) : ℂ) *
        (if g j = g j' then (1 : ℂ) else 0)) =
      ((ε j : ℤ) : ℂ) * ((Z (g j) : ℤ) : ℂ) from by
      rw [Finset.sum_congr rfl (fun j' (_ : j' ∈ Finset.univ) =>
        show ((ε j : ℤ) : ℂ) * ((ε j' : ℤ) : ℂ) *
            (if g j = g j' then (1 : ℂ) else 0) =
          (if g j' = g j
            then ((ε j : ℤ) : ℂ) * ((ε j' : ℤ) : ℂ) else 0)
        from by
        by_cases hc : g j = g j'
        · rw [ite_eq_left hc, ite_eq_left hc.symm, mul_one]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.symm), mul_zero])]
      rw [← Finset.sum_filter, hZc, Finset.mul_sum])]
    rw [← Fintype.sum_fiberwise g
      (fun j => ((ε j : ℤ) : ℂ) * ((Z (g j) : ℤ) : ℂ))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show (∑ j : {j : J // g j = q},
        ((ε j.1 : ℤ) : ℂ) * ((Z (g j.1) : ℤ) : ℂ)) =
      ∑ j : {j : J // g j = q},
        ((ε j.1 : ℤ) : ℂ) * ((Z q : ℤ) : ℂ) from
      Finset.sum_congr rfl fun j _ => by rw [j.2]]
    rw [← Finset.sum_mul]
    congr 1
    rw [hZc]
    exact Finset.sum_subtype _ (fun j =>
      ⟨fun h => (Finset.mem_filter.mp h).2,
        fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩⟩)
      (fun j => ((ε j : ℤ) : ℂ))
  have hnormZ : (∑ q : Quotient sd, Z q * Z q) = 1 := by
    have h2 : (((∑ q : Quotient sd, Z q * Z q : ℤ)) : ℂ) =
        ((1 : ℤ) : ℂ) := by
      push_cast
      exact_mod_cast hnorm
    exact_mod_cast h2
  -- ═══════ STAGE 2: ONE CLASS CARRIES MULTIPLICITY ±1 ═══════
  obtain ⟨q₀, hpm, hzero⟩ := sum_sq_eq_one Z hnormZ
  refine ⟨T q₀.out, hT q₀.out, ?_⟩
  -- ═══════ STAGE 3: COLLAPSE THE SUM TO THAT CLASS ═══════
  have hcollapse : ∀ π : Equiv.Perm (Fin μ.card),
      jtChar μ π = ((Z q₀ : ℤ) : ℂ) * nChar (T q₀.out) π := by
    intro π
    rw [hchar π]
    rw [← Fintype.sum_fiberwise g
      (fun j => ((ε j : ℤ) : ℂ) * nChar (T j) π)]
    rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => show
      (∑ j : {j : J // g j = q},
        ((ε j.1 : ℤ) : ℂ) * nChar (T j.1) π) =
      ((Z q : ℤ) : ℂ) * nChar (T q.out) π from by
      rw [show (∑ j : {j : J // g j = q},
          ((ε j.1 : ℤ) : ℂ) * nChar (T j.1) π) =
        ∑ j : {j : J // g j = q},
          ((ε j.1 : ℤ) : ℂ) * nChar (T q.out) π from
        Finset.sum_congr rfl fun j _ => by
          rw [nChar_of_equiv (((hgr j.1 q.out).mp
            (by rw [j.2]; exact (Quotient.out_eq q).symm)).some)
            π]]
      rw [← Finset.sum_mul, hZc]
      congr 1
      exact (Finset.sum_subtype _ (fun j =>
        ⟨fun h => (Finset.mem_filter.mp h).2,
          fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩⟩)
        (fun j => ((ε j : ℤ) : ℂ))).symm)]
    rw [Finset.sum_eq_single q₀
      (fun q _ hq => by rw [hzero q hq]; push_cast; ring)
      (fun h => absurd (Finset.mem_univ q₀) h)]
  rcases hpm with h1 | h1
  · left
    intro π
    rw [hcollapse π, h1]
    push_cast
    ring
  · right
    intro π
    rw [hcollapse π, h1]
    push_cast
    ring

end RS
