/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Finite-group Property-(T) lemmas for the Zhou §4 transfer chain. This is a
local proof of the finite quotient step and does not supply Zhou's spectral
or EJZK input.
-/
import LeanPool.ConnesRigidity.Core
import Mathlib.RepresentationTheory.Invariants

/-!
The finite property t component of the Connes rigidity formalization.
-/

open scoped BigOperators

namespace Connes

namespace PropertyTTransfer

noncomputable section

/- A unitary representation viewed as a module representation for averaging. Paper: §4.
-/
/--
The `UnitaryRep` construction used in the Connes rigidity formalization.
-/
abbrev UnitaryRep
    (G H : Type*) [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  G →* unitary (H →L[ℂ] H)

/-- The linear representation underlying a unitary representation. Paper: §4.
-/
def unitaryToModuleRepresentation
    {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) : Representation ℂ G H where
  toFun g := (π g : H →L[ℂ] H).toLinearMap
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

/- The finite-group averaging operator has the expected vector formula. Paper: §4. -/
lemma averageMap_apply {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype G] (π : UnitaryRep G H) (ξ : H) :
    Representation.averageMap (unitaryToModuleRepresentation π) ξ =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (π g : H →L[ℂ] H) ξ := by
  simp [Representation.averageMap, GroupAlgebra.average, Representation.asAlgebraHom,
    unitaryToModuleRepresentation, map_sum]

/- The averaging error is the average of the individual displacement errors. Paper: §4. -/
lemma averageMap_sub_apply {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype G] (π : UnitaryRep G H) (ξ : H) :
    Representation.averageMap (unitaryToModuleRepresentation π) ξ - ξ =
      (Fintype.card G : ℂ)⁻¹ •
        ∑ g : G, ((π g : H →L[ℂ] H) ξ - ξ) := by
  rw [averageMap_apply]
  simp only [Finset.sum_sub_distrib, Finset.sum_const]
  rw [smul_sub]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul]
  simp

/- Every finite countable discrete group has Property-(T). Paper: §4. -/
theorem hasKazhdanPropertyT_of_fintype
    (G : CountableDiscreteGroup) [Finite (G : Type)] :
    HasKazhdanPropertyT G := by
  let _ := Fintype.ofFinite (G : Type)
  intro H _ _ _ π hπ
  let n : ℝ := Fintype.card (G : Type)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩)
  let ε : ℝ := 1 / (2 * n)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨ξ, hξ, hclose⟩ := hπ Finset.univ ε hε
  let ρ : Representation ℂ (G : Type) H := unitaryToModuleRepresentation π
  let η : H := ρ.averageMap ξ
  have hηinv : ∀ g : G, (π g : H →L[ℂ] H) η = η := by
    intro g
    have hg := Representation.averageMap_invariant ρ ξ g
    exact hg
  have hsum :
      ∑ g : G, ‖(π g : H →L[ℂ] H) ξ - ξ‖ ≤
        ∑ _g : G, ε := by
    apply Finset.sum_le_sum
    intro g hg
    exact le_of_lt (hclose g (Finset.mem_univ g))
  have hsum' :
      ∑ g : G, ‖(π g : H →L[ℂ] H) ξ - ξ‖ ≤ n * ε := by
    simpa [n, Finset.card_univ, nsmul_eq_mul] using hsum
  have hdiff : ‖η - ξ‖ ≤ (1 / 2 : ℝ) := by
    dsimp [η]
    change ‖Representation.averageMap (unitaryToModuleRepresentation π) ξ - ξ‖ ≤
      (1 / 2 : ℝ)
    rw [averageMap_sub_apply, norm_smul]
    have hscalar :
        ‖(Fintype.card (G : Type) : ℂ)⁻¹‖ = n⁻¹ := by
      simp [n, norm_inv]
    rw [hscalar]
    calc
      n⁻¹ * ‖∑ g : G, ((π g : H →L[ℂ] H) ξ - ξ)‖ ≤
          n⁻¹ * ∑ g : G, ‖(π g : H →L[ℂ] H) ξ - ξ‖ := by
            gcongr
            exact norm_sum_le _ _
      _ ≤ n⁻¹ * (n * ε) := by
            exact mul_le_mul_of_nonneg_left hsum' (by positivity)
      _ = ε := by
            simp [ne_of_gt hn]
      _ ≤ (1 / 2 : ℝ) := by
            dsimp [ε]
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
            nlinarith [hn, (show (1 : ℝ) ≤ n by
              dsimp [n]
              exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
                (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩))))]
  refine ⟨η, ?_, hηinv⟩
  intro hzero
  have hnorm : ‖η - ξ‖ = 1 := by
    rw [hzero, zero_sub, norm_neg, hξ]
  linarith

end

end PropertyTTransfer

end Connes
