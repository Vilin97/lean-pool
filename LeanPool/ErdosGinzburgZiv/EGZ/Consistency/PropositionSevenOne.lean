/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Helly
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic
import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Constants

/-!
# Regression checks for Proposition 7.1

The proof of Proposition 7.1 has two algebraic inputs which are independent
of the long flag-decomposition argument:

* a family longer than `hollowConstant p d` has a nontrivial zero
  combination of total weight `p`;
* an integer-coordinate affine average whose numerator vanishes modulo `p`
  is again an integer point.

Keeping these as standalone, proved lemmas prevents the later flag interface
from hiding either step in an axiom.
-/

open scoped BigOperators

namespace EGZ

/-! ## The affine cancellation used by the representation -/

/-- An affine map preserves a linear relation provided that the coefficients
also sum to zero.  Proposition 7.1 uses this over `ZMod p`: the natural
coefficients sum to `p`, hence their casts sum to zero. -/
private theorem affineMap_sum_smul_eq_zero
    {R M N I : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Fintype I] (f : M →ᵃ[R] N) (c : I → R) (v : I → M)
    (hc : (∑ i, c i) = 0) (hv : (∑ i, c i • v i) = 0) :
    (∑ i, c i • f (v i)) = 0 := by
  classical
  have hf (i : I) : f (v i) = f.linear (v i) + f 0 := by
    exact congrFun f.decomp (v i)
  simp_rw [hf, smul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [← f.linear.map_smul]
  rw [← map_sum, hv, map_zero,
    ← Finset.sum_smul, hc, zero_smul, add_zero]

private theorem zero_sum_of_full_coefficient {p d n : ℕ}
    (v : Fin n → FpVec p d) (α : Fin n → ℕ)
    (hsum : (∑ i, α i) = p) {i : Fin n} (hi : α i = p) :
    (∑ j, α j • v j) = 0 := by
  classical
  have herase : ∑ j ∈ (Finset.univ.erase i), α j = 0 := by
    have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) α
      (Finset.mem_univ i)
    rw [hi, hsum] at hdecomp
    omega
  have hjzero : ∀ j, j ≠ i → α j = 0 := by
    intro j hji
    have hjmem : j ∈ (Finset.univ.erase i) := by simp [hji]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp herase j hjmem
  calc
    (∑ j, α j • v j) = α i • v i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hjzero j hji]
      · simp
    _ = p • v i := by rw [hi]
    _ = 0 := FpVec.characteristic_nsmul p (v i)

/-- If a family is longer than the extremal `p`-hollow length, it admits a
zero combination of total weight `p` in which every coefficient is strictly
less than `p`.

This is the exact operational consequence of `n > 𝔴(𝔽_p^d)` used in
Proposition 7.1. -/
theorem exists_nontrivial_zero_combination_of_hollowConstant_lt
    {p d n : ℕ} (hp : Nat.Prime p) (hn : hollowConstant p d < n)
    (v : Fin n → FpVec p d) :
    ∃ α : Fin n → ℕ,
      (∑ i, α i) = p ∧
      (∑ i, α i • v i) = 0 ∧
      ∀ i, α i < p := by
  classical
  by_contra hnone
  have hv : IsPHollow p v := by
    intro α hsum
    constructor
    · intro hzero
      by_contra hfull
      have hlt : ∀ i, α i < p := by
        intro i
        have hle : α i ≤ ∑ j, α j :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        rw [hsum] at hle
        have hne : α i ≠ p := by
          intro hi
          exact hfull ⟨i, hi⟩
        omega
      exact hnone ⟨α, hsum, hzero, hlt⟩
    · rintro ⟨i, hi⟩
      exact zero_sum_of_full_coefficient v α hsum hi
  exact (Nat.not_le_of_lt hn) (hollowConstant_max hp ⟨v, hv⟩)

/-- Coordinate form of the affine-lattice calculation in equation `zero` of
the proof of Proposition 7.1.

The vectors `z i` are coordinates relative to an affine lattice origin.
Vanishing of the integer numerator modulo `p` says precisely that its
normalized real sum has integer coordinates.  In Proposition 7.1 the
additional equality `∑ α = p` makes this normalized sum an affine
combination, but it is not needed for the divisibility calculation itself. -/
theorem isIntegral_weighted_average_of_mod_eq_zero
    {p n : ℕ} {I : Type*} [Fintype I]
    (hp : 0 < p) (α : I → ℕ) (z : I → IntCoord n)
    (hmod : (∑ i, α i • (z i).mod p) = 0) :
    IsIntegral (∑ i, ((α i : ℝ) / (p : ℝ)) • (z i).real) := by
  classical
  have hcast (j : Fin n) :
      ((∑ i, (α i : ℤ) * z i j : ℤ) : ZMod p) = 0 := by
    have hj := congrFun hmod j
    simpa [IntCoord.mod, nsmul_eq_mul] using hj
  have hdvd (j : Fin n) : (p : ℤ) ∣ ∑ i, (α i : ℤ) * z i j :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hcast j)
  let zbar : IntCoord n := fun j ↦ (hdvd j).choose
  have hzbar (j : Fin n) :
      ∑ i, (α i : ℤ) * z i j = (p : ℤ) * zbar j :=
    (hdvd j).choose_spec
  refine ⟨zbar, funext fun j ↦ ?_⟩
  simp only [IntCoord.real_apply, Finset.sum_apply, Pi.smul_apply]
  change (zbar j : ℝ) =
    ∑ i, ((α i : ℝ) / (p : ℝ)) * (z i j : ℝ)
  simp_rw [div_mul_eq_mul_div, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hzbarR := congrArg (fun a : ℤ ↦ (a : ℝ)) (hzbar j)
  push_cast at hzbarR
  rw [hzbarR]
  field_simp

/-! ## The representation-level barycenter calculation -/

namespace FpRepresentation

/-- Regression form of equation `comb2` followed by equation `zero` in the
proof of Proposition 7.1.

Each integral flag point is lifted to the representing affine subspace over
`ZMod p`.  A zero combination of those lifts, with total natural weight
`p`, gives an integral convex-combination result.  The proof checks both
places where affine (rather than linear) coordinates matter: compatibility
with the transition map, and cancellation of the translation term because
the coefficient sum is zero in `ZMod p`. -/
theorem convexCombination_isIntegral_of_zero_sum
    {p d n : ℕ} (hp : Nat.Prime p) {F : ConvexFlag}
    (R : FpRepresentation p d F) (points : Fin n → F.Point)
    (z : (i : Fin n) → IntCoord (F.rank (points i).base))
    (hz : ∀ i, (z i).real = (points i).val)
    (v : Fin n → FpCoord p d)
    (hvspace : ∀ i, v i ∈ R.space (points i).base)
    (hvmap : ∀ i, R.map (points i).base (v i) = (z i).mod p)
    (α : Fin n → ℕ) (hαsum : (∑ i, α i) = p)
    (hαzero : (∑ i, α i • v i) = 0)
    (result : F.Point)
    (hcomb : ConvexFlag.ConvexCombination points
      (fun i ↦ (α i : ℝ) / (p : ℝ)) result) :
    result.IsIntegral := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let A := {i : Fin n // 0 < (α i : ℝ) / (p : ℝ)}
  have hpos_iff (i : Fin n) :
      0 < (α i : ℝ) / (p : ℝ) ↔ 0 < α i := by
    constructor
    · intro hi
      rcases div_pos_iff.mp hi with h | h
      · exact_mod_cast h.1
      · exact (not_lt_of_ge hpR.le h.2).elim
    · intro hi
      exact div_pos (by exact_mod_cast hi) hpR
  have hzero_inactive (i : {i : Fin n // ¬ 0 < (α i : ℝ) / (p : ℝ)}) :
      α i = 0 := by
    have : ¬ 0 < α (i : Fin n) := by
      intro hi
      exact i.property ((hpos_iff i).2 hi)
    omega
  have hactive_sum : (∑ i : A, α i) = p := by
    calc
      (∑ i : A, α i) =
          (∑ i : A, α i) +
            ∑ i : {i : Fin n // ¬ 0 < (α i : ℝ) / (p : ℝ)}, α i := by
              have hinactive :
                  (∑ i : {i : Fin n // ¬ 0 < (α i : ℝ) / (p : ℝ)}, α i) = 0 := by
                exact Finset.sum_eq_zero fun i _ ↦ hzero_inactive i
              rw [hinactive, add_zero]
      _ = ∑ i, α i := Fintype.sum_subtype_add_sum_subtype _ _
      _ = p := hαsum
  have hactive_zero : (∑ i : A, α i • v i) = 0 := by
    calc
      (∑ i : A, α i • v i) =
          (∑ i : A, α i • v i) +
            ∑ i : {i : Fin n // ¬ 0 < (α i : ℝ) / (p : ℝ)}, α i • v i := by
              have hinactive :
                  (∑ i : {i : Fin n // ¬ 0 < (α i : ℝ) / (p : ℝ)},
                    α i • v i) = 0 := by
                apply Finset.sum_eq_zero
                intro i _
                simp [hzero_inactive i]
              rw [hinactive, add_zero]
      _ = ∑ i, α i • v i := by
        simpa [A] using
          (Fintype.sum_subtype_add_sum_subtype
            (p := fun i : Fin n ↦ 0 < (α i : ℝ) / (p : ℝ))
            (f := fun i ↦ α i • v i))
      _ = 0 := hαzero
  have hbase (i : A) : (points i).base ≤ result.base :=
    hcomb.base_isLUB.1 i i.property
  let zu : A → IntCoord (F.rank result.base) :=
    fun i ↦ (F.transition (hbase i)).integer (z i)
  have hzu_real (i : A) :
      (zu i).real = (points i).coord (hbase i) := by
    calc
      (zu i).real = (F.transition (hbase i)).real (z i).real :=
        ((F.transition (hbase i)).real_integer (z i)).symm
      _ = (F.transition (hbase i)).real (points i).val := congrArg _ (hz i)
      _ = (points i).coord (hbase i) := rfl
  have hmap_upper (i : A) :
      R.map result.base (v i) = (zu i).mod p := by
    calc
      R.map result.base (v i) =
          (F.transition (hbase i)).modp p (R.map (points i).base (v i)) :=
        R.compatible (hbase i) (hvspace i)
      _ = (F.transition (hbase i)).modp p ((z i).mod p) :=
        congrArg _ (hvmap i)
      _ = (zu i).mod p := (F.transition (hbase i)).mod_integer p (z i)
  have hcoeff_mod : (∑ i : A, (α i : ZMod p)) = 0 := by
    rw [← Nat.cast_sum, hactive_sum]
    exact ZMod.natCast_self p
  have hsource_mod : (∑ i : A, (α i : ZMod p) • v i) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hactive_zero
  have hmapped_mod :
      (∑ i : A, (α i : ZMod p) • R.map result.base (v i)) = 0 :=
    affineMap_sum_smul_eq_zero (R.map result.base)
      (fun i : A ↦ (α i : ZMod p)) (fun i ↦ v i) hcoeff_mod hsource_mod
  have hzu_mod : (∑ i : A, α i • (zu i).mod p) = 0 := by
    calc
      (∑ i : A, α i • (zu i).mod p) =
          ∑ i : A, (α i : ZMod p) • R.map result.base (v i) := by
            apply Fintype.sum_congr
            intro i
            rw [hmap_upper i]
            exact (Nat.cast_smul_eq_nsmul (ZMod p) (α i) ((zu i).mod p)).symm
      _ = 0 := hmapped_mod
  have hint := isIntegral_weighted_average_of_mod_eq_zero hp.pos
    (fun i : A ↦ α i) zu hzu_mod
  apply (R.lattice_eq_standard result.base result.val).2
  rw [hcomb.val_eq]
  simpa only [hzu_real] using hint

/-- The cardinality contradiction at the heart of Proposition 7.1.

This version deliberately assumes only an `FpRepresentation`; none of the
minimality, reducedness, completeness, mass, or face conditions of a flag
decomposition enter the proof. -/
theorem hellyIndependent_card_le_hollowConstant
    {p d n : ℕ} (hp : Nat.Prime p) {F : ConvexFlag}
    (R : FpRepresentation p d F) {Omega : F.ProperPointSet}
    {points : Fin n → F.Point}
    (hind : ConvexFlag.HellyIndependent Omega points) :
    n ≤ hollowConstant p d := by
  classical
  by_contra hnle
  have hn : hollowConstant p d < n := Nat.lt_of_not_ge hnle
  have hstandard (i : Fin n) : EGZ.IsIntegral (points i).val :=
    (R.lattice_eq_standard (points i).base (points i).val).1
      (hind.integral i)
  choose z hz using hstandard
  have hlift (i : Fin n) :
      ∃ vi : FpCoord p d,
        vi ∈ R.space (points i).base ∧
          R.map (points i).base vi = (z i).mod p := by
    exact R.map_surjective (points i).base (Set.mem_univ ((z i).mod p))
  choose v hvspace hvmap using hlift
  obtain ⟨α, hαsum, hαzero, hαlt⟩ :=
    exists_nontrivial_zero_combination_of_hollowConstant_lt hp hn v
  let weight : Fin n → ℝ := fun i ↦ (α i : ℝ) / (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hnonnegative : ∀ i, 0 ≤ weight i := by
    intro i
    exact div_nonneg (Nat.cast_nonneg _) hpR.le
  have hweight_sum : (∑ i, weight i) = 1 := by
    change (∑ i, (α i : ℝ) / (p : ℝ)) = 1
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    have hcast : (∑ i, (α i : ℝ)) = (p : ℝ) := by
      exact_mod_cast hαsum
    rw [hcast]
    exact mul_inv_cancel₀ hpR.ne'
  obtain ⟨result, hcomb⟩ :=
    ConvexFlag.exists_convexCombination points weight hnonnegative hweight_sum
  have hresult : result.IsIntegral :=
    R.convexCombination_isIntegral_of_zero_sum hp points z hz v hvspace hvmap
      α hαsum hαzero result (by simpa only [weight] using hcomb)
  obtain ⟨i, hi⟩ := hind.only_trivial weight result hcomb hresult
  have hiR : (α i : ℝ) = (p : ℝ) := by
    exact (div_eq_one_iff_eq hpR.ne').mp (by simpa only [weight] using hi)
  have hiNat : α i = p := by exact_mod_cast hiR
  exact (Nat.ne_of_lt (hαlt i)) hiNat

/-- Proposition 7.1 at the level of an arbitrary representation. -/
theorem hellyConstant_le_hollowConstant
    {p d : ℕ} (hp : Nat.Prime p) {F : ConvexFlag}
    (R : FpRepresentation p d F) (Omega : F.ProperPointSet) :
    ConvexFlag.hellyConstant Omega ≤ hollowConstant p d := by
  obtain ⟨points, hind⟩ := ConvexFlag.hellyConstant_spec Omega
  exact R.hellyIndependent_card_le_hollowConstant hp hind

end FpRepresentation

namespace FlagDecomposition

/-- Proposition 7.1 (`lbound`) for the proper-point set of a flag
decomposition.  The proof factors through the representation-only result
above, recording precisely which part of the Section 4 structure it uses. -/
theorem propositionSevenOne
    {p d : ℕ} [NeZero p] (hp : Nat.Prime p)
    {f : FpCoord p d → ℕ} (Phi : FlagDecomposition p d f) :
    ConvexFlag.hellyConstant Phi.properPoints ≤ hollowConstant p d :=
  Phi.representation.hellyConstant_le_hollowConstant hp Phi.properPoints

end FlagDecomposition

end EGZ
