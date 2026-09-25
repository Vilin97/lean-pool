/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEquation
public import LeanPool.MarkoffModP.BGS.Markoff.Core.TraceClassification
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Concrete right subgroups for the middle game

All split and nonsplit semisimple eigenvalues are placed in the common quadratic extension.
For a candidate order `d`, the right subgroup is the subgroup of `d`-th roots of unity in that
extension.  Candidate divisibility by `p - 1` or `p + 1` implies that this subgroup has exactly
`d` elements.

Parabolic traces are deliberately excluded from the representation theorem: their rotation
orders are `p` or `2 * p`, not semisimple torus orders dividing `p - 1` or `p + 1`.
-/

@[expose] public section

namespace BGS.Markoff

/-- The canonical right subgroup of order `d` inside the common quadratic extension. -/
noncomputable def middleGameRightSubgroup (p d : ℕ) [Fact p.Prime] :
    Subgroup (quadraticFiniteField p)ˣ :=
  rootsOfUnity d (quadraticFiniteField p)

theorem mem_middleGameRightSubgroup_iff_pow_eq_one
    (p d : ℕ) [Fact p.Prime] (u : (quadraticFiniteField p)ˣ) :
    u ∈ middleGameRightSubgroup p d ↔ u ^ d = 1 := by
  exact mem_rootsOfUnity d u

/-- Every element whose multiplicative order is `d` belongs to the canonical right subgroup. -/
theorem mem_middleGameRightSubgroup_of_orderOf_eq
    (p d : ℕ) [Fact p.Prime] (u : (quadraticFiniteField p)ˣ)
    (hu : orderOf u = d) :
    u ∈ middleGameRightSubgroup p d := by
  rw [mem_middleGameRightSubgroup_iff_pow_eq_one, ← hu]
  exact pow_orderOf_eq_one u

/-- Candidate divisibility by `p - 1` or `p + 1` implies divisibility by the order of the
multiplicative group of the quadratic extension. -/
theorem middleGameCandidateOrder_dvd_quadraticUnitsCard
    (p currentOrder d : ℕ) [Fact p.Prime]
    (hd : d ∈ middleGameCandidateOrders p currentOrder) :
    d ∣ Nat.card (quadraticFiniteField p)ˣ := by
  have hfieldCard : Nat.card (quadraticFiniteField p) = p ^ 2 :=
    GaloisField.card p (n := 2) (by norm_num)
  have hunitsCard : Nat.card (quadraticFiniteField p)ˣ = p ^ 2 - 1 := by
    rw [Nat.card_units, hfieldCard]
  rw [hunitsCard]
  have hfactor : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using (sq_tsub_sq p 1)
  rw [hfactor]
  rcases (mem_middleGameCandidateOrders_iff.mp hd).2 with hminus | hplus
  · exact dvd_mul_of_dvd_right hminus.1 (p + 1)
  · exact dvd_mul_of_dvd_left hplus (p - 1)

/-- The canonical right subgroup indexed by a candidate order has exactly that cardinality. -/
theorem middleGameRightSubgroup_natCard
    (p currentOrder d : ℕ) [Fact p.Prime]
    (hd : d ∈ middleGameCandidateOrders p currentOrder) :
    Nat.card (middleGameRightSubgroup p d) = d := by
  let E := quadraticFiniteField p
  let : Fintype E := Fintype.ofFinite E
  have hdvd : d ∣ Nat.card Eˣ :=
    middleGameCandidateOrder_dvd_quadraticUnitsCard p currentOrder d hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd Nat.card_pos
  let : NeZero d := ⟨hdpos.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  let zeta : Eˣ := g ^ (orderOf g / d)
  have horder : orderOf zeta = d := by
    apply orderOf_pow_orderOf_div
    · rw [hg]
      exact Nat.card_pos.ne'
    · rwa [hg]
  have hprimitive : IsPrimitiveRoot zeta d := IsPrimitiveRoot.iff_orderOf.mpr horder
  exact hprimitive.card_rootsOfUnity'

/-- A split eigenvalue of rotation order `d`, embedded in the quadratic extension, lies in the
canonical right subgroup and has the required reciprocal trace. -/
theorem exists_middleGameRightSubgroup_trace_of_split
    (p d : ℕ) [Fact p.Prime]
    (t : ZMod p) (w : (ZMod p)ˣ)
    (htrace : splitTorusTrace w = t)
    (hw : (w : ZMod p) ^ 2 ≠ 1)
    (hrotation : rotationOrder t = d) :
    ∃ h₂ : middleGameRightSubgroup p d,
      algebraMap (ZMod p) (quadraticFiniteField p) t = splitTorusTrace h₂ := by
  let embedding : (ZMod p)ˣ →* (quadraticFiniteField p)ˣ :=
    Units.map (algebraMap (ZMod p) (quadraticFiniteField p)).toMonoidHom
  let u : (quadraticFiniteField p)ˣ := embedding w
  have horder : orderOf w = d := by
    rw [← rotationOrder_splitTorusTrace w hw, htrace]
    exact hrotation
  have hupow : u ^ d = 1 := by
    calc
      u ^ d = embedding (w ^ d) := (map_pow embedding w d).symm
      _ = embedding 1 := by rw [← horder, pow_orderOf_eq_one]
      _ = 1 := map_one embedding
  let h₂ : middleGameRightSubgroup p d :=
    ⟨u, (mem_middleGameRightSubgroup_iff_pow_eq_one p d u).mpr hupow⟩
  refine ⟨h₂, ?_⟩
  rw [← htrace]
  change algebraMap (ZMod p) (quadraticFiniteField p) (splitTorusTrace w) =
    splitTorusTrace (embedding w)
  rw [splitTorusTrace, splitTorusTrace, map_add]
  rfl

/-- A nonsplit norm-one eigenvalue of rotation order `d` lies in the same canonical quadratic
right subgroup and represents the scalar-extended base-field trace. -/
theorem exists_middleGameRightSubgroup_trace_of_nonsplit
    (p d : ℕ) [Fact p.Prime]
    (t : ZMod p) (w : quadraticNormOneTorus p)
    (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (hrotation : rotationOrder t = d) :
    ∃ h₂ : middleGameRightSubgroup p d,
      algebraMap (ZMod p) (quadraticFiniteField p) t = splitTorusTrace h₂ := by
  let u : (quadraticFiniteField p)ˣ := w
  have horder : orderOf w = d := by
    rw [← rotationOrder_quadraticNormOneTrace p w hw, htrace]
    exact hrotation
  have hwpow : w ^ d = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one w
  have hupow : u ^ d = 1 := by
    exact congrArg Subtype.val hwpow
  let h₂ : middleGameRightSubgroup p d :=
    ⟨u, (mem_middleGameRightSubgroup_iff_pow_eq_one p d u).mpr hupow⟩
  refine ⟨h₂, ?_⟩
  rw [← htrace]
  exact algebraMap_quadraticNormOneTrace p w

/-- Every nonparabolic normalized trace of rotation order `d` is represented in the canonical
right subgroup.  The hypothesis `t^2 != 4` is the explicit boundary separating this theorem
from the parabolic orders `p` and `2 * p`. -/
theorem exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
    (p d : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (hnonparabolic : t ^ 2 ≠ 4)
    (hrotation : rotationOrder t = d) :
    ∃ h₂ : middleGameRightSubgroup p d,
      algebraMap (ZMod p) (quadraticFiniteField p) t = splitTorusTrace h₂ := by
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t hnonparabolic with
    ⟨w, htrace, hw⟩ | ⟨w, htrace, hw⟩
  · exact exists_middleGameRightSubgroup_trace_of_split
      p d t w htrace hw hrotation
  · exact exists_middleGameRightSubgroup_trace_of_nonsplit
      p d t w htrace hw hrotation

/-- Over a prime field, the equation `t^2 = 4` is exactly the explicit parabolic alternative
`t = 2` or `t = -2`. -/
theorem normalizedTrace_sq_eq_four_iff_parabolic
    (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    t ^ 2 = 4 ↔ t = 2 ∨ t = -2 := by
  constructor
  · intro ht
    have hfactor : (t - 2) * (t + 2) = 0 := by
      calc
        (t - 2) * (t + 2) = t ^ 2 - 4 := by ring
        _ = 0 := sub_eq_zero.mpr ht
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · rintro (rfl | rfl) <;> ring

/-- Complete candidate-order classification.  The canonical right subgroup always has exact
cardinality `d`; a trace of rotation order `d` is either one of the two parabolic parameters or
is represented by a reciprocal trace in that subgroup. -/
theorem middleGameRightSubgroup_exactCard_and_traceClassification
    (p currentOrder d : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (hd : d ∈ middleGameCandidateOrders p currentOrder)
    (t : ZMod p) (hrotation : rotationOrder t = d) :
    Nat.card (middleGameRightSubgroup p d) = d ∧
      (t = 2 ∨ t = -2 ∨
        ∃ h₂ : middleGameRightSubgroup p d,
          algebraMap (ZMod p) (quadraticFiniteField p) t = splitTorusTrace h₂) := by
  refine ⟨middleGameRightSubgroup_natCard p currentOrder d hd, ?_⟩
  by_cases hparabolic : t ^ 2 = 4
  · rcases (normalizedTrace_sq_eq_four_iff_parabolic p t).mp hparabolic with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr
      (exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
        p d hpTwo t hparabolic hrotation))

end BGS.Markoff
