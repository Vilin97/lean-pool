/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Maschke
import LeanPool.CommonNeighbourConjecture.Examples.EveryBase.DeletedModule

/-!
# Irreducibility of the odd deleted modules

For odd `d`, the affine group `Hq d` has three orbitals on ordered pairs of
field points.  Thus every equivariant endomorphism of the full binary
permutation module has a three-parameter matrix.  The all-ones parameter
vanishes on the deleted module, leaving `a I + b A`, where `A` is the Paley
adjacency operator.  A two-point vector proves that neither `A` nor `I + A`
is idempotent.  Maschke's theorem then proves irreducibility.
-/

noncomputable section

namespace SaxlCounterexamples.EveryBase

open scoped BigOperators MonoidAlgebra

theorem f2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  have hlt := ZMod.val_lt a
  interval_cases h : a.val
  · left
    apply ZMod.val_injective
    simpa using h
  · right
    apply ZMod.val_injective
    simpa [ZMod.val_one 2] using h

/-! ## Rank-three centralizer algebra -/

variable {H Ω : Type*} [Group H] [MulAction H Ω] [Finite Ω]

/-- A local enumeration supplied by finiteness. -/
noncomputable local instance finiteFintype : Fintype Ω := Fintype.ofFinite Ω

section RankThree

/-- Local classical decidable equality for matrix coefficients. -/
local instance finiteDecidableEq : DecidableEq Ω := Classical.decEq Ω

/-- The `(x,y)` matrix coefficient, with row `x` and column `y`. -/
def matrixCoeff (E : PermMod Ω →ₗ[F2] PermMod Ω) (x y : Ω) : F2 :=
  E (Pi.basisFun F2 Ω y) x

theorem smul_basisFun (g : H) (y : Ω) :
    g • (Pi.basisFun F2 Ω y) = Pi.basisFun F2 Ω (g • y) := by
  classical
  funext x
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  change (Pi.single y (1 : F2) : PermMod Ω) (g⁻¹ • x) =
    (Pi.single (g • y) (1 : F2) : PermMod Ω) x
  have hiff : g⁻¹ • x = y ↔ x = g • y := by
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      simp
  simp only [Pi.single_apply]
  by_cases h : g⁻¹ • x = y
  · simp [hiff.mp h]
  · have h' : x ≠ g • y := fun hx ↦ h (hiff.mpr hx)
    simp [h, h']

theorem matrixCoeff_smul
    (E : PermMod Ω →ₗ[F2] PermMod Ω)
    (hE : ∀ (g : H) f, E (g • f) = g • E f)
    (g : H) (x y : Ω) :
    matrixCoeff E (g • x) (g • y) = matrixCoeff E x y := by
  classical
  rw [matrixCoeff, ← smul_basisFun]
  rw [hE]
  change E (Pi.basisFun F2 Ω y) (g⁻¹ • g • x) = _
  simp [matrixCoeff]

/-- Data saying that the ordered-pair orbitals are the diagonal, `R`, and its
off-diagonal complement. -/
structure RankThreeOrbitals (R : Ω → Ω → Prop) where
  /-- A representative point for the diagonal orbital. -/
  diag : Ω
  /-- The first point of a representative pair in `R`. -/
  relX : Ω
  /-- The second point of a representative pair in `R`. -/
  relY : Ω
  /-- The first point of a representative off-diagonal pair outside `R`. -/
  otherX : Ω
  /-- The second point of a representative off-diagonal pair outside `R`. -/
  otherY : Ω
  rel_mem : R relX relY
  other_ne : otherX ≠ otherY
  other_not_mem : ¬ R otherX otherY
  diag_transport : ∀ x, ∃ g : H, g • diag = x
  rel_transport : ∀ x y, x ≠ y → R x y →
    ∃ g : H, g • relX = x ∧ g • relY = y
  other_transport : ∀ x y, x ≠ y → ¬ R x y →
    ∃ g : H, g • otherX = x ∧ g • otherY = y

theorem matrixCoeff_rankThree
    (R : Ω → Ω → Prop) [DecidableRel R]
    (K : RankThreeOrbitals (H := H) R)
    (E : PermMod Ω →ₗ[F2] PermMod Ω)
    (hE : ∀ (g : H) f, E (g • f) = g • E f) :
    ∀ x y, matrixCoeff E x y =
      if x = y then matrixCoeff E K.diag K.diag
      else if R x y then matrixCoeff E K.relX K.relY
      else matrixCoeff E K.otherX K.otherY := by
  intro x y
  by_cases hxy : x = y
  · subst y
    simp only [ite_true]
    obtain ⟨g, rfl⟩ := K.diag_transport x
    exact matrixCoeff_smul E hE g K.diag K.diag
  · simp only [hxy, ite_false]
    by_cases hR : R x y
    · simp only [hR, ite_true]
      obtain ⟨g, hgx, hgy⟩ := K.rel_transport x y hxy hR
      rw [← hgx, ← hgy]
      exact matrixCoeff_smul E hE g K.relX K.relY
    · simp only [hR, ite_false]
      obtain ⟨g, hgx, hgy⟩ := K.other_transport x y hxy hR
      rw [← hgx, ← hgy]
      exact matrixCoeff_smul E hE g K.otherX K.otherY

theorem apply_eq_sum_matrixCoeff
    (E : PermMod Ω →ₗ[F2] PermMod Ω) (f : PermMod Ω) (x : Ω) :
    E f x = ∑ y, f y * matrixCoeff E x y := by
  conv_lhs => rw [← (Pi.basisFun F2 Ω).sum_repr f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    Pi.basisFun_repr, smul_eq_mul, matrixCoeff]

/-- The linear operator with constant coefficients on the three orbitals. -/
def rankThreeOp (R : Ω → Ω → Prop) [DecidableRel R] (α β γ : F2) :
    PermMod Ω →ₗ[F2] PermMod Ω where
  toFun f x := ∑ y, f y * (if x = y then α else if R x y then β else γ)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  map_smul' a f := by
    funext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

theorem eq_rankThreeOp_of_matrixCoeff
    (E : PermMod Ω →ₗ[F2] PermMod Ω) (R : Ω → Ω → Prop) [DecidableRel R]
    (α β γ : F2)
    (hE : ∀ x y, matrixCoeff E x y =
      if x = y then α else if R x y then β else γ) :
    E = rankThreeOp R α β γ := by
  apply LinearMap.ext
  intro f
  funext x
  rw [apply_eq_sum_matrixCoeff]
  simp_rw [hE]
  rfl

/-- The rank-one operator sending a vector to its constant coordinate sum. -/
def allOnesOp : PermMod Ω →ₗ[F2] PermMod Ω where
  toFun f := fun _ ↦ coordSum f
  map_add' f g := by
    funext x
    exact map_add coordSum f g
  map_smul' a f := by
    funext x
    exact map_smul coordSum a f

/-- This is the exact point at which the all-ones matrix is killed by
restriction to the deleted module. -/
@[simp] theorem allOnesOp_deleted (v : DeletedModule Ω) :
    allOnesOp (v : PermMod Ω) = 0 := by
  funext x
  exact v.property

/-- Sum a vector over the `R`-neighbors of a point. -/
def relationSum (R : Ω → Ω → Prop) [DecidableRel R]
    (v : PermMod Ω) (x : Ω) : F2 :=
  ∑ y, if R x y then v y else 0

theorem rankThreeOp_apply_deleted
    (R : Ω → Ω → Prop) [DecidableRel R]
    (hdiag : ∀ x, ¬ R x x) (α β γ : F2)
    (v : DeletedModule Ω) (x : Ω) :
    rankThreeOp R α β γ (v : PermMod Ω) x =
      (α + γ) * (v : PermMod Ω) x +
        (β + γ) * relationSum R v x := by
  have hlin (a b t : F2) : t * a = (a + b) * t + b * t := by
    have hcancel := ZModModule.add_self (b * t)
    calc
      t * a = a * t := mul_comm _ _
      _ = a * t + (b * t + b * t) := by rw [hcancel, add_zero]
      _ = (a + b) * t + b * t := by rw [add_mul]; abel
  have hcoeff (y : Ω) :
      (v : PermMod Ω) y * (if x = y then α else if R x y then β else γ) =
        (α + γ) * (if x = y then (v : PermMod Ω) y else 0) +
          (β + γ) * (if R x y then (v : PermMod Ω) y else 0) +
            γ * (v : PermMod Ω) y := by
    by_cases hxy : x = y
    · subst y
      simp only [ite_true, hdiag, ite_false, mul_zero, add_zero]
      exact hlin α γ _
    · by_cases hR : R x y
      · simp only [hxy, ite_false, hR, ite_true, mul_zero, zero_add]
        exact hlin β γ _
      · simp only [hxy, ite_false, hR, mul_zero, add_zero, zero_add]
        exact mul_comm _ _
  simp only [rankThreeOp, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [hcoeff]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hdiagSum : (∑ y, if x = y then (v : PermMod Ω) y else 0) =
      (v : PermMod Ω) x := Fintype.sum_ite_eq x (v : PermMod Ω)
  rw [hdiagSum]
  simp only [relationSum]
  have hsum : ∑ y, (v : PermMod Ω) y = 0 := v.property
  rw [hsum, mul_zero, add_zero]

end RankThree

theorem double_sum_eq_diag_of_symmetric
    {I A : Type*} [AddCommMonoid A]
    (hchar2 : ∀ a : A, a + a = 0) (s : Finset I) (f : I → I → A)
    (hsymm : ∀ i j, f i j = f j i) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = ∑ i ∈ s, f i i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      calc
        (∑ i ∈ insert a s, ∑ j ∈ insert a s, f i j) =
            f a a + (∑ j ∈ s, f a j) + (∑ i ∈ s, f i a) +
              (∑ i ∈ s, ∑ j ∈ s, f i j) := by
                rw [Finset.sum_insert ha]
                rw [Finset.sum_insert ha]
                simp_rw [Finset.sum_insert ha]
                rw [Finset.sum_add_distrib]
                abel
        _ = f a a + (∑ i ∈ s, f i i) := by
          rw [ih]
          have hcross : (∑ j ∈ s, f a j) + (∑ i ∈ s, f i a) = 0 := by
            have heq : (∑ i ∈ s, f i a) = ∑ i ∈ s, f a i := by
              apply Finset.sum_congr rfl
              intro i _
              exact hsymm i a
            rw [heq]
            exact hchar2 _
          calc
            f a a + (∑ j ∈ s, f a j) + (∑ i ∈ s, f i a) +
                (∑ i ∈ s, f i i) =
                f a a + ((∑ j ∈ s, f a j) + (∑ i ∈ s, f i a)) +
                  (∑ i ∈ s, f i i) := by abel
            _ = _ := by rw [hcross]; simp
        _ = ∑ i ∈ insert a s, f i i := by rw [Finset.sum_insert ha]

/-! ## Maschke projection -/

variable [Finite H] [NeZero (Nat.card H : F2)]

theorem exists_equivariant_idempotent_projection
    (U : Subrepresentation
      (Representation.ofDistribMulAction F2 H (DeletedModule Ω))) :
    ∃ p : DeletedModule Ω →ₗ[F2] DeletedModule Ω,
      (∀ (g : H) v, p (g • v) = g • p v) ∧
      p.comp p = p ∧ LinearMap.range p = U.toSubmodule := by
  let ρ := Representation.ofDistribMulAction F2 H (DeletedModule Ω)
  obtain ⟨Q, hUQ⟩ := exists_isCompl U
  have hUQ0 : IsCompl U.toSubmodule Q.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      have h := congrArg Subrepresentation.toSubmodule hUQ.disjoint.eq_bot
      calc
        U.toSubmodule ⊓ Q.toSubmodule =
            (⊥ : Subrepresentation ρ).toSubmodule := h
        _ = ⊥ := rfl
    · rw [codisjoint_iff]
      have h := congrArg Subrepresentation.toSubmodule hUQ.codisjoint.eq_top
      calc
        U.toSubmodule ⊔ Q.toSubmodule =
            (⊤ : Subrepresentation ρ).toSubmodule := h
        _ = ⊤ := rfl
  let p : DeletedModule Ω →ₗ[F2] DeletedModule Ω :=
    U.toSubmodule.projection Q.toSubmodule hUQ0
  refine ⟨p, ?_, ?_, ?_⟩
  · intro g v
    have hpU : p v ∈ U.toSubmodule :=
      Submodule.projection_apply_mem hUQ0 v
    have hqQ : v - p v ∈ Q.toSubmodule :=
      Submodule.sub_projection_mem hUQ0 v
    have hgpU : g • p v ∈ U.toSubmodule := U.apply_mem_toSubmodule g hpU
    have hgqQ : g • (v - p v) ∈ Q.toSubmodule := Q.apply_mem_toSubmodule g hqQ
    calc
      p (g • v) = p (g • p v + g • (v - p v)) := by
        congr 2
        rw [← smul_add]
        congr 1
        module
      _ = p (g • p v) + p (g • (v - p v)) := p.map_add _ _
      _ = g • p v := by
        rw [Submodule.projection_apply_of_mem_left hUQ0 hgpU,
          Submodule.projection_apply_of_mem_right hUQ0 hgqQ, add_zero]
  · apply LinearMap.ext
    intro v
    change p (p v) = p v
    exact Submodule.projection_apply_of_mem_left hUQ0
      (Submodule.projection_apply_mem hUQ0 v)
  · exact Submodule.range_projection hUQ0

/-! ## The concrete Paley orbital -/

/-- The Paley relation: `x - y` is a nonzero square. -/
def SquareDiff (d : Nat) (x y : Fq d) : Prop :=
  x ≠ y ∧ IsSquare (x - y)

noncomputable instance squareDiffDecidable (d : Nat) :
    DecidableRel (SquareDiff d) :=
  fun x y ↦ Classical.propDecidable (SquareDiff d x y)

/-- Representatives and transport proofs for the three Paley orbitals. -/
noncomputable def hqRankThreeOrbitals (d : Nat) (hd : Odd d) :
    RankThreeOrbitals (H := Hq d) (SquareDiff d) where
  diag := 0
  relX := 1
  relY := 0
  otherX := -1
  otherY := 0
  rel_mem := by
    constructor
    · exact one_ne_zero
    · rw [sub_zero]
      exact IsSquare.one
  other_ne := neg_ne_zero.mpr one_ne_zero
  other_not_mem := by
    intro h
    exact neg_one_not_square d hd (by simpa using h.2)
  diag_transport x := by
    let g : Hq d := ⟨Multiplicative.ofAdd x, 1⟩
    refine ⟨g, ?_⟩
    simp [g, Saxl.affine_smul_def]
  rel_transport x y hxy hR := by
    have hz0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
    let g := affineOfSquare d y (x - y) hz0 hR.2
    refine ⟨g, ?_, ?_⟩
    · change affineOfSquare d y (x - y) hz0 hR.2 • (1 : Fq d) = x
      rw [affineOfSquare_smul]
      ring
    · change affineOfSquare d y (x - y) hz0 hR.2 • (0 : Fq d) = y
      rw [affineOfSquare_smul]
      ring
  other_transport x y hxy hR := by
    have hz0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hnonsq : ¬ IsSquare (x - y) := by
      intro hs
      exact hR ⟨hxy, hs⟩
    have hsneg : IsSquare (-(x - y)) :=
      neg_isSquare_of_not_isSquare d hd hz0 hnonsq
    let g := affineOfSquare d y (-(x - y)) (neg_ne_zero.mpr hz0) hsneg
    refine ⟨g, ?_, ?_⟩
    · change affineOfSquare d y (-(x - y)) (neg_ne_zero.mpr hz0) hsneg •
        (-1 : Fq d) = x
      rw [affineOfSquare_smul]
      ring
    · change affineOfSquare d y (-(x - y)) (neg_ne_zero.mpr hz0) hsneg •
        (0 : Fq d) = y
      rw [affineOfSquare_smul]
      ring

/-- The finite set of nonzero squares in `Fq d`. -/
noncomputable def squareFinset (d : Nat) : Finset (Fq d) :=
  Finset.univ.filter fun z ↦ z ≠ 0 ∧ IsSquare z

@[simp] theorem mem_squareFinset (d : Nat) (z : Fq d) :
    z ∈ squareFinset d ↔ z ≠ 0 ∧ IsSquare z := by
  classical
  simp [squareFinset]

theorem one_mem_squareFinset (d : Nat) : (1 : Fq d) ∈ squareFinset d := by
  simp

/-- The Paley adjacency operator on the binary permutation module. -/
noncomputable def paleyOp (d : Nat) :
    PermMod (Fq d) →ₗ[F2] PermMod (Fq d) where
  toFun f x := ∑ c ∈ squareFinset d, f (x - c)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a f := by
    funext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]

/-- The finite set of Paley neighbors of `x`. -/
noncomputable def squareRelFinset (d : Nat) (x : Fq d) : Finset (Fq d) :=
  Finset.univ.filter (SquareDiff d x)

@[simp] theorem mem_squareRelFinset (d : Nat) (x y : Fq d) :
    y ∈ squareRelFinset d x ↔ SquareDiff d x y := by
  classical
  simp [squareRelFinset]

theorem relationSum_squareDiff_eq_paley
    (d : Nat) (v : PermMod (Fq d)) (x : Fq d) :
    relationSum (SquareDiff d) v x = paleyOp d v x := by
  have hrel : relationSum (SquareDiff d) v x =
      ∑ y ∈ squareRelFinset d x, v y := by
    classical
    simp only [relationSum, squareRelFinset]
    rw [Finset.sum_filter]
  rw [hrel]
  change (∑ y ∈ squareRelFinset d x, v y) =
    ∑ c ∈ squareFinset d, v (x - c)
  symm
  apply Finset.sum_bij (fun c _ ↦ x - c)
  · intro c hc
    rw [mem_squareRelFinset]
    have hc' := (mem_squareFinset d c).mp hc
    constructor
    · intro h
      exact hc'.1 (sub_eq_self.mp h.symm)
    · convert hc'.2 using 1
      ring
  · intro c₁ _ c₂ _ h
    linear_combination -h
  · intro y hy
    refine ⟨x - y, ?_, by ring⟩
    rw [mem_squareFinset]
    have hy' := (mem_squareRelFinset d x y).mp hy
    exact ⟨sub_ne_zero.mpr hy'.1, hy'.2⟩
  · intro _ _
    rfl

theorem paley_pairVector_zero (d : Nat) (hd : Odd d) :
    paleyOp d (pairVector d : PermMod (Fq d)) 0 = 0 := by
  apply Finset.sum_eq_zero
  intro c hc
  have hc' := (mem_squareFinset d c).mp hc
  have hneg0 : -c ≠ 0 := neg_ne_zero.mpr hc'.1
  have hneg1 : -c ≠ 1 := by
    intro h
    have hcneg : c = -1 := by linear_combination -h
    exact neg_one_not_square d hd (hcneg ▸ hc'.2)
  rw [pairVector_apply, Pi.basisFun_apply, Pi.basisFun_apply]
  simp [hneg0, hneg1]

theorem char_three_neg_add_self (d : Nat) (c : Fq d) : -c - c = c := by
  have h3 : (3 : Fq d) = 0 := CharP.cast_eq_zero (Fq d) 3
  calc
    -c - c = -(3 * c) + c := by ring
    _ = c := by rw [h3, zero_mul, neg_zero, zero_add]

/-- The parity witness with the exact relation orientation `x-y ∈ Cq`:
for the two-point vector `v`, `A v (0)=0` but `A² v (0)=1`. -/
theorem paley_sq_pairVector_zero (d : Nat) :
    paleyOp d (paleyOp d (pairVector d : PermMod (Fq d))) 0 = 1 := by
  simp only [paleyOp, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [zero_sub]
  rw [double_sum_eq_diag_of_symmetric ZModModule.add_self]
  · simp_rw [char_three_neg_add_self]
    rw [Finset.sum_eq_single 1]
    · rw [pairVector_apply, Pi.basisFun_apply, Pi.basisFun_apply]
      simp
    · intro c hc hc1
      have hc0 := (mem_squareFinset d c).mp hc |>.1
      rw [pairVector_apply, Pi.basisFun_apply, Pi.basisFun_apply]
      simp [hc0, hc1]
    · intro hnot
      exact (hnot (one_mem_squareFinset d)).elim
  · intro c e
    ring_nf

theorem paley_map_add (d : Nat) (f g : PermMod (Fq d)) :
    paleyOp d (f + g) = paleyOp d f + paleyOp d g :=
  map_add (paleyOp d) f g

theorem idempotent_rankThree_restriction
    (d : Nat) (hd : Odd d)
    (p : Vq d →ₗ[F2] Vq d)
    (hp : p.comp p = p)
    (a b : F2)
    (hform : ∀ (v : Vq d) (x : Fq d),
      (p v : PermMod (Fq d)) x =
        a * (v : PermMod (Fq d)) x + b * paleyOp d v x) :
    p = 0 ∨ p = LinearMap.id := by
  have hid (v : Vq d) : p (p v) = p v := LinearMap.congr_fun hp v
  rcases f2_eq_zero_or_one a with ha | ha <;>
    rcases f2_eq_zero_or_one b with hb | hb
  all_goals subst a; subst b
  · left
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    have hx := hform v x
    norm_num at hx
    simpa using hx
  · exfalso
    let v := pairVector d
    have hpv_fun : (p v : PermMod (Fq d)) = paleyOp d v := by
      funext x
      have hx := hform v x
      norm_num at hx
      exact hx
    have hpv0 : (p v : PermMod (Fq d)) 0 = 0 := by
      rw [hpv_fun]
      exact paley_pairVector_zero d hd
    have hppv0 : (p (p v) : PermMod (Fq d)) 0 = 1 := by
      calc
        (p (p v) : PermMod (Fq d)) 0 = paleyOp d (p v) 0 := by
          have hx := hform (p v) 0
          norm_num at hx
          exact hx
        _ = paleyOp d (paleyOp d v) 0 := by rw [hpv_fun]
        _ = 1 := paley_sq_pairVector_zero d
    have hid0 := congrArg (fun w : Vq d ↦ (w : PermMod (Fq d)) 0) (hid v)
    rw [hppv0, hpv0] at hid0
    exact one_ne_zero hid0
  · right
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    have hx := hform v x
    norm_num at hx
    simpa using hx
  · exfalso
    let v := pairVector d
    have hpv_fun : (p v : PermMod (Fq d)) =
        (v : PermMod (Fq d)) + paleyOp d v := by
      funext x
      have hx := hform v x
      norm_num at hx
      exact hx
    have hpv0 : (p v : PermMod (Fq d)) 0 = 1 := by
      rw [hpv_fun, Pi.add_apply, pairVector_zero,
        paley_pairVector_zero d hd, add_zero]
    have hApv0 : paleyOp d (p v) 0 = 1 := by
      rw [hpv_fun, paley_map_add, Pi.add_apply,
        paley_pairVector_zero d hd, paley_sq_pairVector_zero d, zero_add]
    have hppv0 : (p (p v) : PermMod (Fq d)) 0 = 0 := by
      rw [hform (p v) 0, hpv0, hApv0]
      exact ZModModule.add_self 1
    have hid0 := congrArg (fun w : Vq d ↦ (w : PermMod (Fq d)) 0) (hid v)
    rw [hppv0, hpv0] at hid0
    exact zero_ne_one hid0

/-- The deleted binary permutation module for `Hq d` is irreducible whenever
`d` is odd. -/
theorem hq_irreducible (d : Nat) (hd : Odd d) :
    Representation.IsIrreducible (hqRepresentation d) := by
  let _ : Finite (Hq d) :=
    Finite.of_injective (fun z : Hq d ↦ (z.left, z.right)) (by
      intro x y h
      apply SemidirectProduct.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)
  let _ : NeZero (Nat.card (Hq d) : F2) := ⟨by
    rw [(hq_odd_card d hd).natCast_zmod_two]
    exact one_ne_zero⟩
  let ρ := hqRepresentation d
  have hbotne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hmod := congrArg Subrepresentation.toSubmodule h
    have hvtop : pairVector d ∈ (⊤ : Subrepresentation ρ).toSubmodule :=
      Submodule.mem_top
    have hvbot : pairVector d ∈ (⊥ : Subrepresentation ρ).toSubmodule :=
      hmod ▸ hvtop
    have hvzero : pairVector d = 0 := by
      change pairVector d ∈ (⊥ : Submodule F2 (Vq d)) at hvbot
      simpa using hvbot
    exact pairVector_ne_zero d hvzero
  let _ : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbotne⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro U hU
  obtain ⟨p, hpEquiv, hpIdem, hpRange⟩ :=
    exists_equivariant_idempotent_projection (H := Hq d) (Ω := Fq d) U
  have hFodd : Odd (Fintype.card (Fq d)) := by
    rw [Fintype.card_eq_nat_card]
    exact fq_odd_card d hd
  let E : PermMod (Fq d) →ₗ[F2] PermMod (Fq d) :=
    extendDeletedEnd hFodd p
  have hE : ∀ (g : Hq d) f, E (g • f) = g • E f := by
    intro g f
    simpa [E] using extendDeletedEnd_smul hFodd p hpEquiv g f
  let K := hqRankThreeOrbitals d hd
  let α := matrixCoeff E K.diag K.diag
  let β := matrixCoeff E K.relX K.relY
  let γ := matrixCoeff E K.otherX K.otherY
  have hcoeff : ∀ x y, matrixCoeff E x y =
      if x = y then α else if SquareDiff d x y then β else γ :=
    matrixCoeff_rankThree (SquareDiff d) K E hE
  have hErank : E = rankThreeOp (SquareDiff d) α β γ :=
    eq_rankThreeOp_of_matrixCoeff E (SquareDiff d) α β γ hcoeff
  have hform (v : Vq d) (x : Fq d) :
      (p v : PermMod (Fq d)) x =
        (α + γ) * (v : PermMod (Fq d)) x +
          (β + γ) * paleyOp d v x := by
    calc
      (p v : PermMod (Fq d)) x = E (v : PermMod (Fq d)) x := by
        have h := congrArg (fun f : PermMod (Fq d) ↦ f x)
          (extendDeletedEnd_incl hFodd p v)
        exact h.symm
      _ = rankThreeOp (SquareDiff d) α β γ v x := by rw [hErank]
      _ = (α + γ) * (v : PermMod (Fq d)) x +
          (β + γ) * relationSum (SquareDiff d) v x := by
        apply rankThreeOp_apply_deleted
        intro z hz
        exact hz.1 rfl
      _ = _ := by rw [relationSum_squareDiff_eq_paley]
  rcases idempotent_rankThree_restriction d hd p hpIdem
      (α + γ) (β + γ) hform with hp0 | hpId
  · exfalso
    apply hU
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = (⊥ : Submodule F2 (Vq d))
    rw [← hpRange, hp0]
    exact LinearMap.range_zero
  · apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = (⊤ : Submodule F2 (Vq d))
    rw [← hpRange, hpId]
    exact LinearMap.range_id

end SaxlCounterexamples.EveryBase
