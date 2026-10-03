/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SeedChild

/-!
# Quartic low--low coordinate separation

This is the finite linear certificate behind the low--low half of quartic
exclusion.  For `x` in the rational-place support `P₁` and `y` in `P₀`,
none of the nine rank-two target forms outside the rational-place space lies
in `x ∧ L + y ∧ L`.  The table below stores one separating linear
functional for each of the `16 × 9` cases.  Lean checks the functionals on
the eight coordinate vectors; arbitrary vectors then follow by linearity.

Thus the certificate is a small algebraic matrix check, not an enumeration
of circuits or Boolean functions.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The 28 upper-triangular coordinate pairs of an alternating `8 × 8`
matrix. -/
@[expose]
def upperPair : Fin 28 → Fin 8 × Fin 8 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),
    (1,2),(1,3),(1,4),(1,5),(1,6),(1,7),
    (2,3),(2,4),(2,5),(2,6),(2,7),
    (3,4),(3,5),(3,6),(3,7),
    (4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

/-- Packed separating covectors.  The flat index order is
`(P₁-A coefficient, P₁-B coefficient, P₀-A coefficient,
P₀-B coefficient, outside-word index)`. -/
@[expose]
def quarticLowLowSeparatorTable (i : Fin 144) : Nat :=
  #[0x0000010,0x0000008,0x0000010,0x0000008,0x0020000,0x0020000,
    0x0000010,0x0000008,0x0000008,
    0x0000010,0x0000010,0x0000010,0x0000020,0x0020000,0x0020000,
    0x0000010,0x0000010,0x0000020,
    0x0000200,0x0000200,0x0000200,0x0000400,0x0020000,0x0020000,
    0x0000200,0x0000200,0x0000400,
    0x0000201,0x0000201,0x0000201,0x0000400,0x0020000,0x0020000,
    0x0000201,0x0000201,0x0000400,
    0x0000018,0x0000028,0x0000018,0x0000018,0x0024000,0x0024000,
    0x0000018,0x0000028,0x0000018,
    0x0000030,0x0000030,0x0000030,0x0000030,0x0028000,0x0028000,
    0x0000050,0x0000030,0x0000030,
    0x0000600,0x0000600,0x0000600,0x0000600,0x0024000,0x0024000,
    0x0000a00,0x0000600,0x0000600,
    0x0000601,0x0000601,0x0000601,0x0000601,0x0024002,0x0024002,
    0x0000a01,0x0000601,0x0000601,
    0x0000208,0x0000410,0x0000208,0x0000208,0x0020040,0x0020040,
    0x0000208,0x0000410,0x0000208,
    0x0000410,0x0000410,0x0000410,0x0000410,0x0020040,0x0020040,
    0x0000820,0x0000410,0x0000410,
    0x0004200,0x0004200,0x0004200,0x0004200,0x0021000,0x0021000,
    0x0008400,0x0004200,0x0004200,
    0x0004283,0x0004283,0x0004283,0x0004283,0x0021000,0x0021000,
    0x0008400,0x0004283,0x0004283,
    0x0000209,0x0000411,0x0000209,0x0000209,0x0020042,0x0020042,
    0x0000209,0x0000411,0x0000209,
    0x0000411,0x0000411,0x0000411,0x0000411,0x0020042,0x0020042,
    0x0000821,0x0000411,0x0000411,
    0x0004280,0x0004280,0x0004280,0x0004280,0x0021080,0x0021080,
    0x0008480,0x0004280,0x0004280,
    0x0004203,0x0004203,0x0004203,0x0004203,0x0021080,0x0021080,
    0x0008480,0x0004203,0x0004203][i.val]'i.isLt

/-- Encode a field element as the natural number zero or one. -/
@[expose]
def f2IndexBit (a : F₂) : Nat := if a = 0 then 0 else 1

/-- Pack four Boolean parameters and an outside-target index into a table row. -/
@[expose]
def quarticSeparatorIndex (a b c d : F₂) (i : Fin 9) : Fin 144 :=
  let n := ((((f2IndexBit a * 2 + f2IndexBit b) * 2 + f2IndexBit c) * 2 +
    f2IndexBit d) * 9 + i.val)
  ⟨n % 144, Nat.mod_lt _ (by decide)⟩

/-- Extract one coefficient of the packed quartic separating covector. -/
@[expose]
def quarticSeparatorBit (a b c d : F₂) (i : Fin 9) (k : Fin 28) : F₂ :=
  if Nat.testBit
      (quarticLowLowSeparatorTable (quarticSeparatorIndex a b c d i)) k.val
    then 1 else 0

/-- Extract one coordinate from a two-form coordinate array. -/
@[expose]
def twoFormCoordinate (i j : Fin 8) : TwoForm →ₗ[F₂] F₂ where
  toFun := fun q => q i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear functional encoded by a quartic separating table row. -/
@[expose]
def quarticSeparatorLinear (a b c d : F₂) (i : Fin 9) : TwoForm →ₗ[F₂] F₂ :=
  ∑ k : Fin 28, quarticSeparatorBit a b c d i k •
    twoFormCoordinate (upperPair k).1 (upperPair k).2

/-- Evaluate a quartic separating covector on a two-form. -/
@[expose]
def quarticSeparatorEval (a b c d : F₂) (i : Fin 9) (q : TwoForm) : F₂ :=
  quarticSeparatorLinear a b c d i q

/-- A vector in the two-dimensional input support at the place one. -/
@[expose] def quarticPoneVector (a b : F₂) : LinearForm :=
  a • placeA 1 + b • placeB 1

/-- A vector in the two-dimensional input support at the place zero. -/
@[expose] def quarticPzeroVector (c d : F₂) : LinearForm :=
  c • placeA 0 + d • placeB 0

theorem quarticSeparator_target_check :
    ∀ (a b c d : F₂) (i : Fin 9),
      quarticSeparatorLinear a b c d i (targetTwo (outsideRankTwoWord i)) = 1 := by
  decide +kernel

theorem quarticSeparator_pone_basis_check :
    ∀ (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticSeparatorLinear a b c d i
        (vectorWedge (quarticPoneVector a b) (coordinateLinear j)) = 0 := by
  intro a b c d
  rcases f2_eq_zero_or_one a with rfl | rfl <;>
    rcases f2_eq_zero_or_one b with rfl | rfl <;>
      rcases f2_eq_zero_or_one c with rfl | rfl <;>
        rcases f2_eq_zero_or_one d with rfl | rfl <;>
          decide +kernel

theorem quarticSeparator_pzero_basis_check :
    ∀ (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticSeparatorLinear a b c d i
        (vectorWedge (quarticPzeroVector c d) (coordinateLinear j)) = 0 := by
  intro a b c d
  rcases f2_eq_zero_or_one a with rfl | rfl <;>
    rcases f2_eq_zero_or_one b with rfl | rfl <;>
      rcases f2_eq_zero_or_one c with rfl | rfl <;>
        rcases f2_eq_zero_or_one d with rfl | rfl <;>
          decide +kernel

theorem quarticSeparator_pone (a b c d : F₂) (i : Fin 9)
    (z : LinearForm) :
    quarticSeparatorLinear a b c d i
      (vectorWedge (quarticPoneVector a b) z) = 0 := by
  change quarticSeparatorLinear a b c d i
    (vectorWedgeBilinear (quarticPoneVector a b) z) = 0
  rw [linear_eq_sum_coordinate z]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j _
  change z j • quarticSeparatorLinear a b c d i
    (vectorWedge (quarticPoneVector a b) (coordinateLinear j)) = 0
  rw [quarticSeparator_pone_basis_check]
  simp

theorem quarticSeparator_pzero (a b c d : F₂) (i : Fin 9)
    (z : LinearForm) :
    quarticSeparatorLinear a b c d i
      (vectorWedge (quarticPzeroVector c d) z) = 0 := by
  change quarticSeparatorLinear a b c d i
    (vectorWedgeBilinear (quarticPzeroVector c d) z) = 0
  rw [linear_eq_sum_coordinate z]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j _
  change z j • quarticSeparatorLinear a b c d i
    (vectorWedge (quarticPzeroVector c d) (coordinateLinear j)) = 0
  rw [quarticSeparator_pzero_basis_check]
  simp

/-- The certified low--low separation statement in coordinate form. -/
theorem outsideRankTwo_not_pone_pzero_wedges
    (a b c d : F₂) (i : Fin 9) (z w : LinearForm) :
    targetTwo (outsideRankTwoWord i) ≠
      vectorWedge (quarticPoneVector a b) z +
        vectorWedge (quarticPzeroVector c d) w := by
  intro h
  have he := congrArg (quarticSeparatorLinear a b c d i) h
  rw [quarticSeparator_target_check] at he
  rw [map_add, quarticSeparator_pone, quarticSeparator_pzero] at he
  exact one_ne_zero he

theorem rationalCoeffRep_add (u v : Fin 3 → F₂) :
    rationalCoeffRep (u + v) = rationalCoeffRep u + rationalCoeffRep v := by
  funext i
  fin_cases i <;>
    simp [rationalCoeffRep, rZeroCoeff, rOneCoeff, rInfinityCoeff] <;>
    ring

/-- In the first quartic orbit, adding a form from `P₁ ∧ L + P₀ ∧ L`
to a rational target form cannot expose a new target direction.  The other
two manuscript orbits are special cases obtained by setting the `P₁` or
both support vectors to zero. -/
theorem target_eq_rational_add_pone_pzero_is_rational
    (t : TargetCoeff) (gamma : Fin 3 → F₂)
    (a b c d : F₂) (z w : LinearForm)
    (h : targetTwo t = rationalTwo gamma +
      vectorWedge (quarticPoneVector a b) z +
        vectorWedge (quarticPzeroVector c d) w) :
    IsRationalCoeff t := by
  let delta : TargetCoeff := t + rationalCoeffRep gamma
  have hdelta : targetTwo delta =
      vectorWedge (quarticPoneVector a b) z +
        vectorWedge (quarticPzeroVector c d) w := by
    rw [show targetTwo delta = targetTwo t + targetTwo (rationalCoeffRep gamma) by
      exact targetTwoLinear.map_add _ _]
    rw [targetTwo_rationalCoeffRep, h]
    funext i j
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  have hdeltaRank : HankelRankLETwo delta := by
    exact target_sum_two_decomposable_rankTwo hdelta
  have hdeltaRat : IsRationalCoeff delta := by
    by_contra hnot
    have hne : delta ≠ 0 := by
      intro hz
      apply hnot
      rw [hz]
      exact ⟨0, 0, 0, by simp⟩
    rcases (outside_rankTwo_classification delta).mp
        ⟨hdeltaRank, hne, hnot⟩ with ⟨i, hi⟩
    have hdelta' := hdelta
    rw [hi] at hdelta'
    exact outsideRankTwo_not_pone_pzero_wedges a b c d i z w hdelta'
  rcases (IsRationalCoeff_iff delta).mp hdeltaRat with ⟨eta, heta⟩
  apply (IsRationalCoeff_iff t).mpr
  refine ⟨eta + gamma, ?_⟩
  rw [rationalCoeffRep_add, ← heta]
  dsimp [delta]
  funext i
  simp only [Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- The direct-sum cubic comparison for the representative quartic plane
`span(r₀,r₁)`: cancellation forces the two linear differences into the
opposite rational-place support planes. -/
theorem quartic_cubic_kernel_zero_one (x y : LinearForm)
    (h : vectorWedgeTwo x (rationalPlaceTwo 1) +
      vectorWedgeTwo y (rationalPlaceTwo 0) = 0) :
    ∃ a b c d : F₂,
      x = quarticPoneVector a b ∧ y = quarticPzeroVector c d := by
  have hA (i : Fin 4) : x (aCoord i) = x (aCoord 0) := by
    fin_cases i
    · rfl
    · have hc := congrFun (congrFun (congrFun h
          (aCoord 0)) (aCoord 1)) (bCoord 1)
      simp only [rationalPlaceTwo, placeA, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, placeB, aCoord, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        Fin.zero_eta, Nat.one_mod, Fin.mk_one, bCoord, Nat.reduceAdd, Fin.reduceFinMk,
        Pi.add_apply, vectorWedgeTwo, vectorWedge, Matrix.cons_val, mul_one, mul_zero,
        add_zero, Pi.zero_apply] at hc
      change x 1 = x 0
      rw [add_comm, ← CharTwo.sub_eq_add] at hc
      exact sub_eq_zero.mp hc
    · have hc := congrFun (congrFun (congrFun h
          (aCoord 0)) (aCoord 2)) (bCoord 1)
      simp only [rationalPlaceTwo, placeA, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, placeB, aCoord, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        Fin.zero_eta, Nat.reduceMod, Fin.reduceFinMk, bCoord, Nat.one_mod, Nat.reduceAdd,
        Pi.add_apply, vectorWedgeTwo, vectorWedge, Matrix.cons_val, mul_one, mul_zero,
        add_zero, Pi.zero_apply] at hc
      change x 2 = x 0
      rw [add_comm, ← CharTwo.sub_eq_add] at hc
      exact sub_eq_zero.mp hc
    · have hc := congrFun (congrFun (congrFun h
          (aCoord 0)) (aCoord 3)) (bCoord 1)
      simp only [rationalPlaceTwo, placeA, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, placeB, aCoord, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        Fin.zero_eta, Nat.mod_succ, Fin.reduceFinMk, bCoord, Nat.one_mod, Nat.reduceAdd,
        Pi.add_apply, vectorWedgeTwo, vectorWedge, Matrix.cons_val, mul_one, mul_zero,
        add_zero, Pi.zero_apply] at hc
      change x 3 = x 0
      rw [add_comm, ← CharTwo.sub_eq_add] at hc
      exact sub_eq_zero.mp hc
  have hB (i : Fin 4) : x (bCoord i) = x (bCoord 0) := by
    fin_cases i
    · rfl
    · have hc := congrFun (congrFun (congrFun h
          (aCoord 1)) (bCoord 0)) (bCoord 1)
      simp only [rationalPlaceTwo, placeA, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, placeB, aCoord, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.mk_one,
        bCoord, Nat.zero_mod, add_zero, Fin.reduceFinMk, Nat.reduceAdd, Pi.add_apply,
        vectorWedgeTwo, vectorWedge, Matrix.cons_val, mul_one, mul_zero, zero_add,
        Pi.zero_apply] at hc
      change x 5 = x 4
      rw [add_comm, ← CharTwo.sub_eq_add] at hc
      exact sub_eq_zero.mp hc
    · have hc := congrFun (congrFun (congrFun h
          (aCoord 1)) (bCoord 0)) (bCoord 2)
      simp only [rationalPlaceTwo, placeA, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, placeB, aCoord, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.mk_one,
        bCoord, Nat.zero_mod, add_zero, Fin.reduceFinMk, Nat.reduceMod, Nat.reduceAdd,
        Pi.add_apply, vectorWedgeTwo, vectorWedge, Matrix.cons_val, mul_one, mul_zero,
        zero_add, Pi.zero_apply] at hc
      change x 6 = x 4
      rw [add_comm, ← CharTwo.sub_eq_add] at hc
      exact sub_eq_zero.mp hc
    · have hc := congrFun (congrFun (congrFun h
          (aCoord 1)) (bCoord 0)) (bCoord 3)
      simp only [rationalPlaceTwo, placeA, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, placeB, aCoord, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.mk_one,
        bCoord, Nat.zero_mod, add_zero, Fin.reduceFinMk, Nat.mod_succ, Nat.reduceAdd,
        Pi.add_apply, vectorWedgeTwo, vectorWedge, Matrix.cons_val, mul_one, mul_zero,
        zero_add, Pi.zero_apply] at hc
      change x 7 = x 4
      rw [add_comm, ← CharTwo.sub_eq_add] at hc
      exact sub_eq_zero.mp hc
  let a : F₂ := x (aCoord 0)
  let b : F₂ := x (bCoord 0)
  have hx : x = quarticPoneVector a b := by
    funext i
    fin_cases i
    · simp [quarticPoneVector, a, b, placeA, placeB, aCoord, bCoord]
    · simpa [quarticPoneVector, a, b, placeA, placeB, aCoord, bCoord]
        using hA 1
    · simpa [quarticPoneVector, a, b, placeA, placeB, aCoord, bCoord]
        using hA 2
    · simpa [quarticPoneVector, a, b, placeA, placeB, aCoord, bCoord]
        using hA 3
    · simp [quarticPoneVector, a, b, placeA, placeB, aCoord, bCoord]
    · simpa [quarticPoneVector, a, b, placeA, placeB, aCoord, bCoord]
        using hB 1
    · simpa [quarticPoneVector, a, b, placeA, placeB, aCoord, bCoord]
        using hB 2
    · simpa [quarticPoneVector, a, b, placeA, placeB, aCoord, bCoord]
        using hB 3
  have hxw : vectorWedgeTwo x (rationalPlaceTwo 1) = 0 := by
    rw [hx]
    simp only [quarticPoneVector, rationalPlaceTwo, vectorWedgeTwo_add_left,
      vectorWedgeTwo_smul_left, vectorWedgeTwo_repeated_left, vectorWedgeTwo_repeated_right,
      smul_zero, add_zero]
  have hyw : vectorWedgeTwo y (rationalPlaceTwo 0) = 0 := by
    rw [hxw, zero_add] at h
    exact h
  have hyw' : vectorWedgeTwo y (vectorWedge (placeA 0) (placeB 0)) = 0 := by
    simpa [rationalPlaceTwo] using hyw
  rcases mem_support_of_vectorWedgeTwo_zero y (placeA 0) (placeB 0)
      (by simpa [rationalPlaceTwo] using rationalPlaceTwo_ne_zero 0)
      hyw' with ⟨c, d, hy⟩
  exact ⟨a, b, c, d, hx, by simpa [quarticPzeroVector] using hy⟩

/-- Select evaluation at zero among the three rational-place coordinates. -/
@[expose] def zeroPlaceCoeff3 : Fin 3 → F₂ := ![1, 0, 0]
/-- Select evaluation at one among the three rational-place coordinates. -/
@[expose] def onePlaceCoeff3 : Fin 3 → F₂ := ![0, 1, 0]

@[simp] theorem rationalTwo_zeroPlaceCoeff3 :
    rationalTwo zeroPlaceCoeff3 = rationalPlaceTwo 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroPlaceCoeff3, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
      Fin.sum_univ_succ]

@[simp] theorem rationalTwo_onePlaceCoeff3 :
    rationalTwo onePlaceCoeff3 = rationalPlaceTwo 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [onePlaceCoeff3, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
      Fin.sum_univ_succ]

theorem exists_rationalTwo_of_mem {q : TwoForm}
    (hq : q ∈ rationalPlaceTwoSpace) :
    ∃ gamma : Fin 3 → F₂, q = rationalTwo gamma := by
  rw [rationalPlaceTwoSpace] at hq
  rcases (Submodule.mem_span_range_iff_exists_fun
      (R := F₂)
      (v := fun theta : Fin 3 => targetTwo (rationalPlaceCoeff theta))
      (x := q)).mp hq with ⟨gamma, hgamma⟩
  refine ⟨gamma, ?_⟩
  rw [← hgamma, rationalTwo]
  apply Finset.sum_congr rfl
  intro theta _
  rw [targetTwo_rationalPlaceCoeff]

/-- Low--low quartic collision for the representative plane
`span(r₀,r₁)`.  Equal cubic highs force the linear differences into
`P₁` and `P₀`; the certified separation lemma then sends every target
quadratic difference back to the rational-place span. -/
theorem aligned_zero_one_lowLow_target_is_rational
    (a₀ b₀ a₁ b₁ : F₂)
    (ell₀ m₀ ell₁ m₁ : LinearForm)
    (t : TargetCoeff)
    (hcubic :
      rationalProductCubic ell₀ m₀ zeroPlaceCoeff3 onePlaceCoeff3 =
        rationalProductCubic ell₁ m₁ zeroPlaceCoeff3 onePlaceCoeff3)
    (hquadratic : targetTwo t =
      rationalProductQuadratic a₀ b₀ ell₀ m₀
          zeroPlaceCoeff3 onePlaceCoeff3 +
        rationalProductQuadratic a₁ b₁ ell₁ m₁
          zeroPlaceCoeff3 onePlaceCoeff3) :
    IsRationalCoeff t := by
  let x : LinearForm := ell₀ + ell₁
  let y : LinearForm := m₀ + m₁
  have hkernel : vectorWedgeTwo x (rationalPlaceTwo 1) +
      vectorWedgeTwo y (rationalPlaceTwo 0) = 0 := by
    change vectorWedgeTwo (ell₀ + ell₁) (rationalPlaceTwo 1) +
      vectorWedgeTwo (m₀ + m₁) (rationalPlaceTwo 0) = 0
    rw [vectorWedgeTwo_add_left, vectorWedgeTwo_add_left]
    have hsum :
        rationalProductCubic ell₀ m₀ zeroPlaceCoeff3 onePlaceCoeff3 +
          rationalProductCubic ell₁ m₁ zeroPlaceCoeff3 onePlaceCoeff3 = 0 := by
      rw [hcubic]
      funext i j k
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    calc
      (vectorWedgeTwo ell₀ (rationalPlaceTwo 1) +
          vectorWedgeTwo ell₁ (rationalPlaceTwo 1)) +
          (vectorWedgeTwo m₀ (rationalPlaceTwo 0) +
            vectorWedgeTwo m₁ (rationalPlaceTwo 0)) =
        (vectorWedgeTwo ell₀ (rationalPlaceTwo 1) +
          vectorWedgeTwo m₀ (rationalPlaceTwo 0)) +
          (vectorWedgeTwo ell₁ (rationalPlaceTwo 1) +
            vectorWedgeTwo m₁ (rationalPlaceTwo 0)) := by ac_rfl
      _ = 0 := by simpa [rationalProductCubic] using hsum
  rcases quartic_cubic_kernel_zero_one x y hkernel with
    ⟨ax, bx, ay, dy, hx, hy⟩
  have hxw : vectorWedgeTwo x (rationalPlaceTwo 1) = 0 := by
    rw [hx]
    simp only [quarticPoneVector, rationalPlaceTwo, vectorWedgeTwo_add_left,
      vectorWedgeTwo_smul_left, vectorWedgeTwo_repeated_left, vectorWedgeTwo_repeated_right,
      smul_zero, add_zero]
  have hyw : vectorWedgeTwo y (rationalPlaceTwo 0) = 0 := by
    rw [hy]
    simp only [quarticPzeroVector, rationalPlaceTwo, vectorWedgeTwo_add_left,
      vectorWedgeTwo_smul_left, vectorWedgeTwo_repeated_left, vectorWedgeTwo_repeated_right,
      smul_zero, add_zero]
  let rho : TwoForm :=
    a₀ • rationalPlaceTwo 1 + b₀ • rationalPlaceTwo 0 +
    a₁ • rationalPlaceTwo 1 + b₁ • rationalPlaceTwo 0 +
    booleanContraction x (rationalPlaceTwo 1) +
    booleanContraction y (rationalPlaceTwo 0)
  have hrho : rho ∈ rationalPlaceTwoSpace := by
    dsimp only [rho]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.add_mem _
            (Submodule.add_mem _
              (Submodule.smul_mem _ _ (rationalPlaceTwo_mem 1))
              (Submodule.smul_mem _ _ (rationalPlaceTwo_mem 0)))
            (Submodule.smul_mem _ _ (rationalPlaceTwo_mem 1)))
        (Submodule.smul_mem _ _ (rationalPlaceTwo_mem 0)))
        (by
          simpa using rational_contraction_mem_of_cubic_zero onePlaceCoeff3 x
            (by simpa using hxw)))
      (by
        simpa using rational_contraction_mem_of_cubic_zero zeroPlaceCoeff3 y
          (by simpa using hyw))
  rcases exists_rationalTwo_of_mem hrho with ⟨gamma, hgamma⟩
  apply target_eq_rational_add_pone_pzero_is_rational
    t gamma ax bx ay dy m₀ ell₁
  rw [← hgamma, hquadratic]
  rw [← hx, ← hy]
  funext i j
  simp only [rho, x, y, rationalProductQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    booleanContraction, vectorWedge, twoHadamard]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]
  ring

end

end N4
end UnrestrictedBooleanMul
