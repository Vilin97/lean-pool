/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.SourceStableSpecialization
import Mathlib.Tactic

/-! # Source Stable Slice -/

namespace BeyondBethe

/-!
# The stable bivariate slice of a coefficient table

We now justify the bivariate polynomial used at one induction step.  All tail
variables are placed on the real boundary, with the right variables sign
reversed.  The finite closure theorem says that the resulting polynomial in
the next left--right pair is stable or zero.
-/

def pairVariablesSignedRealPoint :
    ∀ n : ℕ, (Fin n → ℝ) → (Fin n → ℝ) → PairVariables n → ℝ
  | 0, _, _, i => PEmpty.elim i
  | n + 1, y, z, none => y 0
  | n + 1, y, z, some none => -z 0
  | n + 1, y, z, some (some i) =>
      pairVariablesSignedRealPoint n (fun j ↦ y j.succ) (fun j ↦ z j.succ) i

theorem pairTableStablePolynomial_eval_signed :
    ∀ (n : ℕ) (c : PairTable n) (y z : Fin n → ℝ),
      (pairTableStablePolynomial n c).eval
          (fun i ↦ (pairVariablesSignedRealPoint n y z i : ℂ)) =
        (pairTableEval n c y z : ℂ) := by
  intro n
  induction n with
  | zero =>
      intro c y z
      simp [pairTableStablePolynomial, pairTableEval]
  | succ n ih =>
      intro c y z
      let yt : Fin n → ℝ := fun i ↦ y i.succ
      let zt : Fin n → ℝ := fun i ↦ z i.succ
      let w : Option (Option (PairVariables n)) → ℂ
        | none => (y 0 : ℂ)
        | some none => -(z 0 : ℂ)
        | some (some i) => (pairVariablesSignedRealPoint n yt zt i : ℂ)
      simp only [pairTableStablePolynomial, pairTableEval]
      change PairVariables (n + 1) → ℂ at w
      have hpoint :
          (fun i ↦ (pairVariablesSignedRealPoint (n + 1) y z i : ℂ)) = w := by
        funext i
        change Option (Option (PairVariables n)) at i
        cases i with
        | none => rfl
        | some i =>
            cases i with
            | none => simp [w, pairVariablesSignedRealPoint]
            | some i => rfl
      rw [hpoint]
      change Option (Option (PairVariables n)) → ℂ at w
      change
        (linearExtension
          (linearExtension (pairTableStablePolynomial n (pairTableSection c false false))
            (-pairTableStablePolynomial n (pairTableSection c false true)))
          (linearExtension (pairTableStablePolynomial n (pairTableSection c true false))
            (-pairTableStablePolynomial n (pairTableSection c true true)))).eval
          w = _
      rw [linearExtension_eval, linearExtension_eval, linearExtension_eval]
      have hcomp :
          (w ∘ some) ∘ some =
            fun i ↦ (pairVariablesSignedRealPoint n yt zt i : ℂ) := by
        funext i
        rfl
      have hnone : w none = y 0 := rfl
      have hsomeNone : (w ∘ some) none = -(z 0 : ℂ) := by rfl
      rw [hcomp, hnone, hsomeNone]
      simp only [MvPolynomial.eval_neg]
      rw [
        ih (pairTableSection c false false) yt zt,
        ih (pairTableSection c false true) yt zt,
        ih (pairTableSection c true false) yt zt,
        ih (pairTableSection c true true) yt zt]
      push_cast
      ring

/-- Separate the tail variables from the next left--right pair.  `false` is
the new left variable and `true` the new (sign-reversed) right variable. -/
def pairHeadTailEquiv (n : ℕ) :
    PairVariables (n + 1) ≃ PairVariables n ⊕ Bool where
  toFun
    | none => Sum.inr false
    | some none => Sum.inr true
    | some (some i) => Sum.inl i
  invFun
    | Sum.inr false => none
    | Sum.inr true => some none
    | Sum.inl i => some (some i)
  left_inv x := by
    change Option (Option (PairVariables n)) at x
    cases x with
    | none => rfl
    | some x => cases x <;> rfl
  right_inv x := by
    cases x with
    | inl x => rfl
    | inr x => cases x <;> rfl

noncomputable def pairTableHeadPolynomial
    {n : ℕ} (c : PairTable (n + 1)) :
    MvPolynomial (PairVariables n ⊕ Bool) ℂ :=
  MvPolynomial.rename (pairHeadTailEquiv n) (pairTableStablePolynomial (n + 1) c)

theorem pairTableHeadPolynomial_multiaffine
    {n : ℕ} (c : PairTable (n + 1)) :
    IsComplexMultiaffine (pairTableHeadPolynomial c) := by
  intro i
  change MvPolynomial.degreeOf i
      (MvPolynomial.rename (pairHeadTailEquiv n)
        (pairTableStablePolynomial (n + 1) c)) ≤ 1
  have hdegree := MvPolynomial.degreeOf_rename_of_injective
    (pairHeadTailEquiv n).injective ((pairHeadTailEquiv n).symm i)
      (p := pairTableStablePolynomial (n + 1) c)
  convert hdegree.trans_le
    (pairTableStablePolynomial_multiaffine c ((pairHeadTailEquiv n).symm i)) using 1
  simp

theorem pairTableHeadPolynomial_stable
    {n : ℕ} {c : PairTable (n + 1)}
    (hstable : IsUpperHalfPlaneStable (pairTableStablePolynomial (n + 1) c)) :
    IsUpperHalfPlaneStable (pairTableHeadPolynomial c) := by
  exact hstable.rename (pairHeadTailEquiv n)

noncomputable def pairTableBivariateSlice
    {n : ℕ} (c : PairTable (n + 1))
    (y z : Fin n → ℝ) : MvPolynomial Bool ℂ :=
  partialSpecialization (pairTableHeadPolynomial c)
    (pairVariablesSignedRealPoint n y z)

theorem pairTableBivariateSlice_eval
    {n : ℕ} (c : PairTable (n + 1)) (y z : Fin n → ℝ)
    (Y Z : ℂ) :
    (pairTableBivariateSlice c y z).eval (fun b ↦ bif b then Z else Y) =
      -(pairTableEval n (pairTableSection c true true) y z : ℂ) * Y * Z +
        (pairTableEval n (pairTableSection c true false) y z : ℂ) * Y -
        (pairTableEval n (pairTableSection c false true) y z : ℂ) * Z +
        (pairTableEval n (pairTableSection c false false) y z : ℂ) := by
  rw [pairTableBivariateSlice, partialSpecialization_eval,
    pairTableHeadPolynomial, MvPolynomial.eval_rename]
  let w : PairVariables (n + 1) → ℂ :=
    fun i ↦ Sum.elim
      (fun j ↦ (pairVariablesSignedRealPoint n y z j : ℂ))
      (fun b ↦ bif b then Z else Y) (pairHeadTailEquiv n i)
  change Option (Option (PairVariables n)) → ℂ at w
  change (pairTableStablePolynomial (n + 1) c).eval w = _
  simp only [pairTableStablePolynomial]
  change
    (linearExtension
      (linearExtension (pairTableStablePolynomial n (pairTableSection c false false))
        (-pairTableStablePolynomial n (pairTableSection c false true)))
      (linearExtension (pairTableStablePolynomial n (pairTableSection c true false))
        (-pairTableStablePolynomial n (pairTableSection c true true)))).eval w = _
  rw [linearExtension_eval, linearExtension_eval, linearExtension_eval]
  have htail : (w ∘ some) ∘ some =
      fun i ↦ (pairVariablesSignedRealPoint n y z i : ℂ) := by
    funext i
    rfl
  have hy : w none = Y := by rfl
  have hz : (w ∘ some) none = Z := by rfl
  rw [htail, hy, hz]
  simp only [MvPolynomial.eval_neg]
  rw [
    pairTableStablePolynomial_eval_signed,
    pairTableStablePolynomial_eval_signed,
    pairTableStablePolynomial_eval_signed,
    pairTableStablePolynomial_eval_signed]
  ring

theorem pairTableBivariateSlice_stableOrZero
    {n : ℕ} {c : PairTable (n + 1)}
    (y z : Fin n → ℝ)
    (hstable : IsUpperHalfPlaneStable (pairTableStablePolynomial (n + 1) c)) :
    pairTableBivariateSlice c y z = 0 ∨
      IsUpperHalfPlaneStable (pairTableBivariateSlice c y z) := by
  exact pairVariables_partialSpecialization_stableOrZero n
    (pairTableHeadPolynomial c) (pairVariablesSignedRealPoint n y z)
    (pairTableHeadPolynomial_multiaffine c)
    (pairTableHeadPolynomial_stable hstable)

/-- The coefficient determinant inequality for every real tail specialization.
This is the exact local consequence of stability consumed by the scalar
capacity lemma. -/
theorem pairTable_slice_rayleigh
    {n : ℕ} {c : PairTable (n + 1)}
    (hc : PairTableNonnegative c)
    (hstable : IsUpperHalfPlaneStable (pairTableStablePolynomial (n + 1) c))
    (y z : Fin n → ℝ) (hy : ∀ i, 0 < y i) (hz : ∀ i, 0 < z i) :
    pairTableEval n (pairTableSection c true false) y z *
        pairTableEval n (pairTableSection c false true) y z ≤
      pairTableEval n (pairTableSection c true true) y z *
        pairTableEval n (pairTableSection c false false) y z := by
  let a := pairTableEval n (pairTableSection c true true) y z
  let b := pairTableEval n (pairTableSection c true false) y z
  let cc := pairTableEval n (pairTableSection c false true) y z
  let d := pairTableEval n (pairTableSection c false false) y z
  have hy' : ∀ i, 0 ≤ y i := fun i ↦ (hy i).le
  have hz' : ∀ i, 0 ≤ z i := fun i ↦ (hz i).le
  have ha : 0 ≤ a := pairTableEval_nonnegative
    (pairTableSection_nonnegative hc true true) hy' hz'
  have hb : 0 ≤ b := pairTableEval_nonnegative
    (pairTableSection_nonnegative hc true false) hy' hz'
  have hcc : 0 ≤ cc := pairTableEval_nonnegative
    (pairTableSection_nonnegative hc false true) hy' hz'
  have hd : 0 ≤ d := pairTableEval_nonnegative
    (pairTableSection_nonnegative hc false false) hy' hz'
  rcases pairTableBivariateSlice_stableOrZero y z hstable with hzero | hs
  · have heval :
        (pairTableBivariateSlice c y z).eval
            (fun q ↦ bif q then (0 : ℂ) else 1) =
          (0 : MvPolynomial Bool ℂ).eval
            (fun q ↦ bif q then (0 : ℂ) else 1) := by
      exact congrArg
        (fun p : MvPolynomial Bool ℂ ↦
          p.eval (fun q ↦ bif q then (0 : ℂ) else 1)) hzero
    rw [pairTableBivariateSlice_eval] at heval
    have hbzero : b = 0 := by
      have hsum : (b : ℂ) + (d : ℂ) = 0 := by
        simpa [a, b, cc, d] using heval
      have hre := congrArg Complex.re hsum
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith
    change b * cc ≤ a * d
    rw [hbzero, zero_mul]
    exact mul_nonneg ha hd
  · have hbistable : BivariateBistable a b cc d := by
      intro Y Z hY hZ
      have hne := hs (fun q ↦ bif q then Z else Y) (by
        intro q
        cases q with
        | false => simpa using hY
        | true => simpa using hZ)
      rw [pairTableBivariateSlice_eval] at hne
      simpa only [a, b, cc, d] using hne
    exact bivariate_rayleigh_of_bistable ha hb hcc hd hbistable

end BeyondBethe
