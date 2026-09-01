/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions

/-!
# Division in weighted `ℓ¹` sequence algebras

This file constructs bounded shifts, convolution division by a small tail,
and the specialized one-variable quotient and remainder operators used in
complex-analytic Weierstrass preparation.
-/

open Finset
open scoped ENNReal NNReal Topology
noncomputable section

namespace ClassicalComplexWPT

section ProductAntidiagonal

variable {A B : Type*}

/-- Reassociate a product of two pairs into a pair of products. -/
def prodAntidiagonalEquiv : ((A × A) × (B × B)) ≃ ((A × B) × (A × B)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by rintro ⟨⟨a₁,a₂⟩,⟨b₁,b₂⟩⟩; rfl
  right_inv := by rintro ⟨⟨a₁,b₁⟩,⟨a₂,b₂⟩⟩; rfl

noncomputable instance prodHasAntidiagonal [AddCommMonoid A] [AddCommMonoid B]
    [Finset.HasAntidiagonal A] [Finset.HasAntidiagonal B] :
    Finset.HasAntidiagonal (A × B) where
  antidiagonal n := (Finset.antidiagonal n.1 ×ˢ Finset.antidiagonal n.2).map
    (prodAntidiagonalEquiv (A := A) (B := B)).toEmbedding
  mem_antidiagonal := by
    classical
    rintro ⟨a,b⟩ ⟨⟨a₁,b₁⟩,⟨a₂,b₂⟩⟩
    simp [prodAntidiagonalEquiv, Prod.ext_iff]

end ProductAntidiagonal

namespace L1Coeff

variable {I J : Type*}

/-- Extend an `ℓ¹` coefficient function by zero along an embedding. -/
noncomputable def embedFun (e : I ↪ J) (f : L1Coeff I) (j : J) : ℂ := by
  classical
  exact if h : ∃ i, e i = j then f h.choose else 0

@[simp] lemma embedFun_apply_self (e : I ↪ J) (f : L1Coeff I) (i : I) :
    embedFun e f (e i) = f i := by
  classical
  let h : ∃ k, e k = e i := ⟨i, rfl⟩
  rw [embedFun, dite_eq_left h]
  have hk : e h.choose = e i := h.choose_spec
  rw [e.injective hk]

lemma embedFun_apply_of_not_mem (e : I ↪ J) (f : L1Coeff I) (j : J)
    (hj : j ∉ Set.range e) : embedFun e f j = 0 := by
  classical
  rw [embedFun, dite_eq_right]
  simpa only [Set.mem_range] using hj

/-- Embed an `ℓ¹` coefficient family by extending it by zero. -/
def embed (e : I ↪ J) (f : L1Coeff I) : L1Coeff J :=
  ⟨embedFun e f, by
    classical
    apply memℓp_gen
    apply (Function.Injective.summable_iff e.injective (fun j hj ↦ ?_)).mp
    · simpa [Function.comp_def] using L1Coeff.summable_norm f
    · simp [embedFun_apply_of_not_mem e f j hj]⟩

@[simp] lemma embed_apply_self (e : I ↪ J) (f : L1Coeff I) (i : I) :
    embed e f (e i) = f i := embedFun_apply_self e f i

lemma embed_apply_of_not_mem (e : I ↪ J) (f : L1Coeff I) (j : J)
    (hj : j ∉ Set.range e) : embed e f j = 0 := embedFun_apply_of_not_mem e f j hj

end L1Coeff

section WShift

variable {A : Type*}

/-- The embedding that shifts the distinguished index upward by `d`. -/
def lowIndex (d : ℕ) : A × ℕ ↪ A × ℕ where
  toFun x := (x.1, x.2 + d)
  inj' := by
    rintro ⟨a,n⟩ ⟨b,m⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, Nat.add_right_cancel h.2⟩

/-- Insert `d` zero layers below an `ℓ¹` coefficient family. -/
def lowShift (d : ℕ) (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  L1Coeff.embed (lowIndex (A := A) d) f

@[simp] lemma lowShift_apply_add (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) (n : ℕ) :
    lowShift d f (a, n + d) = f (a,n) := by
  exact L1Coeff.embed_apply_self (lowIndex (A := A) d) f (a,n)

lemma lowShift_apply_of_lt (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : n < d) : lowShift d f (a,n) = 0 := by
  apply L1Coeff.embed_apply_of_not_mem
  rintro ⟨⟨b,m⟩, h⟩
  change (b, m + d) = (a, n) at h
  have h' := congrArg Prod.snd h
  omega

lemma lowShift_apply_of_le (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : d ≤ n) : lowShift d f (a,n) = f (a, n - d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : d + m - d = m := Nat.add_sub_cancel_left d m
  rw [hsub]
  simpa only [Nat.add_comm] using lowShift_apply_add d f a m

@[simp] lemma highShift_lowShift (d : ℕ) (f : L1Coeff (A × ℕ)) :
    highShift d (lowShift d f) = f := by
  apply lp.ext
  funext x
  rcases x with ⟨a,n⟩
  simp

@[simp] lemma highShift_lowCut (d : ℕ) (f : L1Coeff (A × ℕ)) :
    highShift d (lowCut d f) = 0 := by
  apply lp.ext
  funext x
  rcases x with ⟨a,n⟩
  rw [highShift_apply]
  rw [lowCut_apply_of_le d f a (by omega)]
  rfl

theorem lowShift_highShift_add_lowCut (d : ℕ) (f : L1Coeff (A × ℕ)) :
    lowShift d (highShift d f) + lowCut d f = f := by
  apply lp.ext
  funext x
  rcases x with ⟨a,n⟩
  by_cases hn : n < d
  · simp [lowShift_apply_of_lt d _ _ hn, lowCut_apply_of_lt d _ _ hn]
  · change lowShift d (highShift d f) (a,n) + lowCut d f (a,n) = f (a,n)
    rw [lowCut_apply_of_le d f a (Nat.le_of_not_gt hn), add_zero]
    rw [lowShift_apply_of_le d _ a (Nat.le_of_not_gt hn)]
    simp [Nat.sub_add_cancel (Nat.le_of_not_gt hn)]

end WShift

section Division

variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

lemma convolution_comm (f g : L1Coeff A) : convolution f g = convolution g f := by
  apply lp.ext
  funext n
  rw [convolution_apply, convolution_apply]
  refine Finset.sum_bij (fun kl _ ↦ kl.swap) ?_ ?_ ?_ ?_
  · intro kl hkl
    simpa [add_comm] using hkl
  · intro kl₁ h₁ kl₂ h₂ h
    exact Prod.swap_injective h
  · intro kl hkl
    exact ⟨kl.swap, by simpa [add_comm] using hkl, by simp⟩
  · intro kl hkl
    simp [mul_comm]

lemma convolution_add_right (f g₁ g₂ : L1Coeff A) :
    convolution f (g₁ + g₂) = convolution f g₁ + convolution f g₂ := by
  rw [convolution_comm f, convolution_add_left, convolution_comm g₁, convolution_comm g₂]

lemma convolution_smul_right (c : ℂ) (f g : L1Coeff A) :
    convolution f (c • g) = c • convolution f g := by
  rw [convolution_comm f, convolution_smul_left, convolution_comm g]

/-- Right convolution depends continuously and linearly on the coefficient family. -/
def convolutionRightMap :
    L1Coeff A →L[ℂ] (L1Coeff A →L[ℂ] L1Coeff A) :=
  ({
    toFun := convolutionRight
    map_add' := by
      intro p₁ p₂
      apply ContinuousLinearMap.ext
      intro q
      exact convolution_add_right q p₁ p₂
    map_smul' := by
      intro c p
      apply ContinuousLinearMap.ext
      intro q
      exact convolution_smul_right c q p
    } : L1Coeff A →ₗ[ℂ]
      (L1Coeff A →L[ℂ] L1Coeff A)).mkContinuous 1 (by
        intro p
        simpa using norm_convolutionRight_le p)

@[simp] lemma convolutionRightMap_apply (p : L1Coeff A) :
    convolutionRightMap p = convolutionRight p := rfl

/-- The high-shifted convolution perturbation used by division. -/
def divisionPerturbation (d : ℕ) (p : L1Coeff (A × ℕ)) :
    L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) :=
  highShiftCLM d ∘L convolutionRight p

@[simp] lemma divisionPerturbation_apply (d : ℕ) (p q : L1Coeff (A × ℕ)) :
    divisionPerturbation d p q = highShift d (convolution q p) := rfl

theorem norm_divisionPerturbation_le (d : ℕ) (p : L1Coeff (A × ℕ)) :
    ‖divisionPerturbation d p‖ ≤ ‖p‖ := by
  calc
    ‖divisionPerturbation d p‖ ≤ ‖highShiftCLM (A := A) d‖ * ‖convolutionRight p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖p‖ := mul_le_mul (norm_highShiftCLM_le d) (norm_convolutionRight_le p)
      (norm_nonneg _) zero_le_one
    _ = ‖p‖ := one_mul _

/-- The operator-valued linear map `p ↦ S_d C_p`. -/
def divisionPerturbationMap (d : ℕ) :
    L1Coeff (A × ℕ) →L[ℂ] (L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ)) :=
  ({
    toFun := divisionPerturbation d
    map_add' := by
      intro p₁ p₂
      apply ContinuousLinearMap.ext
      intro q
      change highShift d (convolution q (p₁ + p₂)) =
        highShift d (convolution q p₁) + highShift d (convolution q p₂)
      rw [convolution_add_right, highShift_add]
    map_smul' := by
      intro c p
      apply ContinuousLinearMap.ext
      intro q
      change highShift d (convolution q (c • p)) = c • highShift d (convolution q p)
      rw [convolution_smul_right, highShift_smul]
    } : L1Coeff (A × ℕ) →ₗ[ℂ]
      (L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ))).mkContinuous 1 (by
        intro p
        simpa using norm_divisionPerturbation_le (A := A) d p)

@[simp] lemma divisionPerturbationMap_apply (d : ℕ) (p : L1Coeff (A × ℕ)) :
    divisionPerturbationMap d p = divisionPerturbation d p := rfl

private lemma norm_neg_divisionPerturbation_lt_one (d : ℕ) (p : L1Coeff (A × ℕ))
    (hp : ‖p‖ < 1) : ‖-(divisionPerturbation d p)‖ < 1 := by
  rw [norm_neg]
  exact lt_of_le_of_lt (norm_divisionPerturbation_le d p) hp

/-- The inverse of `I + S_d C_p`, constructed by a Neumann series. -/
noncomputable def divisionInverse (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1) :
    L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) :=
  ↑((Units.oneSub (-(divisionPerturbation d p))
    (norm_neg_divisionPerturbation_lt_one d p hp))⁻¹)

theorem divisionInverse_right (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (b : L1Coeff (A × ℕ)) :
    divisionInverse d p hp b +
        highShift d (convolution (divisionInverse d p hp b) p) = b := by
  let T := -(divisionPerturbation d p)
  let hT : ‖T‖ < 1 := norm_neg_divisionPerturbation_lt_one d p hp
  have h := congrArg (fun L : L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) ↦ L b)
    (Units.mul_inv (Units.oneSub T hT))
  simpa [divisionInverse, T, hT, divisionPerturbation_apply, sub_eq_add_neg] using h

theorem divisionInverse_left (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (q : L1Coeff (A × ℕ)) :
    divisionInverse d p hp (q + highShift d (convolution q p)) = q := by
  let T := -(divisionPerturbation d p)
  let hT : ‖T‖ < 1 := norm_neg_divisionPerturbation_lt_one d p hp
  have h := congrArg (fun L : L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) ↦ L q)
    (Units.inv_mul (Units.oneSub T hT))
  simpa [divisionInverse, T, hT, divisionPerturbation_apply, sub_eq_add_neg] using h

/-- Quotient for division by the normalized divisor `w^d + p`. -/
noncomputable def divisionQuotient (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  divisionInverse d p hp (highShift d f)

/-- Proof-independent quotient map, defined on all coefficient pairs by total ring inversion. -/
noncomputable def divisionQuotientGlobal (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  Ring.inverse (1 + divisionPerturbation d pf.1) (highShift d pf.2)

theorem divisionQuotientGlobal_eq (d : ℕ) (p f : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1) :
    divisionQuotientGlobal d (p,f) = divisionQuotient d p hp f := by
  let K := divisionPerturbation d p
  let hK : ‖-K‖ < 1 := norm_neg_divisionPerturbation_lt_one d p hp
  have hinv : Ring.inverse (1 + K) = ↑((Units.oneSub (-K) hK)⁻¹) := by
    rw [show 1 + K = 1 - (-K) by abel]
    exact NormedRing.inverse_one_sub (-K) hK
  change Ring.inverse (1 + K) (highShift d f) =
    (↑((Units.oneSub (-K) hK)⁻¹) :
      L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ)) (highShift d f)
  rw [hinv]

theorem analyticAt_inverseOneAdd_apply
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : X →L[ℂ] (E →L[ℂ] E)) (b : X →L[ℂ] E) (x : X) (hK : ‖K x‖ < 1) :
    AnalyticAt ℂ (fun y ↦ Ring.inverse (1 + K y) (b y)) x := by
  let op : X → (E →L[ℂ] E) := fun y ↦ 1 + K y
  have hop : AnalyticAt ℂ op x := analyticAt_const.add (K.analyticAt x)
  let hneg : ‖-(K x)‖ < 1 := by simpa using hK
  let z := Units.oneSub (-(K x)) hneg
  have hz : (z : E →L[ℂ] E) = op x := by simp [z, op, sub_eq_add_neg]
  have hinvAt : AnalyticAt ℂ Ring.inverse (op x) := by
    rw [← hz]
    exact analyticAt_inverse z
  have hinv : AnalyticAt ℂ (fun y ↦ Ring.inverse (op y)) x := by
    simpa [Function.comp_def] using hinvAt.comp hop
  have happ := (ContinuousLinearMap.apply ℂ E).analyticAt_bilinear
    (b x, Ring.inverse (op x))
  have hpair := (b.analyticAt x).prod hinv
  have hcomp := AnalyticAt.comp (x := x) happ hpair
  simpa [op, Function.comp_def] using hcomp

/-- Extract the divisor perturbation operator from divisor/dividend input. -/
def divisionOperatorInput (d : ℕ) :
    (L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) →L[ℂ]
      (L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ)) :=
  divisionPerturbationMap d ∘L
    ContinuousLinearMap.fst ℂ (L1Coeff (A × ℕ)) (L1Coeff (A × ℕ))

/-- Extract and high-shift the right-hand side from divisor/dividend input. -/
def divisionRhsInput (d : ℕ) :
    (L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) →L[ℂ] L1Coeff (A × ℕ) :=
  highShiftCLM d ∘L
    ContinuousLinearMap.snd ℂ (L1Coeff (A × ℕ)) (L1Coeff (A × ℕ))

@[simp] lemma divisionOperatorInput_apply (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) :
    divisionOperatorInput d pf = divisionPerturbation d pf.1 := rfl

omit [AddCommMonoid A] [Finset.HasAntidiagonal A] in
@[simp] lemma divisionRhsInput_apply (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) :
    divisionRhsInput d pf = highShift d pf.2 := rfl

theorem analyticAt_divisionQuotientFormula (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (fun x ↦ Ring.inverse (1 + divisionOperatorInput d x)
      (divisionRhsInput d x)) pf := by
  have hK : ‖divisionOperatorInput (A := A) d pf‖ < 1 :=
    lt_of_le_of_lt (norm_divisionPerturbation_le d pf.1) hp
  exact analyticAt_inverseOneAdd_apply
    (divisionOperatorInput (A := A) d) (divisionRhsInput (A := A) d) pf hK

theorem divisionQuotientFormula_eq_global (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) :
    Ring.inverse (1 + divisionOperatorInput d pf) (divisionRhsInput d pf) =
      divisionQuotientGlobal d pf := rfl

/-- Remainder, supported in distinguished-variable degrees below `d`. -/
noncomputable def divisionRemainder (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  lowCut d (f - convolution (divisionQuotient d p hp f) p)

theorem divisionQuotient_equation (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) :
    divisionQuotient d p hp f +
        highShift d (convolution (divisionQuotient d p hp f) p) = highShift d f := by
  exact divisionInverse_right d p hp (highShift d f)

@[simp] theorem highShift_divisionRemainder (d : ℕ) (p : L1Coeff (A × ℕ))
    (hp : ‖p‖ < 1) (f : L1Coeff (A × ℕ)) :
    highShift d (divisionRemainder d p hp f) = 0 := by
  exact highShift_lowCut d _

theorem division_factorization (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) :
    f = lowShift d (divisionQuotient d p hp f) +
      convolution (divisionQuotient d p hp f) p + divisionRemainder d p hp f := by
  let q := divisionQuotient d p hp f
  have hq := divisionQuotient_equation d p hp f
  have hhigh : highShift d (f - convolution q p) = q := by
    change highShiftCLM d (f - convolution q p) = q
    rw [map_sub]
    change highShift d f - highShift d (convolution q p) = q
    rw [← hq]
    abel
  have hdec := lowShift_highShift_add_lowCut d (f - convolution q p)
  rw [hhigh] at hdec
  change f = lowShift d q + convolution q p + lowCut d (f - convolution q p)
  calc
    f = (f - convolution q p) + convolution q p := by abel
    _ = (lowShift d q + lowCut d (f - convolution q p)) + convolution q p :=
      congrArg (fun x ↦ x + convolution q p) hdec.symm
    _ = lowShift d q + convolution q p + lowCut d (f - convolution q p) := by abel

theorem divisionQuotient_unique (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f q r : L1Coeff (A × ℕ))
    (hfac : f = lowShift d q + convolution q p + r)
    (hr : highShift d r = 0) : q = divisionQuotient d p hp f := by
  have hmap := congrArg (highShiftCLM (A := A) d) hfac
  have heq : q + highShift d (convolution q p) = highShift d f := by
    change highShift d f = highShift d (lowShift d q + convolution q p + r) at hmap
    rw [highShift_add, highShift_add, highShift_lowShift, hr, add_zero] at hmap
    exact hmap.symm
  change q = divisionInverse d p hp (highShift d f)
  rw [← heq]
  exact (divisionInverse_left d p hp q).symm

/-- Existence and uniqueness of the quotient/remainder pair for a small normalized divisor. -/
theorem division_existsUnique (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) :
    ∃! qr : L1Coeff (A × ℕ) × L1Coeff (A × ℕ),
      f = lowShift d qr.1 + convolution qr.1 p + qr.2 ∧ highShift d qr.2 = 0 := by
  let q := divisionQuotient d p hp f
  let r := divisionRemainder d p hp f
  refine ⟨(q,r), ⟨division_factorization d p hp f, highShift_divisionRemainder d p hp f⟩, ?_⟩
  rintro ⟨q',r'⟩ ⟨hfac',hr'⟩
  have hq : q' = q := divisionQuotient_unique d p hp f q' r' hfac' hr'
  subst q'
  have hfac := division_factorization d p hp f
  have heq : (lowShift d q + convolution q p) + r =
      (lowShift d q + convolution q p) + r' := by
    simpa only [add_assoc] using hfac.symm.trans hfac'
  have hr_eq : r = r' := add_left_cancel heq
  subst r'
  rfl

theorem divisionRemainder_apply_of_le (d : ℕ) (p : L1Coeff (A × ℕ))
    (hp : ‖p‖ < 1) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ} (hn : d ≤ n) :
    divisionRemainder d p hp f (a,n) = 0 := by
  exact lowCut_apply_of_le d _ a hn

end Division

/-! ## Direct `ℓ¹(ℕ)` API -/

section NatDivision

/-- Delete the first `d` coefficients of a one-variable `ℓ¹` sequence. -/
def seqHighShift (d : ℕ) (f : L1Coeff ℕ) : L1Coeff ℕ :=
  ⟨fun n ↦ f (n + d), by
    apply memℓp_gen
    simpa [Function.comp_def] using
      (L1Coeff.summable_norm f).comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)⟩

@[simp] lemma seqHighShift_apply (d : ℕ) (f : L1Coeff ℕ) (n : ℕ) :
    seqHighShift d f n = f (n + d) := rfl

theorem norm_seqHighShift_le (d : ℕ) (f : L1Coeff ℕ) : ‖seqHighShift d f‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  apply (L1Coeff.summable_norm (seqHighShift d f)).tsum_le_tsum_of_inj (fun n ↦ n + d)
    (fun _ _ h ↦ Nat.add_right_cancel h)
  · intro n hn
    exact norm_nonneg _
  · intro n
    exact le_rfl
  · exact L1Coeff.summable_norm f

lemma seqHighShift_add (d : ℕ) (f g : L1Coeff ℕ) :
    seqHighShift d (f + g) = seqHighShift d f + seqHighShift d g := by
  apply lp.ext
  funext n
  rfl

lemma seqHighShift_smul (d : ℕ) (c : ℂ) (f : L1Coeff ℕ) :
    seqHighShift d (c • f) = c • seqHighShift d f := by
  apply lp.ext
  funext n
  rfl

/-- High shift on one-variable sequences as a contraction. -/
def seqHighShiftCLM (d : ℕ) : L1Coeff ℕ →L[ℂ] L1Coeff ℕ :=
  ({
    toFun := seqHighShift d
    map_add' := seqHighShift_add d
    map_smul' := seqHighShift_smul d
    } : L1Coeff ℕ →ₗ[ℂ] L1Coeff ℕ).mkContinuous 1 (by
      intro f
      simpa using norm_seqHighShift_le d f)

/-- The natural-number embedding that shifts indices upward by `d`. -/
def seqLowIndex (d : ℕ) : ℕ ↪ ℕ where
  toFun n := n + d
  inj' := fun _ _ h ↦ Nat.add_right_cancel h

/-- Insert `d` zero coefficients at the beginning of a one-variable sequence. -/
def seqLowShift (d : ℕ) (f : L1Coeff ℕ) : L1Coeff ℕ :=
  L1Coeff.embed (seqLowIndex d) f

@[simp] lemma seqLowShift_apply_add (d : ℕ) (f : L1Coeff ℕ) (n : ℕ) :
    seqLowShift d f (n + d) = f n := L1Coeff.embed_apply_self (seqLowIndex d) f n

lemma seqLowShift_apply_of_lt (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : n < d) :
    seqLowShift d f n = 0 := by
  apply L1Coeff.embed_apply_of_not_mem
  rintro ⟨m, hm⟩
  change m + d = n at hm
  omega

lemma seqLowShift_apply_of_le (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : d ≤ n) :
    seqLowShift d f n = f (n - d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : d + m - d = m := Nat.add_sub_cancel_left d m
  rw [hsub]
  simpa only [Nat.add_comm] using seqLowShift_apply_add d f m

/-- Keep precisely the coefficients below degree `d`. -/
def seqLowCut (d : ℕ) (f : L1Coeff ℕ) : L1Coeff ℕ :=
  ⟨fun n ↦ if n < d then f n else 0, by
    apply memℓp_gen
    simpa using (L1Coeff.summable_norm f).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun n ↦ by split_ifs <;> simp)⟩

@[simp] lemma seqLowCut_apply_of_lt (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : n < d) :
    seqLowCut d f n = f n := by simp [seqLowCut, hn]

@[simp] lemma seqLowCut_apply_of_le (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : d ≤ n) :
    seqLowCut d f n = 0 := by simp [seqLowCut, Nat.not_lt.mpr hn]

theorem norm_seqLowCut_le (d : ℕ) (f : L1Coeff ℕ) : ‖seqLowCut d f‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  apply (L1Coeff.summable_norm (seqLowCut d f)).tsum_le_tsum
  · intro n
    change ‖if n < d then f n else 0‖ ≤ ‖f n‖
    split_ifs <;> simp
  · exact L1Coeff.summable_norm f

lemma seqLowCut_add (d : ℕ) (f g : L1Coeff ℕ) :
    seqLowCut d (f + g) = seqLowCut d f + seqLowCut d g := by
  apply lp.ext
  funext n
  simp only [seqLowCut, lp.coeFn_add, Pi.add_apply]
  split_ifs <;> simp

lemma seqLowCut_smul (d : ℕ) (c : ℂ) (f : L1Coeff ℕ) :
    seqLowCut d (c • f) = c • seqLowCut d f := by
  apply lp.ext
  funext n
  simp only [seqLowCut, lp.coeFn_smul, Pi.smul_apply]
  split_ifs <;> simp

/-- Low-degree cutoff on one-variable sequences as a contraction. -/
def seqLowCutCLM (d : ℕ) : L1Coeff ℕ →L[ℂ] L1Coeff ℕ :=
  ({
    toFun := seqLowCut d
    map_add' := seqLowCut_add d
    map_smul' := seqLowCut_smul d
    } : L1Coeff ℕ →ₗ[ℂ] L1Coeff ℕ).mkContinuous 1 (by
      intro f
      simpa using norm_seqLowCut_le d f)

@[simp] theorem seqHighShift_seqLowShift (d : ℕ) (f : L1Coeff ℕ) :
    seqHighShift d (seqLowShift d f) = f := by
  apply lp.ext
  funext n
  simp

@[simp] theorem seqHighShift_seqLowCut (d : ℕ) (f : L1Coeff ℕ) :
    seqHighShift d (seqLowCut d f) = 0 := by
  apply lp.ext
  funext n
  rw [seqHighShift_apply, seqLowCut_apply_of_le d f (by omega)]
  rfl

theorem seqLowShift_highShift_add_lowCut (d : ℕ) (f : L1Coeff ℕ) :
    seqLowShift d (seqHighShift d f) + seqLowCut d f = f := by
  apply lp.ext
  funext n
  by_cases hn : n < d
  · simp [seqLowShift_apply_of_lt d _ hn, seqLowCut_apply_of_lt d _ hn]
  · change seqLowShift d (seqHighShift d f) n + seqLowCut d f n = f n
    rw [seqLowCut_apply_of_le d f (Nat.le_of_not_gt hn), add_zero]
    rw [seqLowShift_apply_of_le d _ (Nat.le_of_not_gt hn)]
    simp [Nat.sub_add_cancel (Nat.le_of_not_gt hn)]

/-- The high-shifted convolution perturbation `S_d C_p` on `ℓ¹(ℕ)`. -/
def seqDivisionPerturbation (d : ℕ) (p : L1Coeff ℕ) : L1Coeff ℕ →L[ℂ] L1Coeff ℕ :=
  seqHighShiftCLM d ∘L convolutionRight p

@[simp] lemma seqDivisionPerturbation_apply (d : ℕ) (p q : L1Coeff ℕ) :
    seqDivisionPerturbation d p q = seqHighShift d (convolution q p) := rfl

theorem norm_seqDivisionPerturbation_le (d : ℕ) (p : L1Coeff ℕ) :
    ‖seqDivisionPerturbation d p‖ ≤ ‖p‖ := by
  calc
    ‖seqDivisionPerturbation d p‖ ≤ ‖seqHighShiftCLM d‖ * ‖convolutionRight p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖p‖ := by
      apply mul_le_mul
      · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro f
        change ‖seqHighShift d f‖ ≤ 1 * ‖f‖
        simpa using norm_seqHighShift_le d f
      · exact norm_convolutionRight_le p
      · exact norm_nonneg _
      · exact zero_le_one
    _ = ‖p‖ := one_mul _

/-- The continuous-linear family of one-variable division perturbations. -/
def seqDivisionPerturbationMap (d : ℕ) :
    L1Coeff ℕ →L[ℂ] (L1Coeff ℕ →L[ℂ] L1Coeff ℕ) :=
  ({
    toFun := seqDivisionPerturbation d
    map_add' := by
      intro p₁ p₂
      apply ContinuousLinearMap.ext
      intro q
      change seqHighShift d (convolution q (p₁ + p₂)) =
        seqHighShift d (convolution q p₁) + seqHighShift d (convolution q p₂)
      rw [convolution_add_right, seqHighShift_add]
    map_smul' := by
      intro c p
      apply ContinuousLinearMap.ext
      intro q
      change seqHighShift d (convolution q (c • p)) = c • seqHighShift d (convolution q p)
      rw [convolution_smul_right, seqHighShift_smul]
    } : L1Coeff ℕ →ₗ[ℂ] (L1Coeff ℕ →L[ℂ] L1Coeff ℕ)).mkContinuous 1 (by
      intro p
      simpa using norm_seqDivisionPerturbation_le d p)

@[simp] lemma seqDivisionPerturbationMap_apply (d : ℕ) (p : L1Coeff ℕ) :
    seqDivisionPerturbationMap d p = seqDivisionPerturbation d p := rfl

private lemma norm_neg_seqDivisionPerturbation_lt_one (d : ℕ) (p : L1Coeff ℕ)
    (hp : ‖p‖ < 1) : ‖-(seqDivisionPerturbation d p)‖ < 1 := by
  rw [norm_neg]
  exact lt_of_le_of_lt (norm_seqDivisionPerturbation_le d p) hp

/-- The Neumann-series inverse of the one-variable division operator. -/
noncomputable def seqDivisionInverse (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    L1Coeff ℕ →L[ℂ] L1Coeff ℕ :=
  ↑((Units.oneSub (-(seqDivisionPerturbation d p))
    (norm_neg_seqDivisionPerturbation_lt_one d p hp))⁻¹)

theorem seqDivisionInverse_right (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (b : L1Coeff ℕ) :
    seqDivisionInverse d p hp b +
      seqHighShift d (convolution (seqDivisionInverse d p hp b) p) = b := by
  let T := -(seqDivisionPerturbation d p)
  let hT : ‖T‖ < 1 := norm_neg_seqDivisionPerturbation_lt_one d p hp
  have h := congrArg (fun L : L1Coeff ℕ →L[ℂ] L1Coeff ℕ ↦ L b)
    (Units.mul_inv (Units.oneSub T hT))
  simpa [seqDivisionInverse, T, hT, seqDivisionPerturbation_apply,
    sub_eq_add_neg] using h

theorem seqDivisionInverse_left (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (q : L1Coeff ℕ) :
    seqDivisionInverse d p hp (q + seqHighShift d (convolution q p)) = q := by
  let T := -(seqDivisionPerturbation d p)
  let hT : ‖T‖ < 1 := norm_neg_seqDivisionPerturbation_lt_one d p hp
  have h := congrArg (fun L : L1Coeff ℕ →L[ℂ] L1Coeff ℕ ↦ L q)
    (Units.inv_mul (Units.oneSub T hT))
  simpa [seqDivisionInverse, T, hT, seqDivisionPerturbation_apply,
    sub_eq_add_neg] using h

/-- The quotient sequence produced by the division inverse. -/
noncomputable def seqDivisionQuotient (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) : L1Coeff ℕ :=
  seqDivisionInverse d p hp (seqHighShift d f)

/-- The low-degree remainder sequence produced by division. -/
noncomputable def seqDivisionRemainder (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) : L1Coeff ℕ :=
  seqLowCut d (f - convolution (seqDivisionQuotient d p hp f) p)

/-- Extract the sequence perturbation operator from paired input. -/
def seqDivisionOperatorInput (d : ℕ) :
    (L1Coeff ℕ × L1Coeff ℕ) →L[ℂ] (L1Coeff ℕ →L[ℂ] L1Coeff ℕ) :=
  seqDivisionPerturbationMap d ∘L
    ContinuousLinearMap.fst ℂ (L1Coeff ℕ) (L1Coeff ℕ)

/-- Extract and high-shift the sequence right-hand side from paired input. -/
def seqDivisionRhsInput (d : ℕ) :
    (L1Coeff ℕ × L1Coeff ℕ) →L[ℂ] L1Coeff ℕ :=
  seqHighShiftCLM d ∘L ContinuousLinearMap.snd ℂ (L1Coeff ℕ) (L1Coeff ℕ)

@[simp] lemma seqDivisionOperatorInput_apply (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    seqDivisionOperatorInput d pf = seqDivisionPerturbation d pf.1 := rfl

@[simp] lemma seqDivisionRhsInput_apply (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    seqDivisionRhsInput d pf = seqHighShift d pf.2 := rfl

/-- Proof-independent quotient, jointly analytic on the open set `‖p‖ < 1`. -/
noncomputable def seqDivisionQuotientGlobal (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    L1Coeff ℕ :=
  Ring.inverse (1 + seqDivisionOperatorInput d pf) (seqDivisionRhsInput d pf)

theorem seqDivisionQuotientGlobal_eq (d : ℕ) (p f : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    seqDivisionQuotientGlobal d (p,f) = seqDivisionQuotient d p hp f := by
  let K := seqDivisionPerturbation d p
  let hK : ‖-K‖ < 1 := norm_neg_seqDivisionPerturbation_lt_one d p hp
  have hinv : Ring.inverse (1 + K) = ↑((Units.oneSub (-K) hK)⁻¹) := by
    rw [show 1 + K = 1 - (-K) by abel]
    exact NormedRing.inverse_one_sub (-K) hK
  change Ring.inverse (1 + K) (seqHighShift d f) =
    (↑((Units.oneSub (-K) hK)⁻¹) : L1Coeff ℕ →L[ℂ] L1Coeff ℕ) (seqHighShift d f)
  rw [hinv]

theorem analyticAt_seqDivisionQuotientGlobal (d : ℕ)
    (pf : L1Coeff ℕ × L1Coeff ℕ) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (seqDivisionQuotientGlobal d) pf := by
  have hK : ‖seqDivisionOperatorInput d pf‖ < 1 :=
    lt_of_le_of_lt (norm_seqDivisionPerturbation_le d pf.1) hp
  exact analyticAt_inverseOneAdd_apply
    (seqDivisionOperatorInput d) (seqDivisionRhsInput d) pf hK

/-- Proof-independent remainder, jointly analytic wherever the divisor tail has norm below one. -/
noncomputable def seqDivisionRemainderGlobal (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    L1Coeff ℕ :=
  seqLowCut d (pf.2 - convolution (seqDivisionQuotientGlobal d pf) pf.1)

theorem seqDivisionRemainderGlobal_eq (d : ℕ) (p f : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    seqDivisionRemainderGlobal d (p,f) = seqDivisionRemainder d p hp f := by
  simp only [seqDivisionRemainderGlobal, seqDivisionRemainder]
  rw [seqDivisionQuotientGlobal_eq d p f hp]

theorem analyticAt_seqDivisionRemainderGlobal (d : ℕ)
    (pf : L1Coeff ℕ × L1Coeff ℕ) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (seqDivisionRemainderGlobal d) pf := by
  have hq := analyticAt_seqDivisionQuotientGlobal d pf hp
  have happ := (convolutionRightMap (A := ℕ)).analyticAt_bilinear
    (pf.1, seqDivisionQuotientGlobal d pf)
  have hconv : AnalyticAt ℂ
      (fun x : L1Coeff ℕ × L1Coeff ℕ ↦
        convolution (seqDivisionQuotientGlobal d x) x.1) pf := by
    have hpair := (analyticAt_fst (𝕜 := ℂ)).prod hq
    simpa [Function.comp_def] using AnalyticAt.comp (x := pf) happ hpair
  have hdiff : AnalyticAt ℂ
      (fun x : L1Coeff ℕ × L1Coeff ℕ ↦
        x.2 - convolution (seqDivisionQuotientGlobal d x) x.1) pf :=
    (analyticAt_snd (𝕜 := ℂ)).sub hconv
  have hout := (seqLowCutCLM d).analyticAt
    (pf.2 - convolution (seqDivisionQuotientGlobal d pf) pf.1)
  change AnalyticAt ℂ (fun x : L1Coeff ℕ × L1Coeff ℕ ↦
    seqLowCut d (x.2 - convolution (seqDivisionQuotientGlobal d x) x.1)) pf
  have hcomp := AnalyticAt.comp (x := pf) hout hdiff
  simpa [seqLowCutCLM, Function.comp_def] using hcomp

theorem seqDivisionQuotient_equation (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) :
    seqDivisionQuotient d p hp f +
      seqHighShift d (convolution (seqDivisionQuotient d p hp f) p) =
        seqHighShift d f := by
  exact seqDivisionInverse_right d p hp (seqHighShift d f)

@[simp] theorem seqHighShift_divisionRemainder (d : ℕ) (p : L1Coeff ℕ)
    (hp : ‖p‖ < 1) (f : L1Coeff ℕ) :
    seqHighShift d (seqDivisionRemainder d p hp f) = 0 :=
  seqHighShift_seqLowCut d _

theorem seqDivision_factorization (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) :
    f = seqLowShift d (seqDivisionQuotient d p hp f) +
      convolution (seqDivisionQuotient d p hp f) p + seqDivisionRemainder d p hp f := by
  let q := seqDivisionQuotient d p hp f
  have hq := seqDivisionQuotient_equation d p hp f
  have hhigh : seqHighShift d (f - convolution q p) = q := by
    change seqHighShiftCLM d (f - convolution q p) = q
    rw [map_sub]
    change seqHighShift d f - seqHighShift d (convolution q p) = q
    rw [← hq]
    abel
  have hdec := seqLowShift_highShift_add_lowCut d (f - convolution q p)
  rw [hhigh] at hdec
  change f = seqLowShift d q + convolution q p + seqLowCut d (f - convolution q p)
  calc
    f = (f - convolution q p) + convolution q p := by abel
    _ = (seqLowShift d q + seqLowCut d (f - convolution q p)) + convolution q p :=
      congrArg (fun x ↦ x + convolution q p) hdec.symm
    _ = seqLowShift d q + convolution q p + seqLowCut d (f - convolution q p) := by abel

theorem seqDivisionQuotient_unique (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f q r : L1Coeff ℕ)
    (hfac : f = seqLowShift d q + convolution q p + r)
    (hr : seqHighShift d r = 0) : q = seqDivisionQuotient d p hp f := by
  have hmap := congrArg (seqHighShiftCLM d) hfac
  have heq : q + seqHighShift d (convolution q p) = seqHighShift d f := by
    change seqHighShift d f = seqHighShift d (seqLowShift d q + convolution q p + r) at hmap
    rw [seqHighShift_add, seqHighShift_add, seqHighShift_seqLowShift, hr, add_zero] at hmap
    exact hmap.symm
  change q = seqDivisionInverse d p hp (seqHighShift d f)
  rw [← heq]
  exact (seqDivisionInverse_left d p hp q).symm

/-- The direct Nat-indexed division theorem with a unique quotient/remainder pair. -/
theorem seqDivision_existsUnique (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) :
    ∃! qr : L1Coeff ℕ × L1Coeff ℕ,
      f = seqLowShift d qr.1 + convolution qr.1 p + qr.2 ∧ seqHighShift d qr.2 = 0 := by
  let q := seqDivisionQuotient d p hp f
  let r := seqDivisionRemainder d p hp f
  refine ⟨(q,r), ⟨seqDivision_factorization d p hp f,
    seqHighShift_divisionRemainder d p hp f⟩, ?_⟩
  rintro ⟨q',r'⟩ ⟨hfac',hr'⟩
  have hq : q' = q := seqDivisionQuotient_unique d p hp f q' r' hfac' hr'
  subst q'
  have hfac := seqDivision_factorization d p hp f
  have heq : (seqLowShift d q + convolution q p) + r =
      (seqLowShift d q + convolution q p) + r' := by
    simpa only [add_assoc] using hfac.symm.trans hfac'
  have hr_eq : r = r' := add_left_cancel heq
  subst r'
  rfl

theorem seqDivisionRemainder_apply_of_le (d : ℕ) (p : L1Coeff ℕ)
    (hp : ‖p‖ < 1) (f : L1Coeff ℕ) {n : ℕ} (hn : d ≤ n) :
    seqDivisionRemainder d p hp f n = 0 := seqLowCut_apply_of_le d _ hn

theorem seqDivisionGlobal_factorization (d : ℕ) (p f : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    f = seqLowShift d (seqDivisionQuotientGlobal d (p,f)) +
      convolution (seqDivisionQuotientGlobal d (p,f)) p +
        seqDivisionRemainderGlobal d (p,f) := by
  rw [seqDivisionQuotientGlobal_eq d p f hp, seqDivisionRemainderGlobal_eq d p f hp]
  exact seqDivision_factorization d p hp f

@[simp] theorem seqHighShift_divisionRemainderGlobal (d : ℕ) (p f : L1Coeff ℕ)
    (hp : ‖p‖ < 1) :
    seqHighShift d (seqDivisionRemainderGlobal d (p,f)) = 0 := by
  rw [seqDivisionRemainderGlobal_eq d p f hp]
  exact seqHighShift_divisionRemainder d p hp f

end NatDivision

end ClassicalComplexWPT
