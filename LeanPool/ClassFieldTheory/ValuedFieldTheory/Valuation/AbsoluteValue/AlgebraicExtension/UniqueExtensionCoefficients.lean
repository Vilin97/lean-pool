/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds
/-!
# the nonarchimedean valuation construction, the irreducible coefficient estimate: the
  coefficient norm of an irreducible polynomial

The unique nonarchimedean extension to a splitting field is invariant under
all ground-field automorphisms.  Normality of a splitting field therefore
forces all conjugate roots of an irreducible polynomial to have one common
absolute value.  Vieta's factorization and the strong triangle inequality
then bound every coefficient by the larger endpoint coefficient.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- The hypothesis that `w` is the unique nonarchimedean exact
extension of `v` to `L`. -/
def IsUniqueNonarchimedeanAbsoluteValueExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) : Prop :=
  LubinTate.Valuations.NonarchimedeanAbsoluteValue w ∧ AbsoluteValue.Extends v w ∧
    ∀ u : AbsoluteValue L ℝ,
      LubinTate.Valuations.NonarchimedeanAbsoluteValue u → AbsoluteValue.Extends v u → u = w

/-- Uniqueness of the nonarchimedean extension makes it invariant under every
ground-field automorphism of the splitting field. -/
theorem uniqueNonarchimedeanAbsoluteValueExtension_map_algEquiv_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (huniq : IsUniqueNonarchimedeanAbsoluteValueExtension v w)
    (σ : L ≃ₐ[K] L) (x : L) :
    w (σ x) = w x := by
  let u : AbsoluteValue L ℝ := w.comp (f := σ.toRingHom) σ.injective
  have hu_nonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue u := by
    rcases huniq.1 with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    change w (σ (n : L)) ≤ C
    simpa using hC n
  have hu_extends : AbsoluteValue.Extends v u := by
    intro a
    change w (σ (algebraMap K L a)) = v a
    rw [σ.commutes]
    exact huniq.2.1 a
  have hueq : u = w := huniq.2.2 u hu_nonarch hu_extends
  exact congrArg (fun z : AbsoluteValue L ℝ => z x) hueq

/-- In a normal extension, roots of one irreducible ground-field polynomial
have equal absolute value under the unique extension. -/
theorem uniqueNonarchimedeanAbsoluteValueExtension_eq_on_roots_of_irreducible
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (huniq : IsUniqueNonarchimedeanAbsoluteValueExtension v w)
    {p : Polynomial K} (hp : Irreducible p)
    {α β : L}
    (hα : α ∈ (p.map (algebraMap K L)).roots)
    (hβ : β ∈ (p.map (algebraMap K L)).roots) :
    w α = w β := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hmap0 : p.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hp0
  have hαeval : (aeval α) p = 0 := by
    simpa [aeval_def] using (Polynomial.mem_roots hmap0).1 hα
  have hβeval : (aeval β) p = 0 := by
    simpa [aeval_def] using (Polynomial.mem_roots hmap0).1 hβ
  have hmin : minpoly K α = minpoly K β := by
    rw [← minpoly.eq_of_irreducible hp hαeval,
      ← minpoly.eq_of_irreducible hp hβeval]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).1 hmin
  rw [← hσ]
  exact uniqueNonarchimedeanAbsoluteValueExtension_map_algEquiv_eq huniq σ β

/-- A direct nonarchimedean Vieta estimate.  If every element of `s` has
absolute value at most `B`, with `B ≥ 1`, then every coefficient of
`∏_{α∈s}(X-α)` has absolute value at most `B ^ |s|`. -/
theorem abs_coeff_prod_X_sub_C_le_pow_card
    {L : Type*} [Field L]
    (w : AbsoluteValue L ℝ) (hstrong : LubinTate.Valuations.StrongTriangle w)
    (B : ℝ) (hB : 1 ≤ B) (s : Multiset L)
    (hs : ∀ α ∈ s, w α ≤ B) (i : ℕ) :
    w (((s.map (fun α => X - C α)).prod).coeff i) ≤ B ^ s.card := by
  induction s using Multiset.induction_on generalizing i with
  | empty =>
      cases i <;> simp [Polynomial.coeff_one]
  | @cons α s ih =>
      have hα : w α ≤ B := hs α (by simp)
      have hs' : ∀ β ∈ s, w β ≤ B := by
        intro β hβ
        exact hs β (by simp [hβ])
      have hB0 : 0 ≤ B := zero_le_one.trans hB
      have hpow_step : B ^ s.card ≤ B ^ (s.card + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (pow_nonneg hB0 _) hB
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
      cases i with
      | zero =>
          have hq := ih hs' 0
          calc
            w (((X - C α) * (s.map (fun β => X - C β)).prod).coeff 0) =
                w α * w (((s.map (fun β => X - C β)).prod).coeff 0) := by
              simp [Polynomial.coeff_zero_eq_eval_zero]
            _ ≤ B * B ^ s.card :=
              mul_le_mul hα hq (w.nonneg _) hB0
            _ = B ^ (s.card + 1) := by
              rw [pow_succ]
              ac_rfl
      | succ j =>
          rw [Polynomial.coeff_X_sub_C_mul]
          have hqj := ih hs' j
          have hqsucc := ih hs' (j + 1)
          have hterm :
              w (α * ((s.map (fun β => X - C β)).prod).coeff (j + 1)) ≤
                B ^ (s.card + 1) := by
            rw [w.map_mul]
            calc
              w α * w (((s.map (fun β => X - C β)).prod).coeff (j + 1)) ≤
                  B * B ^ s.card :=
                mul_le_mul hα hqsucc (w.nonneg _) hB0
              _ = B ^ (s.card + 1) := by
                rw [pow_succ]
                ac_rfl
          have hsum := hstrong
            (((s.map (fun β => X - C β)).prod).coeff j)
            (-α * ((s.map (fun β => X - C β)).prod).coeff (j + 1))
          calc
            w (((s.map (fun β => X - C β)).prod).coeff j -
                α * ((s.map (fun β => X - C β)).prod).coeff (j + 1)) ≤
                max
                  (w (((s.map (fun β => X - C β)).prod).coeff j))
                  (w (α * ((s.map (fun β => X - C β)).prod).coeff (j + 1))) := by
              simpa [sub_eq_add_neg] using hsum
            _ ≤ B ^ (s.card + 1) :=
              max_le (hqj.trans hpow_step) hterm

/-- If all entries of a multiset have one absolute value, the absolute value
of their product is the corresponding power. -/
theorem abs_multiset_prod_eq_pow_card_of_eq
    {L : Type*} [Field L] (w : AbsoluteValue L ℝ)
    (t : ℝ) (s : Multiset L) (hs : ∀ α ∈ s, w α = t) :
    w s.prod = t ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons α s ih =>
      have hα : w α = t := hs α (by simp)
      have hs' : ∀ β ∈ s, w β = t := by
        intro β hβ
        exact hs β (by simp [hβ])
      simp only [Multiset.prod_cons, Multiset.card_cons, w.map_mul, hα, ih hs', pow_succ]
      ac_rfl

/-- the irreducible coefficient estimate, coefficient estimate before taking the finite maximum.
All conjugate roots have one value; Vieta's formula and the direct finite
nonarchimedean estimate above bound every coefficient by an endpoint. -/
theorem uniqueExtensionCoefficients_coeff_abs_le_endpoint_max_of_unique_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (f : Polynomial K) [IsSplittingField K L f]
    (huniq : IsUniqueNonarchimedeanAbsoluteValueExtension v w)
    (hirr : Irreducible f) :
    ∀ i : ℕ, v (f.coeff i) ≤ max (v (f.coeff 0)) (v f.leadingCoeff) := by
  let : Normal K L := Normal.of_isSplittingField f
  have hsplit : (f.map (algebraMap K L)).Splits :=
    IsSplittingField.splits L f
  have hmap0 : f.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hirr.ne_zero
  have hroots_ne : (f.map (algebraMap K L)).roots ≠ 0 := by
    intro hz
    have hcard := hsplit.natDegree_eq_card_roots
    rw [hz] at hcard
    have hdeg : f.natDegree = 0 := by
      simpa using hcard
    exact hirr.natDegree_pos.ne' hdeg
  obtain ⟨α, hα⟩ := Multiset.exists_mem_of_ne_zero hroots_ne
  let t : ℝ := w α
  have hall : ∀ β ∈ (f.map (algebraMap K L)).roots, w β = t := by
    intro β hβ
    exact uniqueNonarchimedeanAbsoluteValueExtension_eq_on_roots_of_irreducible
      huniq hirr hβ hα
  have ht0 : 0 ≤ t := w.nonneg α
  have hstrong : LubinTate.Valuations.StrongTriangle w :=
    LubinTate.Valuations.strong_triangle_of_nonarchimedean w huniq.1
  have hlead : w (algebraMap K L f.leadingCoeff) = v f.leadingCoeff :=
    huniq.2.1 f.leadingCoeff
  have hconst :
      v (f.coeff 0) =
        v f.leadingCoeff * t ^ (f.map (algebraMap K L)).roots.card := by
    calc
      v (f.coeff 0) = w (algebraMap K L (f.coeff 0)) :=
        (huniq.2.1 (f.coeff 0)).symm
      _ = w ((f.map (algebraMap K L)).coeff 0) := by
        rw [Polynomial.coeff_map]
      _ = w (((-1) ^ (f.map (algebraMap K L)).natDegree) *
          (f.map (algebraMap K L)).leadingCoeff *
            (f.map (algebraMap K L)).roots.prod) := by
        rw [hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots]
      _ = v f.leadingCoeff * t ^ (f.map (algebraMap K L)).roots.card := by
        rw [w.map_mul, w.map_mul,
          Polynomial.leadingCoeff_map_of_injective (algebraMap K L).injective,
          hlead,
          abs_multiset_prod_eq_pow_card_of_eq w t
            (f.map (algebraMap K L)).roots hall]
        simp
  intro i
  have hcoeff :
      algebraMap K L (f.coeff i) =
        algebraMap K L f.leadingCoeff *
          (((f.map (algebraMap K L)).roots.map (fun β => X - C β)).prod).coeff i := by
    rw [← Polynomial.coeff_map]
    conv_lhs => rw [hsplit.eq_prod_roots]
    rw [Polynomial.coeff_C_mul,
      Polynomial.leadingCoeff_map_of_injective (algebraMap K L).injective]
  have hcoeff_value :
      v (f.coeff i) =
        v f.leadingCoeff *
          w ((((f.map (algebraMap K L)).roots.map
            (fun β => X - C β)).prod).coeff i) := by
    rw [← huniq.2.1 (f.coeff i), hcoeff, w.map_mul, hlead]
  rcases le_total t 1 with ht | ht
  · have hq :
        w ((((f.map (algebraMap K L)).roots.map
          (fun β => X - C β)).prod).coeff i) ≤
            (1 : ℝ) ^ (f.map (algebraMap K L)).roots.card :=
      abs_coeff_prod_X_sub_C_le_pow_card w hstrong 1 le_rfl
        (f.map (algebraMap K L)).roots
        (fun β hβ => (hall β hβ).trans_le ht) i
    rw [hcoeff_value]
    have hmul :
        v f.leadingCoeff *
            w ((((f.map (algebraMap K L)).roots.map
              (fun β => X - C β)).prod).coeff i) ≤
          v f.leadingCoeff := by
      have := mul_le_mul_of_nonneg_left (by simpa using hq)
        (v.nonneg f.leadingCoeff)
      simpa using this
    exact hmul.trans (le_max_right _ _)
  · have hq :
        w ((((f.map (algebraMap K L)).roots.map
          (fun β => X - C β)).prod).coeff i) ≤
            t ^ (f.map (algebraMap K L)).roots.card :=
      abs_coeff_prod_X_sub_C_le_pow_card w hstrong t ht
        (f.map (algebraMap K L)).roots
        (fun β hβ => (hall β hβ).le) i
    rw [hcoeff_value]
    have hmul := mul_le_mul_of_nonneg_left hq (v.nonneg f.leadingCoeff)
    rw [← hconst] at hmul
    exact hmul.trans (le_max_left _ _)

/-- the irreducible coefficient estimate in the notation.  For an irreducible polynomial,
if the nonarchimedean absolute value has a unique exact extension to its
splitting field, its coefficient norm is the larger of its constant and
leading coefficient absolute values. -/
theorem uniqueExtensionCoefficients_polynomialCoeffAbsMax_eq_endpoint_max
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (f : Polynomial K) [IsSplittingField K L f]
    (huniq : IsUniqueNonarchimedeanAbsoluteValueExtension v w)
    (hirr : Irreducible f) :
    polynomialCoeffAbsMax v f =
      max (v (f.coeff 0)) (v f.leadingCoeff) := by
  let T : Finset ℝ :=
    (Finset.range (f.natDegree + 1)).image fun i => v (f.coeff i)
  let hT : T.Nonempty := by
    refine ⟨v (f.coeff 0), ?_⟩
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  change T.max' hT = max (v (f.coeff 0)) (v f.leadingCoeff)
  refine le_antisymm ?_ ?_
  · refine Finset.max'_le T hT _ ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _hi, rfl⟩
    exact uniqueExtensionCoefficients_coeff_abs_le_endpoint_max_of_unique_extension
      v w f huniq hirr i
  · refine max_le ?_ ?_
    · exact Finset.le_max' T (v (f.coeff 0))
        (Finset.mem_image.mpr ⟨0, by simp, rfl⟩)
    · exact Finset.le_max' T (v f.leadingCoeff)
        (Finset.mem_image.mpr
          ⟨f.natDegree, by simp,
            by rw [Polynomial.leadingCoeff]⟩)

end Valuations
end AlgebraicNumberTheory

end
