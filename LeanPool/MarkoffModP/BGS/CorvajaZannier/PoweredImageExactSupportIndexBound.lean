/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageIndexBound

/-!
# Powered-image index from an exact support determinant

The general powered-image theorem replaces a support determinant by its
bidegree-box bound.  This module retains a supplied support triple and hence
its exact determinant.  It is useful for sparse curves whose support lattice
has much smaller index than the ambient degree box.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section


/-- Over algebraically closed constants, the source-to-powered-image degree
is bounded by any nonzero determinant exhibited by three support monomials. -/
theorem finrank_poweredCoordinateImageField_le_supportDet_isAlgClosed
    {F : Type*} [Field F] [IsAlgClosed F]
    {f : MvPolynomial (Fin 2) F}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    {r s t : Fin 2 →₀ ℕ}
    (hr : r ∈ f.support) (hs : s ∈ f.support) (ht : t ∈ f.support)
    (hdet : planeCurveSupportDifferenceDet r s t ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmF : (m : F) ≠ 0) (hnF : (n : F) ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredCoordinateImageField f m n)
        (PlaneCurveFunctionField f) ≤
      (planeCurveSupportDifferenceDet r s t).natAbs := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let B := PoweredCoordinateImageField f m n
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  let : FiniteDimensional B L :=
    finiteDimensional_poweredCoordinateImageField
      hf hpartialSecond m n hm
  let : IsGalois B L :=
    isGalois_over_poweredCoordinateImageField
      hf hpartialFirst hpartialSecond m n hm hn hmF hnF
  have hbasic :=
    poweredCoordinateImageField_adjoin_coordinates_eq_top_and_ne_zero
      hf hpartialFirst hpartialSecond m n
  have hgen : IntermediateField.adjoin B ({x, y} : Set L) = ⊤ :=
    hbasic.1
  have hgenAlg : Algebra.adjoin B ({x, y} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra]
    rw [hgen]
    rfl
  let a : ℤ := (s 0 : ℤ) - (r 0 : ℤ)
  let b : ℤ := (s 1 : ℤ) - (r 1 : ℤ)
  let c : ℤ := (t 0 : ℤ) - (r 0 : ℤ)
  let d : ℤ := (t 1 : ℤ) - (r 1 : ℤ)
  have hdet' : a * d - b * c ≠ 0 := by
    simpa [a, b, c, d, planeCurveSupportDifferenceDet] using hdet
  let : Finite (torusCharacterKernel F a b c d) :=
    finite_torusCharacterKernel_of_det_ne_zero a b c d hdet'
  let supportToKernel : planeCurveSupportCharacterStabilizer F f →
      torusCharacterKernel F a b c d := fun z =>
    ⟨z.1, z.2 r hr s hs, z.2 r hr t ht⟩
  have supportToKernel_injective :
      Function.Injective supportToKernel := by
    intro z w hzw
    apply Subtype.ext
    exact congrArg
      (fun u : torusCharacterKernel F a b c d => u.1) hzw
  let : Finite (planeCurveSupportCharacterStabilizer F f) :=
    Finite.of_injective supportToKernel supportToKernel_injective
  have hscale (σ : L ≃ₐ[B] L) :=
    exists_support_stabilizer_scaling_of_poweredImage_aut
      hf hpartialFirst hpartialSecond m n hm hn hmF hnF σ
  let scalePair : (L ≃ₐ[B] L) → Fˣ × Fˣ := fun σ =>
    Classical.choose (hscale σ)
  have scalePair_spec (σ : L ≃ₐ[B] L) :
      algebraMap F L (scalePair σ).1 * x = σ x ∧
      algebraMap F L (scalePair σ).2 * y = σ y ∧
      ∀ r ∈ f.support, ∀ s ∈ f.support,
        (scalePair σ).1 ^ ((s 0 : ℤ) - (r 0 : ℤ)) *
          (scalePair σ).2 ^ ((s 1 : ℤ) - (r 1 : ℤ)) = 1 :=
    Classical.choose_spec (hscale σ)
  let e : (L ≃ₐ[B] L) → planeCurveSupportCharacterStabilizer F f :=
    fun σ => ⟨scalePair σ, (scalePair_spec σ).2.2⟩
  have he : Function.Injective e := by
    intro σ τ hστ
    have hpairs : scalePair σ = scalePair τ :=
      congrArg Subtype.val hστ
    have hx : σ x = τ x := by
      rw [← (scalePair_spec σ).1, ← (scalePair_spec τ).1, hpairs]
    have hy : σ y = τ y := by
      rw [← (scalePair_spec σ).2.1, ← (scalePair_spec τ).2.1, hpairs]
    apply AlgEquiv.ext
    have hhom : σ.toAlgHom = τ.toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hgenAlg
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact hx
      · exact hy
    exact fun z => DFunLike.congr_fun hhom z
  calc
    Module.finrank B L = Nat.card (L ≃ₐ[B] L) :=
      (IsGalois.card_aut_eq_finrank B L).symm
    _ ≤ Nat.card (planeCurveSupportCharacterStabilizer F f) :=
      Nat.card_le_card_of_injective e he
    _ ≤ (planeCurveSupportDifferenceDet r s t).natAbs :=
      natCard_planeCurveSupportCharacterStabilizer_le_supportDet
        hr hs ht hdet

/-- The determinant-sensitive algebraically closed bound in the
first-coordinate presentation used by Proposition Two. -/
theorem finrank_poweredImageOverFirst_le_supportDet_isAlgClosed
    {F : Type*} [Field F] [IsAlgClosed F]
    {f : MvPolynomial (Fin 2) F}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    {r s t : Fin 2 →₀ ℕ}
    (hr : r ∈ f.support) (hs : s ∈ f.support) (ht : t ∈ f.support)
    (hdet : planeCurveSupportDifferenceDet r s t ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmF : (m : F) ≠ 0) (hnF : (n : F) ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) ≤
      (planeCurveSupportDifferenceDet r s t).natAbs := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  rw [finrank_poweredImageOverFirst_eq_imageField]
  exact finrank_poweredCoordinateImageField_le_supportDet_isAlgClosed
    hf hpartialFirst hpartialSecond hr hs ht hdet
      m n hm hn hmF hnF

/-- Exact-support index bound over arbitrary constants, obtained by the same
base-change descent as the public bidegree theorem. -/
theorem finrank_poweredImageOverFirst_le_supportDet_of_nonzero_natCast
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    {r s t : Fin 2 →₀ ℕ}
    (hr : r ∈ f.support) (hs : s ∈ f.support) (ht : t ∈ f.support)
    (hdet : planeCurveSupportDifferenceDet r s t ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmK : (m : K) ≠ 0) (hnK : (n : K) ≠ 0) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) ≤
      (planeCurveSupportDifferenceDet r s t).natAbs := by
  let A := AlgebraicClosure K
  let fA : MvPolynomial (Fin 2) A :=
    MvPolynomial.map (algebraMap K A) f
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  have hfA : Irreducible fA := habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : IsDomain (PlaneCurveCoordinateRing fA) :=
    planeCurveCoordinateRing_isDomain hfA
  have hpartialFirstA : MvPolynomial.pderiv 0 fA ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hzero
    apply hpartialFirst
    exact MvPolynomial.map_injective (algebraMap K A)
      (algebraMap K A).injective (by simpa using hzero)
  have hpartialSecondA : MvPolynomial.pderiv 1 fA ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hzero
    apply hpartialSecond
    exact MvPolynomial.map_injective (algebraMap K A)
      (algebraMap K A).injective (by simpa using hzero)
  have hsupp : fA.support = f.support :=
    MvPolynomial.support_map_of_injective f (algebraMap K A).injective
  have hrA : r ∈ fA.support := by rwa [hsupp]
  have hsA : s ∈ fA.support := by rwa [hsupp]
  have htA : t ∈ fA.support := by rwa [hsupp]
  have hmA : (m : A) ≠ 0 := by
    rw [← map_natCast (algebraMap K A)]
    simpa using (algebraMap K A).injective.ne hmK
  have hnA : (n : A) ≠ 0 := by
    rw [← map_natCast (algebraMap K A)]
    simpa using (algebraMap K A).injective.ne hnK
  have hindexBaseChange :
      Module.finrank (PoweredCoordinateImageField f m n)
          (PlaneCurveFunctionField f) =
        Module.finrank (PoweredCoordinateImageField fA m n)
          (PlaneCurveFunctionField fA) :=
    finrank_poweredCoordinateImageField_eq_baseChange
      (E := A) habsolute hf hpartialSecond m hm n
  change Module.finrank (PoweredImageOverFirst f m n)
      (PlaneCurveFunctionField f) ≤
    (planeCurveSupportDifferenceDet r s t).natAbs
  rw [finrank_poweredImageOverFirst_eq_imageField]
  calc
    Module.finrank (PoweredCoordinateImageField f m n)
        (PlaneCurveFunctionField f) =
      Module.finrank (PoweredCoordinateImageField fA m n)
        (PlaneCurveFunctionField fA) := hindexBaseChange
    _ ≤ (planeCurveSupportDifferenceDet r s t).natAbs :=
      finrank_poweredCoordinateImageField_le_supportDet_isAlgClosed
        hfA hpartialFirstA hpartialSecondA
          hrA hsA htA hdet m n hm hn hmA hnA

/-- Prime-to-characteristic powers satisfy the exact-support index bound. -/
theorem finrank_poweredImageOverFirst_le_supportDet
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p]
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    {r s t : Fin 2 →₀ ℕ}
    (hr : r ∈ f.support) (hs : s ∈ f.support) (ht : t ∈ f.support)
    (hdet : planeCurveSupportDifferenceDet r s t ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) ≤
      (planeCurveSupportDifferenceDet r s t).natAbs := by
  apply finrank_poweredImageOverFirst_le_supportDet_of_nonzero_natCast
    habsolute hpartialFirst hpartialSecond hr hs ht hdet
      m n hm hn
  · rwa [ne_eq, CharP.cast_eq_zero_iff K p]
  · rwa [ne_eq, CharP.cast_eq_zero_iff K p]

end

end BGS.CorvajaZannier
