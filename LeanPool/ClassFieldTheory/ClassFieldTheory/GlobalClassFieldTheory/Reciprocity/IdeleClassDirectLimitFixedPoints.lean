/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedPointDescent
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Abstract.KummerDelta
/-!
# Fixed points of the rational idele-class direct limit

The actual idele class group of a finite rational intermediate field is
identified with the corresponding fixed subgroup of the direct limit.
-/

@[expose] public section

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Scalar extension of a rational relative adele is fixed by every
absolute Galois element fixing the source field. -/
theorem
    rationalRelativeAdeleEmbedding_fixed_of_mem_fixingSubgroup
    {K : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K]
    {N : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (hKN : K ≤ (N :
      IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (hσ : σ ∈ K.fixingSubgroup)
    (z : RelativeAdeleRing ℚ K) :
    RelativeIdeleGroup.conjugation ℚ N
        (AlgEquiv.restrictNormalHom N σ)
        (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) z) =
      RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul,
        RelativeIdeleGroup.conjugation_tmul]
      congr 1
      apply Subtype.ext
      calc
        (((AlgEquiv.restrictNormalHom N σ)
              (IntermediateField.inclusion hKN x) : N) :
            SeparableClosure ℚ) =
            σ ((IntermediateField.inclusion hKN x : N) :
              SeparableClosure ℚ) :=
          AlgEquiv.restrictNormal_commutes σ N
            (IntermediateField.inclusion hKN x)
        _ = σ (x : SeparableClosure ℚ) := rfl
        _ = (x : SeparableClosure ℚ) :=
          (IntermediateField.mem_fixingSubgroup_iff K σ).1
            hσ x.1 x.2
        _ = ((IntermediateField.inclusion hKN x : N) :
            SeparableClosure ℚ) := rfl
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Scalar extension of a rational relative idele class is fixed by every
absolute Galois element fixing the source field. -/
theorem
    rationalRelativeIdeleClassEmbedding_fixed_of_mem_fixingSubgroup
    {K : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K]
    {N : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (hKN : K ≤ (N :
      IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (hσ : σ ∈ K.fixingSubgroup)
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN) c =
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup ℚ N)
        ((AlgEquiv.restrictNormalHom N σ) •
          RelativeIdeleGroup.ideleEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup ℚ N)
        (RelativeIdeleGroup.ideleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) a)
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ N))
  apply Units.ext
  exact
    rationalRelativeAdeleEmbedding_fixed_of_mem_fixingSubgroup
      hKN σ hσ (a : RelativeAdeleRing ℚ K)

/-- The map from an intermediate idele class group to the direct limit
intertwines compatible finite and absolute Galois actions. -/
theorem rationalIntermediateIdeleClassToDirectLimit_conjugation
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ E]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    σ • rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) =
      rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) (τ • c)) := by
  let N : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    rationalNormalClosure E
  let hEN : E ≤ (N : IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure E
  let : SMul
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ N) :=
    (rationalAbsoluteGaloisIdeleClassAction
      N).toSMul
  have hconjugation :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := N)
          (IntermediateField.inclusion hEN) c =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := N)
          (IntermediateField.inclusion hEN)
          (τ • c) :=
    (rationalRelativeIdeleClassEmbedding_conjugation_of_restrict
      hEN σ τ hστ c).symm
  have hlimit_smul
      (d : RelativeIdeleGroup.ClassGroup ℚ N) :
      σ • rationalRelativeIdeleClassToDirectLimit N d =
        rationalRelativeIdeleClassToDirectLimit N
          (σ • d) := by
    rfl
  calc
    σ • rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) =
      σ • rationalRelativeIdeleClassToDirectLimit N
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := N)
          (IntermediateField.inclusion hEN) c) := by
        convert congrArg (fun z => σ • z)
          (rationalIntermediateIdeleClassToDirectLimit_baseChange E c) using 1
        simp only [N, rationalNormalClosure]
        congr 4
    _ = rationalRelativeIdeleClassToDirectLimit N
        (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := N)
          (IntermediateField.inclusion hEN) c) :=
      hlimit_smul _
    _ = rationalRelativeIdeleClassToDirectLimit N
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := N)
          (IntermediateField.inclusion hEN)
          (τ • c)) :=
      congrArg
        (rationalRelativeIdeleClassToDirectLimit N)
        hconjugation
    _ = rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) (τ • c)) :=
      by
        convert
          (rationalIntermediateIdeleClassToDirectLimit_baseChange E (τ • c)).symm
            using 1
        simp only [N, rationalNormalClosure]
        congr 4

/-- Scalar extension intertwines the ambient automorphism with an induced field equivalence. -/
private theorem rationalRelativeIdeleClassEmbedding_ambientAlgEquiv
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ F]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (hEU : E ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (hFU : F ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) (e : E ≃ₐ[ℚ] F)
    (hσe : ∀ x : E, ((e x : F) : SeparableClosure ℚ) = σ (x : SeparableClosure ℚ))
    (cE : RelativeIdeleGroup.ClassGroup ℚ E) :
    σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
        (IntermediateField.inclusion hEU) cE =
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
        (IntermediateField.inclusion hFU) (relativeIdeleClassCongr (K := ℚ) e cE) := by
  let : MulDistribMulAction
      (U ≃ₐ[ℚ] U)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ U
  let : SMul
      (U ≃ₐ[ℚ] U)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    (RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ U).toSMul
  let : SMul
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    (rationalAbsoluteGaloisIdeleClassAction U).toSMul
  have hrestricted :
      (AlgEquiv.restrictNormalHom U σ) •
          RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          ((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
            (IntermediateField.inclusion hEU)) cE := by
    exact rationalRelativeIdeleClassEmbedding_smul_eq_classEmbedding hEU σ cE
  have hsmul :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          ((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
            (IntermediateField.inclusion hEU)) cE := by
    change (AlgEquiv.restrictNormalHom U σ) •
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
        ((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
          (IntermediateField.inclusion hEU)) cE
    exact hrestricted
  have hclass' :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
          (IntermediateField.inclusion hFU)
          (relativeIdeleClassCongr (K := ℚ) e cE) := by
    calc
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          ((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
            (IntermediateField.inclusion hEU)) cE :=
        hsmul
      _ = RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
          (IntermediateField.inclusion hFU)
          (relativeIdeleClassCongr (K := ℚ) e cE) := by
        rw [RelativeIdeleGroup.classEmbedding_relativeIdeleClassCongr]
        apply congrArg
          (fun f : E →ₐ[ℚ] U =>
            RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U) f cE)
        apply AlgHom.ext
        intro x
        apply Subtype.ext
        calc
          (((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
                (IntermediateField.inclusion hEU)) x :
              SeparableClosure ℚ) =
              σ (x : SeparableClosure ℚ) := by
            exact
              AlgEquiv.restrictNormal_commutes σ U
                (IntermediateField.inclusion hEU x)
          _ = ((e x : F) : SeparableClosure ℚ) :=
            (hσe x).symm
          _ =
              (((IntermediateField.inclusion hFU).comp
                e.toAlgHom) x : U) :=
            rfl
  exact hclass'

/-- The canonical direct-limit realization of idèle classes is natural
under an equivalence between two finite rational intermediate fields
which is induced by an automorphism of the rational separable closure. -/
theorem rationalIntermediateIdeleClassToDirectLimit_ambientAlgEquiv
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ F]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (e : E ≃ₐ[ℚ] F)
    (hσe : ∀ x : E,
      ((e x : F) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : IdeleClassGroup E) :
    σ • rationalIntermediateIdeleClassToDirectLimit E c =
      rationalIntermediateIdeleClassToDirectLimit F
        (ideleClassCongr e c) := by
  let U :
      FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    rationalNormalClosure E ⊔ rationalNormalClosure F
  let hEU :
      E ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)) :=
    (IntermediateField.le_normalClosure E).trans le_sup_left
  let hFU :
      F ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)) :=
    (IntermediateField.le_normalClosure F).trans le_sup_right
  let cE : RelativeIdeleGroup.ClassGroup ℚ E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E)).symm c
  let cF : RelativeIdeleGroup.ClassGroup ℚ F :=
    relativeIdeleClassCongr (K := ℚ) e cE
  let : MulDistribMulAction
      (U ≃ₐ[ℚ] U)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ U
  let : SMul
      (U ≃ₐ[ℚ] U)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    (RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ U).toSMul
  let : SMul
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    (rationalAbsoluteGaloisIdeleClassAction U).toSMul
  have hcF :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) cF =
        ideleClassCongr e c := by
    calc
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) cF =
        ideleClassCongr e
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E) cE) := by
        simpa only [cF] using
          (_root_.relativeIdeleClassBaseChangeMulEquiv_relativeIdeleClassCongr
            e cE)
      _ = ideleClassCongr e c := by
        simp only [cE,
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)).apply_symm_apply]
  have hE :
      rationalIntermediateIdeleClassToDirectLimit E c =
        rationalRelativeIdeleClassToDirectLimit U
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE) := by
    calc
      rationalIntermediateIdeleClassToDirectLimit E c =
          rationalIntermediateIdeleClassToDirectLimit E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E) cE) := by
        simp only [cE,
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)).apply_symm_apply]
      _ =
          rationalIntermediateIdeleClassToDirectLimit
            (U : IntermediateField ℚ (SeparableClosure ℚ))
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := U)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
                (IntermediateField.inclusion hEU) cE)) :=
        (rationalIntermediateIdeleClassToDirectLimit_extension
          hEU cE).symm
      _ =
          rationalRelativeIdeleClassToDirectLimit U
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
              (IntermediateField.inclusion hEU) cE) :=
        rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
          U (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE)
  have hF :
      rationalIntermediateIdeleClassToDirectLimit F
          (ideleClassCongr e c) =
        rationalRelativeIdeleClassToDirectLimit U
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
            (IntermediateField.inclusion hFU) cF) := by
    calc
      rationalIntermediateIdeleClassToDirectLimit F
          (ideleClassCongr e c) =
          rationalIntermediateIdeleClassToDirectLimit F
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) cF) := by
        rw [hcF]
      _ =
          rationalIntermediateIdeleClassToDirectLimit
            (U : IntermediateField ℚ (SeparableClosure ℚ))
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := U)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
                (IntermediateField.inclusion hFU) cF)) :=
        (rationalIntermediateIdeleClassToDirectLimit_extension
          hFU cF).symm
      _ =
          rationalRelativeIdeleClassToDirectLimit U
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
              (IntermediateField.inclusion hFU) cF) :=
        rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
          U (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
            (IntermediateField.inclusion hFU) cF)
  have hclass' := rationalRelativeIdeleClassEmbedding_ambientAlgEquiv
    U hEU hFU σ e hσe cE
  have hclass :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
          (IntermediateField.inclusion hFU) cF := by
    simpa only [cF] using hclass'
  have hlimit_smul :
      σ • rationalRelativeIdeleClassToDirectLimit U
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE) =
        rationalRelativeIdeleClassToDirectLimit U
          (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE) := by
    rfl
  calc
    σ • rationalIntermediateIdeleClassToDirectLimit E c =
      σ • rationalRelativeIdeleClassToDirectLimit U
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE) := by
      rw [hE]
    _ = rationalRelativeIdeleClassToDirectLimit U
        (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE) :=
      hlimit_smul
    _ = rationalRelativeIdeleClassToDirectLimit U
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
          (IntermediateField.inclusion hFU) cF) :=
      congrArg (rationalRelativeIdeleClassToDirectLimit U) hclass
    _ = rationalIntermediateIdeleClassToDirectLimit F
        (ideleClassCongr e c) :=
      hF.symm

/-- The image in the direct limit of an idele class over `K` is fixed by
the absolute Galois subgroup fixing `K`. -/
theorem rationalIntermediateIdeleClassToDirectLimit_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : IdeleClassGroup K)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (hσ : σ ∈ K.fixingSubgroup) :
    σ • rationalIntermediateIdeleClassToDirectLimit K c =
      rationalIntermediateIdeleClassToDirectLimit K c := by
  let N : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    rationalNormalClosure K
  let hKN : K ≤ (N : IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure K
  let : SMul
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ N) :=
    (rationalAbsoluteGaloisIdeleClassAction
      N).toSMul
  let d : RelativeIdeleGroup.ClassGroup ℚ K :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm c
  have hd :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) d = c := by
    simp only [d,
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := K)).apply_symm_apply]
  have hfixed :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d :=
    rationalRelativeIdeleClassEmbedding_fixed_of_mem_fixingSubgroup
      hKN σ hσ d
  have hlimit_smul :
      σ • rationalRelativeIdeleClassToDirectLimit N
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) d) =
        rationalRelativeIdeleClassToDirectLimit N
          (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) d) := by
    rfl
  calc
    σ • rationalIntermediateIdeleClassToDirectLimit K c =
      σ • rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) d) := by
        rw [hd]
    _ = σ • rationalRelativeIdeleClassToDirectLimit N
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d) := by
        convert congrArg (fun z => σ • z)
          (rationalIntermediateIdeleClassToDirectLimit_baseChange K d) using 1
        simp only [N, rationalNormalClosure]
        congr 4
    _ = rationalRelativeIdeleClassToDirectLimit N
        (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d) :=
      hlimit_smul
    _ = rationalRelativeIdeleClassToDirectLimit N
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d) :=
      congrArg
        (rationalRelativeIdeleClassToDirectLimit N) hfixed
    _ = rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) d) :=
      by
        convert
          (rationalIntermediateIdeleClassToDirectLimit_baseChange K d).symm
            using 1
        simp only [N, rationalNormalClosure]
        congr 4
    _ = rationalIntermediateIdeleClassToDirectLimit K c := by
      rw [hd]

/-- Additive idele classes map into the fixed subgroup of the rational
idele-class representation. -/
theorem rationalIntermediateIdeleClassToDirectLimit_mem_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : Additive (IdeleClassGroup K)) :
    MonoidHom.toAdditive
        (rationalIntermediateIdeleClassToDirectLimit K) c ∈
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) := by
  change
    (show rationalIdeleClassRepresentation from
      MonoidHom.toAdditive
        (rationalIntermediateIdeleClassToDirectLimit K) c) ∈
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
  rw [KummerTheory.mem_ambientFixedAddSubgroup_iff]
  intro σ
  change
    Additive.ofMul
        (σ.1 •
          rationalIntermediateIdeleClassToDirectLimit K
            (Additive.toMul c)) =
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit K
          (Additive.toMul c))
  exact congrArg Additive.ofMul
    (rationalIntermediateIdeleClassToDirectLimit_fixed
      K (Additive.toMul c) σ.1 σ.2)

/-- The canonical additive homomorphism from the idele class group of a
finite rational intermediate field to the corresponding fixed subgroup. -/
noncomputable def rationalIntermediateIdeleClassToFixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) :=
  (MonoidHom.toAdditive
      (rationalIntermediateIdeleClassToDirectLimit K)).codRestrict
    (KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ) K))
    (rationalIntermediateIdeleClassToDirectLimit_mem_fixed K)

/-- The canonical map from a finite rational idele class group to the
corresponding fixed subgroup is injective. -/
theorem rationalIntermediateIdeleClassToFixed_injective
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Function.Injective
      (rationalIntermediateIdeleClassToFixed K) := by
  intro a b hab
  have hlim :
      rationalIntermediateIdeleClassToDirectLimit K
          (Additive.toMul a) =
        rationalIntermediateIdeleClassToDirectLimit K
          (Additive.toMul b) := by
    exact congrArg
      (fun z :
          KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation
            (RamificationTheory.closedFixingSubgroup
              ℚ (SeparableClosure ℚ) K) =>
        Additive.toMul
          (z.1 : (rationalIdeleClassRepresentation).V))
      hab
  have hnormal :
      rationalIntermediateIdeleClassToNormalClosure K
          (Additive.toMul a) =
        rationalIntermediateIdeleClassToNormalClosure K
          (Additive.toMul b) :=
    (rationalRelativeIdeleClassToDirectLimit_injective
      (rationalNormalClosure K)) hlim
  have hrelative :
      (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K)).symm (Additive.toMul a) =
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K)).symm (Additive.toMul b) :=
    (rationalRelativeIdeleClassEmbedding_injective
      (IntermediateField.le_normalClosure K)) hnormal
  apply Additive.toMul.injective
  exact
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm.injective hrelative

/-- The canonical map from a finite rational idele class group to the
corresponding fixed subgroup is surjective. -/
theorem rationalIntermediateIdeleClassToFixed_surjective
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Function.Surjective
      (rationalIntermediateIdeleClassToFixed K) := by
  intro x
  let z : rationalIdeleClassDirectLimit :=
    Additive.toMul
      (x.1 : (rationalIdeleClassRepresentation).V)
  have hz_fixed
      (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (hσ : σ ∈ K.fixingSubgroup) :
      σ • z = z := by
    have hfixed := x.2 ⟨σ, hσ⟩
    change Additive.ofMul (σ • z) = Additive.ofMul z at hfixed
    exact Additive.ofMul.injective hfixed
  obtain ⟨q, hqz⟩ :=
    rationalDirectLimit_fixed_exists_ideleClass
      K z hz_fixed
  refine ⟨Additive.ofMul q, ?_⟩
  apply Subtype.ext
  change
    (show rationalIdeleClassRepresentation from
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit K q)) =
      x.1
  rw [hqz]
  exact
    ofMul_toMul
      (x.1 : Additive rationalIdeleClassDirectLimit)

/-- The subgroup of the absolute idele-class direct limit fixed by the
absolute Galois group over a finite rational intermediate field is
exactly that field's actual idele class group. -/
noncomputable def rationalIdeleClassEquivFixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Additive (IdeleClassGroup K) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) :=
  AddEquiv.ofBijective
    (rationalIntermediateIdeleClassToFixed K)
    ⟨rationalIntermediateIdeleClassToFixed_injective K,
      rationalIntermediateIdeleClassToFixed_surjective K⟩

end Reciprocity
end GlobalClassFieldTheory
