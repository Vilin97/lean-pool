/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions
public import LeanPool.CoarseGraining.Homogenization.PDE.HarmonicTranslation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient

/-! # Translation -/

@[expose] public section

namespace Homogenization

namespace BlockState

/-- Translate a block state by precomposing both components with `x ↦ x - z`. -/
def translate {d : ℕ} (X : BlockState d) (z : Vec d) : BlockState d :=
  { potential := fun x => X.potential (x - z)
    flux := fun x => X.flux (x - z) }

@[simp] theorem potential_translate {d : ℕ} (X : BlockState d) (z x : Vec d) :
    (X.translate z).potential x = X.potential (x - z) := rfl

@[simp] theorem flux_translate {d : ℕ} (X : BlockState d) (z x : Vec d) :
    (X.translate z).flux x = X.flux (x - z) := rfl

@[simp] theorem eval_translate {d : ℕ} (X : BlockState d) (z x : Vec d) :
    (X.translate z).eval x = X.eval (x - z) := rfl

end BlockState

theorem isBlockMuAdmissible_translateSet {d : ℕ} {U : Set (Vec d)} {P : BlockVec d}
    {X : BlockState d} (hX : IsBlockMuAdmissible U P X) (z : Vec d) :
    IsBlockMuAdmissible (translateSet z U) P (X.translate z) := by
  rcases hX with ⟨hpotL2, hpot, hsolL2, hsol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [BlockState.translate] using!
      hpotL2.comp_measurePreserving
        (measurePreserving_subRight_restrict_translateSet (d := d) z U)
  · simpa [BlockState.translate, sub_eq_add_neg, add_assoc] using
      isPotentialZeroTraceOn_translateSet (f := fun x => X.potential x - P.1) hpot z
  · simpa [BlockState.translate] using!
      hsolL2.comp_measurePreserving
        (measurePreserving_subRight_restrict_translateSet (d := d) z U)
  · simpa [BlockState.translate, sub_eq_add_neg, add_assoc] using
      isSolenoidalZeroNormalTraceOn_translateSet (g := fun x => X.flux x - P.2) hsol z

theorem blockEnergyDensity_translate_forward {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (z x : Vec d) :
    blockEnergyDensity a (X.translate z) (x + z) =
      blockEnergyDensity (translateCoeffField z a) X x := by
  have harg : (fun i => x i + z i) = x + z := rfl
  simp [BlockState.translate, BlockState.eval, blockEnergyDensity, blockCoeffField, translateCoeffField,
    sub_eq_add_neg, harg]

theorem blockEnergyDensity_translate_backward {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (z x : Vec d) :
    blockEnergyDensity (translateCoeffField z a) (X.translate (-z)) x =
      blockEnergyDensity a X (x + z) := by
  have harg : (fun i => x i + z i) = x + z := rfl
  simp [BlockState.translate, BlockState.eval, blockEnergyDensity, blockCoeffField, translateCoeffField,
    sub_eq_add_neg, harg]

theorem volumeAverage_blockEnergyDensity_translate_forward {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (X : BlockState d) :
    volumeAverage (translateSet z U) (blockEnergyDensity a (X.translate z)) =
      volumeAverage U (blockEnergyDensity (translateCoeffField z a) X) := by
  unfold volumeAverage
  rw [volume_translateSet_eq]
  congr 1
  calc
    ∫ x in translateSet z U, blockEnergyDensity a (X.translate z) x ∂MeasureTheory.volume
      = ∫ y in U, blockEnergyDensity a (X.translate z) (y + z) ∂MeasureTheory.volume := by
          symm
          exact setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
            (blockEnergyDensity a (X.translate z))
    _ = ∫ y in U, blockEnergyDensity (translateCoeffField z a) X y
          ∂MeasureTheory.volume := by
            congr with y
            simpa using blockEnergyDensity_translate_forward a X z y

theorem volumeAverage_blockEnergyDensity_translate_backward {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (X : BlockState d) :
    volumeAverage U (blockEnergyDensity (translateCoeffField z a) (X.translate (-z))) =
      volumeAverage (translateSet z U) (blockEnergyDensity a X) := by
  unfold volumeAverage
  rw [volume_translateSet_eq]
  congr 1
  calc
    ∫ x in U, blockEnergyDensity (translateCoeffField z a) (X.translate (-z)) x
        ∂MeasureTheory.volume
      = ∫ x in U, blockEnergyDensity a X (x + z) ∂MeasureTheory.volume := by
          congr with x
          simpa using blockEnergyDensity_translate_backward a X z x
    _ = ∫ y in translateSet z U, blockEnergyDensity a X y ∂MeasureTheory.volume :=
          setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
            (blockEnergyDensity a X)

theorem muValueSet_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) :
    muValueSet (translateSet z U) P a = muValueSet U P (translateCoeffField z a) := by
  ext m
  constructor
  · rintro ⟨X, hX, hm⟩
    refine ⟨X.translate (-z), ?_, ?_⟩
    · have hX' :
          IsBlockMuAdmissible (translateSet (-z) (translateSet z U)) P (X.translate (-z)) :=
        isBlockMuAdmissible_translateSet (U := translateSet z U) (P := P) (X := X) hX (-z)
      simpa [translateSet_translateSet, BlockState.translate] using hX'
    · calc
        m = volumeAverage (translateSet z U) (blockEnergyDensity a X) := hm
        _ = volumeAverage U (blockEnergyDensity (translateCoeffField z a) (X.translate (-z))) := by
              symm
              exact volumeAverage_blockEnergyDensity_translate_backward z U a X
  · rintro ⟨X, hX, hm⟩
    refine ⟨X.translate z, isBlockMuAdmissible_translateSet (P := P) (X := X) hX z, ?_⟩
    calc
      m = volumeAverage U (blockEnergyDensity (translateCoeffField z a) X) := hm
      _ = volumeAverage (translateSet z U) (blockEnergyDensity a (X.translate z)) := by
            symm
            exact volumeAverage_blockEnergyDensity_translate_forward z U a X

theorem Mu_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) :
    Mu (translateSet z U) P a = Mu U P (translateCoeffField z a) := by
  unfold Mu
  rw [muValueSet_translateSet z U P a]

theorem coarseBlockMatrix_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    coarseBlockMatrix (translateSet z U) a =
      coarseBlockMatrix U (translateCoeffField z a) := by
  apply coarseBlockMatrix_eq_of_mu_eq
  intro P
  exact Mu_translateSet_eq_translateCoeffField z U P a

theorem isCoarseBlockMatrix_translateSet_iff {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (Abar : BlockMat d) :
    IsCoarseBlockMatrix (translateSet z U) a Abar ↔
      IsCoarseBlockMatrix U (translateCoeffField z a) Abar := by
  constructor
  · rintro ⟨hSymm, hMu⟩
    refine ⟨hSymm, ?_⟩
    intro P
    simpa [Mu_translateSet_eq_translateCoeffField z U P a] using hMu P
  · rintro ⟨hSymm, hMu⟩
    refine ⟨hSymm, ?_⟩
    intro P
    simpa [Mu_translateSet_eq_translateCoeffField z U P a] using hMu P

theorem hasQuadraticMu_translateSet_iff {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    HasQuadraticMu (translateSet z U) a ↔
      HasQuadraticMu U (translateCoeffField z a) := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro P
    simpa [Mu_translateSet_eq_translateCoeffField z U P a] using hQ P
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro P
    simpa [Mu_translateSet_eq_translateCoeffField z U P a] using hQ P

theorem isBlockPotentialOn_translateSet {d : ℕ} {U : Set (Vec d)}
    {X : BlockState d} (hX : IsBlockPotentialOn U X) (z : Vec d) :
    IsBlockPotentialOn (translateSet z U) (X.translate z) :=
  isPotentialOn_translateSet hX z

theorem isBlockSolenoidalOn_translateSet {d : ℕ} {U : Set (Vec d)}
    {X : BlockState d} (hX : IsBlockSolenoidalOn U X) (z : Vec d) :
    IsBlockSolenoidalOn (translateSet z U) (X.translate z) :=
  isSolenoidalOn_translateSet hX z

theorem isBlockTestOn_translateSet {d : ℕ} {U : Set (Vec d)}
    {X : BlockState d} (hX : IsBlockTestOn U X) (z : Vec d) :
    IsBlockTestOn (translateSet z U) (X.translate z) :=
  ⟨isPotentialZeroTraceOn_translateSet hX.1 z,
    isSolenoidalZeroNormalTraceOn_translateSet hX.2 z⟩

theorem blockResponseIntegrand_translate_forward {d : ℕ}
    (a : CoeffField d) (P Q : BlockVec d) (X : BlockState d) (z x : Vec d) :
    blockResponseIntegrand a P Q (X.translate z) (x + z) =
      blockResponseIntegrand (translateCoeffField z a) P Q X x := by
  have harg : (fun i => x i + z i) = x + z := rfl
  simp [blockResponseIntegrand, blockEnergyDensity, BlockState.translate, BlockState.eval,
    blockCoeffField, translateCoeffField, sub_eq_add_neg, harg]

theorem volumeAverage_blockResponseIntegrand_translate_forward {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (P Q : BlockVec d)
    (X : BlockState d) :
    volumeAverage (translateSet z U) (blockResponseIntegrand a P Q (X.translate z)) =
      volumeAverage U (blockResponseIntegrand (translateCoeffField z a) P Q X) := by
  unfold volumeAverage
  rw [volume_translateSet_eq]
  congr 1
  calc
    ∫ x in translateSet z U, blockResponseIntegrand a P Q (X.translate z) x
        ∂MeasureTheory.volume
      = ∫ y in U, blockResponseIntegrand a P Q (X.translate z) (y + z)
          ∂MeasureTheory.volume := by
            symm
            exact setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
              (blockResponseIntegrand a P Q (X.translate z))
    _ = ∫ y in U, blockResponseIntegrand (translateCoeffField z a) P Q X y
        ∂MeasureTheory.volume := by
          congr with y
          simpa using blockResponseIntegrand_translate_forward a P Q X z y

theorem blockResponseSpace_translateSet {d : ℕ} (z : Vec d) {U : Set (Vec d)}
    {a : CoeffField d} {X : BlockState d}
    (hX : BlockResponseSpace (translateCoeffField z a) U X) :
    BlockResponseSpace a (translateSet z U) (X.translate z) := by
  refine ⟨isBlockPotentialOn_translateSet hX.1 z,
    isBlockSolenoidalOn_translateSet hX.2.1 z, ?_⟩
  intro Y hY
  have hY' : IsBlockTestOn U (Y.translate (-z)) := by
    have hYtranslate :
        IsBlockTestOn (translateSet (-z) (translateSet z U)) (Y.translate (-z)) :=
      isBlockTestOn_translateSet hY (-z)
    simpa [translateSet_translateSet, BlockState.translate] using hYtranslate
  have htest := hX.2.2 (Y.translate (-z)) hY'
  let F : Vec d → ℝ := fun x =>
    blockVecDot (Y.eval x)
      (blockMatVecMul (blockCoeffField a x) ((X.translate z).eval x))
  have hchange :
      ∫ y in U, F (y + z) ∂MeasureTheory.volume =
        ∫ x in translateSet z U, F x ∂MeasureTheory.volume :=
    setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U F
  have hpoint :
      (fun y : Vec d => F (y + z)) =
        fun y : Vec d =>
          blockVecDot ((Y.translate (-z)).eval y)
            (blockMatVecMul (blockCoeffField (translateCoeffField z a) y) (X.eval y)) := by
    funext y
    have harg : (fun i => y i + z i) = y + z := rfl
    simp [F, BlockState.translate, BlockState.eval, blockCoeffField, translateCoeffField,
      sub_eq_add_neg, harg]
  calc
    ∫ x in translateSet z U,
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x) ((X.translate z).eval x))
          ∂MeasureTheory.volume
      = ∫ x in translateSet z U, F x ∂MeasureTheory.volume := rfl
    _ = ∫ y in U, F (y + z) ∂MeasureTheory.volume := hchange.symm
    _ = ∫ y in U,
        blockVecDot ((Y.translate (-z)).eval y)
          (blockMatVecMul (blockCoeffField (translateCoeffField z a) y) (X.eval y))
          ∂MeasureTheory.volume := by rw [hpoint]
    _ = 0 := htest

theorem blockResponseIntegrabilityData_translateSet {d : ℕ} (z : Vec d) {U : Set (Vec d)}
    {a : CoeffField d} {X : BlockState d}
    (hX : BlockResponseIntegrabilityData U (translateCoeffField z a) X) :
    BlockResponseIntegrabilityData (translateSet z U) a (X.translate z) := by
  refine ⟨?_, ?_⟩
  · simpa [BlockState.translate] using!
      hX.flux_memL2.comp_measurePreserving
        (measurePreserving_subRight_restrict_translateSet (d := d) z U)
  · have hInt :
        MeasureTheory.Integrable
          (fun x : Vec d => blockEnergyDensity (translateCoeffField z a) X (x - z))
          (volumeMeasureOn (translateSet z U)) := by
      have hBase :
          MeasureTheory.MemLp (blockEnergyDensity (translateCoeffField z a) X) 1
            (volumeMeasureOn U) := by
        rw [MeasureTheory.memLp_one_iff_integrable]
        simpa [MeasureTheory.IntegrableOn] using hX.energyIntegrable
      exact MeasureTheory.memLp_one_iff_integrable.mp
        (hBase.comp_measurePreserving
          (measurePreserving_subRight_restrict_translateSet (d := d) z U))
    have hEq :
        (fun x : Vec d => blockEnergyDensity (translateCoeffField z a) X (x - z)) =
          blockEnergyDensity a (X.translate z) := by
      funext x
      simp [blockEnergyDensity, BlockState.translate, BlockState.eval, blockCoeffField,
        translateCoeffField, sub_eq_add_neg]
    simpa [MeasureTheory.IntegrableOn, hEq] using hInt

theorem blockJValueSet_subset_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (P Q : BlockVec d) (a : CoeffField d) :
    blockJValueSet U P Q (translateCoeffField z a) ⊆
      blockJValueSet (translateSet z U) P Q a := by
  rintro m ⟨X, hX, hInt, hm⟩
  refine ⟨X.translate z, blockResponseSpace_translateSet z hX,
    blockResponseIntegrabilityData_translateSet z hInt, ?_⟩
  calc
    m = volumeAverage U (blockResponseIntegrand (translateCoeffField z a) P Q X) := hm
    _ = volumeAverage (translateSet z U) (blockResponseIntegrand a P Q (X.translate z)) := by
          symm
          exact volumeAverage_blockResponseIntegrand_translate_forward z U a P Q X

theorem blockJValueSet_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (P Q : BlockVec d) (a : CoeffField d) :
    blockJValueSet (translateSet z U) P Q a =
      blockJValueSet U P Q (translateCoeffField z a) := by
  ext m
  constructor
  · intro hm
    have hsub :=
      blockJValueSet_subset_translateSet (-z) (translateSet z U) P Q (translateCoeffField z a)
    have hm' :
        m ∈ blockJValueSet (translateSet z U) P Q
          (translateCoeffField (-z) (translateCoeffField z a)) := by
      simpa using hm
    simpa [translateSet_translateSet] using hsub hm'
  · intro hm
    exact blockJValueSet_subset_translateSet z U P Q a hm

theorem BlockJ_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (P Q : BlockVec d) (a : CoeffField d) :
    BlockJ (translateSet z U) P Q a =
      BlockJ U P Q (translateCoeffField z a) := by
  rw [BlockJ, BlockJ, blockJValueSet_translateSet z U P Q a]

theorem scalarResponseIntegrand_translate_forward {d : ℕ}
    (a : CoeffField d) (p q : Vec d) {U : Set (Vec d)}
    (z : Vec d) (u : AHarmonicFunction (translateCoeffField z a) U) (x : Vec d) :
    scalarResponseIntegrand (translateSet z U) a p q (AHarmonicFunction.translate z u) (x + z) =
      scalarResponseIntegrand U (translateCoeffField z a) p q u x := by
  have harg : (fun i => x i + z i) = x + z := rfl
  simp [scalarResponseIntegrand, AHarmonicFunction.translate, H1Function.translate,
    translateCoeffField, sub_eq_add_neg, add_assoc, harg]

theorem volumeAverage_scalarResponseIntegrand_translate_forward {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d)
    (u : AHarmonicFunction (translateCoeffField z a) U) :
    volumeAverage (translateSet z U)
      (scalarResponseIntegrand (translateSet z U) a p q (AHarmonicFunction.translate z u)) =
      volumeAverage U (scalarResponseIntegrand U (translateCoeffField z a) p q u) := by
  unfold volumeAverage
  rw [volume_translateSet_eq]
  congr 1
  calc
    ∫ x in translateSet z U,
        scalarResponseIntegrand (translateSet z U) a p q (AHarmonicFunction.translate z u) x
          ∂MeasureTheory.volume
      = ∫ y in U,
          scalarResponseIntegrand (translateSet z U) a p q (AHarmonicFunction.translate z u) (y + z)
            ∂MeasureTheory.volume := by
              symm
              exact setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
                (scalarResponseIntegrand (translateSet z U) a p q (AHarmonicFunction.translate z u))
    _ = ∫ y in U, scalarResponseIntegrand U (translateCoeffField z a) p q u y
          ∂MeasureTheory.volume := by
            congr with y
            simpa using scalarResponseIntegrand_translate_forward a p q z u y

theorem responseJValueSet_subset_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d) :
    responseJValueSet U p q (translateCoeffField z a) ⊆
      responseJValueSet (translateSet z U) p q a := by
  rintro m ⟨u, hm⟩
  refine ⟨AHarmonicFunction.translate z u, ?_⟩
  calc
    m = volumeAverage U (scalarResponseIntegrand U (translateCoeffField z a) p q u) := hm
    _ = volumeAverage (translateSet z U)
          (scalarResponseIntegrand (translateSet z U) a p q (AHarmonicFunction.translate z u)) := by
            symm
            exact volumeAverage_scalarResponseIntegrand_translate_forward z U a p q u

theorem responseJValueSet_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d) :
    responseJValueSet (translateSet z U) p q a =
      responseJValueSet U p q (translateCoeffField z a) := by
  ext m
  constructor
  · intro hm
    have hsub :=
      responseJValueSet_subset_translateSet (-z) (translateSet z U) p q (translateCoeffField z a)
    have hm' :
        m ∈ responseJValueSet (translateSet z U) p q
          (translateCoeffField (-z) (translateCoeffField z a)) := by
      simpa using hm
    simpa [translateSet_translateSet] using hsub hm'
  · intro hm
    exact responseJValueSet_subset_translateSet z U p q a hm

theorem ResponseJ_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d) :
    ResponseJ (translateSet z U) p q a =
      ResponseJ U p q (translateCoeffField z a) := by
  rw [ResponseJ, ResponseJ, responseJValueSet_translateSet z U p q a]

theorem sigmaStarInvCoarse_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    sigmaStarInvCoarse (translateSet z U) a =
      sigmaStarInvCoarse U (translateCoeffField z a) := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [ResponseJ_translateSet_eq_translateCoeffField]
  · simp [sigmaStarInvCoarse_apply_of_ne, hij, ResponseJ_translateSet_eq_translateCoeffField]

theorem sigmaStarCoarse_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    sigmaStarCoarse (translateSet z U) a =
      sigmaStarCoarse U (translateCoeffField z a) := by
  simp [sigmaStarCoarse, sigmaStarInvCoarse_translateSet_eq_translateCoeffField]

theorem sigmaStarInvKappaCoarse_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    sigmaStarInvKappaCoarse (translateSet z U) a =
      sigmaStarInvKappaCoarse U (translateCoeffField z a) := by
  funext i j
  simp [sigmaStarInvKappaCoarse, ResponseJ_translateSet_eq_translateCoeffField]

theorem kappaCoarse_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    kappaCoarse (translateSet z U) a =
      kappaCoarse U (translateCoeffField z a) := by
  simp [kappaCoarse, sigmaStarCoarse_translateSet_eq_translateCoeffField,
    sigmaStarInvKappaCoarse_translateSet_eq_translateCoeffField]

theorem sigmaCorrectedResponse_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (p : Vec d) :
    sigmaCorrectedResponse (translateSet z U) a p =
      sigmaCorrectedResponse U (translateCoeffField z a) p := by
  simp [sigmaCorrectedResponse, ResponseJ_translateSet_eq_translateCoeffField,
    sigmaStarInvCoarse_translateSet_eq_translateCoeffField,
    kappaCoarse_translateSet_eq_translateCoeffField]

theorem sigmaCoarse_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    sigmaCoarse (translateSet z U) a =
      sigmaCoarse U (translateCoeffField z a) := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [sigmaCorrectedResponse_translateSet_eq_translateCoeffField]
  · simp [sigmaCoarse_apply_of_ne, hij,
      sigmaCorrectedResponse_translateSet_eq_translateCoeffField]

theorem bCoarse_translateSet_eq_translateCoeffField {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    bCoarse (sigmaCoarse (translateSet z U) a)
        (sigmaStarCoarse (translateSet z U) a)
        (kappaCoarse (translateSet z U) a) =
      bCoarse (sigmaCoarse U (translateCoeffField z a))
        (sigmaStarCoarse U (translateCoeffField z a))
        (kappaCoarse U (translateCoeffField z a)) := by
  simp [sigmaCoarse_translateSet_eq_translateCoeffField,
    sigmaStarCoarse_translateSet_eq_translateCoeffField,
    kappaCoarse_translateSet_eq_translateCoeffField]

theorem isSigmaStarCoarse_translateSet_iff {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (sigmaStar : Mat d) :
    IsSigmaStarCoarse (translateSet z U) a sigmaStar ↔
      IsSigmaStarCoarse U (translateCoeffField z a) sigmaStar := by
  constructor
  · rintro ⟨hSymm, hResp⟩
    refine ⟨hSymm, ?_⟩
    intro q
    simpa [ResponseJ_translateSet_eq_translateCoeffField z U 0 q a] using hResp q
  · rintro ⟨hSymm, hResp⟩
    refine ⟨hSymm, ?_⟩
    intro q
    simpa [ResponseJ_translateSet_eq_translateCoeffField z U 0 q a] using hResp q

theorem isKappaCoarse_translateSet_iff {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (sigmaStar kappa : Mat d) :
    IsKappaCoarse (translateSet z U) a sigmaStar kappa ↔
      IsKappaCoarse U (translateCoeffField z a) sigmaStar kappa := by
  constructor
  · intro hK p q
    simpa [ResponseJ_translateSet_eq_translateCoeffField z U p q a,
      ResponseJ_translateSet_eq_translateCoeffField z U p 0 a,
      ResponseJ_translateSet_eq_translateCoeffField z U 0 q a] using hK p q
  · intro hK p q
    simpa [ResponseJ_translateSet_eq_translateCoeffField z U p q a,
      ResponseJ_translateSet_eq_translateCoeffField z U p 0 a,
      ResponseJ_translateSet_eq_translateCoeffField z U 0 q a] using hK p q

theorem isSigmaCoarse_translateSet_iff {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) (sigma sigmaStar kappa : Mat d) :
    IsSigmaCoarse (translateSet z U) a sigma sigmaStar kappa ↔
      IsSigmaCoarse U (translateCoeffField z a) sigma sigmaStar kappa := by
  constructor
  · rintro ⟨hSymm, hResp⟩
    refine ⟨hSymm, ?_⟩
    intro p
    simpa [ResponseJ_translateSet_eq_translateCoeffField z U p 0 a,
      ResponseJ_translateSet_eq_translateCoeffField z U 0 (matVecMul kappa p) a] using hResp p
  · rintro ⟨hSymm, hResp⟩
    refine ⟨hSymm, ?_⟩
    intro p
    simpa [ResponseJ_translateSet_eq_translateCoeffField z U p 0 a,
      ResponseJ_translateSet_eq_translateCoeffField z U 0 (matVecMul kappa p) a] using hResp p

theorem responseJ_blockQuadratic_translateSet_iff {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (a : CoeffField d) :
    (∀ p q : Vec d,
        ResponseJ (translateSet z U) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (translateSet z U) a) (-p, q)) -
              vecDot p q) ↔
      (∀ p q : Vec d,
        ResponseJ U p q (translateCoeffField z a) =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix U (translateCoeffField z a)) (-p, q)) -
              vecDot p q) := by
  constructor
  · intro hResp p q
    simpa [ResponseJ_translateSet_eq_translateCoeffField z U p q a,
      coarseBlockMatrix_translateSet_eq_translateCoeffField z U a] using hResp p q
  · intro hResp p q
    simpa [ResponseJ_translateSet_eq_translateCoeffField z U p q a,
      coarseBlockMatrix_translateSet_eq_translateCoeffField z U a] using hResp p q

end Homogenization
