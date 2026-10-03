/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.FeedbackHomogeneous

/-!
# The normalized hard annihilator and second jet

For a first-jet seed `M ∧ E₀`, eight quintic rows determine the target
annihilator.  They force the last four Hankel coefficients to vanish, so the
annihilator is exactly `⟨E₀,E₁,E₂⟩`.  The bridge below is a fixed algebraic
matrix on coordinate vectors and target basis elements; no truth table or
circuit state is enumerated.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Eight quintic coordinates detecting the second-jet obstruction. -/
def hardQuinticCoord : Fin 8 → Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  ![(0,1,2,4,5), (0,1,2,4,6), (0,1,2,4,7), (0,1,3,4,7),
    (0,1,4,5,6), (0,1,4,5,7), (0,2,4,5,7), (0,3,4,5,7)]

/-- The squarefree monomial for a second-jet quintic coordinate. -/
def hardQuinticSet (u : Fin 8) : Finset (Fin 8) :=
  let c := hardQuinticCoord u
  {c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2}

/-- Extract the eight ANF coefficients used for the second-jet obstruction. -/
def hardQuinticProbeANF : ANF 8 →ₗ[F₂] (Fin 8 → F₂) where
  toFun p u := p.coeff ⟨hardQuinticSet u⟩
  map_add' p q := by funext u; simp
  map_smul' a p := by funext u; simp

/-- The second-jet quintic probes of a linear form, the zero-place form, and a target. -/
def hardQuinticWedgeProbe (M : LinearForm) (c : TargetCoeff) :
    Fin 8 → F₂ := fun u =>
  let r := hardQuinticCoord u
  wedgeThreeTwo (vectorWedgeTwo M (rationalPlaceTwo 0)) (targetTwo c)
    r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2

theorem hardQuinticProbeANF_eq_zero_of_degreeLE_four
    {p : ANF 8} (hp : DegreeLE 4 p) : hardQuinticProbeANF p = 0 := by
  funext u
  apply hp ⟨hardQuinticSet u⟩
  change 4 < (hardQuinticSet u).card
  have hc : (hardQuinticSet u).card = 5 := by
    fin_cases u <;> decide
  omega

private theorem coeff_monomial_mul_targetANF
    (s t : Finset (Fin 8)) (c : TargetCoeff) :
    (monomial s * targetANF c).coeff ⟨t⟩ =
      ∑ i : Fin 4, ∑ j : Fin 4,
        c (hankelIndex i j) *
          (if s ∪ targetPair i j = t then (1 : F₂) else 0) := by
  rw [targetANF_eq_double_sum]
  simp only [Finset.mul_sum, mul_smul_comm, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, monomial_mul, coeff_monomial]

private theorem hardQuinticProbe_coordinate (r : Fin 8) (t : Fin 7) :
    hardQuinticProbeANF
        ((linearANF (coordinateLinear r) *
          rationalANF (rationalSingleton 0)) *
          targetANF (targetBasis t)) =
      hardQuinticWedgeProbe (coordinateLinear r) (targetBasis t) := by
  rw [linearANF_coordinate, rationalANF_singleton_zero, mul_target_zero_anf]
  simp only [X, monomial_mul]
  funext u
  change (monomial _ * targetANF _).coeff ⟨hardQuinticSet u⟩ = _
  rw [coeff_monomial_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert r t u
  decide +kernel

/-- The second-jet quintic probes as a bilinear map in the linear form and target. -/
def hardQuinticWedgeProbeBilinear :
    LinearForm →ₗ[F₂] TargetCoeff →ₗ[F₂] (Fin 8 → F₂) where
  toFun M :=
    { toFun := hardQuinticWedgeProbe M
      map_add' := by
        intro c d
        funext u
        change wedgeThreeTwo
          (vectorWedgeTwo M (rationalPlaceTwo 0)) (targetTwo (c + d))
            (hardQuinticCoord u).1 (hardQuinticCoord u).2.1
            (hardQuinticCoord u).2.2.1 (hardQuinticCoord u).2.2.2.1
            (hardQuinticCoord u).2.2.2.2 = _
        rw [show targetTwo (c + d) = targetTwo c + targetTwo d by
          exact map_add targetTwoLinear c d]
        simp [hardQuinticWedgeProbe, wedgeThreeTwo]
        ring
      map_smul' := by
        intro a c
        funext u
        change wedgeThreeTwo
          (vectorWedgeTwo M (rationalPlaceTwo 0)) (targetTwo (a • c))
            (hardQuinticCoord u).1 (hardQuinticCoord u).2.1
            (hardQuinticCoord u).2.2.1 (hardQuinticCoord u).2.2.2.1
            (hardQuinticCoord u).2.2.2.2 = _
        rw [show targetTwo (a • c) = a • targetTwo c by
          exact map_smul targetTwoLinear a c]
        simp [hardQuinticWedgeProbe, wedgeThreeTwo]
        ring }
  map_add' M N := by
    apply LinearMap.ext
    intro c
    funext u
    change wedgeThreeTwo
      (vectorWedgeTwo (M + N) (rationalPlaceTwo 0)) (targetTwo c)
        (hardQuinticCoord u).1 (hardQuinticCoord u).2.1
        (hardQuinticCoord u).2.2.1 (hardQuinticCoord u).2.2.2.1
        (hardQuinticCoord u).2.2.2.2 = _
    rw [vectorWedgeTwo_add_left]
    simp [hardQuinticWedgeProbe, wedgeThreeTwo]
    ring
  map_smul' a M := by
    apply LinearMap.ext
    intro c
    funext u
    change wedgeThreeTwo
      (vectorWedgeTwo (a • M) (rationalPlaceTwo 0)) (targetTwo c)
        (hardQuinticCoord u).1 (hardQuinticCoord u).2.1
        (hardQuinticCoord u).2.2.1 (hardQuinticCoord u).2.2.2.1
        (hardQuinticCoord u).2.2.2.2 = _
    rw [vectorWedgeTwo_smul_left]
    simp [hardQuinticWedgeProbe, wedgeThreeTwo]
    ring

private theorem hardQuinticProbe_coordinate_target
    (r : Fin 8) (c : TargetCoeff) :
    hardQuinticProbeANF
        ((linearANF (coordinateLinear r) *
          rationalANF (rationalSingleton 0)) * targetANF c) =
      hardQuinticWedgeProbe (coordinateLinear r) c := by
  rw [targetANF]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul]
  calc
    (∑ t : Fin 7, c t • hardQuinticProbeANF
        ((linearANF (coordinateLinear r) *
          rationalANF (rationalSingleton 0)) * Mul 4 t)) =
        ∑ t : Fin 7, c t • hardQuinticWedgeProbe
          (coordinateLinear r) (targetBasis t) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← targetANF_targetBasis_feedback t,
        hardQuinticProbe_coordinate]
    _ = hardQuinticWedgeProbeBilinear (coordinateLinear r) c := by
      conv_rhs =>
        rw [← targetBasis_reconstruction c]
        simp only [map_sum, map_smul]
      rfl

/-- The selected ANF degree-five rows are the corresponding exterior rows
of the first-jet cubic against an arbitrary target word. -/
theorem hardQuinticProbe_linear_zeroPlace_target
    (M : LinearForm) (c : TargetCoeff) :
    hardQuinticProbeANF
        ((linearANF M * rationalANF (rationalSingleton 0)) * targetANF c) =
      hardQuinticWedgeProbe M c := by
  rw [linearANF]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
  calc
    (∑ r : Fin 8, M r • hardQuinticProbeANF
        ((X r * rationalANF (rationalSingleton 0)) * targetANF c)) =
        ∑ r : Fin 8, M r •
          hardQuinticWedgeProbe (coordinateLinear r) c := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← linearANF_coordinate r, hardQuinticProbe_coordinate_target]
    _ = hardQuinticWedgeProbeBilinear M c := by
      conv_rhs =>
        rw [linear_eq_sum_coordinate M]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl

private theorem hardAnnihilator_scalar_certificate :
    ∀ (pa pb ja jb : F₂) (c : TargetCoeff),
      (ja ≠ 0 ∨ jb ≠ 0) →
      hardQuinticWedgeProbe (normalizedFirstJetVector pa pb ja jb) c = 0 →
      c 3 = 0 ∧ c 4 = 0 ∧ c 5 = 0 ∧ c 6 = 0 := by
  intro pa pb ja jb c hjet hzero
  rcases f2_eq_zero_or_one ja with rfl | rfl <;>
    rcases f2_eq_zero_or_one jb with rfl | rfl
  · simp at hjet
  all_goals
    have h0 := congrFun hzero 0
    have h1 := congrFun hzero 1
    have h2 := congrFun hzero 2
    have h3 := congrFun hzero 3
    have h4 := congrFun hzero 4
    have h5 := congrFun hzero 5
    have h6 := congrFun hzero 6
    have h7 := congrFun hzero 7
    simp [hardQuinticWedgeProbe, hardQuinticCoord, wedgeThreeTwo, vectorWedgeTwo,
      rationalPlaceTwo, targetTwo, normalizedFirstJetVector, vectorWedge, placeA, placeB,
      ] at h0 h1 h2 h3 h4 h5 h6 h7
    aesop

/-- Eight fixed quintic rows reduce the annihilator of a nonzero normalized
first-jet seed to its first three Hankel coordinates. -/
theorem hardAnnihilator_rows_classify
    (pa pb ja jb : F₂) (c : TargetCoeff)
    (hjet : ja ≠ 0 ∨ jb ≠ 0)
    (hzero : hardQuinticWedgeProbe
      (normalizedFirstJetVector pa pb ja jb) c = 0) :
    c 3 = 0 ∧ c 4 = 0 ∧ c 5 = 0 ∧ c 6 = 0 :=
  hardAnnihilator_scalar_certificate pa pb ja jb c hjet hzero

theorem hardAnnihilator_classification
    (pa pb ja jb : F₂) (c : TargetCoeff)
    (hjet : ja ≠ 0 ∨ jb ≠ 0)
    (hzero : hardQuinticWedgeProbe
      (normalizedFirstJetVector pa pb ja jb) c = 0) :
    c = c 2 • targetBasis 2 + c 1 • targetBasis 1 +
      c 0 • targetBasis 0 := by
  rcases hardAnnihilator_rows_classify pa pb ja jb c hjet hzero with
    ⟨h3, h4, h5, h6⟩
  funext i
  fin_cases i <;>
    simp [targetBasis, Pi.basisFun, h3, h4, h5, h6]

/-- A hard annihilator outside the feedback state is exactly a second jet. -/
theorem hardAnnihilator_outside_feedback_is_secondJet
    (pa pb ja jb : F₂) (c : TargetCoeff)
    (hjet : ja ≠ 0 ∨ jb ≠ 0)
    (houtside : c ∉ feedbackCoeffSpace)
    (hzero : hardQuinticWedgeProbe
      (normalizedFirstJetVector pa pb ja jb) c = 0) :
    ∃ α β : F₂, c = secondJetFeedbackCoeff α β := by
  have hrep := hardAnnihilator_classification pa pb ja jb c hjet hzero
  rcases f2_eq_zero_or_one (c 2) with htwo | htwo
  · exfalso
    apply houtside
    rw [hrep, htwo, zero_smul, zero_add]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨1, by simp⟩)
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨0, by simp⟩)
  · refine ⟨c 1, c 0, ?_⟩
    calc
      c = c 2 • targetBasis 2 + c 1 • targetBasis 1 +
          c 0 • targetBasis 0 := hrep
      _ = secondJetFeedbackCoeff (c 1) (c 0) := by
        rw [htwo, one_smul]
        rfl

theorem degreeLE_two_of_mem_zeroFeedbackLowSpace {p : ANF 8}
    (hp : p ∈ zeroFeedbackLowSpace) : DegreeLE 2 p := by
  rcases exists_feedbackLow_rep hp with ⟨a, ell, q, rfl⟩
  exact (degreeLE_one_affineANF a ell).mono (by omega) |>.add
    (degreeLE_two_targetANF (feedbackCoeffRep q))

theorem anfThreeProjection_eq_zero_of_degreeLE_two
    {p : ANF 8} (hp : DegreeLE 2 p) : anfThreeProjection p = 0 := by
  funext i j k
  by_cases hcard : ({i, j, k} : Finset (Fin 8)).card = 3
  · change (if ({i, j, k} : Finset (Fin 8)).card = 3 then
      p.coeff ⟨{i, j, k}⟩ else 0) = 0
    rw [ite_eq_left hcard]
    exact hp _ (by simp [hcard])
  · simp [anfThreeProjection, hcard]

/-- Multiplication by a quadratic target sees only the cubic homogeneous
part in the selected hard rows. -/
theorem hardQuinticProbe_mul_target_congr_of_cubic
    {p q : ANF 8} (hp : DegreeLE 3 p) (hq : DegreeLE 3 q)
    (hcubic : anfThreeProjection p = anfThreeProjection q)
    (c : TargetCoeff) :
    hardQuinticProbeANF (p * targetANF c) =
      hardQuinticProbeANF (q * targetANF c) := by
  have hpqCubic : anfThreeProjection (p + q) = 0 := by
    rw [map_add, hcubic]
    funext i j k
    exact CharTwo.add_self_eq_zero _
  have hpqLow : DegreeLE 2 (p + q) :=
    degreeLE_two_of_degreeLE_three_of_cubic_zero (hp.add hq) hpqCubic
  have hprobe : hardQuinticProbeANF ((p + q) * targetANF c) = 0 :=
    hardQuinticProbeANF_eq_zero_of_degreeLE_four
      ((hpqLow.mul (degreeLE_two_targetANF c)).mono (by omega))
  rw [add_mul, map_add] at hprobe
  calc
    hardQuinticProbeANF (p * targetANF c) =
        (hardQuinticProbeANF (p * targetANF c) +
          hardQuinticProbeANF (q * targetANF c)) +
            hardQuinticProbeANF (q * targetANF c) := by
      symm
      rw [add_assoc]
      have hself : hardQuinticProbeANF (q * targetANF c) +
          hardQuinticProbeANF (q * targetANF c) = 0 := by
        funext u
        exact CharTwo.add_self_eq_zero _
      rw [hself, add_zero]
    _ = hardQuinticProbeANF (q * targetANF c) := by
      rw [hprobe]
      simp

/-- Degree five in a normalized seed absorption identity supplies the hard
annihilator equation used by the second-jet classification. -/
theorem normalizedSeed_absorption_hardAnnihilator
    {g correction addend : ANF 8}
    {M N : LinearForm} {fConst : F₂} {fLinear : LinearForm}
    {c : TargetCoeff}
    (hg : DegreeLE 3 g) (hcorrection : DegreeLE 2 correction)
    (haddend : DegreeLE 2 addend)
    (hseed : g + correction = linearANF M *
      (linearANF N + rationalANF (rationalSingleton 0)))
    (habsorb : (g + addend) *
      (affineANF fConst fLinear + targetANF c) =
        affineANF fConst fLinear + targetANF c) :
    hardQuinticWedgeProbe M c = 0 := by
  have hcorrectionCubic :=
    anfThreeProjection_eq_zero_of_degreeLE_two hcorrection
  have haddendCubic :=
    anfThreeProjection_eq_zero_of_degreeLE_two haddend
  have hseedProjection := congrArg anfThreeProjection hseed
  rw [map_add, hcorrectionCubic, add_zero, mul_add, map_add,
    anfThreeProjection_linear_mul_linear,
    anfThreeProjection_linear_mul_rational, zero_add] at hseedProjection
  let model := linearANF M * rationalANF (rationalSingleton 0)
  have hmodelDegree : DegreeLE 3 model := by
    have hlinear : DegreeLE 1 (linearANF M) := by
      simpa [affineANF] using degreeLE_one_affineANF 0 M
    exact hlinear.mul (degreeLE_two_rationalANF (rationalSingleton 0))
  have hmodelProjection : anfThreeProjection model =
      vectorWedgeTwo M (rationalTwo (rationalSingleton 0)) := by
    exact anfThreeProjection_linear_mul_rational M (rationalSingleton 0)
  have hgaDegree : DegreeLE 3 (g + addend) :=
    hg.add (haddend.mono (by omega))
  have hgaProjection : anfThreeProjection (g + addend) =
      anfThreeProjection model := by
    rw [map_add, haddendCubic, add_zero, hmodelProjection,
      hseedProjection]
  have hleftAffine : hardQuinticProbeANF
      ((g + addend) * affineANF fConst fLinear) = 0 :=
    hardQuinticProbeANF_eq_zero_of_degreeLE_four
      (by simpa using (hgaDegree.mul
        (degreeLE_one_affineANF fConst fLinear)))
  have hrightAffine : hardQuinticProbeANF
      (affineANF fConst fLinear) = 0 :=
    hardQuinticProbeANF_eq_zero_of_degreeLE_four
      ((degreeLE_one_affineANF fConst fLinear).mono (by omega))
  have hrightTarget : hardQuinticProbeANF (targetANF c) = 0 :=
    hardQuinticProbeANF_eq_zero_of_degreeLE_four
      ((degreeLE_two_targetANF c).mono (by omega))
  have hprobeIdentity := congrArg hardQuinticProbeANF habsorb
  simp only [mul_add, map_add] at hprobeIdentity
  rw [hleftAffine, hrightAffine, hrightTarget, zero_add, zero_add]
      at hprobeIdentity
  have hgaTarget : hardQuinticProbeANF
      ((g + addend) * targetANF c) = 0 := by
    simpa using hprobeIdentity
  have hcongr := hardQuinticProbe_mul_target_congr_of_cubic
    hgaDegree hmodelDegree hgaProjection c
  rw [hgaTarget] at hcongr
  change hardQuinticWedgeProbe M c = 0
  rw [← hardQuinticProbe_linear_zeroPlace_target]
  exact hcongr.symm

end

end N4
end UnrestrictedBooleanMul
