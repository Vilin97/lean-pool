/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.HilbertMinimization
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas
public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
public import LeanPool.CoarseGraining.Homogenization.PDE.HarmonicCube
public import LeanPool.CoarseGraining.Homogenization.PDE.HarmonicHilbert

/-! # Existence -/

@[expose] public section

namespace Homogenization

noncomputable section

namespace AHarmonicGradientHilbert

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}

private theorem memVectorL2_const [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (p : Vec d) : MemVectorL2 U (fun _ : Vec d => p) := by
  simpa using
    (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := p))

/-- The linear response functional
`F ↦ ∫_U q·F - p·aF` on the closed `A`-harmonic-gradient Hilbert space. -/
noncomputable def responseFunctionalCLM
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (M : PotentialSolenoidalL2Data U) (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d) :
    Space (U := U) (a := a) M hEll →L[ℝ] ℝ :=
  ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
      (toHilbertVectorL2OfVecField (memVectorL2_const (U := U) q))).comp
    (fieldCLM (U := U) (a := a) M hEll)) -
    ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
        (toHilbertVectorL2OfVecField (memVectorL2_const (U := U) p))).comp
      ((hilbertCoeffOperator hEll).comp (fieldCLM (U := U) (a := a) M hEll)))

theorem responseFunctionalCLM_apply_eq_integral
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {M : PotentialSolenoidalL2Data U} {hEll : IsEllipticFieldOn lam Lam U a}
    (p q : Vec d) (z : Space (U := U) (a := a) M hEll) :
    responseFunctionalCLM (U := U) (a := a) M hEll p q z =
      ∫ x in U,
        (vecDot q (vectorField z x) -
          vecDot p (matVecMul (a x) (vectorField z x))) ∂MeasureTheory.volume := by
  let hqMem : MemVectorL2 U (fun _ : Vec d => q) := memVectorL2_const (U := U) q
  let hpMem : MemVectorL2 U (fun _ : Vec d => p) := memVectorL2_const (U := U) p
  have hqInt :
      MeasureTheory.IntegrableOn (fun x => vecDot q (vectorField z x)) U := by
    simpa using
      integrableOn_vecDot_of_memVectorL2 hqMem (MeasureTheory.Lp.memLp (vectorField z))
  have hpInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot p (matVecMul (a x) (vectorField z x))) U := by
    simpa using
      integrableOn_vecDot_of_memVectorL2 hpMem
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
          (MeasureTheory.Lp.memLp (vectorField z)))
  have hq :
      ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
          (toHilbertVectorL2OfVecField hqMem)).comp
        (fieldCLM (U := U) (a := a) M hEll)) z =
        ∫ x in U, vecDot q (vectorField z x) ∂MeasureTheory.volume := by
    calc
      ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
          (toHilbertVectorL2OfVecField hqMem)).comp
        (fieldCLM (U := U) (a := a) M hEll)) z
          = inner ℝ (toHilbertVectorL2OfVecField hqMem) (field z) := by
              simp [field]
      _ =
          inner ℝ
            (toHilbertVectorL2OfVecField hqMem)
            (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z))) := by
              rw [field_eq_toHilbertVectorL2OfVecField z]
      _ = ∫ x in U, vecDot q (vectorField z x) ∂MeasureTheory.volume := by
            simpa using
              inner_toHilbertVectorL2OfVecField_eq_integral
                (U := U) hqMem (MeasureTheory.Lp.memLp (vectorField z))
  have hA :
      hilbertCoeffOperator hEll (field z) =
        toHilbertVectorL2OfVecField
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
            (MeasureTheory.Lp.memLp (vectorField z))) := by
    rw [field_eq_toHilbertVectorL2OfVecField z]
    exact
      hilbertCoeffOperator_toHilbertVectorL2OfVecField
        (U := U) (a := a) (lam := lam) (Lam := Lam) hEll
        (MeasureTheory.Lp.memLp (vectorField z))
  have hp :
      ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
          (toHilbertVectorL2OfVecField hpMem)).comp
        ((hilbertCoeffOperator hEll).comp (fieldCLM (U := U) (a := a) M hEll))) z =
        ∫ x in U, vecDot p (matVecMul (a x) (vectorField z x))
          ∂MeasureTheory.volume := by
    calc
      ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
          (toHilbertVectorL2OfVecField hpMem)).comp
        ((hilbertCoeffOperator hEll).comp (fieldCLM (U := U) (a := a) M hEll))) z
          = inner ℝ
              (toHilbertVectorL2OfVecField hpMem)
              (hilbertCoeffOperator hEll (field z)) := by
              simp [field]
      _ =
          inner ℝ
            (toHilbertVectorL2OfVecField hpMem)
            (toHilbertVectorL2OfVecField
              (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
                (MeasureTheory.Lp.memLp (vectorField z)))) := by
              rw [hA]
      _ =
          ∫ x in U, vecDot p (matVecMul (a x) (vectorField z x))
            ∂MeasureTheory.volume := by
            simpa using
              inner_toHilbertVectorL2OfVecField_eq_integral
                (U := U) hpMem
                (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
                  (MeasureTheory.Lp.memLp (vectorField z)))
  calc
    responseFunctionalCLM (U := U) (a := a) M hEll p q z
        =
          ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
              (toHilbertVectorL2OfVecField hqMem)).comp
            (fieldCLM (U := U) (a := a) M hEll)) z -
            ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
                (toHilbertVectorL2OfVecField hpMem)).comp
              ((hilbertCoeffOperator hEll).comp (fieldCLM (U := U) (a := a) M hEll))) z := by
            rfl
    _ =
        (∫ x in U, vecDot q (vectorField z x) ∂MeasureTheory.volume) -
          ∫ x in U, vecDot p (matVecMul (a x) (vectorField z x))
            ∂MeasureTheory.volume := by
          rw [hq, hp]
    _ =
        ∫ x in U,
          (vecDot q (vectorField z x) -
            vecDot p (matVecMul (a x) (vectorField z x))) ∂MeasureTheory.volume := by
          symm
          exact MeasureTheory.integral_sub hqInt hpInt

/-- The Hilbert-space stationary point for the scalar response functional. -/
noncomputable def responseStationaryGradient
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (M : PotentialSolenoidalL2Data U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d) :
    Space (U := U) (a := a) M hEll :=
  linearQuadraticResponseMaximizer
    (symmCoeffBilin (U := U) (a := a) M hEll)
    (isCoercive_symmCoeffBilin (U := U) (a := a) (M := M) hne hEll)
    (responseFunctionalCLM (U := U) (a := a) M hEll p q)

theorem responseStationaryGradient_firstVariation
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {M : PotentialSolenoidalL2Data U} (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d)
    (w : Space (U := U) (a := a) M hEll) :
    symmCoeffBilin (U := U) (a := a) M hEll
        (responseStationaryGradient (U := U) (a := a) M hne hEll p q) w =
      responseFunctionalCLM (U := U) (a := a) M hEll p q w := by
  exact
    linearQuadraticResponseMaximizer_firstVariation
      (symmCoeffBilin (U := U) (a := a) M hEll)
      (isCoercive_symmCoeffBilin (U := U) (a := a) (M := M) hne hEll)
      (responseFunctionalCLM (U := U) (a := a) M hEll p q) w

/-- Recover the Hilbert stationary point as a concrete `A`-harmonic function
using the Hodge converse. -/
noncomputable def responseStationaryAHarmonicFunction
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hne : Set.Nonempty U) (hHodge : HodgeConverseCriterion U)
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d) :
    AHarmonicFunction a U :=
  toAHarmonicFunction (U := U) (a := a) hHodge
    (responseStationaryGradient
      (U := U) (a := a)
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hne hEll p q)

theorem responseStationaryAHarmonicFunction_firstVariation_integral_eq_zero
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hne : Set.Nonempty U) (hHodge : HodgeConverseCriterion U)
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d)
    (w : AHarmonicFunction a U) :
    ∫ x in U,
      scalarFirstVariationIntegrand U a p q
        (responseStationaryAHarmonicFunction
          (U := U) (a := a) hne hHodge hEll p q) w x
        ∂MeasureTheory.volume = 0 := by
  let M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U
  let z : Space (U := U) (a := a) M hEll :=
    responseStationaryGradient (U := U) (a := a) M hne hEll p q
  let u : AHarmonicFunction a U :=
    responseStationaryAHarmonicFunction (U := U) (a := a) hne hHodge hEll p q
  let W : Space (U := U) (a := a) M hEll :=
    ofAHarmonicFunction (U := U) (a := a) M hEll w
  have hstationary :
      symmCoeffBilin (U := U) (a := a) M hEll z W =
        responseFunctionalCLM (U := U) (a := a) M hEll p q W :=
    responseStationaryGradient_firstVariation (U := U) (a := a)
      (M := M) hne hEll p q W
  rw [symmCoeffBilin_apply_eq_integral_comm, responseFunctionalCLM_apply_eq_integral] at hstationary
  have hWae : vectorField W =ᵐ[volumeMeasureOn U] w.toH1.grad := by
    rw [vectorField_ofAHarmonicFunction]
    exact H1Function.coeFn_gradToVectorL2 w.toH1
  have hgrad_u :
      u.toH1.grad =
        vectorField
          (responseStationaryGradient
            (U := U) (a := a)
            (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hne hEll p q) := by
    dsimp [u, responseStationaryAHarmonicFunction]
    exact
      grad_toAHarmonicFunction (U := U) (a := a) hHodge
        (responseStationaryGradient
          (U := U) (a := a)
          (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hne hEll p q)
  have hgrad_uz : u.toH1.grad = vectorField z := by
    simpa [M, z] using hgrad_u
  have hlinInt :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot q (vectorField W x) -
            vecDot p (matVecMul (a x) (vectorField W x))) U := by
    simpa [sub_eq_add_neg, MeasureTheory.IntegrableOn] using!
      (integrableOn_vecDot_of_memVectorL2
          (memVectorL2_const (U := U) q) (MeasureTheory.Lp.memLp (vectorField W))).integrable.sub
        (integrableOn_vecDot_of_memVectorL2
          (memVectorL2_const (U := U) p)
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
            (MeasureTheory.Lp.memLp (vectorField W)))).integrable
  have hcrossInt :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot (vectorField W x) (matVecMul (symmPart (a x)) (vectorField z x))) U := by
    exact
      integrableOn_vecDot_of_memVectorL2
        (MeasureTheory.Lp.memLp (vectorField W))
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll
          (MeasureTheory.Lp.memLp (vectorField z)))
  have hrewrite :
      ∫ x in U,
        scalarFirstVariationIntegrand U a p q u w x ∂MeasureTheory.volume =
          ∫ x in U,
            (vecDot q (vectorField W x) -
              vecDot p (matVecMul (a x) (vectorField W x)) -
              vecDot (vectorField W x)
                (matVecMul (symmPart (a x)) (vectorField z x)))
              ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hWae] with x hxW
    have hgrad_ux : u.toH1.grad x = vectorField z x := by
      exact congrFun hgrad_uz x
    simp [scalarFirstVariationIntegrand, hxW, hgrad_ux]
  rw [hrewrite]
  have hsplit :
      ∫ x in U,
        (vecDot q (vectorField W x) -
          vecDot p (matVecMul (a x) (vectorField W x)) -
          vecDot (vectorField W x)
            (matVecMul (symmPart (a x)) (vectorField z x)))
          ∂MeasureTheory.volume =
        ∫ x in U,
          (vecDot q (vectorField W x) -
            vecDot p (matVecMul (a x) (vectorField W x))) ∂MeasureTheory.volume -
          ∫ x in U,
            vecDot (vectorField W x)
              (matVecMul (symmPart (a x)) (vectorField z x)) ∂MeasureTheory.volume := by
    exact MeasureTheory.integral_sub hlinInt hcrossInt
  rw [hsplit]
  rw [← hstationary]
  ring

end AHarmonicGradientHilbert

namespace ScalarCanonicalMaximizer

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}

theorem nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hne : Set.Nonempty U) (hHodge : HodgeConverseCriterion U)
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d) :
    Nonempty (ScalarCanonicalMaximizer U p q a) := by
  refine nonempty_of_exists_firstVariation_integral_eq_zero_of_isEllipticFieldOn hEll p q ?_
  refine ⟨AHarmonicGradientHilbert.responseStationaryAHarmonicFunction
    (U := U) (a := a) hne hHodge hEll p q, ?_⟩
  intro w
  exact AHarmonicGradientHilbert.responseStationaryAHarmonicFunction_firstVariation_integral_eq_zero
    (U := U) (a := a) hne hHodge hEll p q w

theorem nonempty_of_isOpenBoundedConvexDomain
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d) :
    Nonempty (ScalarCanonicalMaximizer U p q a) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  exact nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
    (U := U) (a := a) hne
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hU)
    hEll p q

theorem volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f := by
  simp only [volumeAverage, volume_openCubeSet_eq_volume_cubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

theorem isResponseMaximizer_toCubeSet_of_openCubeSet {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {a : CoeffField d} {p q : Vec d}
    (v : ScalarCanonicalMaximizer (openCubeSet Q) p q a) :
    IsResponseMaximizer (cubeSet Q) p q a
      ((v : AHarmonicFunction a (openCubeSet Q)).toCubeSet) := by
  intro w
  have hmax := v.isResponseMaximizer w.toOpenCubeSet
  have hresp_w :
      scalarResponseIntegrand (cubeSet Q) a p q w =
        scalarResponseIntegrand (openCubeSet Q) a p q w.toOpenCubeSet := by
    funext x
    simp only [scalarResponseIntegrand, AHarmonicFunction.grad_toOpenCubeSet]
  have hresp_v :
      scalarResponseIntegrand (cubeSet Q) a p q
          ((v : AHarmonicFunction a (openCubeSet Q)).toCubeSet) =
        scalarResponseIntegrand (openCubeSet Q) a p q
          (v : AHarmonicFunction a (openCubeSet Q)) := by
    funext x
    simp only [scalarResponseIntegrand, AHarmonicFunction.grad_toCubeSet]
  calc
    volumeAverage (cubeSet Q) (scalarResponseIntegrand (cubeSet Q) a p q w)
        = volumeAverage (openCubeSet Q) (scalarResponseIntegrand (cubeSet Q) a p q w) := by
            exact volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube Q _
    _ = volumeAverage (openCubeSet Q)
          (scalarResponseIntegrand (openCubeSet Q) a p q w.toOpenCubeSet) := by
            rw [hresp_w]
    _ ≤ volumeAverage (openCubeSet Q)
          (scalarResponseIntegrand (openCubeSet Q) a p q
            (v : AHarmonicFunction a (openCubeSet Q))) := hmax
    _ = volumeAverage (openCubeSet Q)
          (scalarResponseIntegrand (cubeSet Q) a p q
            ((v : AHarmonicFunction a (openCubeSet Q)).toCubeSet)) := by
            rw [hresp_v]
    _ = volumeAverage (cubeSet Q)
          (scalarResponseIntegrand (cubeSet Q) a p q
            ((v : AHarmonicFunction a (openCubeSet Q)).toCubeSet)) := by
            exact (volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube Q _).symm

noncomputable def toCubeSetOfOpenCubeSet {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {a : CoeffField d} {p q : Vec d}
    (v : ScalarCanonicalMaximizer (openCubeSet Q) p q a) :
    ScalarCanonicalMaximizer (cubeSet Q) p q a := by
  letI : Fact (MeasureTheory.volume (cubeSet Q) < ⊤) := ⟨volume_cubeSet_lt_top Q⟩
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
    change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet Q))
    infer_instance
  exact
    ofIsResponseMaximizer
      ((v : AHarmonicFunction a (openCubeSet Q)).toCubeSet)
      (isResponseMaximizer_toCubeSet_of_openCubeSet v)

theorem nonempty_cubeSet_of_isEllipticFieldOn_openCubeSet {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (cubeSet Q) p q a) := by
  have hne : Set.Nonempty (openCubeSet Q) := by
    refine ⟨cubeCenter Q, ?_⟩
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q)
  rcases nonempty_of_isOpenBoundedConvexDomain
      (U := openCubeSet Q) (a := a) hne
      (isOpenBoundedConvexDomain_openCubeSet Q) hEll p q with
    ⟨v⟩
  exact ⟨toCubeSetOfOpenCubeSet v⟩

end ScalarCanonicalMaximizer

namespace ScalarCanonicalMaximizer

namespace GradientBasisData

theorem nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hne : Set.Nonempty U) (hHodge : HodgeConverseCriterion U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Nonempty (GradientBasisData U a) :=
  GradientBasisData.nonempty_of_forall_nonempty fun i =>
    ScalarCanonicalMaximizer.nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
      (U := U) (a := a) hne hHodge hEll 0 (Pi.single i 1)

theorem nonempty_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Nonempty (GradientBasisData U a) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  exact nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
    (U := U) (a := a) hne
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hU)
    hEll

end GradientBasisData

namespace FluxBasisData

theorem nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hne : Set.Nonempty U) (hHodge : HodgeConverseCriterion U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Nonempty (FluxBasisData U a) :=
  FluxBasisData.nonempty_of_forall_nonempty fun i =>
    ScalarCanonicalMaximizer.nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
      (U := U) (a := a) hne hHodge hEll (Pi.single i 1) 0

theorem nonempty_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Nonempty (FluxBasisData U a) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  exact nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
    (U := U) (a := a) hne
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hU)
    hEll

end FluxBasisData

end ScalarCanonicalMaximizer

end

end Homogenization
