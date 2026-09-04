/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Toric.ToricSpace2
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Toric.ToricSpace2

/-!
# Hopf problem: uniformization · cusp uniformization 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-- The normalized complex exponential with period one. -/
public
def CuspUniformization.exponential (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * z)

private theorem
    CuspUniformization.exponential_factor_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  exact
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

@[simp]
private theorem CuspUniformization.exponential_ne_zero (z : ℂ) : exponential z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
private theorem CuspUniformization.exponential_zero : exponential 0 = 1 := by simp [exponential]

private theorem CuspUniformization.exponential_add (z w : ℂ) :
    exponential (z + w) = exponential z * exponential w := by
  simp only [exponential, mul_add, Complex.exp_add]

@[simp]
private theorem CuspUniformization.exponential_int (n : ℤ) : exponential n = 1 := by
  simpa only [exponential, mul_comm] using Complex.exp_int_mul_two_pi_mul_I n

private theorem CuspUniformization.exponential_eq_iff (z w : ℂ) :
    exponential z = exponential w ↔ ∃ n : ℤ, z = w + n := by
  rw [exponential, exponential, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, mul_left_cancel₀ exponential_factor_ne_zero ?_⟩
    calc
      (2 * Real.pi * Complex.I : ℂ) * z = _ := hn
      _ = (2 * Real.pi * Complex.I : ℂ) * (w + n) := by ring
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

/-- The normalized principal logarithm inverse to `exponential` away from zero. -/
public
def CuspUniformization.logarithm (t : ℂ) : ℂ :=
  Complex.log t / (2 * Real.pi * Complex.I)

private theorem CuspUniformization.exponential_logarithm {t : ℂ} (ht : t ≠ 0) :
    exponential (logarithm t) = t := by
  rw [exponential, logarithm, mul_div_cancel₀ _ exponential_factor_ne_zero]
  exact Complex.exp_log ht

private theorem CuspUniformization.exponential_holomorphic : ContDiff ℂ ω exponential :=
  (contDiff_const.mul contDiff_id).cexp

private theorem CuspUniformization.log_norm_exponential (s : ℂ) :
    Real.log ‖exponential s‖ = -2 * Real.pi * s.im := by
  simp [exponential, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private def CuspUniformization.torusPoint (w : ToricCharts.CoordinateSpace 3) : ToricSpace.Space :=
  ToricSpace.inclusion ToricSpace.referenceTriangle
    (ToricCharts.monomial ToricSpace.referenceTriangle.dual w)

private theorem CuspUniformization.torusPoint_mem {w : ToricCharts.CoordinateSpace 3}
    (hw : w ∈ ToricCharts.torus) : torusPoint w ∈ ToricSpace.openTorus :=
  ToricSpace.inclusion_torus_subset _ ⟨_, ToricCharts.monomial_mapsTo_torus _ hw, rfl⟩

private theorem CuspUniformization.torusCoordinates_torusPoint {w : ToricCharts.CoordinateSpace 3}
    (hw : w ∈ ToricCharts.torus) : ToricSpace.torusCoordinates (torusPoint w) = w := by
  rw [torusPoint,
    ToricSpace.torusCoordinates_inclusion _ (ToricCharts.monomial_mapsTo_torus _ hw),
    ToricCharts.monomial_mul_on_torus _ _ hw, ToricFan.Triangle.rays_dual,
    ToricCharts.monomial_one]

private theorem CuspUniformization.torusPoint_torusCoordinates {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) : torusPoint (ToricSpace.torusCoordinates x) = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [ToricSpace.torusCoordinates_inclusion _ hz, torusPoint,
    ToricCharts.monomial_mul_on_torus _ _ hz, ToricFan.Triangle.dual_rays,
    ToricCharts.monomial_one]

private theorem CuspUniformization.torusCoordinates_injective :
    Set.InjOn ToricSpace.torusCoordinates ToricSpace.openTorus := by
  intro x hx y hy he
  rw [← torusPoint_torusCoordinates hx, ← torusPoint_torusCoordinates hy, he]

private def CuspUniformization.exponentialCoordinates (t : ℂ) (z : ComplexPlane₂) :
    ToricCharts.CoordinateSpace 3 :=
  ![exponential (z 0), exponential (z 1), t]

private theorem
    CuspUniformization.exponentialCoordinates_mem {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    exponentialCoordinates t z ∈ ToricCharts.torus := by
  intro i
  fin_cases i
  · exact exponential_ne_zero _
  · exact exponential_ne_zero _
  · exact ht

private theorem CuspUniformization.exponentialCoordinates_holomorphic (t : ℂ) :
    ContDiff ℂ ω (exponentialCoordinates t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact exponential_holomorphic.comp (contDiff_apply ℂ ℂ 0)
  · exact exponential_holomorphic.comp (contDiff_apply ℂ ℂ 1)
  · exact contDiff_const

private def CuspUniformization.exponentialPoint (t : ℂ) : ComplexPlane₂ → ToricSpace.Space :=
  torusPoint ∘ exponentialCoordinates t

private theorem CuspUniformization.exponentialPoint_mem {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    exponentialPoint t z ∈ ToricSpace.openTorus :=
  torusPoint_mem (exponentialCoordinates_mem ht z)

private theorem CuspUniformization.torusCoordinates_exponentialPoint {t : ℂ} (ht : t ≠ 0)
    (z : ComplexPlane₂) :
    ToricSpace.torusCoordinates (exponentialPoint t z) = exponentialCoordinates t z :=
  torusCoordinates_torusPoint (exponentialCoordinates_mem ht z)

private theorem CuspUniformization.time_exponentialPoint {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    ToricSpace.time (exponentialPoint t z) = t := by
  simpa [exponentialCoordinates] using congrFun (torusCoordinates_exponentialPoint ht z) 2

private theorem CuspUniformization.exponentialPoint_holomorphic {t : ℂ} (ht : t ≠ 0) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (exponentialPoint t) := by
  apply (ToricSpace.inclusion_holomorphic ToricSpace.referenceTriangle).comp
  apply ContDiff.contMDiff
  apply contDiffOn_univ.mp
  exact
    (ToricCharts.monomial_contDiffOn ToricSpace.referenceTriangle.dual ω).comp
      (exponentialCoordinates_holomorphic t).contDiffOn
      (fun z _ => ToricCharts.torus_subset_domain _ (exponentialCoordinates_mem ht z))

private theorem CuspUniformization.exponentialPoint_surjective_fibre {t : ℂ} (ht : t ≠ 0)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = t) :
    ∃ z : ComplexPlane₂, exponentialPoint t z = x := by
  have hxT : x ∈ ToricSpace.openTorus := (ToricSpace.mem_openTorus_iff _).mpr (hx ▸ ht)
  let z : ComplexPlane₂ := fun i => logarithm (ToricSpace.torusCoordinates x i.castSucc)
  refine ⟨z, torusCoordinates_injective (exponentialPoint_mem ht z) hxT ?_⟩
  rw [torusCoordinates_exponentialPoint ht]
  ext i
  fin_cases i
  · exact exponential_logarithm (ToricSpace.torusCoordinates_nonzero hxT 0)
  · exact exponential_logarithm (ToricSpace.torusCoordinates_nonzero hxT 1)
  · simpa [exponentialCoordinates] using hx.symm

private theorem
    CuspUniformization.exponentialPoint_eq_iff {t : ℂ} (ht : t ≠ 0) (z w : ComplexPlane₂) :
    exponentialPoint t z = exponentialPoint t w ↔ ∃ m : Fin 2 → ℤ, z = w + (fun i => (m i : ℂ)) :=
  by
  constructor
  · intro he
    have hec := congrArg ToricSpace.torusCoordinates he
    rw [torusCoordinates_exponentialPoint ht, torusCoordinates_exponentialPoint ht] at hec
    have hi (i : Fin 2) : ∃ n : ℤ, z i = w i + n := by
      apply (exponential_eq_iff _ _).mp
      have hi := congrFun hec i.castSucc
      fin_cases i <;> exact hi
    choose m hm using hi
    exact ⟨m, funext hm⟩
  · rintro ⟨m, rfl⟩
    apply torusCoordinates_injective (exponentialPoint_mem ht _) (exponentialPoint_mem ht _)
    rw [torusCoordinates_exponentialPoint ht, torusCoordinates_exponentialPoint ht]
    ext i
    fin_cases i
    · exact (exponential_eq_iff _ _).mpr ⟨m 0, rfl⟩
    · exact (exponential_eq_iff _ _).mpr ⟨m 1, rfl⟩
    · rfl

private theorem CuspUniformization.torusPoint_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω torusPoint ToricCharts.torus :=
  (ToricSpace.inclusion_holomorphic ToricSpace.referenceTriangle).comp_contMDiffOn
    ((ToricCharts.monomial_contDiffOn ToricSpace.referenceTriangle.dual ω).mono
        (ToricCharts.torus_subset_domain _)).contMDiffOn

private def CuspUniformization.torusChart :
    OpenPartialHomeomorph ToricSpace.Space (ToricCharts.CoordinateSpace 3)
    where
  toFun := ToricSpace.torusCoordinates
  invFun := torusPoint
  source := ToricSpace.openTorus
  target := ToricCharts.torus
  map_source' _ hx := ToricSpace.torusCoordinates_nonzero hx
  map_target' _ hw := torusPoint_mem hw
  left_inv' _ hx := torusPoint_torusCoordinates hx
  right_inv' _ hw := torusCoordinates_torusPoint hw
  open_source := ToricSpace.openTorus_isOpen
  open_target := ToricCharts.torus_open
  continuousOn_toFun := ToricSpace.torusCoordinates_holomorphic.continuousOn
  continuousOn_invFun := torusPoint_holomorphic.continuousOn

private def CuspUniformization.logarithmicPeriod (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  s • B₀.map (Int.castRingHom ℂ) + C (exponential s)

private theorem
    CuspUniformization.logarithmicPeriod_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    (logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i =
      s * (ToricSpace.cuspVector v i : ℂ) + (C (exponential s) *ᵥ (fun j => (v j : ℂ))) i := by
  fin_cases i <;>
      simp [logarithmicPeriod, B₀, ToricSpace.cuspVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, smul_eq_mul] <;>
    ring

private theorem CuspUniformization.imaginary_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (ht : Real.log ‖exponential s‖ ≠ 0) (v : Fin 2 → ℝ) :
    Real.log ‖exponential s‖ • ToricSpace.displacement C (exponential s) v =
      (-2 * Real.pi) • ((logarithmicPeriod C s).map Complex.im *ᵥ v) := by
  change
    Real.log ‖exponential s‖ •
        (ToricSpace.realCuspVector v +
          (Real.log ‖exponential s‖)⁻¹ • (ToricSpace.driftMatrix C (exponential s) *ᵥ v)) =
      _
  rw [smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul]
  ext i
  fin_cases i <;>
      simp [logarithmicPeriod, B₀, ToricSpace.realCuspVector, ToricSpace.driftMatrix, smul_eq_mul,
        log_norm_exponential] <;>
    ring

private theorem
    CuspUniformization.logarithmicPeriod_nondegenerate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (ht : Real.log ‖exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Function.Bijective ((logarithmicPeriod C s).map Complex.im).mulVecLin := by
  have hinj : Function.Injective ((logarithmicPeriod C s).map Complex.im).mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have he := imaginary_displacement C s ht.ne v
    change (logarithmicPeriod C s).map Complex.im *ᵥ v = 0 at hv
    rw [hv, smul_zero] at he
    have hd : ToricSpace.displacement C (exponential s) v = 0 :=
      (smul_eq_zero.mp he).resolve_left ht.ne
    exact (ToricSpace.displacement_bijective C ht hR).injective (hd.trans (map_zero _).symm)
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

private def CuspUniformization.periodData (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (ht : Real.log ‖exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    FullPeriodMatrix :=
  ⟨logarithmicPeriod C s, logarithmicPeriod_nondegenerate C s ht hR⟩

private theorem CuspUniformization.exponential_logarithmicPeriod (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (v : Fin 2 → ℤ) (i : Fin 2) :
    exponential ((logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i) =
      (ToricSpace.exponentialMultiplier C v (exponential s) i : ℂ) *
        exponential s ^ ToricSpace.cuspVector v i := by
  rw [logarithmicPeriod_apply, exponential_add]
  have he :
    exponential (s * (ToricSpace.cuspVector v i : ℂ)) =
      exponential s ^ ToricSpace.cuspVector v i := by
    unfold exponential
    rw [show
        (2 * Real.pi * Complex.I : ℂ) * (s * (ToricSpace.cuspVector v i : ℂ)) =
          (ToricSpace.cuspVector v i : ℂ) * (2 * Real.pi * Complex.I * s)
        by ring,
      Complex.exp_int_mul]
  rw [he]
  exact mul_comm _ _

private theorem
    CuspUniformization.twistedTranslate_exponentialPoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (v : Fin 2 → ℤ) (z : ComplexPlane₂) :
    ToricSpace.twistedTranslate C v (exponentialPoint (exponential s) z) =
      exponentialPoint (exponential s) (z + logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) := by
  have ht := exponential_ne_zero s
  have hx := exponentialPoint_mem ht z
  have hx' :
    ToricSpace.twistedTranslate C v (exponentialPoint (exponential s) z) ∈ ToricSpace.openTorus :=
    by simpa only [ToricSpace.mem_openTorus_iff, ToricSpace.time_twistedTranslate] using hx
  apply torusCoordinates_injective hx' (exponentialPoint_mem ht _)
  have hi (i : Fin 2) :
    ToricSpace.torusCoordinates
        (ToricSpace.twistedTranslate C v (exponentialPoint (exponential s) z)) i.castSucc =
      exponential (z i + (logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i) := by
    rw [ToricSpace.torusCoordinates_twistedTranslate_apply C v hx, time_exponentialPoint ht]
    have hz :
      ToricSpace.torusCoordinates (exponentialPoint (exponential s) z) i.castSucc =
        exponential (z i) := by
      rw [torusCoordinates_exponentialPoint ht]
      fin_cases i <;> rfl
    rw [hz, exponential_add, exponential_logarithmicPeriod]
    ring
  rw [torusCoordinates_exponentialPoint ht]
  ext i
  fin_cases i
  · exact hi 0
  · exact hi 1
  · simp [exponentialCoordinates, ToricSpace.time_twistedTranslate, time_exponentialPoint ht]

private def CuspUniformization.exponentialLift (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (z : ComplexPlane₂) : ToricSpace.Tube (CuspQuotient.disc ε) :=
  ⟨exponentialPoint (exponential s) z,
    by
    change ToricSpace.time (exponentialPoint (exponential s) z) ∈ Metric.ball 0 ε
    simpa only [time_exponentialPoint (exponential_ne_zero s), Metric.mem_ball,
      dist_zero_right] using hs⟩

private theorem
    CuspUniformization.exponentialLift_continuous (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) :
    Continuous (exponentialLift ε s hs) :=
  (exponentialPoint_holomorphic (exponential_ne_zero s)).continuous.subtype_mk _

private theorem CuspUniformization.exponentialLift_holomorphic (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (exponentialLift ε s hs) := by
  intro z
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ ComplexPlane₂)
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        (fun w => (exponentialLift ε s hs w : ToricSpace.Space)) z ↔
      ContMDiffAt (modelWithCornersSelf ℂ ComplexPlane₂)
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (exponentialLift ε s hs) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (exponentialPoint_holomorphic (exponential_ne_zero s) z)

private def CuspUniformization.fibreCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) : ComplexPlane₂ → CuspQuotient.QuotientSpace C ε :=
  CuspQuotient.quotientMap C ε ∘ exponentialLift ε s hs

private theorem CuspUniformization.fibreCover_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) (hs : ‖exponential s‖ < ε) : Continuous (fibreCover C ε s hs) :=
  (CuspQuotient.quotientMap_continuous C ε).comp (exponentialLift_continuous ε s hs)

@[simp]
private theorem CuspUniformization.projection_fibreCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) (hs : ‖exponential s‖ < ε) (z : ComplexPlane₂) :
    CuspQuotient.projection C ε (fibreCover C ε s hs z) = exponential s :=
  time_exponentialPoint (exponential_ne_zero s) z

private theorem
    CuspUniformization.fibreCover_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (z w : ComplexPlane₂) :
    fibreCover C ε s hs z = fibreCover C ε s hs w ↔ z - w ∈ (periodData C s hlog hRp).lattice := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  constructor
  · intro he
    have horb := Quotient.exact he
    change
      exponentialLift ε s hs z ∈
        MulAction.orbit CuspQuotient.LatticeGroup (exponentialLift ε s hs w) at horb
    obtain ⟨g, hg⟩ := horb
    have hp :
      exponentialPoint (exponential s) z =
        exponentialPoint (exponential s)
          (w + logarithmicPeriod C s *ᵥ (fun j => (g.toAdd j : ℂ))) :=
      (congrArg Subtype.val hg).symm.trans (twistedTranslate_exponentialPoint C s g.toAdd w)
    obtain ⟨m, hm⟩ := (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mp hp
    apply (FullPeriodMatrix.mem_lattice_iff _ _).mpr
    refine ⟨m, g.toAdd, ?_⟩
    change z - w = (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (g.toAdd j : ℂ))
    rw [hm]
    abel
  · intro he
    obtain ⟨m, n, hmn⟩ := (FullPeriodMatrix.mem_lattice_iff _ _).mp he
    have hp :
      exponentialPoint (exponential s) z =
        exponentialPoint (exponential s) (w + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) := by
      apply (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mpr
      refine ⟨m, ?_⟩
      have he := sub_eq_iff_eq_add.mp hmn
      change z = (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ)) + w at he
      rw [he]
      abel
    have hl :
      exponentialLift ε s hs z =
        ToricSpace.tubeTranslate C (CuspQuotient.disc ε) n (exponentialLift ε s hs w) :=
      Subtype.ext (hp.trans (twistedTranslate_exponentialPoint C s n w).symm)
    change
      CuspQuotient.quotientMap C ε (exponentialLift ε s hs z) =
        CuspQuotient.quotientMap C ε (exponentialLift ε s hs w)
    rw [hl, CuspQuotient.quotientMap_translate]

private def CuspUniformization.fibreMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    (periodData C s hlog hRp).Torus → CuspQuotient.QuotientSpace C ε :=
  Quotient.lift (fibreCover C ε s hs)
    (by
      intro z w hzw
      apply (fibreCover_eq_iff C ε s hs hlog hRp z w).mpr
      exact (Submodule.Quotient.eq _).mp (Quotient.sound hzw))

private theorem
    CuspUniformization.fibreMap_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Function.Injective (fibreMap C ε s hs hlog hRp) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h z =>
    induction y using Quotient.inductionOn with
    | h w =>
      intro he
      exact (Submodule.Quotient.eq _).mpr ((fibreCover_eq_iff C ε s hs hlog hRp z w).mp he)

private theorem
    CuspUniformization.fibreMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Continuous (fibreMap C ε s hs hlog hRp) :=
  (fibreCover_continuous C ε s hs).quotient_lift _

@[simp]
private theorem
    CuspUniformization.projection_fibreMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (x : (periodData C s hlog hRp).Torus) :
    CuspQuotient.projection C ε (fibreMap C ε s hs hlog hRp x) = exponential s := by
  induction x using Quotient.inductionOn with
  | h z => exact projection_fibreCover C ε s hs z

private theorem CuspUniformization.fibreMap_range (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Set.range (fibreMap C ε s hs hlog hRp) = CuspQuotient.projection C ε ⁻¹' {exponential s} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact projection_fibreMap C ε s hs hlog hRp x
  · induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      have ht : ToricSpace.time (x : ToricSpace.Space) = exponential s := hx
      obtain ⟨z, hz⟩ := exponentialPoint_surjective_fibre (exponential_ne_zero s) ht
      refine ⟨(periodData C s hlog hRp).lattice.mkQ z, ?_⟩
      apply congrArg (CuspQuotient.quotientMap C ε)
      exact Subtype.ext hz

private theorem
    CuspUniformization.fibreMap_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (fibreMap C ε s hs hlog hRp) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply DiscreteQuotient.contMDiff_of_comp_mkQ
  exact
    (CuspQuotient.quotientMap_holomorphic C ε hε hε1 hC hR).comp
      (exponentialLift_holomorphic ε s hs)

private def CuspUniformization.fibreMapToFibre (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (x : (periodData C s hlog hRp).Torus) : CuspQuotient.projection C ε ⁻¹' {exponential s} :=
  ⟨fibreMap C ε s hs hlog hRp x, projection_fibreMap C ε s hs hlog hRp x⟩

private theorem
    CuspUniformization.fibreMapToFibre_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Function.Bijective (fibreMapToFibre C ε s hs hlog hRp) := by
  constructor
  · intro x y he
    exact fibreMap_injective C ε s hs hlog hRp (congrArg Subtype.val he)
  · intro q
    have hq : (q : CuspQuotient.QuotientSpace C ε) ∈ Set.range (fibreMap C ε s hs hlog hRp) := by
      rw [fibreMap_range]
      exact q.2
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, Subtype.ext hx⟩

private def CuspUniformization.fibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    (periodData C s hlog hRp).Torus ≃ₜ CuspQuotient.projection C ε ⁻¹' {exponential s} := by
  let := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  let e :=
    Equiv.ofBijective (fibreMapToFibre C ε s hs hlog hRp)
      (fibreMapToFibre_bijective C ε s hs hlog hRp)
  exact
    Continuous.homeoOfEquivCompactToT2 (f := e)
      ((fibreMap_continuous C ε s hs hlog hRp).subtype_mk _)

private theorem
    CuspUniformization.fibreMap_isEmbedding (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : Topology.IsEmbedding (fibreMap C ε s hs hlog hRp) := by
  exact
    Topology.IsEmbedding.subtypeVal.comp
      (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR).isEmbedding

private theorem CuspUniformization.nonzero_fibre_torus (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∃ p : FullPeriodMatrix,
      ∃ f : p.Torus → CuspQuotient.QuotientSpace C ε,
        ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
            (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω f ∧
          Topology.IsEmbedding f ∧ Set.range f = CuspQuotient.projection C ε ⁻¹' { t } := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let s := logarithm t
  have hst : exponential s = t := exponential_logarithm ht0
  have hs : ‖exponential s‖ < ε := by simpa only [hst] using ht
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr (exponential_ne_zero s)
  have hlog := Real.log_neg hpos (hs.trans hε1)
  have hRp := hR _ hpos hs
  refine
    ⟨periodData C s hlog hRp, fibreMap C ε s hs hlog hRp,
      fibreMap_holomorphic C ε s hs hlog hRp hε hε1 hC hR,
      fibreMap_isEmbedding C ε s hs hlog hRp hε hε1 hC hR, ?_⟩
  simpa only [hst] using fibreMap_range C ε s hs hlog hRp

private theorem
    CuspUniformization.nonzero_fibre_pathConnected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    IsPathConnected (CuspQuotient.projection C ε ⁻¹' { t }) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  obtain ⟨p, f, hf, _, he⟩ := nonzero_fibre_torus C ε hε hε1 hC hR ht0 ht
  rw [← he]
  exact isPathConnected_range hf.continuous

private theorem
    CuspUniformization.fibre_connected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (t : CuspQuotient.disc ε) :
    IsConnected (CuspQuotient.projection C ε ⁻¹' {(t : ℂ)}) := by
  by_cases ht0 : (t : ℂ) = 0
  · rw [ht0]
    exact CuspQuotient.central_fibre_connected C ε hε
  · have ht : ‖(t : ℂ)‖ < ε := by
      have htball : (t : ℂ) ∈ Metric.ball 0 ε := t.2
      simpa only [Metric.mem_ball, dist_zero_right] using htball
    exact (nonzero_fibre_pathConnected C ε hε hε1 hC hR ht0 ht).isConnected

private def CuspUniformization.exponentialPair (z : ComplexPlane₂) : ComplexPlane₂ := fun i =>
  exponential (z i)

private theorem CuspUniformization.exponential_hasDerivAt (z : ℂ) :
    HasDerivAt exponential (exponential z * (2 * Real.pi * Complex.I)) z := by
  change
    HasDerivAt (fun w : ℂ => Complex.exp (2 * Real.pi * Complex.I * w))
      (Complex.exp (2 * Real.pi * Complex.I * z) * (2 * Real.pi * Complex.I)) z
  convert! ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I)).cexp using 1
  simp

private def CuspUniformization.exponentialPairDerivative (z : ComplexPlane₂) :
    ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  ContinuousLinearEquiv.piCongrRight fun i =>
    ContinuousLinearEquiv.unitsEquivAut ℂ
      (Units.mk0 (exponential (z i) * (2 * Real.pi * Complex.I))
        (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero))

private theorem CuspUniformization.exponentialPair_hasFDerivAt (z : ComplexPlane₂) :
    HasFDerivAt exponentialPair (exponentialPairDerivative z : ComplexPlane₂ →L[ℂ] ComplexPlane₂)
      z := by
  apply hasFDerivAt_pi''
  intro i
  convert!
    ((exponential_hasDerivAt (z i)).hasFDerivAt_equiv
          (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero)).comp
      z (hasFDerivAt_apply (𝕜 := ℂ) i z) using
    1

/-- The two-by-two period correction matrix determined by three coefficient functions. -/
public
def SpecialPeriods.cuspCorrection (μ b h : ℂ → ℂ) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![6 * μ t, h t; b t - h t, μ t]

private theorem SpecialPeriods.cuspCorrection_holomorphicOn {μ b h : ℂ → ℂ} {U : Set ℂ}
    (hμ : ContDiffOn ℂ ω μ U) (hb : ContDiffOn ℂ ω b U) (hh : ContDiffOn ℂ ω h U) (i j : Fin 2) :
    ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) U := by
  fin_cases i <;> fin_cases j
  · exact contDiffOn_const.mul hμ
  · exact hh
  · exact hb.sub hh
  · exact hμ

private theorem SpecialPeriods.exists_cuspCorrection_admissible_radius {μ b h : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hμ : ContDiffOn ℂ ω μ (Metric.ball 0 r))
    (hb : ContDiffOn ℂ ω b (Metric.ball 0 r)) (hh : ContDiffOn ℂ ω h (Metric.ball 0 r)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < r ∧
          ε < 1 ∧
            ToricSpace.SmallDrift (cuspCorrection μ b h) ε ∧
              ∀ i j, ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) (Metric.ball 0 ε) :=
  CuspQuotient.exists_admissible_radius (cuspCorrection μ b h) hr
    (cuspCorrection_holomorphicOn hμ hb hh)

private theorem SpecialPeriods.exists_cuspCorrection_admissible_radius_of_analyticAt {μ b h : ℂ → ℂ}
    (hμ : AnalyticAt ℂ μ 0) (hb : AnalyticAt ℂ b 0) (hh : AnalyticAt ℂ h 0) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < 1 ∧
          ToricSpace.SmallDrift (cuspCorrection μ b h) ε ∧
            ∀ i j, ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) (Metric.ball 0 ε) := by
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp
      (hμ.eventually_analyticAt.and (hb.eventually_analyticAt.and hh.eventually_analyticAt))
  have hμr : ContDiffOn ℂ ω μ (Metric.ball 0 r) := fun t ht =>
    (hball ht).1.contDiffAt.contDiffWithinAt
  have hbr : ContDiffOn ℂ ω b (Metric.ball 0 r) := fun t ht =>
    (hball ht).2.1.contDiffAt.contDiffWithinAt
  have hhr : ContDiffOn ℂ ω h (Metric.ball 0 r) := fun t ht =>
    (hball ht).2.2.contDiffAt.contDiffWithinAt
  obtain ⟨ε, hε, _, hε1, hR, hC⟩ := exists_cuspCorrection_admissible_radius hr hμr hbr hhr
  exact ⟨ε, hε, hε1, hR, hC⟩

private def SpecialPeriods.cuspPeriodPoint (μ b h : ℂ → ℂ) (s : ℂ) : PeriodPoint :=
  ⟨s + h (CuspUniformization.exponential s), μ (CuspUniformization.exponential s),
    b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s)⟩

private theorem SpecialPeriods.cuspPeriodPoint_leftBlock (μ b h : ℂ → ℂ) (s : ℂ) :
    (cuspPeriodPoint μ b h s).leftBlock =
      CuspUniformization.logarithmicPeriod (cuspCorrection μ b h) s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspPeriodPoint, PeriodPoint.leftBlock, CuspUniformization.logarithmicPeriod,
      cuspCorrection, B₀, smul_eq_mul]
  ring

private theorem SpecialPeriods.correction_im_bound_of_smallDrift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4)
    (i j : Fin 2) : |(C (CuspUniformization.exponential s) i j).im| ≤ s.im / 4 := by
  have hentry :
    ‖ToricSpace.driftMatrix C (CuspUniformization.exponential s) i j‖ ≤
      -Real.log ‖CuspUniformization.exponential s‖ / 4 :=
    ((norm_le_pi_norm (ToricSpace.driftMatrix C (CuspUniformization.exponential s) i) j).trans
          (norm_le_pi_norm
            (fun k : Fin 2 => fun l : Fin 2 =>
              ToricSpace.driftMatrix C (CuspUniformization.exponential s) k l)
            i)).trans
      hR
  have hscaled :
    (2 * Real.pi) * |(C (CuspUniformization.exponential s) i j).im| ≤
      (2 * Real.pi) * (s.im / 4) := by
    simpa [ToricSpace.driftMatrix, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
      CuspUniformization.log_norm_exponential, neg_mul, mul_div_assoc] using hentry
  exact le_of_mul_le_mul_left hscaled (by positivity : 0 < 2 * Real.pi)

private theorem SpecialPeriods.cuspPeriodPoint_admissible (μ b h : ℂ → ℂ) (s : ℂ)
    (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (cuspCorrection μ b h) (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4) :
    (cuspPeriodPoint μ b h s).Admissible := by
  have hs : 0 < s.im := by
    rw [CuspUniformization.log_norm_exponential] at hlog
    have hp := Real.pi_pos
    nlinarith
  have hh := (abs_le.mp (correction_im_bound_of_smallDrift (cuspCorrection μ b h) s hR 0 1)).1
  have hbh := (abs_le.mp (correction_im_bound_of_smallDrift (cuspCorrection μ b h) s hR 1 0)).2
  change -(s.im / 4) ≤ (h (CuspUniformization.exponential s)).im at hh
  change
    (b (CuspUniformization.exponential s) - h (CuspUniformization.exponential s)).im ≤
      s.im / 4 at hbh
  have hτ : 0 < (s + h (CuspUniformization.exponential s)).im := by
    rw [Complex.add_im]
    linarith
  have hβ :
    (b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s)).im < 0 := by
    rw [Complex.sub_im] at hbh
    rw [Complex.sub_im, Complex.sub_im]
    linarith
  refine ⟨hτ, ?_⟩
  change
    (b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s)).im -
        6 * (μ (CuspUniformization.exponential s)).im ^ 2 /
          (s + h (CuspUniformization.exponential s)).im <
      0
  have hn :
    0 ≤
      6 * (μ (CuspUniformization.exponential s)).im ^ 2 /
        (s + h (CuspUniformization.exponential s)).im :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hτ.le
  linarith

private def SpecialPeriods.cuspPeriodDomain (μ b h : ℂ → ℂ) (s : ℂ)
    (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (cuspCorrection μ b h) (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4) :
    PeriodDomain :=
  ⟨cuspPeriodPoint μ b h s, cuspPeriodPoint_admissible μ b h s hlog hR⟩

private theorem SpecialPeriods.leftBlock_eq_logarithmicPeriod_of_cusp_expansion (μ b h : ℂ → ℂ)
    (p : PeriodPoint) (s : ℂ) (hτ : p.τ = s + h (CuspUniformization.exponential s))
    (hμ : p.μ = μ (CuspUniformization.exponential s))
    (hβ : p.β = b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s)) :
    p.leftBlock = CuspUniformization.logarithmicPeriod (cuspCorrection μ b h) s := by
  have hp : p = cuspPeriodPoint μ b h s := PeriodPoint.ext hτ hμ hβ
  rw [hp, cuspPeriodPoint_leftBlock]

private theorem SpecialPeriods.cusp_period_lattice_eq (μ b h : ℂ → ℂ) (p : PeriodDomain) (s : ℂ)
    (hτ : p.val.τ = s + h (CuspUniformization.exponential s))
    (hμ : p.val.μ = μ (CuspUniformization.exponential s))
    (hβ :
      p.val.β = b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s))
    (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (cuspCorrection μ b h) (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4) :
    (CuspUniformization.periodData (cuspCorrection μ b h) s hlog hRp).lattice = p.lattice := by
  apply p.fullPeriodLattice_eq
  exact (leftBlock_eq_logarithmicPeriod_of_cusp_expansion μ b h p.val s hτ hμ hβ).symm

/-- The logarithmic covering domain lying over a disc of radius `ε`. -/
public
def CuspUniformization.logDomain (ε : ℝ) : TopologicalSpace.Opens (ℂ × ComplexPlane₂) :=
  ⟨(fun p : ℂ × ComplexPlane₂ => exponential p.1) ⁻¹' Metric.ball 0 ε,
    Metric.isOpen_ball.preimage (exponential_holomorphic.continuous.comp continuous_fst)⟩

/-- The logarithmic cover of the radius-`ε` cusp domain. -/
public
abbrev CuspUniformization.LogCover (ε : ℝ) :=
  logDomain ε

@[simp]
private theorem CuspUniformization.mem_logDomain (ε : ℝ) (p : ℂ × ComplexPlane₂) :
    p ∈ logDomain ε ↔ ‖exponential p.1‖ < ε := by simp [logDomain, Metric.mem_ball]

private def CuspUniformization.puncturedTubeOpen (ε : ℝ) :
    TopologicalSpace.Opens (ToricSpace.Tube (CuspQuotient.disc ε)) :=
  ⟨{x | ToricSpace.time (x : ToricSpace.Space) ≠ 0},
    isOpen_ne_fun (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val)
      continuous_const⟩

private abbrev CuspUniformization.PuncturedTube (ε : ℝ) :=
  puncturedTubeOpen ε

private def CuspUniformization.puncturedQuotientOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    TopologicalSpace.Opens (CuspQuotient.QuotientSpace C ε) :=
  ⟨{x | CuspQuotient.projection C ε x ≠ 0},
    isOpen_ne_fun (CuspQuotient.projection_continuous C ε) continuous_const⟩

private abbrev CuspUniformization.PuncturedQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  puncturedQuotientOpen C ε

private def CuspUniformization.totalExponentialPoint (p : ℂ × ComplexPlane₂) : ToricSpace.Space :=
  exponentialPoint (exponential p.1) p.2

@[simp]
private theorem CuspUniformization.time_totalExponentialPoint (p : ℂ × ComplexPlane₂) :
    ToricSpace.time (totalExponentialPoint p) = exponential p.1 :=
  time_exponentialPoint (exponential_ne_zero p.1) p.2

private theorem CuspUniformization.totalExponentialPoint_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω totalExponentialPoint := by
  apply (ToricSpace.inclusion_holomorphic ToricSpace.referenceTriangle).comp
  apply ContDiff.contMDiff
  apply contDiffOn_univ.mp
  apply (ToricCharts.monomial_contDiffOn ToricSpace.referenceTriangle.dual ω).comp
  · apply ContDiff.contDiffOn
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 0).comp contDiff_snd)
    · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 1).comp contDiff_snd)
    · exact exponential_holomorphic.comp contDiff_fst
  · intro p _
    exact
      ToricCharts.torus_subset_domain _ (exponentialCoordinates_mem (exponential_ne_zero p.1) p.2)

private def CuspUniformization.totalExponentialLift (ε : ℝ) (p : LogCover ε) :
    ToricSpace.Tube (CuspQuotient.disc ε) :=
  ⟨totalExponentialPoint p,
    by
    change ToricSpace.time (totalExponentialPoint p) ∈ Metric.ball 0 ε
    rw [time_totalExponentialPoint]
    exact p.2⟩

private def CuspUniformization.puncturedExponential (ε : ℝ) (p : LogCover ε) : PuncturedTube ε :=
  ⟨totalExponentialLift ε p,
    by
    change ToricSpace.time (totalExponentialPoint p) ≠ 0
    rw [time_totalExponentialPoint]
    exact exponential_ne_zero _⟩

private def CuspUniformization.totalCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : LogCover ε) : CuspQuotient.QuotientSpace C ε :=
  CuspQuotient.quotientMap C ε (totalExponentialLift ε p)

@[simp]
private theorem
    CuspUniformization.projection_totalCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : LogCover ε) : CuspQuotient.projection C ε (totalCuspCover C ε p) = exponential p.1.1 :=
  time_totalExponentialPoint p

private def CuspUniformization.puncturedCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : LogCover ε) : PuncturedQuotient C ε :=
  ⟨totalCuspCover C ε p,
    by
    change CuspQuotient.projection C ε (totalCuspCover C ε p) ≠ 0
    rw [projection_totalCuspCover]
    exact exponential_ne_zero _⟩

private def CuspUniformization.puncturedQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : PuncturedTube ε) : PuncturedQuotient C ε :=
  ⟨CuspQuotient.quotientMap C ε p, p.2⟩

private theorem CuspUniformization.totalExponentialLift_holomorphic (ε : ℝ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (totalExponentialLift ε) := by
  intro p
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        (fun q => (totalExponentialLift ε q : ToricSpace.Space)) p ↔
      ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (totalExponentialLift ε) p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (totalExponentialPoint_holomorphic.comp contMDiff_subtype_val p)

private theorem CuspUniformization.puncturedExponential_surjective (ε : ℝ) :
    Function.Surjective (puncturedExponential ε) := by
  intro x
  let t : ℂ := ToricSpace.time (x.1 : ToricSpace.Space)
  have ht : t ≠ 0 := x.2
  obtain ⟨z, hz⟩ := exponentialPoint_surjective_fibre ht (x := (x.1 : ToricSpace.Space)) rfl
  let p : LogCover ε :=
    ⟨(logarithm t, z), by
      change exponential (logarithm t) ∈ Metric.ball 0 ε
      rw [exponential_logarithm ht]
      exact x.1.2⟩
  refine ⟨p, Subtype.ext (Subtype.ext ?_)⟩
  change exponentialPoint (exponential (logarithm t)) z = (x.1 : ToricSpace.Space)
  rw [exponential_logarithm ht]
  exact hz

private theorem
    CuspUniformization.puncturedQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Function.Surjective (puncturedQuotientMap C ε) := by
  intro q
  obtain ⟨x, hx⟩ := Quotient.exists_rep q.1
  have hp : ToricSpace.time (x : ToricSpace.Space) ≠ 0 := by
    have h := q.2
    change CuspQuotient.projection C ε q.1 ≠ 0 at h
    rwa [← hx] at h
  exact ⟨⟨x, hp⟩, Subtype.ext hx⟩

private theorem CuspUniformization.puncturedCuspCover_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Function.Surjective (puncturedCuspCover C ε) :=
  (puncturedQuotientMap_surjective C ε).comp (puncturedExponential_surjective ε)

/-- The relation identifying points that differ by total cusp periods. -/
public
def CuspUniformization.TotalPeriodRelated (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (p q : ℂ × ComplexPlane₂) : Prop :=
  ∃ (k : ℤ) (m n : Fin 2 → ℤ),
    p.1 = q.1 + k ∧
      p.2 = q.2 + (fun i => (m i : ℂ)) + logarithmicPeriod C q.1 *ᵥ (fun i => (n i : ℂ))

private theorem CuspUniformization.totalCuspCover_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p q : LogCover ε) : totalCuspCover C ε p = totalCuspCover C ε q ↔ TotalPeriodRelated C p q :=
  by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  constructor
  · intro h
    have hs : exponential p.1.1 = exponential q.1.1 := by
      simpa only [projection_totalCuspCover] using congrArg (CuspQuotient.projection C ε) h
    obtain ⟨k, hk⟩ := (exponential_eq_iff _ _).mp hs
    have horb := Quotient.exact h
    change
      totalExponentialLift ε p ∈
        MulAction.orbit CuspQuotient.LatticeGroup (totalExponentialLift ε q) at horb
    obtain ⟨g, hg⟩ := horb
    have hp :
      exponentialPoint (exponential q.1.1) p.1.2 =
        exponentialPoint (exponential q.1.1)
          (q.1.2 + logarithmicPeriod C q.1.1 *ᵥ (fun i => (g.toAdd i : ℂ))) := by
      have he :=
        (congrArg Subtype.val hg).symm.trans
          (twistedTranslate_exponentialPoint C q.1.1 g.toAdd q.1.2)
      change exponentialPoint (exponential p.1.1) p.1.2 = _ at he
      rwa [hs] at he
    obtain ⟨m, hm⟩ := (exponentialPoint_eq_iff (exponential_ne_zero q.1.1) _ _).mp hp
    refine ⟨k, m, g.toAdd, hk, ?_⟩
    rw [hm]
    abel
  · rintro ⟨k, m, n, hk, hmn⟩
    have hs := (exponential_eq_iff p.1.1 q.1.1).mpr ⟨k, hk⟩
    have hp :
      totalExponentialPoint p = ToricSpace.twistedTranslate C n (totalExponentialPoint q) := by
      change
        exponentialPoint (exponential p.1.1) p.1.2 =
          ToricSpace.twistedTranslate C n (exponentialPoint (exponential q.1.1) q.1.2)
      rw [hs, twistedTranslate_exponentialPoint]
      apply (exponentialPoint_eq_iff (exponential_ne_zero q.1.1) _ _).mpr
      refine ⟨m, ?_⟩
      rw [hmn]
      abel
    have hl :
      totalExponentialLift ε p =
        ToricSpace.tubeTranslate C (CuspQuotient.disc ε) n (totalExponentialLift ε q) :=
      Subtype.ext hp
    change
      CuspQuotient.quotientMap C ε (totalExponentialLift ε p) =
        CuspQuotient.quotientMap C ε (totalExponentialLift ε q)
    rw [hl, CuspQuotient.quotientMap_translate]

private theorem
    CuspUniformization.puncturedCuspCover_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p q : LogCover ε) :
    puncturedCuspCover C ε p = puncturedCuspCover C ε q ↔ TotalPeriodRelated C p q := by
  rw [← totalCuspCover_eq_iff C ε p q]
  exact Subtype.ext_iff

@[simp]
private theorem CuspUniformization.exponential_add_int (s : ℂ) (k : ℤ) :
    exponential (s + k) = exponential s := by rw [exponential_add, exponential_int, mul_one]

private theorem
    CuspUniformization.logarithmicPeriod_mulVec_add_int (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (k : ℤ) (n : Fin 2 → ℤ) :
    logarithmicPeriod C (s + k) *ᵥ (fun i => (n i : ℂ)) =
      logarithmicPeriod C s *ᵥ (fun i => (n i : ℂ)) + fun i =>
        (k : ℂ) * (ToricSpace.cuspVector n i : ℂ) := by
  ext i
  simp only [Pi.add_apply, logarithmicPeriod_apply, exponential_add_int]
  ring

@[ext]
private structure CuspUniformization.LogDeck where
  k : ℤ
  m : Fin 2 → ℤ
  n : Fin 2 → ℤ
  deriving DecidableEq

private instance CuspUniformization.LogDeck.instLocal1 : One CuspUniformization.LogDeck :=
  ⟨⟨0, 0, 0⟩⟩

private instance CuspUniformization.LogDeck.instLocal2 : Mul CuspUniformization.LogDeck :=
  ⟨fun g h => ⟨g.k + h.k, g.m + h.m + h.k • ToricSpace.cuspVector g.n, g.n + h.n⟩⟩

private instance CuspUniformization.LogDeck.instLocal3 : Inv CuspUniformization.LogDeck :=
  ⟨fun g => ⟨-g.k, -g.m + g.k • ToricSpace.cuspVector g.n, -g.n⟩⟩

@[simp]
private theorem CuspUniformization.LogDeck.mul_k (g h : CuspUniformization.LogDeck) :
    (g * h).k = g.k + h.k :=
  rfl

@[simp]
private theorem CuspUniformization.LogDeck.mul_m (g h : CuspUniformization.LogDeck) :
    (g * h).m = g.m + h.m + h.k • ToricSpace.cuspVector g.n :=
  rfl

@[simp]
private theorem CuspUniformization.LogDeck.mul_n (g h : CuspUniformization.LogDeck) :
    (g * h).n = g.n + h.n :=
  rfl

private instance CuspUniformization.LogDeck.instLocal4 : Group CuspUniformization.LogDeck
    where
  mul_assoc g h
    l := by
    apply CuspUniformization.LogDeck.ext
    · simp only [mul_k, add_assoc]
    · simp only [mul_m, mul_k, mul_n, ToricSpace.cuspVector_add, smul_add, add_smul]
      abel
    · simp only [mul_n, add_assoc]
  one_mul
    g := by
    have hone : (1 : CuspUniformization.LogDeck) = ⟨0, 0, 0⟩ := rfl
    apply CuspUniformization.LogDeck.ext <;> simp [hone]
  mul_one
    g := by
    have hone : (1 : CuspUniformization.LogDeck) = ⟨0, 0, 0⟩ := rfl
    apply CuspUniformization.LogDeck.ext <;> simp [hone]
  inv_mul_cancel
    g := by
    have hone : (1 : CuspUniformization.LogDeck) = ⟨0, 0, 0⟩ := rfl
    have hinv : g⁻¹ = ⟨-g.k, -g.m + g.k • ToricSpace.cuspVector g.n, -g.n⟩ := rfl
    apply CuspUniformization.LogDeck.ext
    · simp [hone, hinv]
    · ext i
      fin_cases i <;> simp [hone, hinv, ToricSpace.cuspVector]
    · simp [hone, hinv]

private def CuspUniformization.logDeckTransform (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g : LogDeck)
    (x : ℂ × ComplexPlane₂) : ℂ × ComplexPlane₂ :=
  (x.1 + g.k, x.2 + (fun i => (g.m i : ℂ)) + logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)))

@[simp]
private theorem
    CuspUniformization.logDeckTransform_fst (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g : LogDeck)
    (x : ℂ × ComplexPlane₂) : (logDeckTransform C g x).1 = x.1 + g.k :=
  rfl

@[simp]
private theorem
    CuspUniformization.logDeckTransform_snd (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g : LogDeck)
    (x : ℂ × ComplexPlane₂) :
    (logDeckTransform C g x).2 =
      x.2 + (fun i => (g.m i : ℂ)) + logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)) :=
  rfl

@[simp]
private theorem CuspUniformization.logDeckTransform_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (x : ℂ × ComplexPlane₂) : logDeckTransform C 1 x = x := by
  have hone : (1 : LogDeck) = ⟨0, 0, 0⟩ := rfl
  apply Prod.ext
  · simp [hone, logDeckTransform]
  · ext i
    fin_cases i <;> simp [hone, logDeckTransform, Matrix.vecHead, Matrix.vecTail]

private theorem
    CuspUniformization.logDeckTransform_mul (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g h : LogDeck)
    (x : ℂ × ComplexPlane₂) :
    logDeckTransform C (g * h) x = logDeckTransform C g (logDeckTransform C h x) := by
  apply Prod.ext
  · simp only [logDeckTransform_fst, LogDeck.mul_k, Int.cast_add]
    ring
  · ext i
    simp only [logDeckTransform_snd, logDeckTransform_fst, LogDeck.mul_m, LogDeck.mul_n,
      logarithmicPeriod_mulVec_add_int, Pi.add_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_id]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

private theorem CuspUniformization.logDeckTransform_eq_self_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (g : LogDeck) (x : ℂ × ComplexPlane₂)
    (hP : Function.Bijective ((logarithmicPeriod C x.1).map Complex.im).mulVecLin) :
    logDeckTransform C g x = x ↔ g = 1 := by
  constructor
  · intro hx
    have hk : g.k = 0 := by
      have he := congrArg Prod.fst hx
      have he' : (g.k : ℂ) = 0 := by simpa only [logDeckTransform_fst, add_eq_left] using he
      exact_mod_cast he'
    let p : FullPeriodMatrix := ⟨logarithmicPeriod C x.1, hP⟩
    have he : p.periodLinear ((fun i => (g.m i : ℝ)), fun i => (g.n i : ℝ)) = p.periodLinear 0 := by
      have hs : (fun i => (g.m i : ℂ)) + logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)) = 0 := by
        have hs := congrArg Prod.snd hx
        simpa only [logDeckTransform_snd, add_assoc, add_eq_left] using hs
      rw [map_zero]
      ext i
      simpa [FullPeriodMatrix.periodLinear, p] using congrFun hs i
    have he' := p.periodLinear_bijective.injective he
    apply LogDeck.ext hk
    · ext i
      have hm := congrFun (congrArg Prod.fst he') i
      change (g.m i : ℝ) = 0 at hm
      change g.m i = 0
      exact_mod_cast hm
    · ext i
      have hn := congrFun (congrArg Prod.snd he') i
      change (g.n i : ℝ) = 0 at hn
      change g.n i = 0
      exact_mod_cast hn
  · rintro rfl
    exact logDeckTransform_one C x

private theorem CuspUniformization.logDeckTransform_mem_logDomain (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (g : LogDeck) (x : ℂ × ComplexPlane₂) :
    logDeckTransform C g x ∈ logDomain ε ↔ x ∈ logDomain ε := by simp

private def
    CuspUniformization.logCoverTransform (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (g : LogDeck)
    (x : LogCover ε) : LogCover ε :=
  ⟨logDeckTransform C g x, (logDeckTransform_mem_logDomain C ε g x).mpr x.2⟩

@[simp]
private theorem CuspUniformization.logCoverTransform_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (g : LogDeck) (x : LogCover ε) :
    (logCoverTransform C ε g x : ℂ × ComplexPlane₂) = logDeckTransform C g x :=
  rfl

@[instance_reducible]
private def CuspUniformization.logCoverAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    MulAction LogDeck (LogCover ε)
    where
  smul := logCoverTransform C ε
  one_smul x := Subtype.ext (logDeckTransform_one C x)
  mul_smul g h x := Subtype.ext (logDeckTransform_mul C g h x)

private theorem CuspUniformization.logarithmicPeriod_logDomain_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (i j : Fin 2) :
    ContDiffOn ℂ ω (fun x : ℂ × ComplexPlane₂ => logarithmicPeriod C x.1 i j) (logDomain ε) := by
  have he : ContDiff ℂ ω (fun x : ℂ × ComplexPlane₂ => exponential x.1) :=
    exponential_holomorphic.comp contDiff_fst
  change
    ContDiffOn ℂ ω
      (fun x : ℂ × ComplexPlane₂ =>
        x.1 * (B₀.map (Int.castRingHom ℂ)) i j + C (exponential x.1) i j)
      _
  exact
    (contDiff_fst.mul contDiff_const).contDiffOn.add
      ((hC i j).comp he.contDiffOn (fun x hx => hx))

private theorem CuspUniformization.logarithmicPeriod_logDomain_mulVec_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (n : Fin 2 → ℤ) :
    ContDiffOn ℂ ω (fun x : ℂ × ComplexPlane₂ => logarithmicPeriod C x.1 *ᵥ (fun i => (n i : ℂ)))
      (logDomain ε) := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact
    ((logarithmicPeriod_logDomain_holomorphic C ε hC i 0).mul contDiffOn_const).add
      ((logarithmicPeriod_logDomain_holomorphic C ε hC i 1).mul contDiffOn_const)

private theorem
    CuspUniformization.logDeckTransform_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (g : LogDeck) :
    ContDiffOn ℂ ω (logDeckTransform C g) (logDomain ε) := by
  have hv :
    ContDiffOn ℂ ω
      (fun x : ℂ × ComplexPlane₂ => logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)))
      (logDomain ε) :=
    logarithmicPeriod_logDomain_mulVec_holomorphic C ε hC g.n
  exact
    (contDiff_fst.add contDiff_const).contDiffOn.prodMk
      ((contDiff_snd.add contDiff_const).contDiffOn.add hv)

private theorem
    CuspUniformization.logCover_action_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (g : LogDeck) :
    letI := logCoverAction C ε
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun x : LogCover ε => g • x) := by
  let := logCoverAction C ε
  intro x
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
        (fun y : LogCover ε => ((g • y : LogCover ε) : ℂ × ComplexPlane₂)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun y : LogCover ε => g • y) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  have h := (logDeckTransform_holomorphic C ε hC g).contMDiffOn
  exact
    (h.contMDiffAt ((logDomain ε).isOpen.mem_nhds x.2)).comp x contMDiff_subtype_val.contMDiffAt

private theorem
    CuspUniformization.logCover_continuousConstSMul (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    letI := logCoverAction C ε
    ContinuousConstSMul LogDeck (LogCover ε) := by
  let := logCoverAction C ε
  exact ⟨fun g => (logCover_action_holomorphic C ε hC g).continuous⟩

private theorem CuspUniformization.logCover_free_action (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift C ε) :
    letI := logCoverAction C ε
    IsCancelSMul LogDeck (LogCover ε) := by
  let := logCoverAction C ε
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  have hs : ‖exponential x.1.1‖ < ε := (mem_logDomain ε x).mp x.2
  have hp : 0 < ‖exponential x.1.1‖ := norm_pos_iff.mpr (exponential_ne_zero _)
  apply
    (logDeckTransform_eq_self_iff C g x
        (logarithmicPeriod_nondegenerate C x.1.1 (Real.log_neg hp (hs.trans hε1))
          (hR _ hp hs))).mp
  exact congrArg Subtype.val hx

private theorem CuspUniformization.totalPeriodRelated_iff_exists_logDeck
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (p q : ℂ × ComplexPlane₂) :
    TotalPeriodRelated C p q ↔ ∃ g : LogDeck, logDeckTransform C g q = p := by
  constructor
  · rintro ⟨k, m, n, hs, hz⟩
    exact ⟨⟨k, m, n⟩, Prod.ext hs.symm hz.symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g.k, g.m, g.n, (congrArg Prod.fst hg).symm, (congrArg Prod.snd hg).symm⟩

private theorem
    CuspUniformization.puncturedCuspCover_eq_iff_orbit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p q : LogCover ε) :
    letI := logCoverAction C ε
    puncturedCuspCover C ε p = puncturedCuspCover C ε q ↔ p ∈ MulAction.orbit LogDeck q := by
  let := logCoverAction C ε
  rw [puncturedCuspCover_eq_iff, totalPeriodRelated_iff_exists_logDeck]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩

private theorem
    CuspUniformization.mem_logDomain_iff_im (ε : ℝ) (hε : 0 < ε) (p : ℂ × ComplexPlane₂) :
    p ∈ logDomain ε ↔ -Real.log ε / (2 * Real.pi) < p.1.im := by
  rw [mem_logDomain, ← Real.log_lt_log_iff (norm_pos_iff.mpr (exponential_ne_zero p.1)) hε,
    log_norm_exponential, div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
  constructor <;> intro h <;> nlinarith

private theorem CuspUniformization.logDomain_nonempty (ε : ℝ) (hε : 0 < ε) :
    (logDomain ε : Set (ℂ × ComplexPlane₂)).Nonempty := by
  refine ⟨(((↑(-Real.log ε / (2 * Real.pi) + 1) : ℂ) * Complex.I), 0), ?_⟩
  apply (mem_logDomain_iff_im ε hε _).mpr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, MulZeroClass.mul_zero, add_zero]
  linarith

private abbrev CuspUniformization.LogModel :=
  ℂ × ComplexPlane₂

private def CuspUniformization.logCoordinateLinear : LogModel ≃ₗ[ℂ] ToricCharts.CoordinateSpace 3
    where
  toFun p := ![p.2 0, p.2 1, p.1]
  invFun w := (w 2, ![w 0, w 1])
  left_inv
    p := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  right_inv
    w := by
    ext i
    fin_cases i <;> rfl
  map_add' p
    q := by
    ext i
    fin_cases i <;> rfl
  map_smul' c
    p := by
    ext i
    fin_cases i <;> rfl

private def CuspUniformization.logCoordinateEquiv : LogModel ≃L[ℂ] ToricCharts.CoordinateSpace 3 :=
  logCoordinateLinear.toContinuousLinearEquiv

private def CuspUniformization.totalExponentialCoordinates (p : LogModel) :
    ToricCharts.CoordinateSpace 3 :=
  ![exponential (p.2 0), exponential (p.2 1), exponential p.1]

private theorem CuspUniformization.totalExponentialCoordinates_mem_torus (p : LogModel) :
    totalExponentialCoordinates p ∈ ToricCharts.torus := by
  intro i
  fin_cases i <;> exact exponential_ne_zero _

private theorem CuspUniformization.totalExponentialCoordinates_holomorphic :
    ContDiff ℂ ω totalExponentialCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 0).comp contDiff_snd)
  · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 1).comp contDiff_snd)
  · exact exponential_holomorphic.comp contDiff_fst

private def CuspUniformization.totalExponentialDerivative (p : LogModel) :
    LogModel ≃L[ℂ] ToricCharts.CoordinateSpace 3 :=
  ((ContinuousLinearEquiv.unitsEquivAut ℂ
            (Units.mk0 (exponential p.1 * (2 * Real.pi * Complex.I))
              (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero))).prodCongr
        (exponentialPairDerivative p.2)).trans
    logCoordinateEquiv

private theorem CuspUniformization.totalExponentialCoordinates_hasFDerivAt (p : LogModel) :
    HasFDerivAt totalExponentialCoordinates
      (totalExponentialDerivative p : LogModel →L[ℂ] ToricCharts.CoordinateSpace 3) p := by
  convert!
    logCoordinateEquiv.hasFDerivAt.comp p
      (((exponential_hasDerivAt p.1).hasFDerivAt_equiv
            (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero)).prodMap
        p (exponentialPair_hasFDerivAt p.2)) using
    1

end Mathoverflow1973

end
