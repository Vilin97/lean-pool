/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspBoundaryTopVanishing
public import LeanPool.HopfProblem.MainTheorem.SixSphereCube2
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology2
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz2
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Smale6
import all LeanPool.HopfProblem.Recognition.Smale7
import all LeanPool.HopfProblem.Recognition.Smale8
import all LeanPool.HopfProblem.Recognition.Smale9
import all LeanPool.HopfProblem.Recognition.Smale10
import all LeanPool.HopfProblem.Recognition.Smale11
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz1
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz2
import all LeanPool.HopfProblem.CuspFibre.CuspBoundaryTopVanishing
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube2

/-!
# Hopf problem: recognition · smale 12

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

private theorem Smale.LocalDegree.BoundaryData.normalized_homology_eq_sign_smul {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) {f : EuclideanSpace ℝ (Fin (n + 2)) → F}
    {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (b : Smale.LocalDegree.BoundaryData f L s) (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1) a =
      (SignType.sign (L.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  rw [b.normalized_homology_compare]
  exact Smale.LinearSphereAction.homology_relative_sign n L B k a

private def Smale.SphereNormalCoordinates.chartJacobian {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) (z : EuclideanSpace ℝ (Fin m)) :
    ℝ :=
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  ((chartRadialFrame c z).comp j'.symm.toContinuousLinearMap).det

private theorem
    Smale.SphereNormalCoordinates.chartJacobian_ne_zero {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) : chartJacobian c j B z ≠ 0 :=
  (Smale.RegularValues.bijective_iff_det_ne_zero _).mp
    ((bijective_chartRadialFrame c hz).comp
      ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans
          j).symm.bijective)

private theorem
    Smale.SphereNormalCoordinates.chartJacobian_factor {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)) *
        (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
      chartJacobian c j B z := by
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] F := mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)
  let C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) c z
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  have hd : fderiv ℝ (f ∘ c) z = A.comp C := by
    have h := mfderiv_comp z hf (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hB : (B.symm.toContinuousLinearMap.comp A).IsInvertible :=
    (show B.symm.toContinuousLinearMap.IsInvertible from ⟨B.symm, rfl⟩).comp hA
  have h := normalJacobian_mul_chartDet j' (c z) (B.symm.toContinuousLinearMap.comp A) hB C
  rw [normalJacobian_change_normal_model j B (c z) A hA] at h
  change normalJacobian j (c z) A * _ = _
  rw [hd]
  rw [← ContinuousLinearMap.comp_assoc]
  apply h.trans
  unfold chartJacobian
  rw [chartRadialFrame_eq c hz]

private theorem Smale.SphereNormalCoordinates.sign_factor_mo1973_5719 {a b c : ℝ} (hb : b ≠ 0)
    (h : a * b = c) : SignType.sign c * SignType.sign b = SignType.sign a := by
  have hsq : SignType.sign b * SignType.sign b = 1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hb)
  rw [← h, sign_mul, mul_assoc, hsq, mul_one]

private theorem Smale.SphereNormalCoordinates.chartJacobian_sign_factor {V F : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    SignType.sign (chartJacobian c j B z) *
        SignType.sign (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
      SignType.sign (normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z))) := by
  have h := chartJacobian_factor c j B hz f hf hA
  apply sign_factor_mo1973_5719 _ h
  intro hd
  rw [hd, MulZeroClass.mul_zero] at h
  exact chartJacobian_ne_zero c j B hz h.symm

private theorem Smale.SpherePoint.chart_radial_frame_det {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y)
    (j : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] V) :
    ((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y)
                0).comp
            j.symm.toContinuousLinearMap).det *
        (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det *
        ((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered x)
                0).comp
            j.symm.toContinuousLinearMap).det := by
  let L := Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he
  let Q := (ContinuousLinearMap.id ℝ ℝ).prodMap L.toContinuousLinearMap
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (Q.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = L.toLinearEquiv.toLinearMap.det := by
    have hconj : T.det = Q.det := LinearMap.det_conj Q.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) L.toLinearEquiv.toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor :
    ((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y)
                0).comp
            j.symm.toContinuousLinearMap).comp
        T =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered x)
              0).comp
          j.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    change
      Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y) 0
          (j.symm (j (Q (j.symm v)))) =
        R
          (Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered x)
            0 (j.symm v))
    rw [j.symm_apply_apply]
    exact
      congrArg (fun A : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] V => A (j.symm v))
        (chart_radial_frame_comp x y R he)
  calc
    _ =
        (((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y)
                    0).comp
                j.symm.toContinuousLinearMap).comp
            T).det := by
      rw [hdetT.symm]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := (congrArg ContinuousLinearMap.det hfactor).trans (LinearMap.det_comp _ _)

private theorem Smale.SpherePoint.chartJacobian_transport {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (ℝ × F) ≃L[ℝ] V)
    (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered y) j B 0 *
        (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det *
        Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B
          0 :=
  chart_radial_frame_det x y R he
    ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j)

private theorem Smale.SpherePoint.chartJacobian_transport_sign {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hR : R.toLinearEquiv.toLinearMap.det = 1)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    SignType.sign
          (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered y) j
            B 0) *
        SignType.sign
          (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
              he).toLinearEquiv.toLinearMap.det =
      SignType.sign
        (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B
          0) := by
  have h := chartJacobian_transport x y R he j B
  rw [hR, one_mul] at h
  rw [← sign_mul, h]

private def Smale.CoverNaturality.overlapCoordinateMap {X Y S T : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace S] [TopologicalSpace T] (U V : Set X) (U' V' : Set Y)
    (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (eS : S ≃ₕ ↥(U ∩ V))
    (eT : T ≃ₕ ↥(U' ∩ V')) : C(S, T) :=
  eT.invFun.comp
    ((mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hfU hfV)).comp eS.toFun)

private theorem Smale.CoverNaturality.normalized_connecting_naturality {X Y S T : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S] [TopologicalSpace T]
    (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (eS : S ≃ₕ ↥(U ∩ V)) (eT : T ≃ₕ ↥(U' ∩ V')) (hU : IsOpen U)
    (hV : IsOpen V) (hc : U ∪ V = Set.univ) (hU' : IsOpen U') (hV' : IsOpen V')
    (hc' : U' ∪ V' = Set.univ) (k : ℕ) (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (overlapCoordinateMap U V U' V' f hfU hfV eS eT) k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv eS k).symm
          (SingularMayerVietoris.connectingHomomorphism U V hU hV hc k a)) =
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv eT k).symm
        (SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' k
          (SingularMayerVietoris.singularHomologyMap f (k + 1) a)) := by
  have hS :
    SingularMayerVietoris.singularHomologyMap eS.toFun k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv eS k).symm
          (SingularMayerVietoris.connectingHomomorphism U V hU hV hc k a)) =
      SingularMayerVietoris.connectingHomomorphism U V hU hV hc k a :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv eS k).apply_symm_apply _
  unfold overlapCoordinateMap
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply, hS,
    connecting_naturality_apply U V U' V' f hfU hfV hU hV hc hU' hV' hc',
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply]
  rfl

private theorem
    Smale.LocalDegree.PointTransition.maps_point_complement {M : Type} [TopologicalSpace M]
    (e : M ≃ₜ M) (x y : M) (he : e x = y) : Set.MapsTo e { x }ᶜ { y }ᶜ := by
  intro z hz h
  exact hz (e.injective (h.trans he.symm))

private def Smale.LocalDegree.PointTransition.coordinateMap {E F G M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered (D := E) x) Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy)) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1) :=
  Smale.CoverNaturality.overlapCoordinateMap { x }ᶜ
    (Smale.LocalDegree.NativeNeighborhood.openSet x dx) { y }ᶜ
    (Smale.LocalDegree.NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv x dx)
    (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv y dy)

private theorem Smale.LocalDegree.PointTransition.coordinateMap_coe {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G}
    {Wx Wy : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered (D := E) x) Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy))
    (u : Metric.sphere (0 : E) 1) :
    (coordinateMap x y dx dy e he hV u).val =
      ‖(Smale.NativeParametrization.centered (D := E) y).symm
              (e
                (Smale.NativeParametrization.centered (D := E) x
                  (dx.innerBoundary.radius • (u : E))))‖⁻¹ •
        (Smale.NativeParametrization.centered (D := E) y).symm
          (e
            (Smale.NativeParametrization.centered (D := E) x
              (dx.innerBoundary.radius • (u : E)))) :=
  rfl

private theorem Smale.LocalDegree.PointTransition.connecting_naturality {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G}
    {Wx Wy : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered (D := E) x) Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy))
    [T1Space M] (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (coordinateMap x y dx dy e he hV) k
        (Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx k a) =
      Smale.LocalDegree.NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) :=
  Smale.CoverNaturality.normalized_connecting_naturality { x }ᶜ
    (Smale.LocalDegree.NativeNeighborhood.openSet x dx) { y }ᶜ
    (Smale.LocalDegree.NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv x dx)
    (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv y dy) isClosed_singleton.isOpen_compl
    (Smale.LocalDegree.NativeNeighborhood.isOpen_openSet x dx)
    (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover x dx) isClosed_singleton.isOpen_compl
    (Smale.LocalDegree.NativeNeighborhood.isOpen_openSet y dy)
    (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover y dy) k a

private def Smale.LocalDegree.NeighborhoodData.restrictRadius {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) (r : ℝ) (hr : 0 < r)
    (hrR : r ≤ d.radius) : Smale.LocalDegree.NeighborhoodData f L s
    where
  radius := r
  radius_pos := hr
  center_zero := d.center_zero
  ball_subset := (Metric.closedBall_subset_closedBall hrR).trans d.ball_subset
  continuous := d.continuous.mono (Metric.closedBall_subset_closedBall hrR)
  remainder_bound x hx := d.remainder_bound x (Metric.closedBall_subset_closedBall hrR hx)

private theorem Smale.LocalDegree.NativeNeighborhood.identity_center_mo1973_5731 {M : Type}
    [TopologicalSpace M] (x : M) : (Homeomorph.refl M) x = x :=
  rfl

private theorem Smale.LocalDegree.NativeNeighborhood.openSet_restrictRadius_subset {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    openSet x (d.restrictRadius r hr hrR) ⊆ openSet x d := by
  change
    (Smale.NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph '' Metric.ball 0 r ⊆
      (Smale.NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph ''
        Metric.ball 0 d.radius
  exact Set.image_mono (Metric.ball_subset_ball hrR)

private theorem Smale.LocalDegree.NativeNeighborhood.mapsTo_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    Set.MapsTo (Homeomorph.refl M) (openSet x (d.restrictRadius r hr hrR)) (openSet x d) :=
  openSet_restrictRadius_subset x d r hr hrR

private theorem Smale.LocalDegree.NativeNeighborhood.coordinateMap_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    Smale.LocalDegree.PointTransition.coordinateMap x x (d.restrictRadius r hr hrR) d
        (Homeomorph.refl M) (identity_center_mo1973_5731 x) (mapsTo_restrictRadius x d r hr hrR) =
      ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [Smale.LocalDegree.PointTransition.coordinateMap_coe]
  let ds := d.restrictRadius r hr hrR
  change
    ‖(Smale.NativeParametrization.centered (D := E) x).symm
              (Smale.NativeParametrization.centered (D := E) x
                (ds.innerBoundary.radius • (u : E)))‖⁻¹ •
        (Smale.NativeParametrization.centered (D := E) x).symm
          (Smale.NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
      (u : E)
  have hu : ds.innerBoundary.radius • (u : E) ∈ (Smale.NativeParametrization.centered x).source :=
    closedBall_subset_source x ds (Metric.ball_subset_closedBall (ds.innerBoundary_mem_ball u))
  have hleft :
    (Smale.NativeParametrization.centered (D := E) x).symm
        (Smale.NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
      ds.innerBoundary.radius • (u : E) :=
    (Smale.NativeParametrization.centered x).left_inv' hu
  rw [hleft, Smale.LocalDegree.norm_radius_smul _ ds.innerBoundary.radius_pos,
    inv_smul_smul₀ ds.innerBoundary.radius_pos.ne']

private theorem Smale.LocalDegree.NativeNeighborhood.sphereConnecting_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) [T1Space M] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    sphereConnecting x (d.restrictRadius r hr hrR) k a = sphereConnecting x d k a := by
  have h :=
    Smale.LocalDegree.PointTransition.connecting_naturality x x (d.restrictRadius r hr hrR) d
      (Homeomorph.refl M) (identity_center_mo1973_5731 x) (mapsTo_restrictRadius x d r hr hrR) k a
  rw [coordinateMap_restrictRadius, PeriodTorusHigherHomology.singularHomologyMap_id,
    LinearMap.id_apply] at h
  change
    sphereConnecting x (d.restrictRadius r hr hrR) k a =
      sphereConnecting x d k
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id M) (k + 1) a) at h
  rwa [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at h

private theorem Smale.LocalDegree.NativeNeighborhood.sphereConnecting_eq {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f' : M → F'}
    {L' : E ≃L[ℝ] F'} {W' : Set M}
    (d' :
      Smale.LocalDegree.NeighborhoodData (f' ∘ Smale.NativeParametrization.centered (D := E) x) L'
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W'))
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    sphereConnecting x d k a = sphereConnecting x d' k a := by
  let ρ := Min.min d.radius d'.radius
  have hρ : 0 < ρ := lt_min d.radius_pos d'.radius_pos
  rw [← sphereConnecting_restrictRadius x d ρ hρ (min_le_left _ _) k a, ←
    sphereConnecting_restrictRadius x d' ρ hρ (min_le_right _ _) k a]
  rfl

private theorem Smale.LocalDegree.PointTransition.coordinateMap_eq_boundary {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData
        (((Smale.NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          Smale.NativeParametrization.centered (D := E) x)
        Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy)) :
    coordinateMap x y dx dy e he hV = dx.innerBoundary.normalizedMap :=
  rfl

private theorem Smale.LocalDegree.PointTransition.coordinateMap_homology {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData
        (((Smale.NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          Smale.NativeParametrization.centered (D := E) x)
        Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy))
    (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap (coordinateMap x y dx dy e he hV) k =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k := by
  rw [coordinateMap_eq_boundary]
  exact dx.innerBoundary.normalized_homology_compare k

private theorem Smale.LocalDegree.PointTransition.connecting_derivative_naturality {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData
        (((Smale.NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          Smale.NativeParametrization.centered (D := E) x)
        Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy))
    [T1Space M] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f₀ : M → F} {L₀ : E ≃L[ℝ] F}
    {W₀ : Set M}
    (d₀ :
      Smale.LocalDegree.NeighborhoodData (f₀ ∘ Smale.NativeParametrization.centered (D := E) x) L₀
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W₀))
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k
        (Smale.LocalDegree.NativeNeighborhood.sphereConnecting x d₀ k a) := by
  have h := connecting_naturality x y dx dy e he hV k a
  rw [coordinateMap_homology x y e he dy dx hV k,
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting_eq x dx d₀ k a] at h
  exact h.symm

private theorem
    Smale.LocalDegree.pointConnecting_diffeomorph {E F G M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F}
    {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
    (dx :
      NeighborhoodData (fx ∘ Smale.NativeParametrization.centered (D := E) x) Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomeomorph.toHomotopyEquiv.toFun (k + 1)
          a) =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap
          (Smale.NativeChartTransition.linear x y e he).toContinuousLinearMap
          (Smale.NativeChartTransition.linear x y e he).injective)
        k (NativeNeighborhood.sphereConnecting x dx k a) := by
  let W := e.toHomeomorph ⁻¹' NativeNeighborhood.openSet y dy
  have hW : W ∈ 𝓝 x := by
    apply e.toHomeomorph.continuous.continuousAt
    have hy :=
      (NativeNeighborhood.isOpen_openSet y dy).mem_nhds
        (NativeNeighborhood.center_mem_openSet y dy)
    exact he.symm ▸ hy
  obtain ⟨b⟩ := Smale.NativeChartTransition.nonempty_neighborhoodData x y e he W hW
  have hV :
    Set.MapsTo e.toHomeomorph (NativeNeighborhood.openSet x b)
      (NativeNeighborhood.openSet y dy) :=
    NativeNeighborhood.openSet_subset x b
  exact PointTransition.connecting_derivative_naturality x y e.toHomeomorph he dy b hV dx k a

private theorem Smale.SpherePoint.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] Smale.SpherePoint.instLocal1 in
private def Smale.SpherePoint.pointDiffeomorph (n : ℕ) (x y : SphereHomology.UnitSphere (n + 2)) :
    Diffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2))
      (SphereHomology.UnitSphere (n + 2)) ∞ :=
  sphereDiffeomorph (positiveTransport (n + 1) x y)

attribute [local instance] Smale.SpherePoint.instLocal1 in
private theorem Smale.SpherePoint.pointDiffeomorph_apply (n : ℕ)
    (x y : SphereHomology.UnitSphere (n + 2)) : pointDiffeomorph n x y x = y :=
  positiveTransport_moves (n + 1) x y

attribute [local instance] Smale.SpherePoint.instLocal1 in
private def Smale.SpherePoint.pointChartLinear (n : ℕ) (x y : SphereHomology.UnitSphere (n + 2)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  Smale.NativeChartTransition.linear x y (pointDiffeomorph n x y) (pointDiffeomorph_apply n x y)

attribute [local instance] Smale.SpherePoint.instLocal1 in
private theorem
    Smale.SpherePoint.pointClass_sign_compare (n : ℕ) {F G : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (x y : SphereHomology.UnitSphere (n + 2)) {fx : SphereHomology.UnitSphere (n + 2) → F}
    {fy : SphereHomology.UnitSphere (n + 2) → G} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G}
    {Wx Wy : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered y) Ly
        ((Smale.NativeParametrization.centered y).source ∩
          Smale.NativeParametrization.centered y ⁻¹' Wy))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      (SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det : ℤ) •
        Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a := by
  have h :=
    Smale.LocalDegree.pointConnecting_diffeomorph x y dx dy (pointDiffeomorph n x y)
      (pointDiffeomorph_apply n x y) (k + 1) a
  have hid :
    SingularMayerVietoris.singularHomologyMap
        (pointDiffeomorph n x y).toHomeomorph.toHomotopyEquiv.toFun (k + 2) a =
      a :=
    positiveTransport_homology (n + 1) x y (k + 2) a
  rw [hid] at h
  apply h.trans
  exact Smale.LinearSphereAction.homology_eq_sign_smul n (pointChartLinear n x y) k _

private def
    Smale.SpherePoint.punctureHomeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1) :
    ↥({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) x).symm).trans
    ((stereographic' n x).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target x)).trans (Homeomorph.Set.univ _)))

private theorem Smale.SpherePoint.puncture_contractible {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) : ContractibleSpace ({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) :=
  (punctureHomeomorph (n := n) x).contractibleSpace

private def Smale.SpherePoint.connectingHomologyEquiv {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (x : Metric.sphere (0 : V) 1)
    {f : Metric.sphere (0 : V) 1 → F} {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] F}
    {W : Set (Metric.sphere (0 : V) 1)}
    (d :
      Smale.LocalDegree.NeighborhoodData
        (f ∘ Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x) L
        ((Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x).source ∩
          Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x ⁻¹' W))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : V) 1) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
        (k + 1) := by
  let : ContractibleSpace ({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) :=
    puncture_contractible (n := n) x
  exact Smale.LocalDegree.NativeNeighborhood.sphereHomologyEquiv x d k

private theorem Smale.SpherePoint.instLocal2 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] Smale.SpherePoint.instLocal2 in
private def Smale.SpherePoint.outwardPointClass (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  (SignType.sign
        (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B
          0) :
      ℤ) •
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1)

attribute [local instance] Smale.SpherePoint.instLocal2 in
private theorem Smale.SpherePoint.outwardPointClass_eq (n : ℕ) {F G H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x y : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {fy : SphereHomology.UnitSphere (n + 2) → G}
    {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G}
    {Wx Wy : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered y) Ly
        ((Smale.NativeParametrization.centered y).source ∩
          Smale.NativeParametrization.centered y ⁻¹' Wy))
    (k : ℕ) : outwardPointClass n j B y dy k = outwardPointClass n j B x dx k := by
  have hs :=
    chartJacobian_transport_sign x y (positiveTransport (n + 1) x y)
      (positiveTransport_moves (n + 1) x y) (positiveTransport_det (n + 1) x y) j B
  have hs' :
    SignType.sign
          (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered y) j
            B 0) *
        SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det =
      SignType.sign
        (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B
          0) :=
    hs
  apply LinearMap.ext
  intro a
  change
    (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered y)
              j B 0) :
          ℤ) •
        Smale.LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      _
  rw [pointClass_sign_compare n x y dx dy k a, smul_smul, ← SignType.coe_mul, hs']
  rfl

attribute [local instance] Smale.SpherePoint.instLocal2 in
private theorem Smale.SpherePoint.chartSign_mul_self (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2)) :
    (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) *
        (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) =
      1 := by
  have hn :=
    Smale.SphereNormalCoordinates.chartJacobian_ne_zero (Smale.NativeParametrization.centered x) j
      B (Smale.NativeParametrization.zero_mem_centered_source x)
  have hs :
    SignType.sign
          (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j
            B 0) *
        SignType.sign
          (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j
            B 0) =
      1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hn)
  simpa only [SignType.coe_mul, SignType.coe_one] using congrArg (fun s : SignType => (s : ℤ)) hs

attribute [local instance] Smale.SpherePoint.instLocal2 in
private theorem
    Smale.SpherePoint.connecting_eq_sign_outward (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a =
      (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        outwardPointClass n j B x dx k a := by
  change
    _ =
      (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        ((SignType.sign
              (Smale.SphereNormalCoordinates.chartJacobian
                (Smale.NativeParametrization.centered x) j B 0) :
            ℤ) •
          Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a)
  rw [smul_smul, chartSign_mul_self n j B x, one_smul]

attribute [local instance] Smale.SpherePoint.instLocal2 in
private def Smale.SpherePoint.outwardPointClassEquiv (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) := by
  let C := connectingHomologyEquiv x dx k
  let s : ℤ :=
    SignType.sign
      (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B 0)
  have hs : s * s = 1 := chartSign_mul_self n j B x
  refine LinearEquiv.ofBijective (outwardPointClass n j B x dx k) ⟨?_, ?_⟩
  · intro a b hab
    apply C.injective
    have h := congrArg (fun z => s • z) hab
    change s • (s • C a) = s • (s • C b) at h
    simpa only [smul_smul, hs, one_smul] using h
  · intro b
    refine ⟨C.symm (s • b), ?_⟩
    change s • C (C.symm (s • b)) = b
    rw [C.apply_symm_apply, smul_smul, hs, one_smul]

private theorem Smale.SpherePoint.instLocal3 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] Smale.SpherePoint.instLocal3 in
private def Smale.SpherePoint.referencePoint (n : ℕ) : SphereHomology.UnitSphere (n + 2) :=
  Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)

attribute [local instance] Smale.SpherePoint.instLocal3 in
private def
    Smale.SpherePoint.referenceNeighborhood (n : ℕ) (x : SphereHomology.UnitSphere (n + 2)) :
    Smale.LocalDegree.NeighborhoodData
      (((Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin (n + 2))) x).symm ∘
          Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) ∘
        Smale.NativeParametrization.centered x)
      (Smale.NativeChartTransition.linear x x
        (Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) rfl)
      ((Smale.NativeParametrization.centered x).source ∩
        Smale.NativeParametrization.centered x ⁻¹'
          (Set.univ : Set (SphereHomology.UnitSphere (n + 2)))) :=
  Classical.choice
    (Smale.NativeChartTransition.nonempty_neighborhoodData x x
      (Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) rfl Set.univ (by simp))

attribute [local instance] Smale.SpherePoint.instLocal3 in
private def
    Smale.SpherePoint.outwardClass (n : ℕ) {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  outwardPointClass n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

attribute [local instance] Smale.SpherePoint.instLocal3 in
private def Smale.SpherePoint.outwardClassEquiv (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  outwardPointClassEquiv n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

attribute [local instance] Smale.SpherePoint.instLocal3 in
private theorem
    Smale.SpherePoint.outwardPointClass_eq_global (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : SphereHomology.UnitSphere (n + 2))
    {f : SphereHomology.UnitSphere (n + 2) → F} {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {W : Set (SphereHomology.UnitSphere (n + 2))}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered x) L
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' W))
    (k : ℕ) : outwardPointClass n j B x d k = outwardClass n j B k :=
  outwardPointClass_eq n j B (referencePoint n) x (referenceNeighborhood n (referencePoint n)) d k

attribute [local instance] Smale.SpherePoint.instLocal3 in
private theorem
    Smale.SpherePoint.pointConnecting_eq_outward (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : SphereHomology.UnitSphere (n + 2))
    {f : SphereHomology.UnitSphere (n + 2) → F} {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {W : Set (SphereHomology.UnitSphere (n + 2))}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered x) L
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' W))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting x d (k + 1) a =
      (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        outwardClass n j B k a := by
  rw [connecting_eq_sign_outward n j B x d k a, outwardPointClass_eq_global]

private def
    Smale.SpherePoint.sourceCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (n + 2) ≃ₗ[ℤ] ℤ :=
  (outwardClassEquiv n j B n).trans (SphereHomology.unitSphereHomologyTopEquiv n)

private def
    Smale.SpherePoint.overlapCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) (n + 1) ≃ₗ[ℤ] ℤ :=
  (Smale.LinearSphereAction.homologyEquiv B (n + 1)).symm.trans
    (SphereHomology.unitSphereHomologyTopEquiv n)

private def
    Smale.SpherePoint.targetCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (n + 2) ≃ₗ[ℤ] ℤ :=
  (Smale.OnePointCover.sphereHomologyEquiv 1 zero_lt_one n).trans (overlapCountMark n B)

private theorem Smale.SpherePoint.overlapCountMark_linear (n : ℕ) {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (n + 1)) :
    overlapCountMark n B
        (SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (n + 1) a) =
      SphereHomology.unitSphereHomologyTopEquiv n a := by
  rw [← Smale.LinearSphereAction.homologyEquiv_apply]
  change
    SphereHomology.unitSphereHomologyTopEquiv n
        ((Smale.LinearSphereAction.homologyEquiv B (n + 1)).symm
          (Smale.LinearSphereAction.homologyEquiv B (n + 1) a)) =
      _
  rw [LinearEquiv.symm_apply_apply]

private theorem Smale.SpherePoint.countMark_of_connecting (n : ℕ) {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)
    (u : SingularMayerVietoris.SingularHomology (OnePoint N) (n + 2))
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (n + 2))
    (c : ℤ)
    (h :
      Smale.OnePointCover.sphereConnecting 1 zero_lt_one (n + 1) u =
        c •
          SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (n + 1)
            (outwardClass n j B n a)) :
    targetCountMark n B u = c * sourceCountMark n j B a := by
  have h' := congrArg (overlapCountMark n B) h
  rw [map_zsmul, overlapCountMark_linear] at h'
  exact h'

private theorem Smale.HomologyTransport.exists_split_rank_one_extension {R : Type*} [CommRing R]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (i : A →ₗ[R] B)
    (p : B →ₗ[R] R) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.ker p = LinearMap.range i) :
    ∃ e : (A × R) ≃ₗ[R] B, (∀ a, e (a, 0) = i a) ∧ ∀ z, p (e z) = z.2 := by
  obtain ⟨b, hb⟩ := hp 1
  let s : R →ₗ[R] B := LinearMap.toSpanSingleton R B b
  have hs (z : R) : p (s z) = z := by
    change p (z • b) = z
    rw [map_smul, hb, smul_eq_mul, mul_one]
  have hz (a : A) : p (i a) = 0 := by
    have h : i a ∈ LinearMap.range i := ⟨a, rfl⟩
    rw [← hk] at h
    exact h
  let F : (A × R) →ₗ[R] B := i.coprod s
  have hF (z : A × R) : p (F z) = z.2 := by
    change p (i z.1 + s z.2) = z.2
    rw [map_add, hz, hs, zero_add]
  have hinj : Function.Injective F := by
    intro x y h
    have h₂ : x.2 = y.2 := (hF x).symm.trans ((congrArg p h).trans (hF y))
    apply Prod.ext _ h₂
    apply hi
    change i x.1 + s x.2 = i y.1 + s y.2 at h
    rw [h₂] at h
    exact add_right_cancel h
  have hsurj : Function.Surjective F := by
    intro v
    have hv : v - s (p v) ∈ LinearMap.ker p := by
      change p (v - s (p v)) = 0
      rw [map_sub, hs, sub_self]
    rw [hk] at hv
    obtain ⟨a, ha⟩ := hv
    refine ⟨(a, p v), ?_⟩
    change i a + s (p v) = v
    rw [ha, sub_add_cancel]
  refine ⟨LinearEquiv.ofBijective F ⟨hinj, hsurj⟩, ?_, hF⟩
  intro a
  change i a + s 0 = i a
  rw [map_zero, add_zero]

private theorem Smale.HomologyTransport.exists_add_split_rank_one_extension {R : Type*} [CommRing R]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (i : A →ₗ[R] B)
    (p : B →ₗ[R] R) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.ker p = LinearMap.range i) :
    ∃ e : (A × R) ≃+ B, (∀ a, e (a, 0) = i a) ∧ ∀ z, p (e z) = z.2 := by
  obtain ⟨e, he, hp⟩ := exists_split_rank_one_extension i p hi hp hk
  exact ⟨e.toAddEquiv, he, hp⟩

private def
    Smale.ManifoldMorse.MorseSurgeryData.indexTwoNormalModel {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] d.chart.NegativeCoordinates :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [hindex])

private def Smale.ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2 →ₗ[ℤ] ℤ :=
  (Smale.SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2)

private theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    Function.Surjective (d.indexTwoCollapseCoordinate hf hindex) :=
  (Smale.SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).surjective.comp
    (d.upperCollapse_surjective_of_lower hf 0)

private theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    LinearMap.ker (d.indexTwoCollapseCoordinate hf hindex) =
      LinearMap.range (d.lowerRealizationHomologyMap 2) := by
  rw [← d.upperCollapse_homology_kernel hf 1]
  ext a
  let C := Smale.SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)
  change
    C (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2 a) = 0 ↔
      SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2 a = 0
  constructor
  · intro h
    exact C.injective (h.trans (map_zero C).symm)
  · intro h
    rw [h, map_zero]

private theorem Smale.ManifoldMorse.MorseSurgeryData.lowerRealization_two_injective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    Function.Injective (d.lowerRealizationHomologyMap 2) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :=
    d.attachingHomology_subsingleton_of_index 2 (by norm_num) (by omega) (by omega)
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_lower hf 2 (by norm_num)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.coreBoundaryHomologyMap 2 a = 0
  rw [Subsingleton.elim a 0, map_zero]

private theorem Smale.ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    ∃ H :
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2 × ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2,
      (∀ a, H (a, 0) = d.lowerRealizationHomologyMap 2 a) ∧
        ∀ z, d.indexTwoCollapseCoordinate hf hindex (H z) = z.2 := by
  obtain ⟨H, hH, hcoord⟩ :=
    Smale.HomologyTransport.exists_add_split_rank_one_extension (d.lowerRealizationHomologyMap 2)
      (d.indexTwoCollapseCoordinate hf hindex) (d.lowerRealization_two_injective hf hindex)
      (d.indexTwoCoordinate_surjective hf hindex) (d.indexTwoCoordinate_kernel hf hindex)
  exact ⟨H.toIntLinearEquiv, hH, hcoord⟩

private def Smale.HomologyTransport.integerCoordinateSplit (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃+ ((Fin n → ℤ) × ℤ)
    where
  toFun v := (fun i => v i.succ, v 0)
  invFun v := Fin.cons v.2 v.1
  left_inv
    v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv v := rfl
  map_add' _ _ := rfl

private theorem Smale.ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)]
    (n : ℕ)
    (e :
      (Fin n → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) :
    ∃ H :
      (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2,
      (∀ v, H (Fin.cons 0 v) = d.lowerRealizationHomologyMap 2 (e v)) ∧
        ∀ v, d.indexTwoCollapseCoordinate hf hindex (H v) = v 0 := by
  obtain ⟨H, hH, hcoord⟩ := d.exists_indexTwoHomology_split hf hindex
  let G :=
    (Smale.HomologyTransport.integerCoordinateSplit n).trans
      ((e.toAddEquiv.prodCongr (AddEquiv.refl ℤ)).trans H.toAddEquiv)
  refine ⟨G.toIntLinearEquiv, ?_, ?_⟩
  · intro v
    exact hH (e v)
  · intro v
    exact hcoord (e (fun i => v i.succ), v 0)

private def Smale.ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (n : ℕ) : Prop :=
  ∀ i : Fin S.count,
    0 < i.val → i.val ≤ n → Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2

private theorem
    Smale.ManifoldMorse.SurgeryWindows.indexTwoPrefix_mono {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) {n m : ℕ} (hnm : n ≤ m)
    (h : S.HasIndexTwoPrefix m) : S.HasIndexTwoPrefix n := fun i hi hin => h i hi (hin.trans hnm)

private theorem
    Smale.ManifoldMorse.SurgeryWindows.indexTwoBasis_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    (hn : n + 1 < S.count) (hpre : S.HasIndexTwoPrefix (n + 1))
    (e :
      (Fin n → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology
          { x : M // f x ≤ S.upper (S.point ⟨n, Nat.lt_of_succ_lt hn⟩) } 2) :
    let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
    ∃ H :
      (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n + 1, hn⟩) } 2,
      (∀ v,
          H (Fin.cons 0 v) =
            (S.data (S.point ⟨n + 1, hn⟩)).lowerRealizationHomologyMap 2
              (B.homologyEquiv 2 (e v))) ∧
        ∀ v,
          (S.data (S.point ⟨n + 1, hn⟩)).indexTwoCollapseCoordinate hf.continuous
              (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) (H v) =
            v 0 := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) - (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2 }
        1) :=
    S.lower_homologyOne_subsingleton_of_indices hf ⟨n + 1, hn⟩ (Nat.succ_pos n)
      (fun i hi hin => by
        have h := hpre i hi (Nat.le_of_lt hin)
        omega)
  let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
  exact
    (S.data (S.point ⟨n + 1, hn⟩)).exists_indexTwoBasis_extension hf.continuous
      (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) n (e.trans (B.homologyEquiv 2))

private def Smale.ManifoldMorse.SurgeryWindows.indexTwoBasis {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    (n : ℕ) →
      (hn : n < S.count) →
        S.HasIndexTwoPrefix n →
          (Fin n → ℤ) ≃ₗ[ℤ]
            SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n, hn⟩) } 2
  | 0, hn, _ =>
    by
    let :
      Subsingleton
        (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨0, hn⟩) } 2) :=
      by
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 2 (by norm_num)
    exact LinearEquiv.ofSubsingleton _ _
  | n + 1, hn, hpre =>
    Classical.choose
      (S.indexTwoBasis_step hf n hn hpre
        (indexTwoBasis (S := S) hf n (Nat.lt_of_succ_lt hn)
          (S.indexTwoPrefix_mono (Nat.le_succ n) hpre)))

private def Smale.ManifoldMorse.MorseSurgeryData.indexThreeBoundaryEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2 ≃ₗ[ℤ]
      ℤ := by
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1) := ⟨hindex⟩
  let H :=
    PeriodTorusHigherHomology.homeomorphHomologyEquiv
      (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 2).toHomeomorph
      2
  exact H.symm.trans (SphereHomology.unitSphereHomologyTopEquiv 1)

private theorem Smale.ManifoldMorse.MorseSurgeryData.indexThreeBoundary_scalar {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :
    a = (d.indexThreeBoundaryEquiv hindex a) • (d.indexThreeBoundaryEquiv hindex).symm 1 := by
  apply (d.indexThreeBoundaryEquiv hindex).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply, zsmul_eq_mul, mul_one]
  simp

private def Smale.ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2 :=
  d.coreBoundaryHomologyMap 2 ((d.indexThreeBoundaryEquiv hindex).symm 1)

private theorem Smale.ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :
    d.coreBoundaryHomologyMap 2 a =
      (d.indexThreeBoundaryEquiv hindex a) • d.indexThreeAttachingClass hindex := by
  conv_lhs => rw [d.indexThreeBoundary_scalar hindex a]
  rw [map_zsmul]
  rfl

private theorem Smale.ManifoldMorse.MorseSurgeryData.coreBoundary_two_range {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.range (d.coreBoundaryHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [d.coreBoundary_two_eq_smul hindex b]
    exact
      Submodule.mem_span_singleton.mpr
        ⟨d.indexThreeBoundaryEquiv hindex b,
          int_smul_eq_zsmul
            (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 }
                2).isModule
            _ _⟩
  · intro ha
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp ha
    refine ⟨z • (d.indexThreeBoundaryEquiv hindex).symm 1, ?_⟩
    rw [map_zsmul]
    exact
      (int_smul_eq_zsmul
            (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 }
                2).isModule
            z (d.indexThreeAttachingClass hindex)).symm.trans
        hz

private theorem
    Smale.ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    Function.Surjective (d.lowerRealizationHomologyMap 2) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        1) :=
    d.attachingHomology_subsingleton_of_index 1 one_ne_zero (by omega) (by omega)
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 1) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_upper hf 1] at ha
  exact ha

private theorem Smale.ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.ker (d.lowerRealizationHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  rw [← d.morse_exact_at_lower hf 2 (by norm_num), d.coreBoundary_two_range hindex]

public
theorem Smale.HomologyTransport.ker_comp_span_singleton {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (p : A →ₗ[R] B) (q : B →ₗ[R] C) (v : A) (hq : LinearMap.ker q = Submodule.span R {p v}) :
    LinearMap.ker (q.comp p) = LinearMap.ker p ⊔ Submodule.span R { v } := by
  apply le_antisymm
  · intro a ha
    have hpa : p a ∈ Submodule.span R {p v} := by
      rw [← hq]
      exact ha
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hpa
    have hk : a - r • v ∈ LinearMap.ker p := by
      change p (a - r • v) = 0
      rw [map_sub, map_smul, hr, sub_self]
    exact
      Submodule.mem_sup.mpr
        ⟨a - r • v, hk, r • v, Submodule.smul_mem _ _ (Submodule.subset_span (by simp)),
          sub_add_cancel _ _⟩
  · apply sup_le
    · intro a ha
      change q (p a) = 0
      change p a = 0 at ha
      rw [ha, map_zero]
    · apply Submodule.span_le.mpr
      intro a ha
      have ha' : a = v := Set.mem_singleton_iff.mp ha
      subst a
      change p v ∈ LinearMap.ker q
      rw [hq]
      exact Submodule.subset_span (by simp)

private structure
    Smale.IntegerPresentation (B : Type*) [AddCommGroup B] [Module ℤ B] (r c : ℕ) where
  map : (Fin r → ℤ) →ₗ[ℤ] B
  columns : Fin c → (Fin r → ℤ)
  surjective : Function.Surjective map
  kernel_eq : LinearMap.ker map = Submodule.span ℤ (Set.range columns)

private def Smale.IntegerPresentation.ofEquiv {B : Type*} [AddCommGroup B] [Module ℤ B] {r : ℕ}
    (e : (Fin r → ℤ) ≃ₗ[ℤ] B) : Smale.IntegerPresentation B r 0
    where
  map := e.toLinearMap
  columns := Fin.elim0
  surjective := e.surjective
  kernel_eq := by
    rw [LinearMap.ker_eq_bot.mpr e.injective]
    simp

private def Smale.IntegerPresentation.transport {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : Smale.IntegerPresentation B r c) (e : B ≃ₗ[ℤ] C) :
    Smale.IntegerPresentation C r c
    where
  map := e.toLinearMap.comp P.map
  columns := P.columns
  surjective := e.surjective.comp P.surjective
  kernel_eq := by
    have h : LinearMap.ker (e.toLinearMap.comp P.map) = LinearMap.ker P.map := by
      ext v
      change e (P.map v) = 0 ↔ P.map v = 0
      constructor
      · intro hv
        exact e.injective (hv.trans (map_zero e).symm)
      · intro hv
        rw [hv, map_zero]
    exact h.trans P.kernel_eq

private def
    Smale.IntegerPresentation.liftRelation {B : Type*} [AddCommGroup B] [Module ℤ B] {r c : ℕ}
    (P : Smale.IntegerPresentation B r c) (b : B) : Fin r → ℤ :=
  Classical.choose (P.surjective b)

private theorem Smale.IntegerPresentation.map_liftRelation {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : Smale.IntegerPresentation B r c) (b : B) : P.map (P.liftRelation b) = b :=
  Classical.choose_spec (P.surjective b)

private def
    Smale.IntegerPresentation.adjoin {B C : Type*} [AddCommGroup B] [AddCommGroup C] [Module ℤ B]
    [Module ℤ C] {r c : ℕ} (P : Smale.IntegerPresentation B r c) (q : B →ₗ[ℤ] C)
    (hq : Function.Surjective q) (b : B) (hker : LinearMap.ker q = Submodule.span ℤ { b }) :
    Smale.IntegerPresentation C r (c + 1)
    where
  map := q.comp P.map
  columns := Fin.cons (P.liftRelation b) P.columns
  surjective := hq.comp P.surjective
  kernel_eq := by
    have hk : LinearMap.ker q = Submodule.span ℤ {P.map (P.liftRelation b)} := by
      rw [P.map_liftRelation]
      exact hker
    rw [Smale.HomologyTransport.ker_comp_span_singleton P.map q (P.liftRelation b) hk,
      P.kernel_eq, Fin.range_cons, Submodule.span_insert, sup_comm]

private def Smale.ManifoldMorse.MorseSurgeryData.indexThreePresentation {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) {r c : ℕ}
    (P :
      Smale.IntegerPresentation
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) r c) :
    Smale.IntegerPresentation
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2) r
      (c + 1) :=
  P.adjoin (d.lowerRealizationHomologyMap 2) (d.indexThree_lowerRealization_surjective hf hindex)
    (d.indexThreeAttachingClass hindex) (d.indexThree_lowerRealization_kernel hf hindex)

private def
    Smale.ManifoldMorse.SurgeryWindows.HasIndexThreeBlock {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (r c : ℕ) : Prop :=
  ∀ i : Fin S.count,
    r < i.val →
      i.val ≤ r + c → Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3

private theorem Smale.ManifoldMorse.SurgeryWindows.indexThreeBlock_mono {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) {r c b : ℕ} (hcb : c ≤ b)
    (h : S.HasIndexThreeBlock r b) : S.HasIndexThreeBlock r c := fun i hri hic =>
  h i hri (hic.trans (Nat.add_le_add_left hcb r))

private theorem Smale.ManifoldMorse.SurgeryWindows.indexThreeBlock_last {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (r c : ℕ) (hc : r + (c + 1) < S.count)
    (h : S.HasIndexThreeBlock r (c + 1)) :
    Module.finrank ℝ (S.data (S.point ⟨r + (c + 1), hc⟩)).chart.NegativeCoordinates = 3 :=
  h ⟨r + (c + 1), hc⟩ (by change r < r + (c + 1); omega) le_rfl

private def
    Smale.ManifoldMorse.SurgeryWindows.middlePresentation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r : ℕ)
    (htwo : S.HasIndexTwoPrefix r) :
    (c : ℕ) →
      (hc : r + c < S.count) →
        S.HasIndexThreeBlock r c →
          Smale.IntegerPresentation
            (SingularMayerVietoris.SingularHomology
              { x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩) } 2)
            r c
  | 0, hc, _ => Smale.IntegerPresentation.ofEquiv (S.indexTwoBasis hf r hc htwo)
  | c + 1, hc, hthree =>
    let P :=
      middlePresentation (S := S) hf r htwo c (Nat.lt_of_succ_lt hc)
        (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
    let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
    (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation hf.continuous
      (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2))

private def Smale.IntegerPresentation.matrix {B : Type*} [AddCommGroup B] [Module ℤ B] {r c : ℕ}
    (P : Smale.IntegerPresentation B r c) : Matrix (Fin r) (Fin c) ℤ := fun i j => P.columns j i

private theorem
    Smale.IntegerPresentation.columns_sum_eq_mulVec {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : Smale.IntegerPresentation B r c) (z : Fin c → ℤ) :
    (∑ j, z j • P.columns j) = P.matrix.mulVec z := by
  funext i
  simp [Smale.IntegerPresentation.matrix, Matrix.mulVec, dotProduct, mul_comm]

private theorem
    Smale.IntegerPresentation.mem_range_matrix_iff {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : Smale.IntegerPresentation B r c) (v : Fin r → ℤ) :
    v ∈ Set.range P.matrix.mulVec ↔ v ∈ Submodule.span ℤ (Set.range P.columns) := by
  rw [Submodule.mem_span_range_iff_exists_fun ℤ]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (P.columns_sum_eq_mulVec z).trans hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (P.columns_sum_eq_mulVec z).symm.trans hz⟩

private theorem
    Smale.IntegerPresentation.matrix_image_eq_kernel {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : Smale.IntegerPresentation B r c) :
    Set.range P.matrix.mulVec = (LinearMap.ker P.map : Set (Fin r → ℤ)) := by
  ext v
  rw [P.mem_range_matrix_iff, P.kernel_eq]
  rfl

private theorem Smale.IntegerPresentation.matrix_relation {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : Smale.IntegerPresentation B r c) (z : Fin c → ℤ) :
    P.map (P.matrix.mulVec z) = 0 := by
  have h : P.matrix.mulVec z ∈ Set.range P.matrix.mulVec := ⟨z, rfl⟩
  rw [P.matrix_image_eq_kernel] at h
  exact h

private theorem Smale.IntegerPresentation.columns_span_of_subsingleton {B : Type*} [AddCommGroup B]
    [Module ℤ B] {r c : ℕ} (P : Smale.IntegerPresentation B r c) [Subsingleton B] :
    Submodule.span ℤ (Set.range P.columns) = ⊤ := by
  apply top_unique
  intro v _
  rw [← P.kernel_eq]
  exact Subsingleton.elim _ _

private theorem
    Smale.IntegerPresentation.matrix_surjective_of_subsingleton {B : Type*} [AddCommGroup B]
    [Module ℤ B] {r c : ℕ} (P : Smale.IntegerPresentation B r c) [Subsingleton B] :
    Function.Surjective P.matrix.mulVec := by
  intro v
  apply (P.mem_range_matrix_iff v).mpr
  rw [P.columns_span_of_subsingleton]
  trivial

private theorem Smale.homotopySixSphere_homology_subsingleton {M : Type} [TopologicalSpace M]
    (h : M ≃ₕ Smale.SixSphere) (k : ℕ) (hk : k ≠ 0) (hktop : k ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology M k) := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology Smale.SixSphere k) :=
    SphereHomology.unitSphere_homology_subsingleton 5 k hk hktop
  exact (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv h k).injective.subsingleton

private def
    Smale.ManifoldMorse.SurgeryWindows.lastUpperHomeomorph {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    { x : M // f x ≤ S.upper (S.last h) } ≃ₜ M :=
  (Homeomorph.setCongr (S.last_upper_univ hf h)).trans (Homeomorph.Set.univ M)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (h : 0 < S.count) (k : ℕ)
    (hk : 0 < k) (hk5 : k < 5) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.last h) } k) := by
  let d := S.data (S.last h)
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1 :=
    (S.last_index_dimension hf h).trans hdim
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1) := ⟨hindex⟩
  let : Subsingleton (SingularMayerVietoris.SingularHomology M k) :=
    Smale.homotopySixSphere_homology_subsingleton hM k hk.ne' (by omega)
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ f (S.last h) + d.radius ^ 2 } k) :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (S.lastUpperHomeomorph hf h)
        k).injective.subsingleton
  let : Subsingleton (SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere 5) k) :=
    SphereHomology.unitSphere_homology_subsingleton 4 k hk.ne' (by omega)
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
            5).symm.toHomeomorph
        k).injective.subsingleton
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf.continuous k hk.ne'

private theorem Smale.ManifoldMorse.SurgeryWindows.upper_homology_subsingleton_of_later_indices
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (j : Fin S.count)
    (hj : j.val + 1 < S.count) (k : ℕ) (hk : 0 < k) (hk5 : k < 5)
    (hindex :
      ∀ i : Fin S.count,
        j.val < i.val →
          i.val + 1 < S.count →
            2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point j) } k) := by
  have hcount : 0 < S.count := by omega
  let P : ℕ → Prop := fun i =>
    ∀ hi : i < S.count,
      Subsingleton
        (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point ⟨i, hi⟩) } k)
  have hlow : P (j.val + 1) := by
    apply Nat.decreasingInduction' (P := P) (m := j.val + 1) (n := S.count - 1)
    · intro i hi hji ih hi'
      have hs : i + 1 < S.count := by omega
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨i + 1, hs⟩) - (S.data (S.point ⟨i + 1, hs⟩)).radius ^ 2 }
            k) :=
        ih hs
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨i, hi'⟩ ⟨i + 1, hs⟩ rfl
      let H :=
        (S.data (S.point ⟨i, hi'⟩)).bandSublevelHomeomorph (S.data (S.point ⟨i + 1, hs⟩))
          T.toHomeomorph hT
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨i, hi'⟩) + (S.data (S.point ⟨i, hi'⟩)).radius ^ 2 } k) :=
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv H k).injective.subsingleton
      obtain ⟨hlo, hne⟩ := hindex ⟨i, hi'⟩ (by change j.val < i; omega) hs
      exact
        (S.data (S.point ⟨i, hi'⟩)).lowerHomology_subsingleton_of_upper_and_index hf.continuous k
          hk.ne' hlo hne
    · omega
    · intro hi
      exact S.lastLower_homology_subsingleton hf hdim hM hcount k hk hk5
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M //
          f x ≤ f (S.point ⟨j.val + 1, hj⟩) - (S.data (S.point ⟨j.val + 1, hj⟩)).radius ^ 2 }
        k) :=
    hlow hj
  obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf j ⟨j.val + 1, hj⟩ rfl
  let H :=
    (S.data (S.point j)).bandSublevelHomeomorph (S.data (S.point ⟨j.val + 1, hj⟩)) T.toHomeomorph
      hT
  exact (PeriodTorusHigherHomology.homeomorphHomologyEquiv H k).injective.subsingleton

private def Smale.ManifoldMorse.SurgeryWindows.middleMatrix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c) :
    Matrix (Fin r) (Fin c) ℤ :=
  (S.middlePresentation hf r htwo c hc hthree).matrix

private theorem
    Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hj : r + c + 1 < S.count)
    (hafter :
      ∀ i : Fin S.count,
        r + c < i.val →
          i.val + 1 < S.count →
            2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ 3) :
    Function.Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩) }
        2) :=
    S.upper_homology_subsingleton_of_later_indices hf hdim hM ⟨r + c, hc⟩ hj 2 (by norm_num)
      (by norm_num) hafter
  exact (S.middlePresentation hf r htwo c hc hthree).matrix_surjective_of_subsingleton

private theorem
    Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  apply S.middleMatrix_surjective_of_homotopySphere hf hdim hM r c htwo hc hthree (by omega)
  intro i hi hi'
  omega

private theorem
    MorseCancel.native_indices_monotone {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
     [TopologicalSpace M] [ChartedSpace E M]
       {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) :
    Monotone (fun i : Fin S.count => nativeMorseIndex E f (S.point i)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact horder _ _ (S.point_strictMono hlt)
  · exact le_rfl

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_middle_index_blocks {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) :
    ∃ r c : ℕ,
      S.HasIndexTwoPrefix r ∧
        ∃ _ : r + c < S.count,
          S.HasIndexThreeBlock r c ∧
            r + c + 1 < S.count ∧
              ∀ i : Fin S.count,
                r + c < i.val →
                  4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates := by
  have hn := S.count_pos hf
  let index := fun i : Fin S.count => nativeMorseIndex E f (S.point i)
  have hmono : Monotone index := native_indices_monotone S horder
  have hfirst : index ⟨0, hn⟩ = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hlast : index ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ = 6 :=
    (nativeMorseIndex_eq_chart (S.data (S.last hn)).chart).trans
      ((S.last_index_dimension hf hn).trans hdim)
  have hcut (k : ℕ) : ∃ j : Fin S.count, ∀ i : Fin S.count, i ≤ j ↔ index i ≤ k := by
    let K := Finset.univ.filter (fun i : Fin S.count => index i ≤ k)
    have hK : K.Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfirst]; exact Nat.zero_le k⟩⟩
    let j := K.max' hK
    have hj : index j ≤ k := (Finset.mem_filter.mp (K.max'_mem hK)).2
    refine ⟨j, fun i => ⟨fun hij => (hmono hij).trans hj, ?_⟩⟩
    intro hi
    exact K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  obtain ⟨a, ha⟩ := hcut 2
  obtain ⟨b, hb⟩ := hcut 3
  have hab : a ≤ b := (hb a).mpr (((ha a).mp le_rfl).trans (by omega))
  have hbLast : b.val + 1 < S.count := by
    have hb3 := (hb b).mp le_rfl
    have hne : b ≠ ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      intro he
      rw [he, hlast] at hb3
      omega
    have hvalne : b.val ≠ S.count - 1 := fun he => hne (Fin.ext he)
    omega
  have hnonzero (i : Fin S.count) (hi : 0 < i.val) : index i ≠ 0 := by
    intro hz
    have he : S.point i = S.first hn :=
      Subtype.ext (native_index_zero_point_unique S hf hn hzero _ (S.point i).property hz)
    have hi0 : i.val = 0 := congrArg Fin.val (S.point.injective he)
    omega
  have hnonone (i : Fin S.count) : index i ≠ 1 :=
    native_index_one_excluded S hone _ (S.point i).property
  refine ⟨a.val, b.val - a.val, ?_, by omega, ?_, by omega, ?_⟩
  · intro i hi hia
    have hi2 := (ha i).mp (show i ≤ a from hia)
    have hi0 := hnonzero i hi
    have hi1 := hnonone i
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 2
    omega
  · intro i hai hib
    have hi3 := (hb i).mp (show i ≤ b by change i.val ≤ b.val; omega)
    have hi2 : ¬index i ≤ 2 := fun he => (not_le_of_gt hai) ((ha i).mpr he)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 3
    omega
  · intro i hbi
    have hi3 : ¬index i ≤ 3 := fun he =>
      (by
        have hh : i.val ≤ b.val := (hb i).mpr he
        omega)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change 4 ≤ index i
    omega

private def MorseCancel.nativeMiddleBlockPoint {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) (j : Fin n) :
    Smale.ManifoldMorse.criticalPoints E f :=
  S.toSurgeryWindows.point ⟨r + j.val + 1, by omega⟩

private theorem AdaptedWindows.exists_ordered_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hthree : S.toSurgeryWindows.HasIndexThreeBlock r n)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ T : AdaptedWindows E f,
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
        (∀ p, (T.data p).radius < ε p) ∧
          (∀ p ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
            ∃ α : Fin n → (Smale.Hemisphere.Sphere 2) → (S.data q).UpperLevel,
              MorseCancel.IsNativeMiddleBasinFamily T hf (S.data q).upper_regular
                (MorseCancel.nativeMiddleBlockPoint S r n hn) α := by
  let W := S.toSurgeryWindows
  have hnW : r + n < W.count := hn
  let q := W.point ⟨r, by omega⟩
  let p := MorseCancel.nativeMiddleBlockPoint S r n hn
  have hp (j : Fin n) : MorseCancel.nativeMorseIndex E f (p j) = 3 :=
    (MorseCancel.nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have horder : StrictMono (fun j => f (p j)) := by
    intro i j hij
    apply W.point_strictMono
    change r + i.val + 1 < r + j.val + 1
    omega
  have habove (j : Fin n) : W.upper q < f (p j) := by
    have hqj : f q < f (p j) := W.point_strictMono (by change r < r + j.val + 1; omega)
    exact (W.separated q (p j) hqj).trans (W.lower_lt_value (p j))
  have hblock (j : Fin n) (z : Smale.ManifoldMorse.criticalPoints E f) (hz : W.upper q < f z)
    (hzj : f z ≤ f (p j)) : z ∈ Set.range p := by
    obtain ⟨k, rfl⟩ := W.point.surjective z
    have hrk : r < k.val := W.point_strictMono.lt_iff_lt.mp ((W.value_lt_upper q).trans hz)
    have hkj : k.val ≤ r + j.val + 1 := W.point_strictMono.le_iff_le.mp hzj
    let i : Fin n := ⟨k.val - (r + 1), by omega⟩
    refine ⟨i, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (k.val - (r + 1)) + 1 = k.val
    omega
  exact
    S.exists_middle_block_realization hf hm hdim n (S.data q).upper_regular p hp horder habove
      hblock ε hε

private def Degree.DiskCube.target {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (L : V ≃L[ℝ] (Fin n → ℝ)) : Set V :=
  L ⁻¹' HigherHurewicz.realCubeSet n

private theorem Degree.DiskCube.target_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : IsCompact (target L) :=
  L.toHomeomorph.isCompact_preimage.mpr (HigherHurewicz.isCompact_realCubeSet n)

private theorem
    Degree.DiskCube.target_convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (L : V ≃L[ℝ] (Fin n → ℝ)) : Convex ℝ (target L) :=
  (HigherHurewicz.convex_realCubeSet n).linear_preimage L.toLinearMap

private theorem Degree.DiskCube.target_interior_nonempty {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : (interior (target L)).Nonempty := by
  obtain ⟨v, hv⟩ := HigherHurewicz.interior_realCubeSet_nonempty n
  refine ⟨L.symm v, ?_⟩
  change L.symm v ∈ interior (L.toHomeomorph ⁻¹' HigherHurewicz.realCubeSet n)
  rw [← L.toHomeomorph.preimage_interior]
  change L (L.symm v) ∈ interior (HigherHurewicz.realCubeSet n)
  rwa [L.apply_symm_apply]

private theorem Degree.DiskCube.exists_ambient {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ∃ e : V ≃ₜ V,
      e '' Metric.closedBall (0 : V) 1 = target L ∧
        e '' frontier (Metric.closedBall (0 : V) 1) = frontier (target L) := by
  obtain ⟨e, _, he, hb⟩ :=
    exists_homeomorph_image_eq (convex_closedBall (0 : V) 1)
      (show (interior (Metric.closedBall (0 : V) 1)).Nonempty from
        ⟨0, Metric.ball_subset_interior_closedBall (by simp)⟩)
      ((ProperSpace.isCompact_closedBall (0 : V) 1).isVonNBounded ℝ) (target_convex L)
      (target_interior_nonempty L) ((target_compact L).isVonNBounded ℝ)
  exact
    ⟨e, by
      simpa only [Metric.isClosed_closedBall.closure_eq,
        (target_compact L).isClosed.closure_eq] using he,
      hb⟩

private def Degree.DiskCube.ambient {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : V ≃ₜ V :=
  Classical.choose (exists_ambient L)

private theorem Degree.DiskCube.ambient_image {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ambient L '' Metric.closedBall (0 : V) 1 = target L :=
  (Classical.choose_spec (exists_ambient L)).1

private theorem
    Degree.DiskCube.ambient_frontier {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ambient L '' frontier (Metric.closedBall (0 : V) 1) = frontier (target L) :=
  (Classical.choose_spec (exists_ambient L)).2

private theorem Degree.DiskCube.ambient_mem_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) (v : V) :
    v ∈ Metric.closedBall (0 : V) 1 ↔ L (ambient L v) ∈ HigherHurewicz.realCubeSet n := by
  change v ∈ Metric.closedBall (0 : V) 1 ↔ ambient L v ∈ target L
  rw [← ambient_image]
  exact ((ambient L).injective.mem_set_image).symm

private def Degree.DiskCube.homeomorph {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    Degree.DiskCylinder.Disk (E := V) ≃ₜ (Fin n → (unitInterval)) :=
  (((ambient L).trans L.toHomeomorph).subtype (ambient_mem_iff L)).trans
    (HigherHurewicz.realCubeHomeomorph n)

private theorem Degree.DiskCube.boundary_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ))
    (z : Degree.DiskCylinder.Disk (E := V)) :
    homeomorph L z ∈ Cube.boundary (Fin n) ↔ ‖(z : V)‖ = 1 := by
  change HigherHurewicz.realCubeHomeomorph n _ ∈ Cube.boundary (Fin n) ↔ _
  rw [HigherHurewicz.realCubeHomeomorph_mem_boundary_iff]
  change L (ambient L z.val) ∈ frontier (HigherHurewicz.realCubeSet n) ↔ _
  have hpre :
    L (ambient L z.val) ∈ frontier (HigherHurewicz.realCubeSet n) ↔
      ambient L z.val ∈ frontier (target L) := by
    change ambient L z.val ∈ L.toHomeomorph ⁻¹' frontier (HigherHurewicz.realCubeSet n) ↔ _
    rw [L.toHomeomorph.preimage_frontier]
    rfl
  rw [hpre, ← ambient_frontier]
  rw [(ambient L).injective.mem_set_image]
  rw [frontier_closedBall (0 : V) (one_ne_zero), mem_sphere_zero_iff_norm]

private theorem
    Degree.DiskCube.symm_boundary_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → (unitInterval)) :
    ‖((homeomorph L).symm z : V)‖ = 1 ↔ z ∈ Cube.boundary (Fin n) := by
  rw [← boundary_iff, Homeomorph.apply_symm_apply]

private theorem Degree.Sphere.piTwo_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 2 SixSphereCube.StandardSphere x) :=
  SphereHomology.unitSphere_piTwo_subsingleton 3 x

private theorem Degree.Sphere.piThree_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 3 SixSphereCube.StandardSphere x) := by
  let := piTwo_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 3 (by decide) (by decide)
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

private theorem Degree.Sphere.piFour_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 4 SixSphereCube.StandardSphere x) := by
  let := piTwo_subsingleton x
  let := piThree_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 4 (by decide) (by decide)
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

private theorem Degree.Sphere.piFive_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 5 SixSphereCube.StandardSphere x) := by
  let := piTwo_subsingleton x
  let := piThree_subsingleton x
  let := piFour_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 5 (by decide) (by decide)
  exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton

end Mathoverflow1973

end
