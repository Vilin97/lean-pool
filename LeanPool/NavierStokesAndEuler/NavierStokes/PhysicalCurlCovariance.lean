/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualBridge
public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialCurl
public import LeanPool.NavierStokesAndEuler.NavierStokes.CopyAngularInvariance

@[expose] public section

/-!
# Physical covariance of the actual wave curl

The potential is differentiated before any cutoff or carrier is removed.
All operators below are actual Frechet derivatives.
-/

namespace NavierStokes.PhysicalCurlCovariance

open Set Filter Function
open ProblemStatement HarmonicCalculus
open scoped Topology ContDiff

noncomputable section


abbrev Cylinder := PhysicalResidualBridge.Cylinder
abbrev ScaledGraph := PhysicalResidualBridge.ScaledGraph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def realVector (a : ComplexVector) : Space :=
  AxisymmetricResidual.pack (a 0).re (a 1).re (a 2).re

@[simp] theorem realVector_apply (a : ComplexVector) (i : Fin 3) :
    realVector a i = (a i).re := by
  fin_cases i <;> simp [realVector]

noncomputable def realCurl (R : E → ℝ) (Vr Vθ Vz : E → E)
    (a : E → Fin 3 → ℝ) (x : E) : Fin 3 → ℝ :=
  ![(R x)⁻¹ * along Vθ (fun y => a y 2) x - along Vz (fun y => a y 1) x,
    along Vz (fun y => a y 0) x - along Vr (fun y => a y 2) x,
    along Vr (fun y => a y 1) x + (R x)⁻¹ * a x 1 -
      (R x)⁻¹ * along Vθ (fun y => a y 0) x]

theorem real_cylindricalCurl (R : E → ℝ) (Vr Vθ Vz : E → E)
    {a : E → ComplexVector} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x) (i : Fin 3) :
    (CurlClassBounds.cylindricalCurl R Vr Vθ Vz a x i).re =
      realCurl R Vr Vθ Vz (fun y j => (a y j).re) x i := by
  have hD (V : E → E) (j : Fin 3) :
      along V (fun y => (a y j).re) x = (along V (fun y => a y j) x).re :=
    LinearWaveResidual.along_map Complex.reCLM V (ha j)
  fin_cases i <;>
    simp [CurlClassBounds.cylindricalCurl, realCurl, hD, Complex.real_smul]

/-- Curl, like its underlying alternating tensor, rotates with an oriented
orthonormal cylindrical frame. -/
theorem curlLinear_rotation (L : Space →L[ℝ] Space) (θ : ℝ) :
    CylindricalResidual.frame (-θ) (SpatialCurl.curlLinear L) =
      SpatialCurl.curlLinear ((CylindricalResidual.frame (-θ)).comp
        (L.comp (CylindricalResidual.frame θ))) := by
  ext i
  fin_cases i <;>
    simp [CylindricalResidual.frame_apply, AxisymmetricResidual.pack,
      coordinateVector]
  · ring
  · ring
  · linear_combination
      -((L (EuclideanSpace.single 0 1)) 1 - (L (EuclideanSpace.single 1 1)) 0) *
        Real.cos_sq_add_sin_sq θ

noncomputable def cylindricalSpatialCurl (a : Space → Space) (q : Space) : Space :=
  AxisymmetricResidual.pack
    (CylindricalResidual.dCoord 1 a q 2 / q 0 - CylindricalResidual.dCoord 2 a q 1)
    (CylindricalResidual.dCoord 2 a q 0 - CylindricalResidual.dCoord 0 a q 2)
    (CylindricalResidual.dCoord 0 a q 1 + a q 1 / q 0 - CylindricalResidual.dCoord 1 a q 0 / q 0)

/-- The moving-frame connection term is part of the genuine Cartesian curl. -/
theorem cartesianCurl_components {a : Space → Space} {q : Space}
    (ha : DifferentiableAt ℝ a (CylindricalResidual.chart q)) (hr : q 0 ≠ 0) :
    CylindricalResidual.frame (-(q 1)) (SpatialCurl.curl a (CylindricalResidual.chart q)) =
      cylindricalSpatialCurl (CylindricalResidual.components a) q := by
  rw [SpatialCurl.curl, curlLinear_rotation]
  ext i
  fin_cases i
  · change SpatialCurl.curlLinear _ 0 = _
    rw [SpatialCurl.curlLinear_apply_zero]
    simp only [ContinuousLinearMap.comp_apply]
    rw [CylindricalResidual.cartesianDerivative_components ha hr,
      CylindricalResidual.cartesianDerivative_components ha hr]
    simp [cylindricalSpatialCurl, coordinateVector,
      CylindricalResidual.connection_apply, div_eq_mul_inv]
    ring
  · change SpatialCurl.curlLinear _ 1 = _
    rw [SpatialCurl.curlLinear_apply_one]
    simp only [ContinuousLinearMap.comp_apply]
    rw [CylindricalResidual.cartesianDerivative_components ha hr,
      CylindricalResidual.cartesianDerivative_components ha hr]
    simp [cylindricalSpatialCurl, coordinateVector,
      CylindricalResidual.connection_apply, div_eq_mul_inv]
  · change SpatialCurl.curlLinear _ 2 = _
    rw [SpatialCurl.curlLinear_apply_two]
    simp only [ContinuousLinearMap.comp_apply]
    rw [CylindricalResidual.cartesianDerivative_components ha hr,
      CylindricalResidual.cartesianDerivative_components ha hr]
    simp [cylindricalSpatialCurl, coordinateVector,
      CylindricalResidual.connection_apply, div_eq_mul_inv]
    ring

theorem along_complex_pull {Γ : E → F} {V : E → E} {W : F → F}
    {f : F → ℂ} {x : E} (c : ℂ) (k : ℝ)
    (hΓ : DifferentiableAt ℝ Γ x) (hf : DifferentiableAt ℝ f (Γ x))
    (hV : fderiv ℝ Γ x (V x) = k • W (Γ x)) :
    along V (fun y => c * f (Γ y)) x = c * (k : ℂ) * along W f (Γ x) := by
  have hd := (hf.hasFDerivAt.comp x hΓ.hasFDerivAt).const_mul c
  dsimp only [Function.comp_def] at hd
  unfold along
  rw [hd.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    hV, map_smul, Complex.real_smul, smul_eq_mul]
  ring

theorem cylindricalCurl_pull {Γ : E → F} {R : F → ℝ} {r : E → ℝ}
    {Vr Vθ Vz : F → F} {Sr Sθ Sz : E → E} {x : E} {l : ℝ}
    (hl : l ≠ 0) (hr : r x ≠ 0) (hΓ : DifferentiableAt ℝ Γ x)
    (hDr : fderiv ℝ Γ x (Sr x) = l • Vr (Γ x))
    (hDθ : fderiv ℝ Γ x (Sθ x) = Vθ (Γ x))
    (hDz : fderiv ℝ Γ x (Sz x) = l • Vz (Γ x)) (hR : R (Γ x) = l * r x)
    {a : F → ComplexVector} (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) (Γ x))
    (c : ℂ) :
    CurlClassBounds.cylindricalCurl r Sr Sθ Sz (fun y => c • a (Γ y)) x =
      (c * (l : ℂ)) • CurlClassBounds.cylindricalCurl R Vr Vθ Vz a (Γ x) := by
  have hθ : fderiv ℝ Γ x (Sθ x) = (1 : ℝ) • Vθ (Γ x) := by simpa using hDθ
  have h1 i := along_complex_pull c l hΓ (ha i) hDr
  have h2 i := along_complex_pull c 1 hΓ (ha i) hθ
  have h3 i := along_complex_pull c l hΓ (ha i) hDz
  have hlc : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  have hrc : (r x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  ext i
  fin_cases i <;>
    simp [CurlClassBounds.cylindricalCurl, Pi.smul_apply, smul_eq_mul, h1, h2, h3,
      hR, Complex.real_smul] <;> (try field_simp [hlc, hrc])

theorem phaseNormal_pull {Γ : E → F} {R : F → ℝ} {r : E → ℝ}
    {Vr Vθ Vz : F → F} {Sr Sθ Sz : E → E} {x : E} {l : ℝ}
    (hl : l ≠ 0) (hr : r x ≠ 0) (hΓ : DifferentiableAt ℝ Γ x)
    (hDr : fderiv ℝ Γ x (Sr x) = l • Vr (Γ x))
    (hDθ : fderiv ℝ Γ x (Sθ x) = Vθ (Γ x))
    (hDz : fderiv ℝ Γ x (Sz x) = l • Vz (Γ x)) (hR : R (Γ x) = l * r x)
    {Φ : F → ℝ} (hΦ : DifferentiableAt ℝ Φ (Γ x)) (b : ℝ) :
    phaseNormal r Sr Sθ Sz (fun y => b * Φ (Γ y)) x =
      (b * l) • phaseNormal R Vr Vθ Vz Φ (Γ x) := by
  have hθ : fderiv ℝ Γ x (Sθ x) = (1 : ℝ) • Vθ (Γ x) := by simpa using hDθ
  have h1 := PhysicalResidualBridge.along_scaled_pull b l hΓ hΦ hDr
  have h2 := PhysicalResidualBridge.along_scaled_pull b 1 hΓ hΦ hθ
  have h3 := PhysicalResidualBridge.along_scaled_pull b l hΓ hΦ hDz
  ext i
  fin_cases i <;> simp [phaseNormal, h1, h2, h3, hR, smul_eq_mul]
  field_simp [hl, hr]

theorem normalCoefficient_scale (n : Space) (a : ComplexVector) {s : ℝ}
    (hs : s ≠ 0) (c : ℝ) :
    CurlClassBounds.normalCoefficient (s • n) (c • a) =
      (c / s) • CurlClassBounds.normalCoefficient n a := by
  have hc : CurlClassBounds.normalCross (s • n) (c • a) =
      (s * c) • CurlClassBounds.normalCross n a := by
    simp [CurlClassBounds.normalCross, map_smul, smul_smul, mul_comm]
  rw [CurlClassBounds.normalCoefficient, hc, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, smul_smul, CurlClassBounds.normalCoefficient, smul_smul]
  congr 1
  have hsc : (s ^ 2)⁻¹ * (s * c) = c / s := by field_simp [hs]
  calc
    (s ^ 2 * ‖n‖ ^ 2)⁻¹ * (s * c) = (‖n‖ ^ 2)⁻¹ * ((s ^ 2)⁻¹ * (s * c)) := by
      rw [mul_inv_rev]
      ring
    _ = (c / s) * (‖n‖ ^ 2)⁻¹ := by rw [hsc]; ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem carrier_eq_of_products {K L : ℝ} {Φ : E → ℝ} {Ψ : F → ℝ} {x : E} {y : F}
    (h : K * Φ x = L * Ψ y) : carrier K Φ x = carrier L Ψ y := by
  unfold carrier phaseFactor
  congr 1
  have hc : (K : ℂ) * (Φ x : ℂ) = (L : ℂ) * (Ψ y : ℂ) := by exact_mod_cast h
  calc
    (K : ℂ) * Complex.I * (Φ x : ℂ) = ((K : ℂ) * (Φ x : ℂ)) * Complex.I := by ring
    _ = ((L : ℂ) * (Ψ y : ℂ)) * Complex.I := by rw [hc]
    _ = _ := by ring

/-- The phase rescaling and inverse carrier cancel exactly. This is why
the potential has one fewer inverse length than the velocity. -/
theorem vectorPotential_pull {Γ : E → F} {R : F → ℝ} {r : E → ℝ}
    {Vr Vθ Vz : F → F} {Sr Sθ Sz : E → E} {x : E} {l b K L : ℝ}
    (hl : l ≠ 0) (hr : r x ≠ 0) (hK : K ≠ 0) (hb : b ≠ 0) (hKL : K * b = L)
    (hΓ : DifferentiableAt ℝ Γ x)
    (hDr : fderiv ℝ Γ x (Sr x) = l • Vr (Γ x))
    (hDθ : fderiv ℝ Γ x (Sθ x) = Vθ (Γ x))
    (hDz : fderiv ℝ Γ x (Sz x) = l • Vz (Γ x)) (hR : R (Γ x) = l * r x)
    {Φ : F → ℝ} (hΦ : DifferentiableAt ℝ Φ (Γ x)) (a : F → ComplexVector) (c : ℝ) :
    CurlClassBounds.vectorPotential K r Sr Sθ Sz (fun y => b * Φ (Γ y))
      (fun y => c • a (Γ y)) x =
      (c / l) • CurlClassBounds.vectorPotential L R Vr Vθ Vz Φ a (Γ x) := by
  have hN := phaseNormal_pull hl hr hΓ hDr hDθ hDz hR hΦ b
  have hphase : carrier K (fun y => b * Φ (Γ y)) x = carrier L Φ (Γ x) :=
    carrier_eq_of_products (by rw [← mul_assoc, hKL])
  have hs : CurlClassBounds.inverseCarrier K * ((c / (b * l) : ℝ) : ℂ) =
      ((c / l : ℝ) : ℂ) * CurlClassBounds.inverseCarrier L := by
    rw [← hKL]
    unfold CurlClassBounds.inverseCarrier
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hK, Complex.ofReal_ne_zero.mpr hb,
      Complex.ofReal_ne_zero.mpr hl]
  ext i
  simp only [CurlClassBounds.vectorPotential, vectorMode, mode, CurlClassBounds.coefficient,
    hN, normalCoefficient_scale _ _ (mul_ne_zero hb hl) c, hphase, Pi.smul_apply,
    Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc (CurlClassBounds.inverseCarrier K), hs]
  ring

theorem realCurl_eq_cylindrical {a : VelocityField} {t : ℝ} {q : Space}
    (ha : DifferentiableAt ℝ a (t, q)) (i : Fin 3) :
    realCurl LinearWaveResidual.coordinateRadius (LinearWaveResidual.spaceDirection 0)
      (LinearWaveResidual.spaceDirection 1) (LinearWaveResidual.spaceDirection 2)
      (fun z j => a z j) (t, q) i = cylindricalSpatialCurl (fun y => a (t, y)) q i := by
  have hs : DifferentiableAt ℝ (fun y => a (t, y)) q :=
    ha.comp q ((differentiableAt_const t).prodMk differentiableAt_id)
  have hfirst (k j : Fin 3) :
      along (LinearWaveResidual.spaceDirection k) (fun z => a z j) (t, q) =
        CylindricalResidual.dCoord k (fun y => a (t, y)) q j := by
    have hj : DifferentiableAt ℝ (fun z => a z j) (t, q) :=
      (AxisymmetricFields.projection j).differentiableAt.comp (t, q) ha
    rw [LinearWaveResidual.along_space_slice hj]
    exact CylindricalResidual.dCoord_map (AxisymmetricFields.projection j) hs k
  fin_cases i <;>
    simp [realCurl, cylindricalSpatialCurl, LinearWaveResidual.coordinateRadius,
      hfirst, div_eq_mul_inv] <;> ring

theorem cylindricalSpatialCurl_congr {a b : Space → Space} {q : Space}
    (hab : a =ᶠ[𝓝 q] b) : cylindricalSpatialCurl a q = cylindricalSpatialCurl b q := by
  simp only [cylindricalSpatialCurl, CylindricalResidual.dCoord_congr hab 0,
    CylindricalResidual.dCoord_congr hab 1, CylindricalResidual.dCoord_congr hab 2,
    hab.eq_of_nhds]

/-- A potential value identity gives its physical curl identity by the actual
chain rule. It is not necessary to assume matching velocity fields. -/
theorem curl_of_representation {A w : VelocityField} {t : ℝ} {q : Space}
    (hA : DifferentiableAt ℝ A (t, CylindricalResidual.chart q))
    (hw : DifferentiableAt ℝ w (t, q)) (hr : q 0 ≠ 0)
    (hrep : (fun z : SpaceTime => A (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1) (w z))) (i : Fin 3) :
    CylindricalResidual.frame (-(q 1))
      (SpatialCurl.spatialCurl A (t, CylindricalResidual.chart q)) i =
      realCurl LinearWaveResidual.coordinateRadius (LinearWaveResidual.spaceDirection 0)
        (LinearWaveResidual.spaceDirection 1) (LinearWaveResidual.spaceDirection 2)
        (fun z j => w z j) (t, q) i := by
  have hs : DifferentiableAt ℝ (fun y => A (t, y)) (CylindricalResidual.chart q) :=
    hA.comp _ ((differentiableAt_const t).prodMk differentiableAt_id)
  have he : CylindricalResidual.components (fun y => A (t, y)) =ᶠ[𝓝 q] fun y => w (t, y) := by
    have h := hrep.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [h] with y hy
    dsimp only [Function.comp_def, id_eq] at hy
    change CylindricalResidual.frame (-(y 1)) (A (t, CylindricalResidual.chart y)) = _
    rw [hy, CylindricalResidual.frame_inverse]
  change CylindricalResidual.frame (-(q 1)) (SpatialCurl.curl (fun y => A (t, y))
    (CylindricalResidual.chart q)) i = _
  rw [cartesianCurl_components hs hr, cylindricalSpatialCurl_congr he]
  exact (realCurl_eq_cylindrical hw i).symm

theorem realVector_differentiableAt {a : E → ComplexVector} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x) :
    DifferentiableAt ℝ (fun y => realVector (a y)) x := by
  have hr i := Complex.reCLM.differentiableAt.comp x (ha i)
  exact (((hr 0).smul_const _).add ((hr 1).smul_const _)).add ((hr 2).smul_const _)

namespace ScaledGraph

noncomputable def complexPotential (G : ScaledGraph) (c : ℝ) (B : Cylinder → ComplexVector)
    (z : SpaceTime) : ComplexVector := (c : ℂ) • B (G.map z)

noncomputable def realPotential (G : ScaledGraph) (c : ℝ) (B : Cylinder → ComplexVector) :
    VelocityField := fun z => realVector (complexPotential G c B z)

theorem complexPotential_differentiableAt (G : ScaledGraph) {z : SpaceTime}
    (hr : G.radialScale * z.2 0 ≠ 0) {B : Cylinder → ComplexVector}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) (G.map z)) (c : ℝ) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => complexPotential G c B y i) z :=
  ((hB i).comp z ((G.map_smoothAt hr).differentiableAt (by simp))).const_mul (c : ℂ)

theorem physical_curl (G : ScaledGraph) (hl : 0 < G.radialScale)
    {B : Cylinder → ComplexVector} {t : ℝ} {q : Space} (hr : 0 < q 0)
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) (G.map (t, q))) (c : ℝ)
    {A : VelocityField} (hA : DifferentiableAt ℝ A (t, CylindricalResidual.chart q))
    (hrep : (fun z : SpaceTime => A (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1) (realPotential G c B z))) (i : Fin 3) :
    CylindricalResidual.frame (-(q 1))
      (SpatialCurl.spatialCurl A (t, CylindricalResidual.chart q)) i =
      c * G.radialScale * (CurlClassBounds.cylindricalCurl PhysicalResidualBridge.ScaledGraph.radius
        G.radial PhysicalResidualBridge.ScaledGraph.angular G.axial B (G.map (t, q)) i).re := by
  have hr' : G.radialScale * q 0 ≠ 0 := (mul_pos hl hr).ne'
  have hb := complexPotential_differentiableAt G hr' hB c
  rw [curl_of_representation hA (realVector_differentiableAt hb) hr.ne' hrep]
  simp only [realVector_apply]
  rw [← real_cylindricalCurl _ _ _ _ hb i]
  change (CurlClassBounds.cylindricalCurl _ _ _ _ (fun y => (c : ℂ) • B (G.map y)) (t, q) i).re = _
  rw [cylindricalCurl_pull (Γ := G.map) (r := LinearWaveResidual.coordinateRadius)
    (R := PhysicalResidualBridge.ScaledGraph.radius) (x := (t, q))
    (Sr := LinearWaveResidual.spaceDirection 0) (Sθ := LinearWaveResidual.spaceDirection 1)
    (Sz := LinearWaveResidual.spaceDirection 2) hl.ne' hr.ne'
    ((G.map_smoothAt hr').differentiableAt (by simp)) (G.map_radial hr')
    (G.map_angular hr') (G.map_axial hr') rfl hB (c : ℂ)]
  simp [smul_eq_mul, Complex.mul_re]

end ScaledGraph

/-! Coordinate reassociation and smooth cutoffs. -/

noncomputable def reindexVector (e : E ≃L[ℝ] F) (V : F → F) (x : E) : E :=
  e.symm (V (e x))

theorem along_reindex (e : E ≃L[ℝ] F) (V : F → F) {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : F → W} {x : E}
    (hf : DifferentiableAt ℝ f (e x)) :
    along (reindexVector e V) (fun y => f (e y)) x = along V f (e x) := by
  have hd := hf.hasFDerivAt.comp x e.hasFDerivAt
  dsimp only [Function.comp_def] at hd
  unfold along reindexVector
  rw [hd.fderiv]
  simp

theorem cylindricalCurl_reindex (e : E ≃L[ℝ] F) (R : F → ℝ) (Vr Vθ Vz : F → F)
    {B : F → ComplexVector} {x : E} (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) (e x)) :
    CurlClassBounds.cylindricalCurl (fun y => R (e y)) (reindexVector e Vr)
      (reindexVector e Vθ) (reindexVector e Vz) (fun y => B (e y)) x =
      CurlClassBounds.cylindricalCurl R Vr Vθ Vz B (e x) := by
  simp only [CurlClassBounds.cylindricalCurl, along_reindex e _ (hB _)]

theorem phaseNormal_reindex (e : E ≃L[ℝ] F) (R : F → ℝ) (Vr Vθ Vz : F → F)
    {Φ : F → ℝ} {x : E} (hΦ : DifferentiableAt ℝ Φ (e x)) :
    phaseNormal (fun y => R (e y)) (reindexVector e Vr) (reindexVector e Vθ)
      (reindexVector e Vz) (fun y => Φ (e y)) x = phaseNormal R Vr Vθ Vz Φ (e x) := by
  simp only [phaseNormal, along_reindex e _ hΦ]

theorem vectorPotential_reindex (e : E ≃L[ℝ] F) (K : ℝ) (R : F → ℝ) (Vr Vθ Vz : F → F)
    {Φ : F → ℝ} (a : F → ComplexVector) {x : E} (hΦ : DifferentiableAt ℝ Φ (e x)) :
    CurlClassBounds.vectorPotential K (fun y => R (e y)) (reindexVector e Vr)
      (reindexVector e Vθ) (reindexVector e Vz) (fun y => Φ (e y)) (fun y => a (e y)) x =
      CurlClassBounds.vectorPotential K R Vr Vθ Vz Φ a (e x) := by
  ext i
  simp only [CurlClassBounds.vectorPotential, vectorMode, mode, CurlClassBounds.coefficient,
    phaseNormal_reindex e R Vr Vθ Vz hΦ, carrier]

/-- Cutoff differentiation produces the full gradient-cross-potential term. -/
theorem cylindricalCurl_cutoff (R : E → ℝ) (Vr Vθ Vz : E → E)
    {χ : E → ℝ} {B : E → ComplexVector} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x) :
    CurlClassBounds.cylindricalCurl R Vr Vθ Vz (fun y => χ y • B y) x =
      χ x • CurlClassBounds.cylindricalCurl R Vr Vθ Vz B x +
        CurlClassBounds.normalCross (phaseNormal R Vr Vθ Vz χ x) (B x) := by
  have hD (V : E → E) (j : Fin 3) := CurlClassBounds.along_real_smul V hχ (hB j)
  have hD' (V : E → E) (j : Fin 3) :
      along V (fun y => (χ y : ℂ) * B y j) x =
        Complex.ofReal (along V χ x) * B x j + (χ x : ℂ) * along V (fun y => B y j) x := by
    simpa only [Complex.real_smul] using hD V j
  ext i
  fin_cases i <;>
    simp [CurlClassBounds.cylindricalCurl, Pi.smul_apply, hD', phaseNormal,
      Complex.real_smul, div_eq_mul_inv] <;> ring

theorem vectorPotential_cutoff (K : ℝ) (R : E → ℝ) (Vr Vθ Vz : E → E)
    (Φ : E → ℝ) (a : E → ComplexVector) (χ : E → ℝ) (x : E) :
    CurlClassBounds.vectorPotential K R Vr Vθ Vz Φ (fun y => χ y • a y) x =
      χ x • CurlClassBounds.vectorPotential K R Vr Vθ Vz Φ a x := by
  ext i
  simp only [CurlClassBounds.vectorPotential, vectorMode, mode, CurlClassBounds.coefficient,
    CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross_real_smul,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-- A local equality of the full potentials, including their cutoffs and
carriers, automatically propagates to equality of actual curls. -/
theorem cylindricalCurl_congr {R : E → ℝ} {Vr Vθ Vz : E → E}
    {A B : E → ComplexVector} {x : E} (hAB : A =ᶠ[𝓝 x] B) :
    CurlClassBounds.cylindricalCurl R Vr Vθ Vz A x =
      CurlClassBounds.cylindricalCurl R Vr Vθ Vz B x := by
  have hcomp i : (fun y => A y i) =ᶠ[𝓝 x] fun y => B y i :=
    hAB.mono (fun y hy => congrFun hy i)
  have hD V i : along V (fun y => A y i) x = along V (fun y => B y i) x := by
    exact congrArg (fun L : E →L[ℝ] ℂ => L (V x)) (hcomp i).fderiv_eq
  simp only [CurlClassBounds.cylindricalCurl, hD, hAB.eq_of_nhds]

noncomputable def radiusCLM : Cylinder →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (PhysicalResidualBridge.Plane × PhysicalResidualBridge.Plane)).comp
    (ContinuousLinearMap.fst ℝ PhysicalResidualBridge.Lift ℝ)

namespace ScaledGraph

noncomputable def radialCurve (G : ScaledGraph) (r : ℝ) : Cylinder :=
  ((1, ((0, 0), (G.frequency * GraphCalculus.radialSpeed G.exponent r) • G.radialVector)), 0)

theorem radialCurve_smoothAt (G : ScaledGraph) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (radialCurve G) r := by
  have hc : ContDiffAt ℝ ∞ (fun y : ℝ =>
      (G.frequency * GraphCalculus.radialSpeed G.exponent y) • G.radialVector) r :=
    (contDiffAt_const.mul (contDiffAt_const.mul
      (contDiffAt_id.rpow_const_of_ne hr))).smul contDiffAt_const
  exact (contDiffAt_const.prodMk (contDiffAt_const.prodMk hc)).prodMk contDiffAt_const

theorem radial_aux_derivative (G : ScaledGraph) {x : Cylinder} (hx : x.1.1 ≠ 0)
    (v : Cylinder) (hv : v.1.1 = 0) : fderiv ℝ G.radial x v = 0 := by
  change fderiv ℝ (radialCurve G ∘ radiusCLM) x v = 0
  rw [fderiv_comp x ((G.radialCurve_smoothAt hx).differentiableAt (by simp))
    radiusCLM.differentiableAt, ContinuousLinearMap.fderiv]
  change fderiv ℝ (radialCurve G) x.1.1 v.1.1 = 0
  rw [hv, map_zero]

theorem geometry (G : ScaledGraph) {U : Set Cylinder} (hU : IsOpen U)
    (hR : ∀ x ∈ U, x.1.1 ≠ 0) :
    CurlClassBounds.CylindricalGeometry U PhysicalResidualBridge.ScaledGraph.radius
      G.radial PhysicalResidualBridge.ScaledGraph.angular G.axial := by
  have hca (x : Cylinder) : fderiv ℝ G.axial x = 0 :=
    (hasFDerivAt_const (𝕜 := ℝ) (((0, ((G.epsilon, 0), 0)), 0) : Cylinder) x).fderiv
  have hcθ (x : Cylinder) : fderiv ℝ PhysicalResidualBridge.ScaledGraph.angular x = 0 :=
    (hasFDerivAt_const (𝕜 := ℝ) ((0, 1) : Cylinder) x).fderiv
  refine ⟨hU, radiusCLM.contDiff.contDiffOn, hR, G.radial_smooth hR,
    contDiffOn_const, contDiffOn_const, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change fderiv ℝ radiusCLM x (G.radial x) = 1
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    change fderiv ℝ radiusCLM x (PhysicalResidualBridge.ScaledGraph.angular x) = 0
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    change fderiv ℝ radiusCLM x (G.axial x) = 0
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    rw [G.radial_aux_derivative (hR x hx) _ rfl, hcθ, _root_.zero_apply]
  · intro x hx
    rw [G.radial_aux_derivative (hR x hx) _ rfl, hca, _root_.zero_apply]
  · intro x hx
    rw [hca, hcθ]
    rfl

end ScaledGraph

open PhysicalResidualBridge (commonGraph)

theorem commonGraph_potentialScale {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ) :
    (commonGraph Q h k).velocityScale / (commonGraph Q h k).radialScale = Q ^ (-h) := by
  change Q ^ (-CoordinateAlgebra.A h) / Q ^ (-(1 / 2 : ℝ)) = Q ^ (-h)
  rw [← Real.rpow_sub hQ]
  congr 1
  unfold CoordinateAlgebra.A
  ring

theorem commonGraph_curlScale {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ) :
    Q ^ (-h) * (commonGraph Q h k).radialScale = Q ^ (-CoordinateAlgebra.A h) := by
  change Q ^ (-h) * Q ^ (-(1 / 2 : ℝ)) = _
  rw [← Real.rpow_add hQ]
  congr 1
  unfold CoordinateAlgebra.A
  ring

/-- Arbitrary native or common covering index, with the exact potential
weight `Q^(-h)` and velocity weight `Q^(-A)`. -/
theorem commonGraph_physical_curl {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ)
    {B : Cylinder → ComplexVector} {t : ℝ} {q : Space} (hr : 0 < q 0)
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) ((commonGraph Q h k).map (t, q)))
    {A : VelocityField} (hA : DifferentiableAt ℝ A (t, CylindricalResidual.chart q))
    (hrep : (fun z : SpaceTime => A (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1)
        (ScaledGraph.realPotential (commonGraph Q h k) (Q ^ (-h)) B z))) (i : Fin 3) :
    (CurlClassBounds.cylindricalCurl PhysicalResidualBridge.ScaledGraph.radius
      (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (commonGraph Q h k).axial B ((commonGraph Q h k).map (t, q)) i).re =
      Q ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(q 1))
        (SpatialCurl.spatialCurl A (t, CylindricalResidual.chart q)) i := by
  have he := ScaledGraph.physical_curl (commonGraph Q h k) (Real.rpow_pos_of_pos hQ _)
    hr hB (Q ^ (-h)) hA hrep i
  rw [commonGraph_curlScale hQ] at he
  rw [he, ← mul_assoc, ← Real.rpow_add hQ, add_neg_cancel, Real.rpow_zero, one_mul]

/-- Derivation of the potential pullback from raw amplitude and phase
scaling. The real factor `b` also covers signed harmonics. -/
theorem commonGraph_vectorPotential_pull {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ)
    {K L : ℝ} (hK : K ≠ 0) (hL : L ≠ 0) {Φ : Cylinder → ℝ}
    {x : SpaceTime} (hr : 0 < x.2 0)
    (hΦ : DifferentiableAt ℝ Φ ((commonGraph Q h k).map x)) (a : Cylinder → ComplexVector) :
    CurlClassBounds.vectorPotential K LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2)
      (fun y => (L / K) * Φ ((commonGraph Q h k).map y))
      (fun y => Q ^ (-CoordinateAlgebra.A h) • a ((commonGraph Q h k).map y)) x =
      Q ^ (-h) • CurlClassBounds.vectorPotential L PhysicalResidualBridge.ScaledGraph.radius
        (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
        (commonGraph Q h k).axial Φ a ((commonGraph Q h k).map x) := by
  let G := commonGraph Q h k
  have hl : 0 < G.radialScale := Real.rpow_pos_of_pos hQ _
  have hr' : G.radialScale * x.2 0 ≠ 0 := (mul_pos hl hr).ne'
  have hKL : K * (L / K) = L := by field_simp
  have he := vectorPotential_pull (Γ := G.map) (r := LinearWaveResidual.coordinateRadius)
    (R := PhysicalResidualBridge.ScaledGraph.radius) (x := x)
    (Sr := LinearWaveResidual.spaceDirection 0) (Sθ := LinearWaveResidual.spaceDirection 1)
    (Sz := LinearWaveResidual.spaceDirection 2) hl.ne' hr.ne' hK (div_ne_zero hL hK) hKL
    ((G.map_smoothAt hr').differentiableAt (by simp)) (G.map_radial hr') (G.map_angular hr')
    (G.map_axial hr') rfl hΦ a G.velocityScale
  rw [commonGraph_potentialScale hQ] at he
  exact he

theorem vectorPotential_congr (K : ℝ) (R : E → ℝ) (Vr Vθ Vz : E → E)
    {Φ Ψ : E → ℝ} {a b : E → ComplexVector} {x : E}
    (hΦ : Φ =ᶠ[𝓝 x] Ψ) (ha : a x = b x) :
    CurlClassBounds.vectorPotential K R Vr Vθ Vz Φ a x =
      CurlClassBounds.vectorPotential K R Vr Vθ Vz Ψ b x := by
  have hD (V : E → E) : along V Φ x = along V Ψ x :=
    congrArg (fun L : E →L[ℝ] ℝ => L (V x)) hΦ.fderiv_eq
  ext i
  simp only [CurlClassBounds.vectorPotential, vectorMode, mode, CurlClassBounds.coefficient,
    phaseNormal, hD, ha, carrier, hΦ.eq_of_nhds]

/-- The single reference potential expressed in physical cylindrical
coordinates, before taking its real part and rotating to Cartesian axes. -/
noncomputable def referencePotential (K : ℝ) (Ψ : SpaceTime → ℝ)
    (a : SpaceTime → ComplexVector) : SpaceTime → ComplexVector :=
  CurlClassBounds.vectorPotential K LinearWaveResidual.coordinateRadius
    (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
    (LinearWaveResidual.spaceDirection 2) Ψ a

/-- Potential covariance is derived from the primitive phase and amplitude
identities. No identity between curls or corrected velocities is assumed. -/
theorem referencePotential_eq_on {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ)
    {U : Set Cylinder} (hU : IsOpen U) {K L : ℝ} (hK : K ≠ 0) (hL : L ≠ 0)
    {Φ : Cylinder → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (a : Cylinder → ComplexVector)
    (Ψ : SpaceTime → ℝ) (v : SpaceTime → ComplexVector)
    (hphase : ∀ z ∈ (commonGraph Q h k).source U,
      K * Ψ z = L * Φ ((commonGraph Q h k).map z))
    (hamplitude : ∀ z ∈ (commonGraph Q h k).source U,
      v z = Q ^ (-CoordinateAlgebra.A h) • a ((commonGraph Q h k).map z)) :
    EqOn (referencePotential K Ψ v)
      (fun z => Q ^ (-h) • CurlClassBounds.vectorPotential L
        PhysicalResidualBridge.ScaledGraph.radius
        (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
        (commonGraph Q h k).axial Φ a ((commonGraph Q h k).map z))
      ((commonGraph Q h k).source U) := by
  intro z hz
  have ho := (commonGraph Q h k).source_open (Real.rpow_pos_of_pos hQ _) hU
  have he : Ψ =ᶠ[𝓝 z] fun y => (L / K) * Φ ((commonGraph Q h k).map y) := by
    apply eventually_of_mem (ho.mem_nhds hz)
    intro y hy
    apply mul_left_cancel₀ hK
    rw [hphase y hy]
    field_simp
  unfold referencePotential
  rw [vectorPotential_congr K _ _ _ _
    (b := fun y => Q ^ (-CoordinateAlgebra.A h) • a ((commonGraph Q h k).map y)) he (hamplitude z
      hz)]
  exact commonGraph_vectorPotential_pull hQ h k hK hL hz.1
    ((hΦ.contDiffAt (hU.mem_nhds hz.2)).differentiableAt (by simp)) a

/-- One Cartesian reference potential supplies every compatible band's
actual corrected wave. Amplitude and phase compatibility are primitive
field-value identities; the curl and cutoff derivatives are derived. -/
theorem reference_correctedWave {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ)
    {U : Set Cylinder} (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0)
    {K L : ℝ} (hK : K ≠ 0) (hL : L ≠ 0)
    {Φ : Cylinder → ℝ} {a : Cylinder → ComplexVector}
    (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (commonGraph Q h k).axial Φ x ≠ 0)
    (ht : ∀ x ∈ U, normalDot (phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (commonGraph Q h k).axial Φ x) (a x) = 0)
    (Ψ : SpaceTime → ℝ) (v : SpaceTime → ComplexVector)
    (hphase : ∀ z ∈ (commonGraph Q h k).source U,
      K * Ψ z = L * Φ ((commonGraph Q h k).map z))
    (hamplitude : ∀ z ∈ (commonGraph Q h k).source U,
      v z = Q ^ (-CoordinateAlgebra.A h) • a ((commonGraph Q h k).map z))
    {t : ℝ} {q : Space} (hz : (t, q) ∈ (commonGraph Q h k).source U)
    {A : VelocityField} (hA : DifferentiableAt ℝ A (t, CylindricalResidual.chart q))
    (hAvalue : (fun z : SpaceTime => A (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1) (realVector (referencePotential K Ψ v z))))
    (i : Fin 3) :
    (vectorMode L Φ (CurlClassBounds.realizedCoefficient L PhysicalResidualBridge.ScaledGraph.radius
      (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (commonGraph Q h k).axial Φ a) ((commonGraph Q h k).map (t, q)) i).re =
      Q ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(q 1))
        (SpatialCurl.spatialCurl A (t, CylindricalResidual.chart q)) i := by
  let G := commonGraph Q h k
  let B := CurlClassBounds.vectorPotential L PhysicalResidualBridge.ScaledGraph.radius
    G.radial PhysicalResidualBridge.ScaledGraph.angular G.axial Φ a
  have hgeom := ScaledGraph.geometry G hU hR
  have hBs := CurlClassBounds.vectorPotential_contDiffOn hgeom L hΦ ha hn
  have hB i : DifferentiableAt ℝ (fun y => B y i) (G.map (t, q)) :=
    (((contDiffOn_pi.mp hBs) i).contDiffAt (hU.mem_nhds hz.2)).differentiableAt (by simp)
  have he := referencePotential_eq_on hQ h k hU hK hL hΦ a Ψ v hphase hamplitude
  have hre : (fun z : SpaceTime => A (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1) (ScaledGraph.realPotential G (Q ^ (-h)) B z)) :=
        by
    filter_upwards [hAvalue, (G.source_open (Real.rpow_pos_of_pos hQ _) hU).mem_nhds hz] with z hAz
      hzU
    rw [hAz, he hzU]
    congr 2
  have hc := commonGraph_physical_curl hQ h k hz.1 hB hA hre i
  rw [CurlClassBounds.cylindricalCurl_vectorPotential hgeom hL hΦ ha hn ht hz.2] at hc
  exact hc

theorem wave_cutoff_potential (a : LinearWaveBounds.WaveCoefficients E)
    (s : WeightedClasses.StripData E) (d : LinearWaveBounds.GraphDirections E)
    (ψ : ℕ → E → ℝ) (n : ℕ) (x : E) :
    (a.withCutoff ψ).curlPotential s d n x = ψ n x • a.curlPotential s d n x :=
  vectorPotential_cutoff _ _ _ _ _ _ _ _ _

/-- The coefficient used by the wave pipeline, after the cutoff, is the
coefficient of the actual curl. The cutoff is applied exactly once. -/
theorem corrected_is_curl (a : LinearWaveBounds.WaveCoefficients E)
    (s : WeightedClasses.StripData E) (d : LinearWaveBounds.GraphDirections E)
    (ψ : ℕ → E → ℝ) (n : ℕ)
    (G : CurlClassBounds.CylindricalGeometry s.domain (a.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n))
    (hK : a.frequency n ≠ 0) (hΦ : ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (ha : ContDiffOn ℝ ∞ (a.amplitude n) s.domain)
    (hψ : ContDiffOn ℝ ∞ (ψ n) s.domain)
    (hn : ∀ x ∈ s.domain, a.normal s d n x ≠ 0)
    (ht : ∀ x ∈ s.domain, normalDot (a.normal s d n x) (a.amplitude n x) = 0)
    {x : E} (hx : x ∈ s.domain) :
    CurlClassBounds.cylindricalCurl (a.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) ((a.withCutoff ψ).curlPotential s d n) x =
      vectorMode (a.frequency n) (a.phase n) ((a.corrected s d ψ).amplitude n) x := by
  have hcut : ∀ y ∈ s.domain, normalDot (a.normal s d n y) (ψ n y • a.amplitude n y) = 0 := by
    intro y hy
    have he : normalDot (a.normal s d n y) (ψ n y • a.amplitude n y) =
        (ψ n y : ℂ) * normalDot (a.normal s d n y) (a.amplitude n y) := by
      simp [normalDot, Complex.real_smul]
      ring
    rw [he, ht y hy, mul_zero]
  exact CurlClassBounds.cylindricalCurl_vectorPotential G hK hΦ (hψ.smul ha) hn hcut hx

theorem spatialCurl_zero_of_zero_near {A : VelocityField} {z : SpaceTime}
    (hA : A =ᶠ[𝓝 z] fun _ => 0) : SpatialCurl.spatialCurl A z = 0 := by
  have hs : (fun y => A (z.1, y)) =ᶠ[𝓝 z.2] fun _ => 0 :=
    hA.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  change SpatialCurl.curl (fun y => A (z.1, y)) z.2 = 0
  rw [SpatialCurl.curl_eq_of_eventuallyEq hs]
  simp [SpatialCurl.curl]

/-- Annularly localized potentials have zero actual curl on the axis,
without assigning a cylindrical angle there. -/
theorem spatialCurl_axis_zero (A : VelocityField) (t : ℝ) (x : Space)
    (hx₀ : x 0 = 0) (hx₁ : x 1 = 0) {r : ℝ} (hr : 0 < r)
    (hA : ∀ y : Space, (y 0) ^ 2 + (y 1) ^ 2 < r ^ 2 → A (t, y) = 0) :
    SpatialCurl.spatialCurl A (t, x) = 0 := by
  have hc : Continuous (fun y : Space => (y 0) ^ 2 + (y 1) ^ 2) :=
    ((AxisymmetricFields.projection 0).continuous.pow 2).add
      ((AxisymmetricFields.projection 1).continuous.pow 2)
  have hx : (x 0) ^ 2 + (x 1) ^ 2 < r ^ 2 := by simp [hx₀, hx₁, sq_pos_of_pos hr]
  have hn : {y : Space | (y 0) ^ 2 + (y 1) ^ 2 < r ^ 2} ∈ 𝓝 x :=
    (isOpen_lt hc continuous_const).mem_nhds hx
  have he : (fun y => A (t, y)) =ᶠ[𝓝 x] fun _ => 0 := eventually_of_mem hn hA
  change SpatialCurl.curl (fun y => A (t, y)) x = 0
  rw [SpatialCurl.curl_eq_of_eventuallyEq he]
  simp [SpatialCurl.curl]

/-! ## A concrete Cartesian potential in an actual inverse polar chart -/

theorem realVector_smooth : ContDiff ℝ ∞ realVector := by
  apply (contDiff_piLp 2).mpr
  intro i
  simp only [realVector_apply]
  exact Complex.reCLM.contDiff.comp (ContinuousLinearMap.proj i : ComplexVector →L[ℝ] ℂ).contDiff

noncomputable def polarInput (a : ℝ) (j : PolarCharts.Index) (z : SpaceTime) :
    PhysicalResidualBridge.Plane :=
  PolarCharts.chart a j (PhysicalGraphBounds.radialProjection z)

noncomputable def polarCoordinates (a : ℝ) (j : PolarCharts.Index) (z : SpaceTime) : SpaceTime :=
  (z.1, AxisymmetricResidual.pack (polarInput a j z).1 (polarInput a j z).2 (z.2 2))

/-- The actual Cartesian field, not a prescribed derivative or a matching
predicate. Its inverse polar chart has a smooth global extension. -/
noncomputable def cartesianPotential (a : ℝ) (j : PolarCharts.Index)
    (B : SpaceTime → ComplexVector) (z : SpaceTime) : Space :=
  CylindricalResidual.frame (polarInput a j z).2 (realVector (B (polarCoordinates a j z)))

theorem polarInput_smooth {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) :
    ContDiff ℝ ∞ (polarInput a j) :=
  (PolarCharts.chart_contDiff ha j).comp PhysicalGraphBounds.radialProjection.contDiff

theorem polarCoordinates_smooth {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) :
    ContDiff ℝ ∞ (polarCoordinates a j) := by
  have hp := polarInput_smooth ha j
  have hz : ContDiff ℝ ∞ (fun z : SpaceTime => z.2 2) :=
    (PhysicalGraphBounds.coordinateProjection 2).contDiff
  exact contDiff_fst.prodMk (((hp.fst.smul contDiff_const).add
    (hp.snd.smul contDiff_const)).add (hz.smul contDiff_const))

theorem cartesianPotential_smoothAt {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {B : SpaceTime → ComplexVector} {z : SpaceTime}
    (hB : ContDiffAt ℝ ∞ B (polarCoordinates a j z)) :
    ContDiffAt ℝ ∞ (cartesianPotential a j B) z :=
  (CylindricalResidual.contDiff_frame.contDiffAt.comp z (polarInput_smooth ha
    j).contDiffAt.snd).clm_apply
    (realVector_smooth.contDiffAt.comp z (hB.comp z (polarCoordinates_smooth ha j).contDiffAt))

noncomputable def validCylindrical (a : ℝ) (j : PolarCharts.Index) : Set SpaceTime :=
  {z | 0 < z.2 0 ∧
    (z.2 1 - PolarCharts.offset j) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
    PolarCharts.polar (z.2 0, z.2 1) ∈ PolarCharts.chartDomain a j}

theorem validCylindrical_open (a : ℝ) (j : PolarCharts.Index) :
    IsOpen (validCylindrical a j) :=
  (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous).inter
    ((isOpen_Ioo.preimage ((PhysicalGraphBounds.coordinateProjection 1).continuous.sub
      continuous_const)).inter
      ((PolarCharts.chartDomain_open a j).preimage
        (PolarCharts.polar_contDiff.continuous.comp
          ((PhysicalGraphBounds.coordinateProjection 0).continuous.prodMk
            (PhysicalGraphBounds.coordinateProjection 1).continuous))))

theorem polarInput_forward {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ validCylindrical a j) :
    polarInput a j (z.1, CylindricalResidual.chart z.2) = (z.2 0, z.2 1) := by
  have he : PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2) =
      PolarCharts.polar (z.2 0, z.2 1) := by
    simp [PhysicalGraphBounds.radialProjection_apply, CylindricalResidual.chart, PolarCharts.polar]
  unfold polarInput
  rw [he]
  exact PolarCharts.chart_polar ha j hz.1 hz.2.1 hz.2.2

theorem polarCoordinates_forward {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ validCylindrical a j) :
    polarCoordinates a j (z.1, CylindricalResidual.chart z.2) = z := by
  unfold polarCoordinates
  rw [polarInput_forward ha j hz]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [CylindricalResidual.chart]

theorem cartesianPotential_forward {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (B : SpaceTime → ComplexVector) {z : SpaceTime} (hz : z ∈ validCylindrical a j) :
    cartesianPotential a j B (z.1, CylindricalResidual.chart z.2) =
      CylindricalResidual.frame (z.2 1) (realVector (B z)) := by
  unfold cartesianPotential
  rw [polarInput_forward ha j hz, polarCoordinates_forward ha j hz]

theorem cartesianPotential_forward_germ {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (B : SpaceTime → ComplexVector) {z : SpaceTime} (hz : z ∈ validCylindrical a j) :
    (fun w : SpaceTime => cartesianPotential a j B (w.1, CylindricalResidual.chart w.2)) =ᶠ[𝓝 z]
      (fun w => CylindricalResidual.frame (w.2 1) (realVector (B w))) :=
  eventually_of_mem ((validCylindrical_open a j).mem_nhds hz)
    (fun _ hw => cartesianPotential_forward ha j B hw)

/-- The constructed Cartesian potential has the prescribed actual curl in
its polar chart. No potential-representation premise remains. -/
theorem cartesianPotential_curl {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {B : SpaceTime → ComplexVector} {z : SpaceTime} (hz : z ∈ validCylindrical a j)
    (hB : ContDiffAt ℝ ∞ B z) (i : Fin 3) :
    CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (cartesianPotential a j B) (z.1, CylindricalResidual.chart z.2)) i =
      (CurlClassBounds.cylindricalCurl LinearWaveResidual.coordinateRadius
        (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
        (LinearWaveResidual.spaceDirection 2) B z i).re := by
  have hBc : ContDiffAt ℝ ∞ B (polarCoordinates a j (z.1, CylindricalResidual.chart z.2)) := by
    rw [polarCoordinates_forward ha j hz]
    exact hB
  have hd : DifferentiableAt ℝ B z := hB.differentiableAt (by simp)
  have hdi k : DifferentiableAt ℝ (fun w => B w k) z := (differentiableAt_pi.mp hd) k
  rw [curl_of_representation ((cartesianPotential_smoothAt ha j hBc).differentiableAt (by simp))
    (realVector_differentiableAt hdi) hz.1.ne' (cartesianPotential_forward_germ ha j B hz)]
  simpa only [realVector_apply] using (real_cylindricalCurl _ _ _ _ hdi i).symm

theorem frame_periodic : Periodic CylindricalResidual.frame (2 * Real.pi) := by
  intro θ
  ext v i
  fin_cases i <;> simp [CylindricalResidual.frame_apply]

/-- Periodicity of the full cylindrical potential gives equality of the
constructed Cartesian potentials on chart overlaps. -/
theorem cartesianPotential_overlap {a : ℝ} (ha : 0 < a) (i j : PolarCharts.Index)
    (B : SpaceTime → ComplexVector)
    (hB : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {x : SpaceTime}
    (hi : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a i)
    (hj : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j) :
    cartesianPotential a i B x = cartesianPotential a j B x := by
  let f : PolarCharts.Plane → Space := fun p =>
    CylindricalResidual.frame p.2 (realVector (B (x.1, AxisymmetricResidual.pack p.1 p.2 (x.2 2))))
  have hf (r : ℝ) : Periodic (fun θ => f (r, θ)) (2 * Real.pi) := by
    intro θ
    dsimp only [f]
    rw [frame_periodic θ]
    have hper := hB x.1 r (x.2 2) θ
    dsimp only at hper
    rw [hper]
  exact PolarCharts.chart_periodic_agree ha f hf i j hi hj

theorem spatialCurl_congr {A B : VelocityField} {z : SpaceTime} (hAB : A =ᶠ[𝓝 z] B) :
    SpatialCurl.spatialCurl A z = SpatialCurl.spatialCurl B z :=
  SpatialCurl.curl_eq_of_eventuallyEq
    (hAB.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt)

theorem cartesianPotential_overlap_germ {a : ℝ} (ha : 0 < a) (i j : PolarCharts.Index)
    (B : SpaceTime → ComplexVector)
    (hB : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {x : SpaceTime}
    (hi : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a i)
    (hj : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j) :
    cartesianPotential a i B =ᶠ[𝓝 x] cartesianPotential a j B := by
  filter_upwards [PhysicalGraphBounds.radialProjection.continuous.continuousAt
    ((PolarCharts.chartDomain_open a i).mem_nhds hi),
    PhysicalGraphBounds.radialProjection.continuous.continuousAt
    ((PolarCharts.chartDomain_open a j).mem_nhds hj)] with y hyi hyj
  exact cartesianPotential_overlap ha i j B hB hyi hyj

theorem cartesianPotential_curl_overlap {a : ℝ} (ha : 0 < a) (i j : PolarCharts.Index)
    (B : SpaceTime → ComplexVector)
    (hB : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {x : SpaceTime}
    (hi : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a i)
    (hj : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j) :
    SpatialCurl.spatialCurl (cartesianPotential a i B) x =
      SpatialCurl.spatialCurl (cartesianPotential a j B) x :=
  spatialCurl_congr (cartesianPotential_overlap_germ ha i j B hB hi hj)

/-- A single actual Cartesian potential is selected from the compatible
local inverse charts. Outside their union it is defined to be zero. -/
noncomputable def globalCartesianPotential (a : ℝ) (B : SpaceTime → ComplexVector)
    (x : SpaceTime) : Space := by
  classical
  exact if h : ∃ j : PolarCharts.Index,
      PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j then
    cartesianPotential a (Classical.choose h) B x
  else 0

theorem globalCartesianPotential_eq_local {a : ℝ} (ha : 0 < a)
    (B : SpaceTime → ComplexVector)
    (hB : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {x : SpaceTime} (j : PolarCharts.Index)
    (hj : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j) :
    globalCartesianPotential a B x = cartesianPotential a j B x := by
  have he : ∃ i : PolarCharts.Index,
      PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a i := ⟨j, hj⟩
  rw [globalCartesianPotential, dite_eq_left he]
  exact cartesianPotential_overlap ha _ j B hB (Classical.choose_spec he) hj

theorem globalCartesianPotential_germ_local {a : ℝ} (ha : 0 < a)
    (B : SpaceTime → ComplexVector)
    (hB : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {x : SpaceTime} (j : PolarCharts.Index)
    (hj : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j) :
    globalCartesianPotential a B =ᶠ[𝓝 x] cartesianPotential a j B := by
  filter_upwards [PhysicalGraphBounds.radialProjection.continuous.continuousAt
    ((PolarCharts.chartDomain_open a j).mem_nhds hj)] with y hy
  exact globalCartesianPotential_eq_local ha B hB j hy

theorem polarCoordinates_radius {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {x : SpaceTime} (hj : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j) :
    (polarCoordinates a j x).2 0 = PolarCharts.radius (PhysicalGraphBounds.radialProjection x) := by
  simp only [polarCoordinates, AxisymmetricResidual.pack_zero, polarInput]
  rw [PolarCharts.chart_eq_localChart ha j hj, PolarCharts.localChart_apply]

theorem globalCartesianPotential_zero {a : ℝ} (ha : 0 < a)
    {B : SpaceTime → ComplexVector}
    (hzero : ∀ z : SpaceTime, z.2 0 ≤ a → B z = 0) {x : SpaceTime}
    (hx : PolarCharts.radius (PhysicalGraphBounds.radialProjection x) ≤ a) :
    globalCartesianPotential a B x = 0 := by
  unfold globalCartesianPotential
  split_ifs with h
  · let j := Classical.choose h
    have hj := Classical.choose_spec h
    have hz : (polarCoordinates a j x).2 0 ≤ a := by rw [polarCoordinates_radius ha j hj]; exact hx
    change cartesianPotential a j B x = 0
    unfold cartesianPotential
    rw [hzero _ hz]
    simp [realVector, AxisymmetricResidual.pack]
  · rfl

/-- Annular vanishing removes the boundary of the selected-chart union;
the resulting Cartesian potential is genuinely smooth everywhere. -/
theorem globalCartesianPotential_smooth {a : ℝ} (ha : 0 < a)
    {B : SpaceTime → ComplexVector}
    (hB : ContDiffOn ℝ ∞ B {z | 0 < z.2 0})
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    (hzero : ∀ z : SpaceTime, z.2 0 ≤ a → B z = 0) :
    ContDiff ℝ ∞ (globalCartesianPotential a B) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hex : ∃ j : PolarCharts.Index,
      PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j
  · obtain ⟨j, hj⟩ := hex
    have hrot : 0 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection x)).1 := by
      have hv : a / 4 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection x)).1 := hj
      linarith
    have hrad : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection x) := by
      rw [← PolarCharts.radius_rotate j]
      exact PolarCharts.radius_pos_of_fst_pos hrot
    have hz : 0 < (polarCoordinates a j x).2 0 := by rw [polarCoordinates_radius ha j hj]; exact
      hrad
    have hopen : IsOpen {z : SpaceTime | 0 < z.2 0} :=
      isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous
    have hs := cartesianPotential_smoothAt ha j (hB.contDiffAt (hopen.mem_nhds hz))
    exact hs.congr_of_eventuallyEq (globalCartesianPotential_germ_local ha B hper j hj)
  · have hnorm : ‖PhysicalGraphBounds.radialProjection x‖ ≤ a / 4 := by
      obtain ⟨j, hj⟩ := PolarCharts.exists_rotate_fst_ge (p := PhysicalGraphBounds.radialProjection
        x) le_rfl
      by_contra hh
      apply hex
      exact ⟨j, lt_of_lt_of_le (lt_of_not_ge hh) hj⟩
    have hrad : PolarCharts.radius (PhysicalGraphBounds.radialProjection x) < a := by
      have hb := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.radialProjection x)
      linarith
    have hc : Continuous (fun y : SpaceTime => PolarCharts.radius
      (PhysicalGraphBounds.radialProjection y)) :=
      PolarCharts.radius_continuous.comp PhysicalGraphBounds.radialProjection.continuous
    have hn : ∀ᶠ y in 𝓝 x, PolarCharts.radius (PhysicalGraphBounds.radialProjection y) < a :=
      (isOpen_lt hc continuous_const).mem_nhds hrad
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    exact globalCartesianPotential_zero ha hzero hy.le

theorem globalCartesianPotential_zero_germ {a : ℝ} (ha : 0 < a)
    {B : SpaceTime → ComplexVector}
    (hzero : ∀ z : SpaceTime, z.2 0 ≤ a → B z = 0) {x : SpaceTime}
    (hx : PolarCharts.radius (PhysicalGraphBounds.radialProjection x) < a) :
    globalCartesianPotential a B =ᶠ[𝓝 x] fun _ => 0 := by
  have hc : Continuous (fun y : SpaceTime =>
      PolarCharts.radius (PhysicalGraphBounds.radialProjection y)) :=
    PolarCharts.radius_continuous.comp PhysicalGraphBounds.radialProjection.continuous
  filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hx] with y hy
  exact globalCartesianPotential_zero ha hzero hy.le

/-- The potential need only be smooth on the physical time domain; no
extension through a possible singular terminal time is required. -/
theorem globalCartesianPotential_smoothOn {a : ℝ} (ha : 0 < a)
    {times : Set ℝ} (hTimes : IsOpen times) {B : SpaceTime → ComplexVector}
    (hB : ContDiffOn ℝ ∞ B {z | z.1 ∈ times ∧ 0 < z.2 0})
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    (hzero : ∀ z : SpaceTime, z.2 0 ≤ a → B z = 0) :
    ContDiffOn ℝ ∞ (globalCartesianPotential a B) (times ×ˢ (univ : Set Space)) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  by_cases hex : ∃ j : PolarCharts.Index,
      PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j
  · obtain ⟨j, hj⟩ := hex
    have hrot : 0 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection x)).1 := by
      have hv : a / 4 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection x)).1 := hj
      linarith
    have hrad : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection x) := by
      rw [← PolarCharts.radius_rotate j]
      exact PolarCharts.radius_pos_of_fst_pos hrot
    have hz : (polarCoordinates a j x).1 ∈ times ∧ 0 < (polarCoordinates a j x).2 0 := by
      constructor
      · exact hx.1
      · rw [polarCoordinates_radius ha j hj]
        exact hrad
    have hopen : IsOpen {z : SpaceTime | z.1 ∈ times ∧ 0 < z.2 0} :=
      (hTimes.preimage continuous_fst).inter
        (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous)
    exact (cartesianPotential_smoothAt ha j (hB.contDiffAt (hopen.mem_nhds
      hz))).congr_of_eventuallyEq
      (globalCartesianPotential_germ_local ha B hper j hj)
  · have hnorm : ‖PhysicalGraphBounds.radialProjection x‖ ≤ a / 4 := by
      obtain ⟨j, hj⟩ := PolarCharts.exists_rotate_fst_ge (p := PhysicalGraphBounds.radialProjection
        x) le_rfl
      by_contra hh
      exact hex ⟨j, lt_of_lt_of_le (lt_of_not_ge hh) hj⟩
    have hrad : PolarCharts.radius (PhysicalGraphBounds.radialProjection x) < a := by
      have hb := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.radialProjection x)
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq (globalCartesianPotential_zero_germ ha hzero hrad)

noncomputable def cartesianVelocity (a : ℝ) (B : SpaceTime → ComplexVector) : VelocityField :=
  SpatialCurl.spatialCurl (globalCartesianPotential a B)

theorem cartesianVelocity_smoothOn {a : ℝ} (ha : 0 < a)
    {times : Set ℝ} (hTimes : IsOpen times) {B : SpaceTime → ComplexVector}
    (hB : ContDiffOn ℝ ∞ B {z | z.1 ∈ times ∧ 0 < z.2 0})
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    (hzero : ∀ z : SpaceTime, z.2 0 ≤ a → B z = 0) :
    ContDiffOn ℝ ∞ (cartesianVelocity a B) (times ×ˢ (univ : Set Space)) :=
  SpatialCurl.contDiffOn_spatialCurl (globalCartesianPotential_smoothOn ha hTimes hB hper hzero)
    (by simp)

theorem cartesianVelocity_divergence {a : ℝ} (ha : 0 < a)
    {times : Set ℝ} (hTimes : IsOpen times) {B : SpaceTime → ComplexVector}
    (hB : ContDiffOn ℝ ∞ B {z | z.1 ∈ times ∧ 0 < z.2 0})
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    (hzero : ∀ z : SpaceTime, z.2 0 ≤ a → B z = 0)
    {t : ℝ} (ht : t ∈ times) (x : Space) :
    spatialDivergence (cartesianVelocity a B) t x = 0 :=
  SpatialCurl.spatialDivergence_spatialCurl_on
    ((globalCartesianPotential_smoothOn ha hTimes hB hper hzero).of_le
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le) ht x

theorem cartesianVelocity_axis_zero {a : ℝ} (ha : 0 < a)
    {B : SpaceTime → ComplexVector}
    (hzero : ∀ z : SpaceTime, z.2 0 ≤ a → B z = 0)
    (t : ℝ) (x : Space) (hx₀ : x 0 = 0) (hx₁ : x 1 = 0) :
    cartesianVelocity a B (t, x) = 0 := by
  apply spatialCurl_zero_of_zero_near
  apply globalCartesianPotential_zero_germ ha hzero
  simpa [PolarCharts.radius, PhysicalGraphBounds.radialProjection_apply, hx₀, hx₁] using ha

theorem globalCartesianPotential_curl {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {B : SpaceTime → ComplexVector}
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {z : SpaceTime} (hz : z ∈ validCylindrical a j) (hB : ContDiffAt ℝ ∞ B z) (i : Fin 3) :
    CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (globalCartesianPotential a B) (z.1, CylindricalResidual.chart z.2))
        i =
      (CurlClassBounds.cylindricalCurl LinearWaveResidual.coordinateRadius
        (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
        (LinearWaveResidual.spaceDirection 2) B z i).re := by
  have hj : PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a j := by
    simpa [PhysicalGraphBounds.radialProjection_apply, CylindricalResidual.chart,
      PolarCharts.polar] using hz.2.2
  rw [spatialCurl_congr (globalCartesianPotential_germ_local ha B hper j hj)]
  exact cartesianPotential_curl ha j hz hB i

theorem globalCartesianPotential_forward_germ {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (B : SpaceTime → ComplexVector)
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {z : SpaceTime} (hz : z ∈ validCylindrical a j) :
    (fun w : SpaceTime => globalCartesianPotential a B (w.1, CylindricalResidual.chart w.2)) =ᶠ[𝓝 z]
      (fun w => CylindricalResidual.frame (w.2 1) (realVector (B w))) := by
  filter_upwards [(validCylindrical_open a j).mem_nhds hz] with y hy
  have hj : PhysicalGraphBounds.radialProjection (y.1, CylindricalResidual.chart y.2) ∈
      PolarCharts.chartDomain a j := by
    simpa [PhysicalGraphBounds.radialProjection_apply, CylindricalResidual.chart,
      PolarCharts.polar] using hy.2.2
  rw [globalCartesianPotential_eq_local ha B hper j hj, cartesianPotential_forward ha j B hy]

theorem globalCartesianPotential_smoothAt_forward {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {B : SpaceTime → ComplexVector}
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {z : SpaceTime} (hz : z ∈ validCylindrical a j) (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (globalCartesianPotential a B) (z.1, CylindricalResidual.chart z.2) := by
  have hj : PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a j := by
    simpa [PhysicalGraphBounds.radialProjection_apply, CylindricalResidual.chart,
      PolarCharts.polar] using hz.2.2
  have hb : ContDiffAt ℝ ∞ B (polarCoordinates a j (z.1, CylindricalResidual.chart z.2)) := by
    rw [polarCoordinates_forward ha j hz]
    exact hB
  exact (cartesianPotential_smoothAt ha j hb).congr_of_eventuallyEq
    (globalCartesianPotential_germ_local ha B hper j hj)

/-- Integer angular frequency makes the complete potential periodic,
including its normal coefficient and inverse carrier. -/
theorem vectorPotential_fullTurn {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {θ : D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    {Φ : D → ℝ} {a : D → ComplexVector} {slope K : ℝ} (m : ℤ)
    (hR : CopyAngularInvariance.Invariant θ R)
    (hr : CopyAngularInvariance.Invariant θ Vr)
    (hθ : CopyAngularInvariance.Invariant θ Vθ)
    (hz : CopyAngularInvariance.Invariant θ Vz)
    (hΦ : CopyAngularInvariance.AffinePhase θ slope Φ)
    (ha : CopyAngularInvariance.Invariant θ a) (hfreq : K * slope = (m : ℝ)) (x : D) :
    CurlClassBounds.vectorPotential K R Vr Vθ Vz Φ a (x + (2 * Real.pi) • θ) =
      CurlClassBounds.vectorPotential K R Vr Vθ Vz Φ a x := by
  have hc := (CopyAngularInvariance.coefficient_invariant hR hr hθ hz hΦ ha).map
    (fun v => CurlClassBounds.inverseCarrier K • v)
  have he : phaseFactor K * ((slope * (2 * Real.pi) : ℝ) : ℂ) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    have hf : (K : ℂ) * (slope : ℂ) = (m : ℂ) := by exact_mod_cast hfreq
    unfold phaseFactor
    push_cast
    calc
      _ = ((K : ℂ) * (slope : ℂ)) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hf]
  unfold CurlClassBounds.vectorPotential
  rw [CopyAngularInvariance.vectorMode_translate hc hΦ, he,
    Complex.exp_int_mul_two_pi_mul_I, one_smul]

/-- The end-to-end band reconstruction uses a single explicitly constructed
Cartesian potential. Only primitive phase/amplitude compatibility and
periodicity are inputs; potential and curl compatibility are conclusions. -/
theorem reference_correctedWave_constructed {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ)
    {U : Set Cylinder} (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0)
    {K L : ℝ} (hK : K ≠ 0) (hL : L ≠ 0)
    {Φ : Cylinder → ℝ} {a : Cylinder → ComplexVector}
    (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (commonGraph Q h k).axial Φ x ≠ 0)
    (ht : ∀ x ∈ U, normalDot (phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (commonGraph Q h k).axial Φ x) (a x) = 0)
    (Ψ : SpaceTime → ℝ) (v : SpaceTime → ComplexVector)
    (hphase : ∀ z ∈ (commonGraph Q h k).source U,
      K * Ψ z = L * Φ ((commonGraph Q h k).map z))
    (hamplitude : ∀ z ∈ (commonGraph Q h k).source U,
      v z = Q ^ (-CoordinateAlgebra.A h) • a ((commonGraph Q h k).map z))
    (hper : ∀ t r z : ℝ, Periodic
      (fun θ => referencePotential K Ψ v (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {t : ℝ} {q : Space} (hz : (t, q) ∈ (commonGraph Q h k).source U)
    {δ : ℝ} (hδ : 0 < δ) (j : PolarCharts.Index) (hchart : (t, q) ∈ validCylindrical δ j)
    (i : Fin 3) :
    (vectorMode L Φ (CurlClassBounds.realizedCoefficient L PhysicalResidualBridge.ScaledGraph.radius
      (commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (commonGraph Q h k).axial Φ a) ((commonGraph Q h k).map (t, q)) i).re =
      Q ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(q 1))
        (SpatialCurl.spatialCurl (globalCartesianPotential δ (referencePotential K Ψ v))
          (t, CylindricalResidual.chart q)) i := by
  let G := commonGraph Q h k
  have hgeom := ScaledGraph.geometry G hU hR
  have hBs := CurlClassBounds.vectorPotential_contDiffOn hgeom L hΦ ha hn
  have hm : ContDiffAt ℝ ∞ G.map (t, q) := G.map_smoothAt
    (mul_pos (Real.rpow_pos_of_pos hQ _) hz.1).ne'
  have htarget := ((hBs.contDiffAt (hU.mem_nhds hz.2)).comp (t, q) hm).const_smul (Q ^ (-h))
  have hEq := referencePotential_eq_on hQ h k hU hK hL hΦ a Ψ v hphase hamplitude
  have hs : ContDiffAt ℝ ∞ (referencePotential K Ψ v) (t, q) :=
    htarget.congr_of_eventuallyEq
      (eventually_of_mem ((G.source_open (Real.rpow_pos_of_pos hQ _) hU).mem_nhds hz) hEq)
  exact reference_correctedWave hQ h k hU hR hK hL hΦ ha hn ht Ψ v hphase hamplitude hz
    ((globalCartesianPotential_smoothAt_forward hδ j hper hchart hs).differentiableAt (by simp))
    (globalCartesianPotential_forward_germ hδ j (referencePotential K Ψ v) hper hchart) i

end

end NavierStokes.PhysicalCurlCovariance
