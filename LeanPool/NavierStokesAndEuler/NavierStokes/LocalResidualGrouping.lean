/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicResidual

/-!
# Actual harmonic residual grouping on a valid open chart

Closed wave supports need be disjoint only after intersection with the valid
chart. At a point in that chart, a nonzero left wave forces the right wave to
have a zero germ, so all cross-label transport terms vanish. The resulting
grouping retains the independent axisymmetric alias in the actual mean mode.
-/

section

/-!
# Grouping the actual residual with an independent axisymmetric alias

The alias removed from the good residual may contain an arbitrary function
of the non-angular variables in addition to the finite harmonic label sums.
Subtracting that function changes the angular mean by the same amount and
leaves the nonconstant residual unchanged.  The needed angular integrability
is derived from the represented finite harmonic fields, with no regularity
or support assumption on the independent alias.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.AxisymmetricResidualGrouping

open Set Function Filter MeasureTheory CorrectionState
open scoped Topology ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Lift an arbitrary mean vector to a field constant in the angular variable. -/
noncomputable def axisymmetricLift (a : MeanVector D) : Oscillation D :=
  fun n x => a n x.1

/-- Add an independent alias without changing any velocity or pressure field. -/
noncomputable def addAxisymmetricAlias (s : State D) (a : MeanVector D) : State D :=
  { s with errors := { s.errors with aliasError := s.errors.aliasError + axisymmetricLift a } }

/-- Remove precisely the specified independent alias from the stored errors. -/
noncomputable def eraseAxisymmetricAlias (s : State D) (a : MeanVector D) : State D :=
  { s with errors := { s.errors with aliasError := s.errors.aliasError - axisymmetricLift a } }

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem add_eraseAxisymmetricAlias (s : State D) (a : MeanVector D) :
    addAxisymmetricAlias (eraseAxisymmetricAlias s a) a = s := by
  simp [addAxisymmetricAlias, eraseAxisymmetricAlias]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem erase_addAxisymmetricAlias (s : State D) (a : MeanVector D) :
    eraseAxisymmetricAlias (addAxisymmetricAlias s a) a = s := by
  simp [addAxisymmetricAlias, eraseAxisymmetricAlias]

@[simp] theorem stateFullResidual_addAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) :
    HarmonicResidual.stateFullResidual c (addAxisymmetricAlias s a) =
      HarmonicResidual.stateFullResidual c s := rfl

@[simp] theorem stateFullResidual_eraseAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) :
    HarmonicResidual.stateFullResidual c (eraseAxisymmetricAlias s a) =
      HarmonicResidual.stateFullResidual c s := rfl

theorem stateGoodResidual_addAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    HarmonicResidual.stateGoodResidual c (addAxisymmetricAlias s a) n x i =
      HarmonicResidual.stateGoodResidual c s n x i - a n x.1 i := by
  simp only [HarmonicResidual.stateGoodResidual, Pi.sub_apply]
  rw [stateFullResidual_addAxisymmetricAlias]
  simp only [ExcludedErrors.total,
    addAxisymmetricAlias, axisymmetricLift, Pi.add_apply]
  ring

theorem stateGoodResidual_eraseAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    HarmonicResidual.stateGoodResidual c (eraseAxisymmetricAlias s a) n x i =
      HarmonicResidual.stateGoodResidual c s n x i + a n x.1 i := by
  simp only [HarmonicResidual.stateGoodResidual, Pi.sub_apply]
  rw [stateFullResidual_eraseAxisymmetricAlias]
  simp only [ExcludedErrors.total,
    eraseAxisymmetricAlias, axisymmetricLift, Pi.add_apply, Pi.sub_apply]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Angular integration needs integrability only on this one fiber. -/
theorem angularAverage_sub_axisymmetric (f : OscillatoryScalar D) (a : ScalarField D)
    (n : ℕ) (x : D)
    (hf : IntervalIntegrable (fun θ => f n (x, θ)) volume 0 (2 * Real.pi)) :
    angularAverage (fun m y => f m y - a m y.1) n x =
      angularAverage f n x - a n x := by
  simp only [angularAverage]
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, sub_div]
  field_simp [Real.pi_ne_zero]

/-- Adding an arbitrary axisymmetric alias leaves the nonconstant residual
unchanged on every angular fiber on which the original residual is integrable. -/
theorem stateGoodWaveResidual_addAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) (n : ℕ) (x : D × ℝ) (i : Fin 3)
    (hf : IntervalIntegrable
      (fun θ => HarmonicResidual.stateGoodResidual c s n (x.1, θ) i)
      volume 0 (2 * Real.pi)) :
    HarmonicResidual.stateGoodWaveResidual c (addAxisymmetricAlias s a) n x i =
      HarmonicResidual.stateGoodWaveResidual c s n x i := by
  simp only [HarmonicResidual.stateGoodWaveResidual]
  simp_rw [stateGoodResidual_addAxisymmetricAlias]
  rw [angularAverage_sub_axisymmetric
    (fun m y => HarmonicResidual.stateGoodResidual c s m y i)
    (fun m y => a m y i) n x.1 hf]
  ring

/-- The finite label representation keeps the independent zero mode explicit. -/
structure Representation {ι : Type*} (labels : ℕ → Finset ι)
    (blocks : ι → HarmonicBlock D)
    (gaussianCoeffs aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D)
    (s : State D) (axis : MeanVector D) : Prop where
  velocity : ∀ n x i, s.oscillation n x i = ∑ l ∈ labels n, (blocks l).oscillation n x i
  pressure : ∀ n x, s.oscillatoryPressure n x =
    ∑ l ∈ labels n, (blocks l).oscillatoryPressure n x
  gaussian : ∀ n x i, s.errors.gaussian n x i =
    ∑ l ∈ labels n,
      ((HarmonicResidual.ofBlock (blocks l) (gaussianCoeffs l) (aliasCoeffs l) n).gaussianField x
          i).re
  aliasError : ∀ n x i, s.errors.aliasError n x i =
    (∑ l ∈ labels n,
      ((HarmonicResidual.ofBlock (blocks l) (gaussianCoeffs l) (aliasCoeffs l) n).aliasField x
          i).re) +
      axis n x.1 i

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem Representation.erase {ι : Type*} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {s : State D} {axis : MeanVector D}
    (h : Representation labels blocks gaussian aliasCoeffs s axis) :
    HarmonicResidual.BlockRepresentation labels blocks gaussian aliasCoeffs
      (eraseAxisymmetricAlias s axis) where
  velocity := h.velocity
  pressure := h.pressure
  gaussian := h.gaussian
  aliasError := by
    intro n x i
    change s.errors.aliasError n x i - axis n x.1 i = _
    rw [h.aliasError]
    exact add_sub_cancel_right _ _

theorem extractionRegular_erase {ι : Type*} {U : Set D} {c : Context D} {s : State D}
    {labels : ℕ → Finset ι} {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D} {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    (axis : MeanVector D) :
    HarmonicResidual.ExtractionRegular U c (eraseAxisymmetricAlias s axis)
      labels blocks gaussian aliasCoeffs n :=
  ⟨h.frame, h.base, h.mean, h.pressure, h.blocks, h.gaussian, h.aliasError,
    h.disjoint, h.angular_nonzero⟩

@[simp] theorem residualBlock_erase (c : Context D) (s : State D) (axis : MeanVector D)
    (b : HarmonicBlock D) (gaussian aliasCoeffs : HarmonicResidual.BlockCoefficients D) :
    HarmonicResidual.residualBlock c (eraseAxisymmetricAlias s axis) b gaussian aliasCoeffs =
      HarmonicResidual.residualBlock c s b gaussian aliasCoeffs := rfl

@[simp] theorem stateMeanCoefficientValue_erase {ι : Type*} (labels : ℕ → Finset ι)
    (blocks : ι → HarmonicBlock D)
    (gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D)
    (c : Context D) (s : State D) (axis : MeanVector D) :
    HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c
      (eraseAxisymmetricAlias s axis) =
      HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c s := rfl

/-- The existing finite harmonic representation implies continuity in the
angular variable even when the independent base error is not regular. -/
theorem represented_goodResidual_angular_continuous {ι : Type*} {U : Set D}
    (hU : IsOpen U) {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    (hrep : HarmonicResidual.BlockRepresentation labels blocks gaussian aliasCoeffs s) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    Continuous (fun θ => HarmonicResidual.stateGoodResidual c s n (x, θ) i) := by
  let data := fun l => HarmonicResidual.ofBlock (blocks l) (gaussian l) (aliasCoeffs l) n
  have he : (fun θ => HarmonicResidual.stateGoodResidual c s n (x, θ) i) =
      fun θ => (HarmonicResidual.meanCoefficients (HarmonicResidual.contextFrame c n)
        (HarmonicResidual.contextBase c n) (HarmonicResidual.stateMean s n)
        (fun y => (s.pressure n y : ℂ)) i 0 x).re +
        HarmonicResidual.contextVirtual c n x i +
        ∑ l ∈ labels n, (HarmonicFields.field
          ((data l).residualCoefficients (HarmonicResidual.contextFrame c n)
            (HarmonicResidual.contextBase c n) (HarmonicResidual.stateMean s n) i)
          (data l).frequency (data l).phase (data l).angularFrequency (x, θ)).re := by
    funext θ
    rw [hrep.goodResidual_eq c n (x, θ) i]
    exact HarmonicResidual.goodResidual_grouped (labels n) data hU h.frame _ _ _ _
      h.base h.mean (Complex.ofRealCLM.contDiff.comp_contDiffOn h.pressure)
      h.blocks h.dataDisjoint ⟨hx, mem_univ θ⟩ i
  rw [he]
  exact continuous_const.add (continuous_finsetSum (labels n) (fun l _ =>
    Complex.continuous_re.comp (HarmonicFields.field_angular_continuous _ _ _ _ _)))

/-- An arbitrary independent alias does not disturb angular continuity. -/
theorem Representation.goodResidual_angular_continuous {ι : Type*} {U : Set D}
    (hU : IsOpen U) {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : Representation labels blocks gaussian aliasCoeffs s axis) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    Continuous (fun θ => HarmonicResidual.stateGoodResidual c s n (x, θ) i) := by
  have hc := represented_goodResidual_angular_continuous hU hrep.erase
    (extractionRegular_erase h axis) hx i
  have he : (fun θ => HarmonicResidual.stateGoodResidual c s n (x, θ) i) =
      fun θ => HarmonicResidual.stateGoodResidual c (eraseAxisymmetricAlias s axis)
        n (x, θ) i - axis n x i := by
    funext θ
    rw [stateGoodResidual_eraseAxisymmetricAlias]
    exact (add_sub_cancel_right _ _).symm
  rw [he]
  exact hc.sub continuous_const

/-- Actual nonconstant residual grouping, with no smoothness or support
assumption on the independent axisymmetric alias. -/
theorem stateGoodWaveResidual_grouped {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : Representation labels blocks gaussian aliasCoeffs s axis) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    HarmonicResidual.stateGoodWaveResidual c s n x i =
      ∑ l ∈ labels n,
        (HarmonicResidual.residualBlock c s (blocks l) (gaussian l) (aliasCoeffs l)).oscillation n
            x i := by
  have hr := extractionRegular_erase h axis
  have hc := represented_goodResidual_angular_continuous hU hrep.erase hr hx.1 i
  have he := stateGoodWaveResidual_addAxisymmetricAlias c (eraseAxisymmetricAlias s axis)
    axis n x i (hc.intervalIntegrable _ _)
  rw [add_eraseAxisymmetricAlias] at he
  rw [he, HarmonicResidual.stateGoodWaveResidual_grouped hU hrep.erase hr hx i]
  rfl

/-- The independent alias changes the actual zero mode by its negative. -/
theorem stateGoodResidual_angularAverage {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : Representation labels blocks gaussian aliasCoeffs s axis) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    angularAverage (fun m y => HarmonicResidual.stateGoodResidual c s m y i) n x =
      HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs
        c s n x i - axis n x i := by
  have hr := extractionRegular_erase h axis
  have hc := represented_goodResidual_angular_continuous hU hrep.erase hr hx i
  have he := angularAverage_sub_axisymmetric
    (fun m y => HarmonicResidual.stateGoodResidual c (eraseAxisymmetricAlias s axis) m y i)
    (fun m y => axis m y i) n x (hc.intervalIntegrable _ _)
  have hb : (fun m y => HarmonicResidual.stateGoodResidual c
      (eraseAxisymmetricAlias s axis) m y i - axis m y.1 i) =
      (fun m y => HarmonicResidual.stateGoodResidual c s m y i) := by
    funext m y
    rw [stateGoodResidual_eraseAxisymmetricAlias]
    exact add_sub_cancel_right _ _
  rw [hb, ← HarmonicResidual.stateMeanCoefficientValue_eq_average hU hrep.erase hr hx i,
    stateMeanCoefficientValue_erase] at he
  exact he

/-- The complete residual retains the actual excluded errors and the corrected
mean mode. In particular the independent alias is never silently discarded. -/
theorem stateFullResidual_reconstructed {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : Representation labels blocks gaussian aliasCoeffs s axis) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    HarmonicResidual.stateFullResidual c s n x i =
      (∑ l ∈ labels n,
        (HarmonicResidual.residualBlock c s (blocks l) (gaussian l) (aliasCoeffs l)).oscillation n
            x i) +
      (HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs
        c s n x.1 i - axis n x.1 i) + s.errors.total n x i := by
  have he := stateGoodWaveResidual_grouped hU hrep h hx i
  simp only [HarmonicResidual.stateGoodWaveResidual] at he
  rw [stateGoodResidual_angularAverage hU hrep h hx.1 i] at he
  simp only [HarmonicResidual.stateGoodResidual, Pi.sub_apply] at he
  linarith

end NavierStokes.AxisymmetricResidualGrouping

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.LocalResidualGrouping

open Set Function Filter MeasureTheory CorrectionState
open HarmonicResidual HarmonicFields HarmonicCalculus
open scoped Topology ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [NormedSpace ℝ D] in
/-- A local separation of closed supports gives an actual zero germ of the
right field whenever the left field is nonzero at the point. -/
theorem zero_germ_of_disjoint_on {U : Set D} {u v : D → ComplexVector}
    (hd : Disjoint (U ∩ tsupport u) (U ∩ tsupport v)) {x : D}
    (hx : x ∈ U) (hu : u x ≠ 0) : v =ᶠ[𝓝 x] fun _ => 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro hv
  have hu' : x ∈ tsupport u := subset_closure hu
  exact Set.disjoint_left.mp hd ⟨hx, hu'⟩ ⟨hx, hv⟩

theorem transport_zero_of_disjoint_on (R : D → ℝ) (Vr Vθ Vz : D → D)
    {U : Set D} {u v : D → ComplexVector}
    (hd : Disjoint (U ∩ tsupport u) (U ∩ tsupport v)) {x : D} (hx : x ∈ U) :
    LinearWaveResidual.transport R Vr Vθ Vz u v x = 0 := by
  by_cases hu : u x = 0
  · ext i
    simp [LinearWaveResidual.transport, hu]
  · have he := zero_germ_of_disjoint_on hd hx hu
    have hv : v x = 0 := he.eq_of_nhds
    have hvd (i : Fin 3) (V : D → D) : along V (fun y => v y i) x = 0 := by
      have hei : (fun y => v y i) =ᶠ[𝓝 x] (fun _ : D => (0 : ℂ)) :=
        he.mono (fun _ hy => congrFun hy i)
      simp only [along, hei.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
        _root_.zero_apply]
    ext i
    fin_cases i <;> simp [LinearWaveResidual.transport, hv, hvd, angularGenerator]

theorem transport_sum_self {ι : Type*} (s : Finset ι) (R : D → ℝ)
    (Vr Vθ Vz : D → D) (u : ι → D → ComplexVector) {U : Set D} {x : D}
    (hu : ∀ l ∈ s, ∀ i, DifferentiableAt ℝ (fun y => u l y i) x)
    (hdisj : ∀ l ∈ s, ∀ j ∈ s, l ≠ j →
      Disjoint (U ∩ tsupport (u l)) (U ∩ tsupport (u j))) (hx : x ∈ U) :
    LinearWaveResidual.transport R Vr Vθ Vz (∑ l ∈ s, u l) (∑ l ∈ s, u l) x =
      ∑ l ∈ s, LinearWaveResidual.transport R Vr Vθ Vz (u l) (u l) x := by
  classical
  rw [Actual.transport_sum_left]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Actual.transport_sum_right s R Vr Vθ Vz (u l) u hu]
  apply Finset.sum_eq_single l
  · intro j hj hjl
    exact transport_zero_of_disjoint_on R Vr Vθ Vz
      (hdisj l hl j hj (Ne.symm hjl)) hx
  · exact fun h => (h hl).elim

/-- Only the nonlinear transport uses separation; all remaining terms use
the already proved linear finite-sum identity on the open chart. -/
theorem nonlinearResidual_sum {ι : Type*} (s : Finset ι) {U : Set D} (hU : IsOpen U)
    (ε : ℝ) (R : D → ℝ) {Vr Vθ Vz : D → D} (Vt : D → D)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (B : D → ComplexVector)
    (u : ι → D → ComplexVector) (p : ι → D → ℂ)
    (hu : ∀ l ∈ s, ∀ i, ContDiffOn ℝ ∞ (fun y => u l y i) U)
    (hp : ∀ l ∈ s, ContDiffOn ℝ ∞ (p l) U)
    (hdisj : ∀ l ∈ s, ∀ j ∈ s, l ≠ j →
      Disjoint (U ∩ tsupport (u l)) (U ∩ tsupport (u j)))
    {x : D} (hx : x ∈ U) :
    Actual.nonlinearResidual ε R Vr Vθ Vz Vt B (∑ l ∈ s, u l) (∑ l ∈ s, p l) x =
      ∑ l ∈ s, Actual.nonlinearResidual ε R Vr Vθ Vz Vt B (u l) (p l) x := by
  unfold Actual.nonlinearResidual
  rw [Actual.linearResidual_sum s hU ε R Vt hr hθ hz B u p hu hp hx,
    transport_sum_self s R Vr Vθ Vz u (fun l hl i =>
      ((hu l hl i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) hdisj hx,
    Finset.sum_add_distrib]

/-- The coefficient formula is unchanged; the actual wave supports are
separated only inside the lifted valid domain. -/
theorem goodResidual_grouped {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U) (hp : ContDiffOn ℝ ∞ p U)
    (hd : ∀ l ∈ labels, (data l).Regular U)
    (hdisj : ∀ l ∈ labels, ∀ j ∈ labels, l ≠ j →
      Disjoint (liftDomain U ∩ tsupport (data l).wave)
        (liftDomain U ∩ tsupport (data j).wave))
    {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    goodResidual labels data g B M p virtual x i =
      (meanCoefficients g B M p i 0 x.1).re + virtual x.1 i +
      ∑ l ∈ labels, (field ((data l).residualCoefficients g B M i)
        (data l).frequency (data l).phase (data l).angularFrequency x).re := by
  have hlu := liftDomain_open hU
  have hf : MapsTo (Prod.fst : D × ℝ → D) (liftDomain U) U := fun _ hy => hy.1
  have hBl i : ContDiffOn ℝ ∞ (fun y : D × ℝ => B y.1 i) (liftDomain U) :=
    (hB i).comp contDiffOn_fst hf
  have hMl i : ContDiffOn ℝ ∞ (fun y : D × ℝ => M y.1 i) (liftDomain U) :=
    (hM i).comp contDiffOn_fst hf
  have hpl : ContDiffOn ℝ ∞ (fun y : D × ℝ => p y.1) (liftDomain U) :=
    hp.comp contDiffOn_fst hf
  have hvel (l) (hl : l ∈ labels) (j : Fin 3) :
      ContDiffOn ℝ ∞ (fun y => (data l).wave y j) (liftDomain U) :=
    field_smoothOn ((hd l hl).velocity j) (hd l hl).phase _ _
  have hpres (l) (hl : l ∈ labels) :
      ContDiffOn ℝ ∞ (data l).pressureField (liftDomain U) :=
    field_smoothOn (hd l hl).pressure (hd l hl).phase _ _
  have hsumv (j : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (∑ l ∈ labels, (data l).wave) y j) (liftDomain U) := by
    simpa only [Finset.sum_apply] using ContDiffOn.sum (fun l hl => hvel l hl j)
  have hsump : ContDiffOn ℝ ∞ (∑ l ∈ labels, (data l).pressureField) (liftDomain U) := by
    convert! ContDiffOn.sum hpres using 1
    ext y
    simp only [Finset.sum_apply]
  have hm := Actual.nonlinearResidual_mean_add (Vθ := angularDirection) hlu g.viscosity
    (fun y => g.radius y.1) (liftDirection g.time) (liftDirection_smooth hg.radial)
    contDiffOn_const (liftDirection_smooth hg.axial) (fun y => B y.1) (fun y => M y.1)
    (∑ l ∈ labels, (data l).wave) (fun y => p y.1) (∑ l ∈ labels, (data l).pressureField)
    hBl hMl hsumv hpl hsump hx
  have hs := nonlinearResidual_sum (Vθ := angularDirection) labels hlu g.viscosity
    (fun y => g.radius y.1) (liftDirection g.time) (liftDirection_smooth hg.radial)
    contDiffOn_const (liftDirection_smooth hg.axial) ((fun y => B y.1) + (fun y => M y.1))
    (fun l => (data l).wave) (fun l => (data l).pressureField) hvel hpres hdisj hx
  have hcoef := meanCoefficients_field hU g hg.radial hg.axial B M p hB hM hp hx
  have hsumcoef := Finset.sum_congr (s₁ := labels) (s₂ := labels) rfl (fun l hl =>
    LabelData.residualCoefficients_field hU g hg.radial hg.axial B M hB hM
      (data l) (hd l hl) hx i)
  unfold goodResidual
  rw [hm, hs, hcoef]
  simp only [Pi.add_apply, Finset.sum_apply, Complex.add_re, Complex.re_sum]
  rw [hsumcoef]
  simp only [Finset.sum_sub_distrib]
  ring

theorem goodResidual_angularMean {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U) (hp : ContDiffOn ℝ ∞ p U)
    (hd : ∀ l ∈ labels, (data l).Regular U)
    (hdisj : ∀ l ∈ labels, ∀ j ∈ labels, l ≠ j →
      Disjoint (liftDomain U ∩ tsupport (data l).wave)
        (liftDomain U ∩ tsupport (data j).wave))
    (hkp : ∀ l ∈ labels, (data l).angularFrequency ≠ 0)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    realAngularMean (fun θ => goodResidual labels data g B M p virtual (x, θ) i) =
      meanResidualValue labels data g B M p virtual x i := by
  have he : (fun θ => goodResidual labels data g B M p virtual (x, θ) i) =
      fun θ => (meanCoefficients g B M p i 0 x).re + virtual x i +
        ∑ l ∈ labels, (field ((data l).residualCoefficients g B M i)
          (data l).frequency (data l).phase (data l).angularFrequency (x, θ)).re := by
    funext θ
    exact goodResidual_grouped labels data hU hg B M p virtual hB hM hp hd hdisj
      ⟨hx, mem_univ θ⟩ i
  let F : ι → ℝ → ℝ := fun l θ => (field ((data l).residualCoefficients g B M i)
    (data l).frequency (data l).phase (data l).angularFrequency (x, θ)).re
  have hF (l : ι) : Continuous (F l) :=
    Complex.continuous_re.comp (field_angular_continuous _ _ _ _ _)
  rw [he]
  change realAngularMean (fun θ => (meanCoefficients g B M p i 0 x).re + virtual x i +
    ∑ l ∈ labels, F l θ) = _
  rw [realAngularMean_add (f := fun _ => (meanCoefficients g B M p i 0 x).re + virtual x i)
    (g := fun θ => ∑ l ∈ labels, F l θ) continuous_const
    (continuous_finsetSum labels (fun l _ => hF l)),
    realAngularMean_const, realAngularMean_sum labels F (fun l _ => hF l)]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  exact realAngularMean_field _ _ _ (hkp l hl) x

theorem goodWaveResidual_grouped {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U) (hp : ContDiffOn ℝ ∞ p U)
    (hd : ∀ l ∈ labels, (data l).Regular U)
    (hdisj : ∀ l ∈ labels, ∀ j ∈ labels, l ≠ j →
      Disjoint (liftDomain U ∩ tsupport (data l).wave)
        (liftDomain U ∩ tsupport (data j).wave))
    (hkp : ∀ l ∈ labels, (data l).angularFrequency ≠ 0)
    {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    goodWaveResidual labels data g B M p virtual x i =
      ∑ l ∈ labels, (field ((data l).waveResidualCoefficients g B M i)
        (data l).frequency (data l).phase (data l).angularFrequency x).re := by
  rw [goodWaveResidual, goodResidual_grouped labels data hU hg B M p virtual
    hB hM hp hd hdisj hx i, goodResidual_angularMean labels data hU hg B M p virtual
    hB hM hp hd hdisj hkp hx.1 i]
  simp only [meanResidualValue, LabelData.waveResidualCoefficients, field_nonconstant,
    Complex.sub_re, Finset.sum_sub_distrib]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem liftDomain_eq_preimage (U : Set D) :
    liftDomain U = (Prod.fst : D × ℝ → D) ⁻¹' U := by
  ext x
  simp [liftDomain]

/-- The regularity needed for actual extraction, with separation only inside
the valid lifted open domain. -/
structure ExtractionRegular {ι : Type*} (U : Set D) (c : Context D) (s : State D)
    (labels : ℕ → Finset ι) (blockFamily : ι → HarmonicBlock D)
    (gaussianCoeffs aliasCoeffs : ι → BlockCoefficients D) (n : ℕ) : Prop where
  frame : (contextFrame c n).Regular U
  base : ∀ i, ContDiffOn ℝ ∞ (fun x => contextBase c n x i) U
  mean : ∀ i, ContDiffOn ℝ ∞ (fun x => stateMean s n x i) U
  pressure : ContDiffOn ℝ ∞ (s.pressure n) U
  blocks : ∀ l ∈ labels n, (ofBlock (blockFamily l) (gaussianCoeffs l) (aliasCoeffs l) n).Regular U
  gaussian : ∀ l ∈ labels n, ∀ i, SmoothCoefficients U (gaussianCoeffs l n i)
  aliasError : ∀ l ∈ labels n, ∀ i, SmoothCoefficients U (aliasCoeffs l n i)
  disjoint : ∀ l ∈ labels n, ∀ j ∈ labels n, l ≠ j →
    Disjoint (liftDomain U ∩ tsupport ((blockFamily l).oscillation n))
      (liftDomain U ∩ tsupport ((blockFamily j).oscillation n))
  angular_nonzero : ∀ l ∈ labels n, (blockFamily l).angularFrequency n ≠ 0

theorem ExtractionRegular.dataDisjoint {ι : Type*} {U : Set D} {c : Context D}
    {s : State D} {labels : ℕ → Finset ι} {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → BlockCoefficients D} {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasCoeffs n) :
    ∀ l ∈ labels n, ∀ j ∈ labels n, l ≠ j →
      Disjoint (liftDomain U ∩ tsupport (ofBlock (blocks l) (gaussian l) (aliasCoeffs l) n).wave)
        (liftDomain U ∩ tsupport (ofBlock (blocks j) (gaussian j) (aliasCoeffs j) n).wave) := by
  intro l hl j hj hlj
  simpa only [ofBlock_tsupport_wave] using h.disjoint l hl j hj hlj

theorem ExtractionRegular.erase {ι : Type*} {U : Set D} {c : Context D} {s : State D}
    {labels : ℕ → Finset ι} {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → BlockCoefficients D} {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasCoeffs n) (axis : MeanVector D) :
    ExtractionRegular U c (AxisymmetricResidualGrouping.eraseAxisymmetricAlias s axis)
      labels blocks gaussian aliasCoeffs n :=
  ⟨h.frame, h.base, h.mean, h.pressure, h.blocks, h.gaussian, h.aliasError,
    h.disjoint, h.angular_nonzero⟩

theorem represented_goodResidual_angular_continuous {ι : Type*} {U : Set D}
    (hU : IsOpen U) {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D} {gaussian aliasCoeffs : ι → BlockCoefficients D}
    (hrep : BlockRepresentation labels blocks gaussian aliasCoeffs s) {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    Continuous (fun θ => stateGoodResidual c s n (x, θ) i) := by
  let data := fun l => ofBlock (blocks l) (gaussian l) (aliasCoeffs l) n
  have he : (fun θ => stateGoodResidual c s n (x, θ) i) =
      fun θ => (meanCoefficients (contextFrame c n) (contextBase c n) (stateMean s n)
        (fun y => (s.pressure n y : ℂ)) i 0 x).re + contextVirtual c n x i +
        ∑ l ∈ labels n, (field ((data l).residualCoefficients (contextFrame c n)
          (contextBase c n) (stateMean s n) i)
          (data l).frequency (data l).phase (data l).angularFrequency (x, θ)).re := by
    funext θ
    rw [hrep.goodResidual_eq c n (x, θ) i]
    exact goodResidual_grouped (labels n) data hU h.frame _ _ _ _ h.base h.mean
      (Complex.ofRealCLM.contDiff.comp_contDiffOn h.pressure)
      h.blocks h.dataDisjoint ⟨hx, mem_univ θ⟩ i
  rw [he]
  exact continuous_const.add (continuous_finsetSum (labels n) (fun l _ =>
    Complex.continuous_re.comp (field_angular_continuous _ _ _ _ _)))

theorem stateGoodWaveResidual_grouped_of_blockRepresentation {ι : Type*} {U : Set D}
    (hU : IsOpen U) {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D} {gaussian aliasCoeffs : ι → BlockCoefficients D}
    (hrep : BlockRepresentation labels blocks gaussian aliasCoeffs s) {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    stateGoodWaveResidual c s n x i = ∑ l ∈ labels n,
      (residualBlock c s (blocks l) (gaussian l) (aliasCoeffs l)).oscillation n x i := by
  rw [hrep.goodWaveResidual_eq c n x i]
  exact goodWaveResidual_grouped (labels n) _ hU h.frame _ _ _ _ h.base h.mean
    (Complex.ofRealCLM.contDiff.comp_contDiffOn h.pressure)
    h.blocks h.dataDisjoint h.angular_nonzero hx i

theorem stateMeanCoefficientValue_eq_average {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D} {gaussian aliasCoeffs : ι → BlockCoefficients D}
    (hrep : BlockRepresentation labels blocks gaussian aliasCoeffs s) {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c s n x i =
      angularAverage (fun m y => stateGoodResidual c s m y i) n x := by
  simp only [angularAverage]
  simp_rw [hrep.goodResidual_eq c n]
  exact (goodResidual_angularMean (labels n) _ hU h.frame _ _ _ _ h.base h.mean
    (Complex.ofRealCLM.contDiff.comp_contDiffOn h.pressure)
    h.blocks h.dataDisjoint h.angular_nonzero hx i).symm

/-- Actual nonconstant grouping with local support separation and an
arbitrary independent axisymmetric alias. -/
theorem stateGoodWaveResidual_grouped {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D} {gaussian aliasCoeffs : ι → BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : AxisymmetricResidualGrouping.Representation labels blocks gaussian aliasCoeffs s axis)
    {n : ℕ} (h : ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    stateGoodWaveResidual c s n x i = ∑ l ∈ labels n,
      (residualBlock c s (blocks l) (gaussian l) (aliasCoeffs l)).oscillation n x i := by
  have hr := h.erase axis
  have hc := represented_goodResidual_angular_continuous hU hrep.erase hr hx.1 i
  have he := AxisymmetricResidualGrouping.stateGoodWaveResidual_addAxisymmetricAlias c
    (AxisymmetricResidualGrouping.eraseAxisymmetricAlias s axis) axis n x i
    (hc.intervalIntegrable _ _)
  rw [AxisymmetricResidualGrouping.add_eraseAxisymmetricAlias] at he
  rw [he, stateGoodWaveResidual_grouped_of_blockRepresentation hU hrep.erase hr hx i]
  rfl

theorem stateGoodResidual_angularAverage {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D} {gaussian aliasCoeffs : ι → BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : AxisymmetricResidualGrouping.Representation labels blocks gaussian aliasCoeffs s axis)
    {n : ℕ} (h : ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    angularAverage (fun m y => stateGoodResidual c s m y i) n x =
      stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c s n x i - axis n x i := by
  have hr := h.erase axis
  have hc := represented_goodResidual_angular_continuous hU hrep.erase hr hx i
  have he := AxisymmetricResidualGrouping.angularAverage_sub_axisymmetric
    (fun m y => stateGoodResidual c (AxisymmetricResidualGrouping.eraseAxisymmetricAlias s axis)
      m y i) (fun m y => axis m y i) n x (hc.intervalIntegrable _ _)
  have hb : (fun m y => stateGoodResidual c
      (AxisymmetricResidualGrouping.eraseAxisymmetricAlias s axis) m y i - axis m y.1 i) =
      (fun m y => stateGoodResidual c s m y i) := by
    funext m y
    rw [AxisymmetricResidualGrouping.stateGoodResidual_eraseAxisymmetricAlias]
    exact add_sub_cancel_right _ _
  rw [hb, ← stateMeanCoefficientValue_eq_average hU hrep.erase hr hx i,
    AxisymmetricResidualGrouping.stateMeanCoefficientValue_erase] at he
  exact he

theorem stateFullResidual_reconstructed {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D} {gaussian aliasCoeffs : ι → BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : AxisymmetricResidualGrouping.Representation labels blocks gaussian aliasCoeffs s axis)
    {n : ℕ} (h : ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    stateFullResidual c s n x i =
      (∑ l ∈ labels n,
        (residualBlock c s (blocks l) (gaussian l) (aliasCoeffs l)).oscillation n x i) +
      (stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c s n x.1 i - axis n x.1 i) +
      s.errors.total n x i := by
  have he := stateGoodWaveResidual_grouped hU hrep h hx i
  simp only [stateGoodWaveResidual] at he
  rw [stateGoodResidual_angularAverage hU hrep h hx.1 i] at he
  simp only [stateGoodResidual, Pi.sub_apply] at he
  linarith

end NavierStokes.LocalResidualGrouping
