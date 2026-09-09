/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricTorusInverse
import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Actual torus inversion for smooth finite-dimensional parameter families

The source is an actual jointly smooth function. Fourier coefficients are
the unit-square integrals of that source. No output regularity or decay
assumptions are part of the construction.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SmoothFamilyTorusInverse

open Set Filter MeasureTheory TorusInverse
open scoped Topology ContDiff BigOperators

/-- Point: an abbreviation for `P × Plane`. -/
abbrev Point (P : Type) := P × Plane
/-- Source: an abbreviation for `Point P → ℂ`. -/
abbrev Source (P : Type) := Point P → ℂ

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Slice, defined pointwise by `f (p, Y)`. -/
noncomputable def slice (f : Source P) (p : P) : Plane → ℂ := fun Y => f (p, Y)

/-- Periodic, given by `∀ p, SmoothFourierData.UnitPeriodic (slice f p)`. -/
def Periodic (f : Source P) : Prop :=
  ∀ p, SmoothFourierData.UnitPeriodic (slice f p)

/-- Coefficient, given by `SmoothFourierData.coefficient (slice f p) k`. -/
noncomputable def coefficient (f : Source P) (p : P) (k : Frequency) : ℂ :=
  SmoothFourierData.coefficient (slice f p) k

/-- Mean, given by `coefficient f p 0`. -/
noncomputable def mean (f : Source P) (p : P) : ℂ := coefficient f p 0
/-- Zero mean, given by `∀ p, mean f p = 0`. -/
def ZeroMean (f : Source P) : Prop := ∀ p, mean f p = 0

/-- Inverse, given by `directionalInverse d (coefficient f z.1) z.2`. -/
noncomputable def inverse (d : Direction) (f : Source P) (z : Point P) : ℂ :=
  directionalInverse d (coefficient f z.1) z.2

/-- Fixed partial, given by `fderiv ℝ f z v`. -/
noncomputable def fixedPartial (v : Point P) (f : Source P) (z : Point P) : ℂ :=
  fderiv ℝ f z v

/-- Parameter partial, given by `fixedPartial (v, 0) f`. -/
noncomputable def parameterPartial (v : P) (f : Source P) : Source P :=
  fixedPartial (v, 0) f

/-- Parameter derivative, given by `(fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ P Plane)`. -/
noncomputable def parameterDerivative (f : Source P) (z : Point P) : P →L[ℝ] ℂ :=
  (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ P Plane)

/-- Torus X jet, given by `(fixedPartial (0, (1, 0)))^[n] f`. -/
noncomputable def torusXJet (n : ℕ) (f : Source P) : Source P :=
  (fixedPartial (0, (1, 0)))^[n] f

/-- Swap torus, defined pointwise by `f (z.1, (z.2.2, z.2.1))`. -/
noncomputable def swapTorus (f : Source P) : Source P :=
  fun z => f (z.1, (z.2.2, z.2.1))

theorem slice_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) (p : P) :
    ContDiff ℝ ∞ (slice f p) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

theorem fixedPartial_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) (v : Point P) :
    ContDiff ℝ ∞ (fixedPartial v f) :=
  (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp (hf.fderiv_right (by simp))

theorem parameterPartial_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) (v : P) :
    ContDiff ℝ ∞ (parameterPartial v f) := fixedPartial_smooth hf (v, 0)

theorem parameterDerivative_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterDerivative f) :=
  (hf.fderiv_right (by simp)).clm_comp contDiff_const

theorem fixedPartial_periodic {f : Source P} (hp : Periodic f) (v : Point P) :
    Periodic (fixedPartial v f) := by
  intro p Y k
  have he : (fun z : Point P => f (z + (0, ((k.1 : ℝ), (k.2 : ℝ))))) = f := by
    funext z
    change f (z.1 + 0, z.2 + ((k.1 : ℝ), (k.2 : ℝ))) = f (z.1, z.2)
    simpa [slice] using hp z.1 z.2 k
  have hd := congrArg (fun g : Source P => fderiv ℝ g (p, Y)) he
  rw [fderiv_comp_add_right] at hd
  simpa only [slice, fixedPartial, Prod.mk_add_mk, add_zero] using
    congrArg (fun L : Point P →L[ℝ] ℂ => L v) hd

theorem parameterPartial_periodic {f : Source P} (hp : Periodic f) (v : P) :
    Periodic (parameterPartial v f) := fixedPartial_periodic hp (v, 0)

theorem torusXJet_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (torusXJet n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      rw [torusXJet, Function.iterate_succ_apply']
      exact fixedPartial_smooth ih _

theorem swapTorus_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (swapTorus f) :=
  hf.comp (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst))

theorem slice_hasFDerivAt {f : Source P} (hf : ContDiff ℝ ∞ f) (p : P) (Y : Plane) :
    HasFDerivAt (slice f p)
      ((fderiv ℝ f (p, Y)).comp (ContinuousLinearMap.inr ℝ P Plane)) Y :=
  ((hf.differentiable (by simp)) (p, Y)).hasFDerivAt.comp Y
    ((hasFDerivAt_const p Y).prodMk (hasFDerivAt_id Y))

theorem parameter_hasFDerivAt {f : Source P} (hf : ContDiff ℝ ∞ f) (p : P) (Y : Plane) :
    HasFDerivAt (fun q => f (q, Y)) (parameterDerivative f (p, Y)) p :=
  ((hf.differentiable (by simp)) (p, Y)).hasFDerivAt.comp p
    ((hasFDerivAt_id p).prodMk (hasFDerivAt_const Y p))

theorem slice_torusXJet {f : Source P} (hf : ContDiff ℝ ∞ f) (n : ℕ) (p : P) :
    slice (torusXJet n f) p = SmoothFourierData.xJet n (slice f p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [torusXJet, Function.iterate_succ_apply', SmoothFourierData.xJet_succ, ← ih]
      funext Y
      exact (congrArg (fun L : Plane →L[ℝ] ℂ => L (1, 0))
        (slice_hasFDerivAt (torusXJet_smooth hf n) p Y).fderiv).symm

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem mean_eq_integral (f : Source P) (p : P) :
    mean f p = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (p, (x, y)) :=
  SmoothFourierData.coefficient_zero_eq_integral _

/-- Weighted source, given by `SmoothFourierData.kernel k (q.2, q.1.2) * f (q.1.1, (q.2,
q.1.2))`. -/
noncomputable def weightedSource (k : Frequency) (f : Source P) (q : (P × ℝ) × ℝ) : ℂ :=
  SmoothFourierData.kernel k (q.2, q.1.2) * f (q.1.1, (q.2, q.1.2))

theorem weightedSource_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) (k : Frequency) :
    ContDiff ℝ ∞ (weightedSource k f) :=
  ((ParametricTorusInverse.kernel_smooth k).comp
    (contDiff_snd.prodMk contDiff_fst.snd)).mul
    (hf.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)))

theorem coefficient_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) (k : Frequency) :
    ContDiff ℝ ∞ (fun p => coefficient f p k) := by
  have hi := TransportPrimitive.parameterIntegral_contDiff (weightedSource_smooth hf k) 0 1
  have ho := TransportPrimitive.parameterIntegral_contDiff hi 0 1
  simpa only [coefficient, SmoothFourierData.coefficient_eq_doubleIntegral,
    weightedSource, slice] using ho

/-- Restricting the actual family to a line only changes its external
parameter. It leaves every torus Fourier integral unchanged. -/
noncomputable def lineSource (f : Source P) (p v : P) : ParametricTorusInverse.Source :=
  fun z => f (p + z.1 • v, z.2)

theorem lineSource_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) (p v : P) :
    ContDiff ℝ ∞ (lineSource f p v) :=
  hf.comp ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd)

theorem parameterPartial_lineSource {f : Source P} (hf : ContDiff ℝ ∞ f) (p v : P) :
    ParametricTorusInverse.parameterPartial (lineSource f p v) =
      lineSource (parameterPartial v f) p v := by
  funext z
  have hd : HasDerivAt (fun t : ℝ => f (p + t • v, z.2))
      (parameterPartial v f (p + z.1 • v, z.2)) z.1 := by
    apply ((hf.differentiable (by simp)) (p + z.1 • v, z.2)).hasFDerivAt.comp_hasDerivAt z.1
    simpa only [one_smul, id_eq] using
      (((hasDerivAt_id z.1).smul_const v |>.const_add p).prodMk
        (hasDerivAt_const z.1 z.2))
  exact (ParametricTorusInverse.parameter_slice_hasDerivAt
    (lineSource_smooth hf p v) z.1 z.2).unique hd

theorem coefficient_fderiv_apply {f : Source P} (hf : ContDiff ℝ ∞ f)
    (k : Frequency) (p v : P) :
    fderiv ℝ (fun q => coefficient f q k) p v =
      coefficient (parameterPartial v f) p k := by
  have hline : HasFDerivAt (fun q => coefficient f q k)
      (fderiv ℝ (fun q => coefficient f q k) p) p :=
    ((coefficient_smooth hf k).differentiable (by simp) p).hasFDerivAt
  have hd : HasDerivAt (fun t : ℝ => coefficient f (p + t • v) k)
      (fderiv ℝ (fun q => coefficient f q k) p v) 0 := by
    apply hline.comp_hasDerivAt_of_eq (0 : ℝ)
    · simpa only [one_smul, id_eq] using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p)
    · simp
  have hs := ParametricTorusInverse.coefficient_hasDerivAt (lineSource_smooth hf p v) k 0
  rw [parameterPartial_lineSource hf p v] at hs
  change HasDerivAt (fun t : ℝ => coefficient f (p + t • v) k)
    (coefficient (parameterPartial v f) (p + (0 : ℝ) • v) k) 0 at hs
  simpa only [zero_smul, add_zero] using hd.unique hs

theorem parameterPartial_zeroMean {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hm : ZeroMean f) (v : P) : ZeroMean (parameterPartial v f) := by
  intro p
  have he : (fun q => coefficient f q 0) = fun _ => (0 : ℂ) := funext hm
  have hd := coefficient_fderiv_apply hf 0 p v
  rw [he] at hd
  simp only [fderiv_fun_const] at hd
  exact hd.symm

theorem exists_uniform_coefficient_bound {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (n : ℕ) {K : Set P} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ k,
      weight k ^ n * ‖coefficient f p k‖ ≤ C := by
  let T : Set (Point P) := K ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hT : IsCompact T := hK.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C₀, h₀⟩ := hT.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨C₁, h₁⟩ := hT.exists_bound_of_continuousOn
    (torusXJet_smooth hf n).continuous.continuousOn
  obtain ⟨C₂, h₂⟩ := hT.exists_bound_of_continuousOn
    (torusXJet_smooth (swapTorus_smooth hf) n).continuous.continuousOn
  let C := max 0 (max C₀ (max C₁ C₂))
  have hC : 0 ≤ C := le_max_left _ _
  have hC₀ : C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₁ : C₁ ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hC₂ : C₂ ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨3 ^ n * C, mul_nonneg (by positivity) hC, ?_⟩
  intro p hparam k
  apply SmoothFourierData.coefficient_polynomial_bound (slice_smooth hf p) (hp p) n
  · intro x hx y hy
    exact (h₀ (p, (x, y)) ⟨hparam, hx, hy⟩).trans hC₀
  · intro x hx y hy
    rw [← slice_torusXJet hf n p]
    exact (h₁ (p, (x, y)) ⟨hparam, hx, hy⟩).trans hC₁
  · intro x hx y hy
    change ‖SmoothFourierData.xJet n (slice (swapTorus f) p) (x, y)‖ ≤ C
    rw [← slice_torusXJet (swapTorus_smooth hf) n p]
    exact (h₂ (p, (x, y)) ⟨hparam, hx, hy⟩).trans hC₂

open ParametricTorusInverse (PolynomialGrowth multiplierX multiplierY)

/-- Apply multiplier, given by `series (fun k => m k * coefficient f z.1 k) z.2`. -/
noncomputable def applyMultiplier (m : Frequency → ℂ) (f : Source P) (z : Point P) : ℂ :=
  series (fun k => m k * coefficient f z.1 k) z.2

theorem multiplied_coeff_rapid {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (p : P) :
    Rapid (fun k => m k * coefficient f p k) :=
  hm.rapid_mul (SmoothFourierData.rapid_coefficient (slice_smooth hf p) (hp p))

theorem uniform_multiplied_coeff_bound {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f)
    {K : Set P} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ k,
      ‖m k * coefficient f p k‖ ≤ C * (weight k ^ 4)⁻¹ := by
  obtain ⟨s, M, hM, hm⟩ := hm
  obtain ⟨B, hB, hb⟩ := exists_uniform_coefficient_bound hf hp (s + 4) hK
  exact ⟨M * B, mul_nonneg hM hB,
    fun p hp k => ParametricTorusInverse.multiplied_coeff_bound hM hm (hb p hp) k⟩

section JetNorms

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_jet_partial {f : E → F} (hf : ContDiff ℝ ∞ f) (v : E) (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun x => fderiv ℝ f x v) z‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f z‖ := by
  simpa only [norm_iteratedFDeriv_fderiv] using
    (norm_iteratedFDeriv_clm_apply_const
      (hf.fderiv_right (by simp)).contDiffAt (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)
      (c := v) (x := z))

theorem norm_jet_linear (L : F →L[ℝ] G) {f : E → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun x => L (f x)) z‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ n f z‖ := by
  rw [show (fun x => L (f x)) = L ∘ f from rfl,
    L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)]
  exact L.norm_compContinuousMultilinearMap_le _

theorem norm_jet_add {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun x => f x + g x) z‖ ≤
      ‖iteratedFDeriv ℝ n f z‖ + ‖iteratedFDeriv ℝ n g z‖ := by
  change ‖iteratedFDeriv ℝ n (f + g) z‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast le_top)).contDiffAt
    (hg.of_le (by exact_mod_cast le_top)).contDiffAt]
  exact norm_add_le _ _

theorem norm_jet_sum {ι : Type} [Fintype ι] {f : ι → E → F}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun x => ∑ i, f i x) z‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ n (f i) z‖ := by
  have he := iteratedFDeriv_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    (hf i).of_le (show (n : WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top))
  rw [he]
  simpa only [Finset.sum_apply] using norm_sum_le Finset.univ (fun i => iteratedFDeriv ℝ n (f i) z)

/-- Repeat partial, given by `(fun g x => fderiv ℝ g x v)^[n] f`. -/
noncomputable def repeatPartial (v : E) (n : ℕ) (f : E → F) : E → F :=
  (fun g x => fderiv ℝ g x v)^[n] f

theorem norm_repeatPartial {f : E → F} (hf : ContDiff ℝ ∞ f)
    (v : E) (n : ℕ) (z : E) :
    ‖repeatPartial v n f z‖ ≤ ‖v‖ ^ n * ‖iteratedFDeriv ℝ n f z‖ := by
  induction n generalizing f with
  | zero => simp [repeatPartial]
  | succ n ih =>
      rw [repeatPartial, Function.iterate_succ_apply]
      have hp : ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
        (ContinuousLinearMap.apply ℝ F v).contDiff.comp (hf.fderiv_right (by simp))
      calc
        _ ≤ ‖v‖ ^ n * ‖iteratedFDeriv ℝ n (fun x => fderiv ℝ f x v) z‖ := ih hp
        _ ≤ ‖v‖ ^ n * (‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f z‖) :=
          mul_le_mul_of_nonneg_left (norm_jet_partial hf v n z) (by positivity)
        _ = _ := by rw [pow_succ]; ring


end JetNorms

section TorusWords
variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Tensor torus word as an element of `w, g => fun Y => fderiv ℝ (tensorTorusWord w g) Y (if b
then (0, 1) else (1, 0))`. -/
noncomputable def tensorTorusWord : List Bool → (Plane → G) → Plane → G
  | [], g => g
  | b :: w, g => fun Y => fderiv ℝ (tensorTorusWord w g) Y
      (if b then (0, 1) else (1, 0))

theorem tensorTorusWord_smooth {g : Plane → G} (hg : ContDiff ℝ ∞ g) (w : List Bool) :
    ContDiff ℝ ∞ (tensorTorusWord w g) := by
  induction w with
  | nil => exact hg
  | cons b w ih =>
      have hd : ContDiff ℝ ∞ (fderiv ℝ (tensorTorusWord w g)) :=
        ih.fderiv_right (by simp)
      exact (ContinuousLinearMap.apply ℝ G (if b then (0, 1) else (1, 0))).contDiff.comp
        hd

theorem tensorTorusWord_map (L : G →L[ℝ] H) {g : Plane → G}
    (hg : ContDiff ℝ ∞ g) (w : List Bool) :
    tensorTorusWord w (fun Y => L (g Y)) = fun Y => L (tensorTorusWord w g Y) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      funext Y
      simp only [tensorTorusWord, ih]
      have hd := L.hasFDerivAt.comp Y
        (((tensorTorusWord_smooth hg w).differentiable (by simp)) Y).hasFDerivAt
      exact congrArg (fun M : Plane →L[ℝ] H => M (if b then (0, 1) else (1, 0))) hd.fderiv

end TorusWords

theorem tensorTorusWord_scalar (g : Plane → ℂ) (w : List Bool) :
    tensorTorusWord w g = derivativeWord w g := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      simp only [tensorTorusWord, derivativeWord, ih]
      rfl

theorem tensorTorusWord_replicate (g : Plane → ℂ) (n : ℕ) :
    tensorTorusWord (List.replicate n false) g = SmoothFourierData.xJet n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, tensorTorusWord, SmoothFourierData.xJet_succ, ih]
      rfl


section FiniteDimensional

variable [FiniteDimensional ℝ P]

/-- Basis index: an abbreviation for `Fin (Module.finrank ℝ P)`. -/
abbrev BasisIndex (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :=
  Fin (Module.finrank ℝ P)

/-- Parameter basis, given by `Module.finBasis ℝ P`. -/
noncomputable def parameterBasis : Module.Basis (BasisIndex P) ℝ P := Module.finBasis ℝ P
/-- Parameter coord, given by `((parameterBasis (P := P)).coord i).toContinuousLinearMap`. -/
noncomputable def parameterCoord (i : BasisIndex P) : P →L[ℝ] ℝ :=
  ((parameterBasis (P := P)).coord i).toContinuousLinearMap

/-- Parameter lift, given by `ContinuousLinearMap.smulRightL ℝ (Point P) ℂ ((parameterCoord
i).comp (ContinuousLinearMap.fst ℝ P Plane))`. -/
noncomputable def parameterLift (i : BasisIndex P) : ℂ →L[ℝ] (Point P →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (Point P) ℂ
    ((parameterCoord i).comp (ContinuousLinearMap.fst ℝ P Plane))

/-- Torus lift X, given by `ContinuousLinearMap.smulRightL ℝ (Point P) ℂ (dx.comp
(ContinuousLinearMap.snd ℝ P Plane))`. -/
noncomputable def torusLiftX : ℂ →L[ℝ] (Point P →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (Point P) ℂ
    (dx.comp (ContinuousLinearMap.snd ℝ P Plane))

/-- Torus lift Y, given by `ContinuousLinearMap.smulRightL ℝ (Point P) ℂ (dy.comp
(ContinuousLinearMap.snd ℝ P Plane))`. -/
noncomputable def torusLiftY : ℂ →L[ℝ] (Point P →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (Point P) ℂ
    (dy.comp (ContinuousLinearMap.snd ℝ P Plane))

@[simp] theorem parameterLift_apply (i : BasisIndex P) (c : ℂ) (v : Point P) :
    parameterLift i c v = parameterCoord i v.1 • c := rfl

omit [FiniteDimensional ℝ P] in
@[simp] theorem torusLiftX_apply (c : ℂ) (v : Point P) :
    torusLiftX c v = v.2.1 • c := rfl

omit [FiniteDimensional ℝ P] in
@[simp] theorem torusLiftY_apply (c : ℂ) (v : Point P) :
    torusLiftY c v = v.2.2 • c := rfl

theorem clm_parameter_expansion (L : P →L[ℝ] ℂ) (v : P) :
    L v = ∑ i : BasisIndex P, parameterCoord i v • L (parameterBasis i) := by
  conv_lhs => rw [← (parameterBasis (P := P)).sum_repr v]
  simp only [map_sum, map_smul, parameterCoord, Module.Basis.coord_apply,
    LinearMap.coe_toContinuousLinearMap']

/-- Multiplier term derivative as an element of `Point P →L[ℝ] ℂ`. -/
noncomputable def multiplierTermDerivative (m : Frequency → ℂ) (f : Source P)
    (k : Frequency) (z : Point P) : Point P →L[ℝ] ℂ :=
  (∑ i : BasisIndex P, parameterLift i
    (m k * coefficient (parameterPartial (parameterBasis i) f) z.1 k * mode k z.2)) +
  torusLiftX (multiplierX m k * coefficient f z.1 k * mode k z.2) +
  torusLiftY (multiplierY m k * coefficient f z.1 k * mode k z.2)

theorem hasFDerivAt_multiplierTerm {f : Source P} (hf : ContDiff ℝ ∞ f)
    (m : Frequency → ℂ) (k : Frequency) (z : Point P) :
    HasFDerivAt (fun w : Point P => m k * coefficient f w.1 k * mode k w.2)
      (multiplierTermDerivative m f k z) z := by
  let L := fderiv ℝ (fun q => coefficient f q k) z.1
  have hc : HasFDerivAt (fun w : Point P => coefficient f w.1 k)
      (L.comp (ContinuousLinearMap.fst ℝ P Plane)) z :=
    (((coefficient_smooth hf k).differentiable (by simp) z.1).hasFDerivAt.comp z
      (hasFDerivAt_fst))
  have he : HasFDerivAt (fun w : Point P => mode k w.2)
      (mode k z.2 • ((phase k).comp (ContinuousLinearMap.snd ℝ P Plane))) z :=
    ((phase k).hasFDerivAt.comp z (hasFDerivAt_snd)).cexp
  have hd : multiplierTermDerivative m f k z =
      (m k * coefficient f z.1 k) •
        (mode k z.2 • ((phase k).comp (ContinuousLinearMap.snd ℝ P Plane))) +
      mode k z.2 • (m k • (L.comp (ContinuousLinearMap.fst ℝ P Plane))) := by
    apply ContinuousLinearMap.ext
    intro v
    have hs : (∑ i : BasisIndex P, parameterCoord i v.1 •
        (m k * coefficient (parameterPartial (parameterBasis i) f) z.1 k * mode k z.2)) =
        mode k z.2 * (m k * L v.1) := by
      rw [clm_parameter_expansion L v.1]
      simp_rw [show ∀ i : BasisIndex P, L (parameterBasis i) =
        coefficient (parameterPartial (parameterBasis i) f) z.1 k from
          fun i => coefficient_fderiv_apply hf k z.1 _, Complex.real_smul]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simp only [multiplierTermDerivative, _root_.add_apply,
      _root_.sum_apply, parameterLift_apply, torusLiftX_apply, torusLiftY_apply]
    rw [hs]
    change mode k z.2 * (m k * L v.1) +
        v.2.1 • (freqX k * m k * coefficient f z.1 k * mode k z.2) +
        v.2.2 • (freqY k * m k * coefficient f z.1 k * mode k z.2) =
      (m k * coefficient f z.1 k) •
        (mode k z.2 • (v.2.1 • freqX k + v.2.2 • freqY k)) +
      mode k z.2 • (m k • L v.1)
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  rw [hd]
  exact (hc.const_mul (m k)).mul he

theorem norm_multiplierTermDerivative_le (m : Frequency → ℂ) (f : Source P)
    (k : Frequency) (z : Point P) :
    ‖multiplierTermDerivative m f k z‖ ≤
      (∑ i : BasisIndex P, ‖parameterLift i‖ *
        ‖m k * coefficient (parameterPartial (parameterBasis i) f) z.1 k‖) +
      ‖torusLiftX (P := P)‖ * ‖multiplierX m k * coefficient f z.1 k‖ +
      ‖torusLiftY (P := P)‖ * ‖multiplierY m k * coefficient f z.1 k‖ := by
  unfold multiplierTermDerivative
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      simpa only [norm_mul, norm_mode, mul_one] using
        (parameterLift i).le_opNorm
          (m k * coefficient (parameterPartial (parameterBasis i) f) z.1 k * mode k z.2)
    · simpa only [norm_mul, norm_mode, mul_one] using
        (torusLiftX (P := P)).le_opNorm (multiplierX m k * coefficient f z.1 k * mode k z.2)
  · simpa only [norm_mul, norm_mode, mul_one] using
      (torusLiftY (P := P)).le_opNorm (multiplierY m k * coefficient f z.1 k * mode k z.2)

theorem uniform_multiplierDerivative_bound {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f)
    {K : Set P} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Point P, z.1 ∈ K → ∀ k,
      ‖multiplierTermDerivative m f k z‖ ≤ C * (weight k ^ 4)⁻¹ := by
  have hparam := fun i : BasisIndex P => uniform_multiplied_coeff_bound hm
    (parameterPartial_smooth hf (parameterBasis i))
    (parameterPartial_periodic hp (parameterBasis i)) hK
  choose CP hCP hP using hparam
  obtain ⟨CX, hCX, hX⟩ := uniform_multiplied_coeff_bound hm.mulX hf hp hK
  obtain ⟨CY, hCY, hY⟩ := uniform_multiplied_coeff_bound hm.mulY hf hp hK
  have hsum : 0 ≤ ∑ i : BasisIndex P, ‖parameterLift i‖ * CP i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg (parameterLift i)) (hCP i))
  refine ⟨(∑ i : BasisIndex P, ‖parameterLift i‖ * CP i) +
    ‖torusLiftX (P := P)‖ * CX + ‖torusLiftY (P := P)‖ * CY, by positivity, ?_⟩
  intro z hz k
  apply (norm_multiplierTermDerivative_le m f k z).trans
  calc
    _ ≤ (∑ i : BasisIndex P, ‖parameterLift i‖ * (CP i * (weight k ^ 4)⁻¹)) +
        ‖torusLiftX (P := P)‖ * (CX * (weight k ^ 4)⁻¹) +
        ‖torusLiftY (P := P)‖ * (CY * (weight k ^ 4)⁻¹) := by
      gcongr with i
      · exact hP i z.1 hz k
      · exact hX z.1 hz k
      · exact hY z.1 hz k
    _ = _ := by simp only [← mul_assoc, ← Finset.sum_mul]; ring

theorem hasFDerivAt_applyMultiplier {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (z : Point P) :
    HasFDerivAt (applyMultiplier m f) (∑' k, multiplierTermDerivative m f k z) z := by
  obtain ⟨C, hC, hb⟩ := uniform_multiplierDerivative_bound hm hf hp
    (isCompact_closedBall z.1 (1 : ℝ))
  have hs := SmoothFourierData.summable_weight_inv_four.mul_left C
  have hbox : ∀ w ∈ Metric.ball z 1, w.1 ∈ Metric.closedBall z.1 1 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_fst_le (w - z)).trans (le_of_lt (by
      simpa only [dist_eq_norm] using Metric.mem_ball.mp hw))
  exact hasFDerivAt_tsum_of_isPreconnected hs Metric.isOpen_ball
    (convex_ball z (1 : ℝ)).isPreconnected
    (fun k w _ => hasFDerivAt_multiplierTerm hf m k w)
    (fun k w hw => hb w (hbox w hw) k)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
    (summable_terms (multiplied_coeff_rapid hm hf hp z.1) z.2)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))

theorem fderiv_applyMultiplier {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (z : Point P) :
    fderiv ℝ (applyMultiplier m f) z =
      (∑ i : BasisIndex P, parameterLift i
        (applyMultiplier m (parameterPartial (parameterBasis i) f) z)) +
      torusLiftX (applyMultiplier (multiplierX m) f z) +
      torusLiftY (applyMultiplier (multiplierY m) f z) := by
  have hP := fun i : BasisIndex P => summable_terms (multiplied_coeff_rapid hm
    (parameterPartial_smooth hf (parameterBasis i))
    (parameterPartial_periodic hp (parameterBasis i)) z.1) z.2
  have hLP := fun i : BasisIndex P => (parameterLift i).summable (hP i)
  have hX := summable_terms (multiplied_coeff_rapid hm.mulX hf hp z.1) z.2
  have hY := summable_terms (multiplied_coeff_rapid hm.mulY hf hp z.1) z.2
  rw [(hasFDerivAt_applyMultiplier hm hf hp z).fderiv]
  simp only [multiplierTermDerivative]
  rw [Summable.tsum_add ((summable_sum fun i hi => hLP i).add
      ((torusLiftX (P := P)).summable hX)) ((torusLiftY (P := P)).summable hY),
    Summable.tsum_add (summable_sum fun i hi => hLP i) ((torusLiftX (P := P)).summable hX),
    Summable.tsum_finsetSum (fun i hi => hLP i)]
  congr 2
  · apply Finset.sum_congr rfl
    intro i hi
    exact ((parameterLift i).map_tsum (hP i)).symm
  · exact ((torusLiftX (P := P)).map_tsum hX).symm
  · exact ((torusLiftY (P := P)).map_tsum hY).symm

theorem applyMultiplier_smooth_nat (n : ℕ) {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    ContDiff ℝ n (applyMultiplier m f) := by
  induction n generalizing m f with
  | zero =>
      exact contDiff_zero.mpr (show Differentiable ℝ (applyMultiplier m f) from
        fun z => (hasFDerivAt_applyMultiplier hm hf hp z).differentiableAt).continuous
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
        contDiff_succ_iff_fderiv]
      refine ⟨fun z => (hasFDerivAt_applyMultiplier hm hf hp z).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (applyMultiplier m f) = fun z =>
          (∑ i : BasisIndex P, parameterLift i
            (applyMultiplier m (parameterPartial (parameterBasis i) f) z)) +
          torusLiftX (applyMultiplier (multiplierX m) f z) +
          torusLiftY (applyMultiplier (multiplierY m) f z) :=
        funext (fderiv_applyMultiplier hm hf hp)
      rw [he]
      have hP : ∀ i : BasisIndex P, ContDiff ℝ n (fun z : Point P =>
          parameterLift i (applyMultiplier m (parameterPartial (parameterBasis i) f) z)) := by
        intro i
        exact (parameterLift i).contDiff.comp
          (ih hm (parameterPartial_smooth hf (parameterBasis i))
            (parameterPartial_periodic hp (parameterBasis i)))
      have hPS : ContDiff ℝ n (fun z : Point P =>
          ∑ i : BasisIndex P, parameterLift i
            (applyMultiplier m (parameterPartial (parameterBasis i) f) z)) :=
        ContDiff.sum (fun i (_ : i ∈ (Finset.univ : Finset (BasisIndex P))) => hP i)
      have hX : ContDiff ℝ n (fun z : Point P =>
          torusLiftX (P := P) (applyMultiplier (multiplierX m) f z)) :=
        (torusLiftX (P := P)).contDiff.comp (ih hm.mulX hf hp)
      have hY : ContDiff ℝ n (fun z : Point P =>
          torusLiftY (P := P) (applyMultiplier (multiplierY m) f z)) :=
        (torusLiftY (P := P)).contDiff.comp (ih hm.mulY hf hp)
      exact (hPS.add hX).add hY

theorem applyMultiplier_smooth {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    ContDiff ℝ ∞ (applyMultiplier m f) :=
  contDiff_infty.mpr (fun n => applyMultiplier_smooth_nat n hm hf hp)

theorem inverse_smooth (d : Direction) {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) : ContDiff ℝ ∞ (inverse d f) :=
  applyMultiplier_smooth (ParametricTorusInverse.inverseMultiplier_growth d) hf hp

omit [FiniteDimensional ℝ P] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem inverse_periodic (d : Direction) (f : Source P) : Periodic (inverse d f) := by
  intro p Y k
  exact directionalInverse_periodic d (coefficient f p) Y k.1 k.2

omit [FiniteDimensional ℝ P] in
theorem mean_applyMultiplier {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (p : P) :
    mean (applyMultiplier m f) p = m 0 * mean f p := by
  have ha := multiplied_coeff_rapid hm hf hp p
  let g : C(Torus, ℂ) :=
    ⟨torusSeries (fun k => m k * coefficient f p k), continuous_torusSeries ha⟩
  have hg : SmoothFourierData.torusLift g = slice (applyMultiplier m f) p := by
    funext Y
    exact (series_eq_torusSeries (fun k => m k * coefficient f p k) Y).symm
  change SmoothFourierData.coefficient (slice (applyMultiplier m f) p) 0 = _
  rw [← hg, SmoothFourierData.coefficient_zero_eq_mean]
  exact integral_torusSeries ha

omit [FiniteDimensional ℝ P] in
theorem inverse_zeroMean (d : Direction) {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) : ZeroMean (inverse d f) := by
  intro p
  change mean (applyMultiplier (multiplier d) f) p = 0
  rw [mean_applyMultiplier (ParametricTorusInverse.inverseMultiplier_growth d) hf hp p]
  simp only [multiplier, symbol_zero, Complex.ofReal_zero, mul_zero, inv_zero, zero_mul]

/-- Directional partial, given by `fderiv ℝ f z (0, vector d)`. -/
noncomputable def directionalPartial (d : Direction) (f : Source P) (z : Point P) : ℂ :=
  fderiv ℝ f z (0, vector d)

theorem inverse_solves (d : Direction) {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (hm : ZeroMean f) : directionalPartial d (inverse d f) = f := by
  funext z
  have hz := SmoothFourierData.inverse_solves_smooth_periodic d
    (slice_smooth hf z.1) (hp z.1) (by
      change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (z.1, (x, y))) = 0
      rw [← mean_eq_integral]
      exact hm z.1) z.2
  have hd := congrArg (fun L : Plane →L[ℝ] ℂ => L (vector d))
    (slice_hasFDerivAt (inverse_smooth d hf hp) z.1 z.2).fderiv
  exact hd.symm.trans hz

omit [FiniteDimensional ℝ P] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem inverse_preserves_parameter_support (d : Direction) (f : Source P) (S : Set P)
    (hs : ∀ p, p ∉ S → ∀ Y, f (p, Y) = 0) :
    ∀ p, p ∉ S → ∀ Y, inverse d f (p, Y) = 0 := by
  apply TorusInverse.inverse_preserves_parameter_support d (coefficient f) S
  intro p hp k
  simp only [coefficient, SmoothFourierData.coefficient_eq_doubleIntegral, slice,
    hs p hp, mul_zero, intervalIntegral.integral_zero]

theorem parameterPartial_applyMultiplier {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (v : P) :
    parameterPartial v (applyMultiplier m f) = applyMultiplier m (parameterPartial v f) := by
  funext z
  have hlp : ParametricTorusInverse.Periodic (lineSource f z.1 v) :=
    fun t => hp (z.1 + t • v)
  have hh := congrFun (ParametricTorusInverse.parameterPartial_applyMultiplier hm
    (lineSource_smooth hf z.1 v) hlp) (0, z.2)
  change ParametricTorusInverse.parameterPartial
    (lineSource (applyMultiplier m f) z.1 v) (0, z.2) =
      ParametricTorusInverse.applyMultiplier m
        (ParametricTorusInverse.parameterPartial (lineSource f z.1 v)) (0, z.2) at hh
  rw [parameterPartial_lineSource (applyMultiplier_smooth hm hf hp) z.1 v,
    parameterPartial_lineSource hf z.1 v] at hh
  change parameterPartial v (applyMultiplier m f) (z.1 + (0 : ℝ) • v, z.2) =
    applyMultiplier m (parameterPartial v f) (z.1 + (0 : ℝ) • v, z.2) at hh
  simpa only [zero_smul, add_zero] using hh

theorem parameterPartial_inverse (d : Direction) {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (v : P) :
    parameterPartial v (inverse d f) = inverse d (parameterPartial v f) :=
  parameterPartial_applyMultiplier (ParametricTorusInverse.inverseMultiplier_growth d) hf hp v

/-- A prefix of actual full joint Fréchet-jet bounds on a parameter set.
The torus argument ranges over the whole universal cover. -/
def JetBound (f : Source P) (S : Set P) (n : ℕ) (C : ℝ) : Prop :=
  ∀ j ≤ n, ∀ p ∈ S, ∀ Y, ‖iteratedFDeriv ℝ j f (p, Y)‖ ≤ C

omit [FiniteDimensional ℝ P] in
theorem JetBound.mono_order {f : Source P} {S : Set P} {n m : ℕ} {C : ℝ}
    (h : JetBound f S n C) (hm : m ≤ n) : JetBound f S m C :=
  fun j hj => h j (hj.trans hm)

omit [FiniteDimensional ℝ P] in
theorem JetBound.fixedPartial {f : Source P} (hf : ContDiff ℝ ∞ f)
    {S : Set P} {n : ℕ} {C : ℝ} (h : JetBound f S (n + 1) C) (v : Point P) :
    JetBound (fixedPartial v f) S n (‖v‖ * C) := by
  intro j hj p hp Y
  exact (norm_jet_partial hf v j (p, Y)).trans
    (mul_le_mul_of_nonneg_left (h (j + 1) (Nat.add_le_add_right hj 1) p hp Y)
      (norm_nonneg _))

omit [FiniteDimensional ℝ P] in
theorem norm_torusXJet_le {f : Source P} (hf : ContDiff ℝ ∞ f) (n : ℕ) (z : Point P) :
    ‖torusXJet n f z‖ ≤ ‖iteratedFDeriv ℝ n f z‖ := by
  have hn : ‖((0 : P), ((1 : ℝ), (0 : ℝ)))‖ = 1 := by simp [Prod.norm_def]
  have h := norm_repeatPartial hf (0, (1, 0)) n z
  simp only [hn, one_pow, one_mul] at h
  exact h

omit [FiniteDimensional ℝ P] in
theorem norm_jet_swapTorus (f : Source P) (n : ℕ) (z : Point P) :
    ‖iteratedFDeriv ℝ n (swapTorus f) z‖ =
      ‖iteratedFDeriv ℝ n f (z.1, (z.2.2, z.2.1))‖ := by
  let e : Point P ≃ₗᵢ[ℝ] Point P :=
    { toLinearEquiv := (LinearEquiv.refl ℝ P).prodCongr (LinearEquiv.prodComm ℝ ℝ ℝ)
      norm_map' := fun z => by
        change max ‖z.1‖ (max ‖z.2.2‖ ‖z.2.1‖) = max ‖z.1‖ (max ‖z.2.1‖ ‖z.2.2‖)
        rw [max_comm ‖z.2.2‖ ‖z.2.1‖] }
  exact e.norm_iteratedFDeriv_comp_right f z n

omit [FiniteDimensional ℝ P] in
theorem coefficient_moment_bound {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f)
    {S : Set P} (l : ℕ) {C : ℝ} (h : JetBound f S (l + 4) C)
    (p : P) (hps : p ∈ S) :
    coeffSeminorm l (coefficient f p) ≤
      (3 ^ (l + 4) * C) * ∑' k : Frequency, (weight k ^ 4)⁻¹ := by
  apply SmoothFourierData.coefficient_seminorm_bound (slice_smooth hf p) (hp p) l
  · intro x hx y hy
    simpa only [slice, norm_iteratedFDeriv_zero] using h 0 (by omega) p hps (x, y)
  · intro x hx y hy
    rw [← slice_torusXJet hf (l + 4) p]
    exact (norm_torusXJet_le hf (l + 4) (p, (x, y))).trans
      (h (l + 4) le_rfl p hps (x, y))
  · intro x hx y hy
    change ‖SmoothFourierData.xJet (l + 4) (slice (swapTorus f) p) (x, y)‖ ≤ C
    rw [← slice_torusXJet (swapTorus_smooth hf) (l + 4) p]
    apply (norm_torusXJet_le (swapTorus_smooth hf) (l + 4) (p, (x, y))).trans
    rw [norm_jet_swapTorus]
    exact h (l + 4) le_rfl p hps (y, x)

/-- Multiplier jet constant used in smooth family torus inverse. -/
noncomputable def multiplierJetConstant : ℕ → ℕ → ℝ
  | 0, l => 3 ^ (l + 4) * ∑' k : Frequency, (weight k ^ 4)⁻¹
  | n + 1, l =>
      (∑ i : BasisIndex P, ‖parameterLift i‖ * ‖(parameterBasis i, (0 : Plane))‖) *
        multiplierJetConstant n l +
      (‖torusLiftX (P := P)‖ + ‖torusLiftY (P := P)‖) * ‖omega‖ *
        multiplierJetConstant n (l + 1)

theorem multiplierJetConstant_nonneg (n l : ℕ) : 0 ≤ multiplierJetConstant (P := P) n l := by
  induction n generalizing l with
  | zero => unfold multiplierJetConstant; positivity
  | succ n ih =>
      rw [multiplierJetConstant]
      exact add_nonneg (mul_nonneg (Finset.sum_nonneg fun i hi => by positivity) (ih l))
        (mul_nonneg (by positivity) (ih (l + 1)))

/-- The loss l+4 comes only from the order-l multiplier and the summable
two-dimensional lattice majorant; it does not grow with jet order. -/
theorem norm_jet_applyMultiplier_le (n l : ℕ) {m : Frequency → ℂ}
    {B : ℝ} (hB : 0 ≤ B) (hm : ∀ k, ‖m k‖ ≤ B * weight k ^ l)
    {f : Source P} (hf : ContDiff ℝ ∞ f) (hp : Periodic f)
    {S : Set P} {C : ℝ} (hC : 0 ≤ C) (h : JetBound f S (n + l + 4) C)
    (p : P) (hps : p ∈ S) (Y : Plane) :
    ‖iteratedFDeriv ℝ n (applyMultiplier m f) (p, Y)‖ ≤
      multiplierJetConstant (P := P) n l * B * C := by
  have hmg : PolynomialGrowth m := ⟨l, B, hB, hm⟩
  induction n generalizing l m B f C with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      have ha := SmoothFourierData.rapid_coefficient (slice_smooth hf p) (hp p)
      have hb : coeffSeminorm 0 (fun k => m k * coefficient f p k) ≤
          B * coeffSeminorm l (coefficient f p) := by
        have hb' : ∀ k, ‖m k * coefficient f p k‖ ≤
            B * (weight k ^ l * ‖coefficient f p k‖) := by
          intro k
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _)).trans_eq (by ring)
        have hh := (multiplied_coeff_rapid hmg hf hp p).summable_norm.tsum_le_tsum hb'
          ((ha l).mul_left B)
        simpa only [coeffSeminorm, pow_zero, one_mul, tsum_mul_left] using hh
      calc
        _ ≤ coeffSeminorm 0 (fun k => m k * coefficient f p k) :=
          norm_series_le (multiplied_coeff_rapid hmg hf hp p) Y
        _ ≤ B * coeffSeminorm l (coefficient f p) := hb
        _ ≤ B * ((3 ^ (l + 4) * C) * ∑' k : Frequency, (weight k ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (coefficient_moment_bound hf hp l (by simpa only [zero_add] using h) p hps) hB
        _ = _ := by simp only [multiplierJetConstant]; ring
  | succ n ih =>
      let G (i : BasisIndex P) : Source P := parameterPartial (parameterBasis i) f
      have hG : ∀ i : BasisIndex P, ContDiff ℝ ∞ (G i) :=
        fun i => parameterPartial_smooth hf _
      have hPG : ∀ i : BasisIndex P, Periodic (G i) :=
        fun i => parameterPartial_periodic hp _
      have hGb : ∀ i : BasisIndex P,
          ‖iteratedFDeriv ℝ n (applyMultiplier m (G i)) (p, Y)‖ ≤
            multiplierJetConstant (P := P) n l * B *
              (‖(parameterBasis i, (0 : Plane))‖ * C) := by
        intro i
        apply ih l hB hm (hG i) (hPG i) (mul_nonneg (norm_nonneg _) hC)
        · have hi := h.fixedPartial hf (parameterBasis i, (0 : Plane))
          convert! hi using 1
          omega
        · exact hmg
      have hmx : ∀ k, ‖multiplierX m k‖ ≤ (‖omega‖ * B) * weight k ^ (l + 1) := by
        intro k
        rw [multiplierX, norm_mul]
        calc
          _ ≤ (‖omega‖ * weight k) * (B * weight k ^ l) :=
            mul_le_mul (norm_freqX_le k) (hm k) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (weight_pos k).le)
          _ = _ := by rw [pow_succ]; ring
      have hmy : ∀ k, ‖multiplierY m k‖ ≤ (‖omega‖ * B) * weight k ^ (l + 1) := by
        intro k
        rw [multiplierY, norm_mul]
        calc
          _ ≤ (‖omega‖ * weight k) * (B * weight k ^ l) :=
            mul_le_mul (norm_freqY_le k) (hm k) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (weight_pos k).le)
          _ = _ := by rw [pow_succ]; ring
      have hbshift : JetBound f S (n + (l + 1) + 4) C := by
        convert! h using 1
        omega
      have hx := ih (l + 1) (mul_nonneg (norm_nonneg _) hB) hmx hf hp hC hbshift hmg.mulX
      have hy := ih (l + 1) (mul_nonneg (norm_nonneg _) hB) hmy hf hp hC hbshift hmg.mulY
      have hLS (i : BasisIndex P) : ContDiff ℝ ∞
          (fun z : Point P => parameterLift i (applyMultiplier m (G i) z)) :=
        (parameterLift i).contDiff.comp (applyMultiplier_smooth hmg (hG i) (hPG i))
      have hLSum := ContDiff.sum (fun i (_ : i ∈ (Finset.univ : Finset (BasisIndex P))) => hLS i)
      have hLX : ContDiff ℝ ∞
          (fun z : Point P => torusLiftX (P := P) (applyMultiplier (multiplierX m) f z)) :=
        (torusLiftX (P := P)).contDiff.comp (applyMultiplier_smooth hmg.mulX hf hp)
      have hLY : ContDiff ℝ ∞
          (fun z : Point P => torusLiftY (P := P) (applyMultiplier (multiplierY m) f z)) :=
        (torusLiftY (P := P)).contDiff.comp (applyMultiplier_smooth hmg.mulY hf hp)
      have he : fderiv ℝ (applyMultiplier m f) = fun z : Point P =>
          (∑ i : BasisIndex P, parameterLift i (applyMultiplier m (G i) z)) +
          torusLiftX (P := P) (applyMultiplier (multiplierX m) f z) +
          torusLiftY (P := P) (applyMultiplier (multiplierY m) f z) :=
        funext (fderiv_applyMultiplier hmg hf hp)
      rw [← norm_iteratedFDeriv_fderiv, he]
      apply (norm_jet_add (hLSum.add hLX) hLY n (p, Y)).trans
      apply (add_le_add_left (norm_jet_add hLSum hLX n (p, Y)) _).trans
      apply (add_le_add_left (add_le_add_left (norm_jet_sum hLS n (p, Y)) _) _).trans
      calc
        _ ≤ (∑ i : BasisIndex P, ‖parameterLift i‖ *
              (multiplierJetConstant (P := P) n l * B *
                (‖(parameterBasis i, (0 : Plane))‖ * C))) +
            ‖torusLiftX (P := P)‖ *
              (multiplierJetConstant (P := P) n (l + 1) * (‖omega‖ * B) * C) +
            ‖torusLiftY (P := P)‖ *
              (multiplierJetConstant (P := P) n (l + 1) * (‖omega‖ * B) * C) := by
          apply add_le_add
          · apply add_le_add
            · apply Finset.sum_le_sum
              intro i hi
              exact (norm_jet_linear (parameterLift i)
                (applyMultiplier_smooth hmg (hG i) (hPG i)) n (p, Y)).trans
                (mul_le_mul_of_nonneg_left (hGb i) (norm_nonneg _))
            · exact (norm_jet_linear (torusLiftX (P := P))
                (applyMultiplier_smooth hmg.mulX hf hp) n (p, Y)).trans
                (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
          · exact (norm_jet_linear (torusLiftY (P := P))
              (applyMultiplier_smooth hmg.mulY hf hp) n (p, Y)).trans
              (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
        _ = _ := by
          rw [multiplierJetConstant]
          have hs : (∑ i : BasisIndex P, ‖parameterLift i‖ *
              (multiplierJetConstant (P := P) n l * B *
                (‖(parameterBasis i, (0 : Plane))‖ * C))) =
              (∑ i : BasisIndex P, ‖parameterLift i‖ * ‖(parameterBasis i, (0 : Plane))‖) *
                multiplierJetConstant (P := P) n l * B * C := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          rw [hs]
          ring

theorem applyMultiplier_finiteJets (n l : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : Frequency → ℂ) (B : ℝ), 0 ≤ B →
      (∀ k, ‖m k‖ ≤ B * weight k ^ l) →
      ∀ (f : Source P) (S : Set P) (C : ℝ), ContDiff ℝ ∞ f → Periodic f → 0 ≤ C →
        JetBound f S (n + l + 4) C → JetBound (applyMultiplier m f) S n (K * B * C) := by
  let K := ∑ j ∈ Finset.range (n + 1), multiplierJetConstant (P := P) j l
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j hj => multiplierJetConstant_nonneg j l)
  refine ⟨K, hK, ?_⟩
  intro m B hB hm f S C hf hp hC h j hj p hps Y
  apply (norm_jet_applyMultiplier_le j l hB hm hf hp hC
    (h.mono_order (by omega)) p hps Y).trans
  have hjK : multiplierJetConstant (P := P) j l ≤ K :=
    Finset.single_le_sum (fun k hk => multiplierJetConstant_nonneg k l)
      (Finset.mem_range.mpr (by omega))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjK hB) hC

/-- Uniform full-tensor bound with five torus derivatives lost. The
constant is chosen before the source, parameter set, or input bound. -/
theorem inverse_finiteJets (d : Direction) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Source P) (S : Set P) (C : ℝ),
      ContDiff ℝ ∞ f → Periodic f → 0 ≤ C →
      JetBound f S (n + 5) C → JetBound (inverse d f) S n (K * C) := by
  obtain ⟨K, hK, hb⟩ := applyMultiplier_finiteJets (P := P) n 1
  refine ⟨K * (6 * ‖omega⁻¹‖), by positivity, ?_⟩
  intro f S C hf hp hC h
  have hh := hb (multiplier d) (6 * ‖omega⁻¹‖) (by positivity)
    (fun k => by simpa only [pow_one] using norm_multiplier_le d k)
    f S C hf hp hC (by simpa only [Nat.add_assoc] using h)
  exact hh

/-- Parameter jet, given by `(iteratedFDeriv ℝ q f z).compContinuousLinearMap (fun _ =>
ContinuousLinearMap.inl ℝ P Plane)`. -/
noncomputable def parameterJet (q : ℕ) (f : Source P) (z : Point P) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => P) ℂ :=
  (iteratedFDeriv ℝ q f z).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inl ℝ P Plane)

/-- Parameter jet apply, defined pointwise by `parameterJet q f z v`. -/
noncomputable def parameterJetApply (q : ℕ) (v : Fin q → P) (f : Source P) : Source P :=
  fun z => parameterJet q f z v

omit [FiniteDimensional ℝ P] in
theorem parameterJet_smooth {f : Source P} (hf : ContDiff ℝ ∞ f) (q : ℕ) :
    ContDiff ℝ ∞ (parameterJet q f) := by
  have hq : ContDiff ℝ ∞ (iteratedFDeriv ℝ q f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (le_top : (⊤ : ℕ∞) + (q : ℕ∞) ≤ ⊤))
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin q => ContinuousLinearMap.inl ℝ P Plane)).contDiff.comp
    hq

omit [FiniteDimensional ℝ P] in
theorem parameterJetApply_smooth {f : Source P} (hf : ContDiff ℝ ∞ f)
    (q : ℕ) (v : Fin q → P) : ContDiff ℝ ∞ (parameterJetApply q v f) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => P) ℂ v).contDiff.comp
    (parameterJet_smooth hf q)

omit [FiniteDimensional ℝ P] in
theorem parameterJet_eq_slice {f : Source P} (hf : ContDiff ℝ ∞ f)
    (q : ℕ) (p : P) (Y : Plane) :
    parameterJet q f (p, Y) = iteratedFDeriv ℝ q (fun t => f (t, Y)) p := by
  let L : P →L[ℝ] Point P := ContinuousLinearMap.inl ℝ P Plane
  let g : Point P → ℂ := fun z => f (z + (0, Y))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun t => f (t, Y)) = g ∘ L := by ext t; simp [g, L]
  rw [he, L.iteratedFDeriv_comp_right hg p (by exact_mod_cast le_top : (q : WithTop ℕ∞) ≤ ∞)]
  change (iteratedFDeriv ℝ q f (p, Y)).compContinuousLinearMap _ =
    (iteratedFDeriv ℝ q (fun z => f (z + (0, Y))) (p, 0)).compContinuousLinearMap _
  rw [iteratedFDeriv_comp_add_right]
  simp only [Prod.mk_add_mk, add_zero, zero_add]
  rfl

omit [FiniteDimensional ℝ P] in
theorem parameterJetApply_succ {f : Source P} (hf : ContDiff ℝ ∞ f)
    (q : ℕ) (v : Fin (q + 1) → P) :
    parameterJetApply (q + 1) v f =
      parameterPartial (v 0) (parameterJetApply q (Fin.tail v) f) := by
  funext z
  change iteratedFDeriv ℝ (q + 1) f z (fun i => (v i, 0)) =
    fderiv ℝ (fun x => iteratedFDeriv ℝ q f x (fun i => (Fin.tail v i, 0))) z (v 0, 0)
  have hq : ContDiff ℝ ∞ (iteratedFDeriv ℝ q f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (le_top : (⊤ : ℕ∞) + (q : ℕ∞) ≤ ⊤))
  rw [iteratedFDeriv_succ_apply_left,
    fderiv_continuousMultilinear_apply_const_apply
      (hq.differentiable (by simp) z)]
  rfl

omit [FiniteDimensional ℝ P] in
theorem parameterJetApply_periodic {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (q : ℕ) (v : Fin q → P) : Periodic (parameterJetApply q v f) := by
  induction q with
  | zero => exact hp
  | succ q ih =>
      rw [parameterJetApply_succ hf]
      exact parameterPartial_periodic (ih (Fin.tail v)) (v 0)

theorem parameterJetApply_inverse (d : Direction) {f : Source P}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (q : ℕ) (v : Fin q → P) :
    parameterJetApply q v (inverse d f) = inverse d (parameterJetApply q v f) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [parameterJetApply_succ (inverse_smooth d hf hp), ih,
        parameterPartial_inverse d (parameterJetApply_smooth hf q (Fin.tail v))
          (parameterJetApply_periodic hf hp q (Fin.tail v)),
        parameterJetApply_succ hf]

theorem parameterJet_inverse (d : Direction) {f : Source P}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (q : ℕ) (z : Point P) (v : Fin q → P) :
    parameterJet q (inverse d f) z v =
      inverse d (fun w => parameterJet q f w v) z :=
  congrFun (parameterJetApply_inverse d hf hp q v) z

/-- Nonzero multiplier, with branches according to `k = 0`. -/
noncomputable def nonzeroMultiplier (k : Frequency) : ℂ := if k = 0 then 0 else 1

theorem nonzeroMultiplier_growth : ParametricTorusInverse.PolynomialGrowth nonzeroMultiplier := by
  refine ⟨0, 1, zero_le_one, ?_⟩
  intro k
  by_cases hk : k = 0 <;> simp [nonzeroMultiplier, hk]

/-- Nonbar part, given by `f z - mean f z.1`. -/
noncomputable def nonbarPart (f : Source P) (z : Point P) : ℂ := f z - mean f z.1

omit [FiniteDimensional ℝ P] in
theorem nonbarPart_eq_applyMultiplier {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) : nonbarPart f = applyMultiplier nonzeroMultiplier f := by
  funext z
  have ha := SmoothFourierData.rapid_coefficient (slice_smooth hf z.1) (hp z.1)
  have he : (fun k => nonzeroMultiplier k * coefficient f z.1 k * mode k z.2) =
      (fun k => coefficient f z.1 k * mode k z.2) -
        (fun k => if k = 0 then coefficient f z.1 0 else 0) := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [nonzeroMultiplier, mode, phase, freqX, freqY, liftX, liftY]
    · simp [nonzeroMultiplier, hk]
  have hs : Summable (fun k : Frequency => if k = 0 then coefficient f z.1 0 else 0) :=
    (hasSum_ite_eq 0 _).summable
  change f z - mean f z.1 = ∑' k, nonzeroMultiplier k * coefficient f z.1 k * mode k z.2
  rw [he]
  change f z - mean f z.1 = ∑' k,
    (coefficient f z.1 k * mode k z.2 - if k = 0 then coefficient f z.1 0 else 0)
  have ht := Summable.tsum_sub (summable_terms ha z.2) hs
  change (∑' k, (coefficient f z.1 k * mode k z.2 -
      if k = 0 then coefficient f z.1 0 else 0)) =
    (∑' k, coefficient f z.1 k * mode k z.2) -
      (∑' k, if k = 0 then coefficient f z.1 0 else 0) at ht
  rw [ht]
  rw [(hasSum_ite_eq (0 : Frequency) (coefficient f z.1 0)).tsum_eq]
  rw [show (∑' k, coefficient f z.1 k * mode k z.2) = f z from
    SmoothFourierData.series_coefficient (slice_smooth hf z.1) (hp z.1) z.2]
  rfl

theorem nonbarPart_smooth {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) : ContDiff ℝ ∞ (nonbarPart f) := by
  rw [nonbarPart_eq_applyMultiplier hf hp]
  exact applyMultiplier_smooth nonzeroMultiplier_growth hf hp

omit [FiniteDimensional ℝ P] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem nonbarPart_periodic {f : Source P} (hp : Periodic f) : Periodic (nonbarPart f) := by
  intro p Y k
  change f (p, Y + ((k.1 : ℝ), (k.2 : ℝ))) - mean f p = f (p, Y) - mean f p
  rw [show f (p, Y + ((k.1 : ℝ), (k.2 : ℝ))) = f (p, Y) from hp p Y k]

omit [FiniteDimensional ℝ P] in
theorem nonbarPart_zeroMean {f : Source P} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) : ZeroMean (nonbarPart f) := by
  rw [nonbarPart_eq_applyMultiplier hf hp]
  intro p
  rw [mean_applyMultiplier nonzeroMultiplier_growth hf hp p]
  simp [nonzeroMultiplier]

theorem centered_inverse_solves (d : Direction) {f : Source P}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    directionalPartial d (inverse d (nonbarPart f)) = nonbarPart f :=
  inverse_solves d (nonbarPart_smooth hf hp) (nonbarPart_periodic hp)
    (nonbarPart_zeroMean hf hp)

theorem nonbarPart_finiteJets (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Source P) (S : Set P) (C : ℝ),
      ContDiff ℝ ∞ f → Periodic f → 0 ≤ C →
      JetBound f S (n + 4) C → JetBound (nonbarPart f) S n (K * C) := by
  obtain ⟨K, hK, hb⟩ := applyMultiplier_finiteJets (P := P) n 0
  refine ⟨K, hK, ?_⟩
  intro f S C hf hp hC h
  rw [nonbarPart_eq_applyMultiplier hf hp]
  have hm : ∀ k, ‖nonzeroMultiplier k‖ ≤ (1 : ℝ) * weight k ^ 0 := by
    intro k
    by_cases hk : k = 0 <;> simp [nonzeroMultiplier, hk]
  simpa only [mul_one, add_zero] using
    hb nonzeroMultiplier 1 zero_le_one hm f S C hf hp hC (by simpa only [add_zero] using h)

omit [FiniteDimensional ℝ P] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem nonbarPart_preserves_parameter_support (f : Source P) (S : Set P)
    (hs : ∀ p, p ∉ S → ∀ Y, f (p, Y) = 0) :
    ∀ p, p ∉ S → ∀ Y, nonbarPart f (p, Y) = 0 := by
  intro p hp Y
  rw [nonbarPart, hs p hp Y, mean_eq_integral]
  simp only [hs p hp, intervalIntegral.integral_zero, sub_zero]

/-- Mixed jet, given by `tensorTorusWord w (fun Y => parameterJet q f (z.1, Y)) z.2`. -/
noncomputable def mixedJet (q : ℕ) (w : List Bool) (f : Source P) (z : Point P) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => P) ℂ :=
  tensorTorusWord w (fun Y => parameterJet q f (z.1, Y)) z.2

omit [FiniteDimensional ℝ P] in
theorem mixedJet_apply {f : Source P} (hf : ContDiff ℝ ∞ f)
    (q : ℕ) (w : List Bool) (z : Point P) (v : Fin q → P) :
    mixedJet q w f z v =
      derivativeWord w (slice (parameterJetApply q v f) z.1) z.2 := by
  have hg : ContDiff ℝ ∞ (fun Y => parameterJet q f (z.1, Y)) :=
    (parameterJet_smooth hf q).comp (contDiff_const.prodMk contDiff_id)
  have h := congrFun (tensorTorusWord_map
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => P) ℂ v) hg w) z.2
  rw [tensorTorusWord_scalar] at h
  exact h.symm

omit [FiniteDimensional ℝ P] in
theorem norm_derivativeWord_inverse_le (d : Direction) {f : Source P}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (w : List Bool) (p : P) (Y : Plane) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (p, (x, y))‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖SmoothFourierData.xJet (w.length + 5) (slice f p) (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖SmoothFourierData.xJet (w.length + 5)
        (SmoothFourierData.swapFunction (slice f p)) (x, y)‖ ≤ C) :
    ‖derivativeWord w (slice (inverse d f) p) Y‖ ≤
      ParametricTorusInverse.mixedLossConstant w.length * C := by
  have hbound := SmoothFourierData.coefficient_seminorm_bound (slice_smooth hf p) (hp p)
    (w.length + 1) hzero (by simpa only [Nat.add_assoc] using hfirst)
    (by simpa only [Nat.add_assoc] using hsecond)
  calc
    _ ≤ ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) *
        coeffSeminorm (w.length + 1) (coefficient f p) :=
      inverse_derivativeWord_bound d
        (SmoothFourierData.rapid_coefficient (slice_smooth hf p) (hp p)) w Y
    _ ≤ ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) *
        ((3 ^ ((w.length + 1) + 4) * C) * ∑' k : Frequency, (weight k ^ 4)⁻¹) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by simp only [ParametricTorusInverse.mixedLossConstant, Nat.add_assoc]; ring

theorem mixedJet_inverse_bound (d : Direction) {f : Source P}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (q : ℕ) (w : List Bool)
    (S : Set P) {C : ℝ} (hC : 0 ≤ C)
    (hzero : ∀ p ∈ S, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖parameterJet q f (p, (x, y))‖ ≤ C)
    (hfirst : ∀ p ∈ S, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖tensorTorusWord (List.replicate (w.length + 5) false)
        (fun Y => parameterJet q f (p, Y)) (x, y)‖ ≤ C)
    (hsecond : ∀ p ∈ S, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖tensorTorusWord (List.replicate (w.length + 5) false)
        (fun Y => parameterJet q f (p, (Y.2, Y.1))) (x, y)‖ ≤ C)
    (p : P) (hps : p ∈ S) (Y : Plane) :
    ‖mixedJet q w (inverse d f) (p, Y)‖ ≤
      ParametricTorusInverse.mixedLossConstant w.length * C := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (ParametricTorusInverse.mixedLossConstant_nonneg w.length) hC)
  intro v
  rw [mixedJet_apply (inverse_smooth d hf hp),
    parameterJetApply_inverse d hf hp]
  have hg : ContDiff ℝ ∞ (fun Y => parameterJet q f (p, Y)) :=
    (parameterJet_smooth hf q).comp (contDiff_const.prodMk contDiff_id)
  have hgs : ContDiff ℝ ∞ (fun Y : Plane => parameterJet q f (p, (Y.2, Y.1))) :=
    hg.comp (contDiff_snd.prodMk contDiff_fst)
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => P) ℂ v
  have hb0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖parameterJetApply q v f (p, (x, y))‖ ≤ C * ∏ i, ‖v i‖ := by
    intro x hx y hy
    exact ContinuousMultilinearMap.le_of_opNorm_le (hzero p hps x hx y hy) v
  have hb1 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖SmoothFourierData.xJet (w.length + 5) (slice (parameterJetApply q v f) p) (x, y)‖ ≤
        C * ∏ i, ‖v i‖ := by
    intro x hx y hy
    have he := congrFun (tensorTorusWord_map L hg (List.replicate (w.length + 5) false)) (x, y)
    rw [tensorTorusWord_replicate] at he
    change SmoothFourierData.xJet (w.length + 5)
      (slice (parameterJetApply q v f) p) (x, y) =
      (tensorTorusWord (List.replicate (w.length + 5) false)
        (fun Y => parameterJet q f (p, Y)) (x, y)) v at he
    rw [he]
    exact ContinuousMultilinearMap.le_of_opNorm_le (hfirst p hps x hx y hy) v
  have hb2 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖SmoothFourierData.xJet (w.length + 5)
        (SmoothFourierData.swapFunction (slice (parameterJetApply q v f) p)) (x, y)‖ ≤
        C * ∏ i, ‖v i‖ := by
    intro x hx y hy
    have he := congrFun (tensorTorusWord_map L hgs (List.replicate (w.length + 5) false)) (x, y)
    rw [tensorTorusWord_replicate] at he
    change SmoothFourierData.xJet (w.length + 5)
      (SmoothFourierData.swapFunction (slice (parameterJetApply q v f) p)) (x, y) =
      (tensorTorusWord (List.replicate (w.length + 5) false)
        (fun Y => parameterJet q f (p, (Y.2, Y.1))) (x, y)) v at he
    rw [he]
    exact ContinuousMultilinearMap.le_of_opNorm_le (hsecond p hps x hx y hy) v
  exact (norm_derivativeWord_inverse_le d (parameterJetApply_smooth hf q v)
    (parameterJetApply_periodic hf hp q v) w p Y hb0 hb1 hb2).trans_eq (by ring)


end FiniteDimensional
end NavierStokes.SmoothFamilyTorusInverse
