/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspSpecialization
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Foundations.LineBundleTransport
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology1
import all LeanPool.HopfProblem.CuspFibre.CuspSpecialization

/-!
# Hopf problem: recognition · degree 1

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

private def
    Degree.AxisCoordinates.transverseBlock {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) : V →L[ℝ] V :=
  (ContinuousLinearMap.snd ℝ ℝ V).comp (L.comp (ContinuousLinearMap.inr ℝ ℝ V))

private theorem Degree.AxisCoordinates.contDiff_tangentShear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] : ContDiff ℝ ∞ (tangentShear (V := V)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

private theorem Degree.AxisCoordinates.contDiff_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] : ContDiff ℝ ∞ (transverseBlock (V := V)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

private theorem Degree.AxisCoordinates.axis_block_apply {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0)) (s : ℝ) (z : V) :
    L (s, z) = (s + tangentShear L z, transverseBlock L z) := by
  have hp : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [hp, map_add, map_smul, hL]
  apply Prod.ext <;> simp [tangentShear, transverseBlock]

private theorem
    Degree.AxisCoordinates.axis_block_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0)) :
    L = Smale.FrameField.shearedBlock (tangentShear L) (transverseBlock L) := by
  apply ContinuousLinearMap.ext
  intro p
  rw [Smale.FrameField.shearedBlock_apply]
  exact axis_block_apply L hL p.1 p.2

private theorem Degree.AxisCoordinates.bijective_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0))
    (hi : Function.Bijective L) : Function.Bijective (transverseBlock L) := by
  constructor
  · intro z w hzw
    have he : L (-tangentShear L z, z) = L (-tangentShear L w, w) := by
      rw [axis_block_apply L hL, axis_block_apply L hL]
      simp only [neg_add_cancel, hzw]
    exact congrArg (fun p : ℝ × V => p.2) (hi.1 he)
  · intro w
    obtain ⟨⟨s, z⟩, hz⟩ := hi.2 (0, w)
    rw [axis_block_apply L hL] at hz
    exact ⟨z, congrArg (fun p : ℝ × V => p.2) hz⟩

private theorem
    Degree.AxisCoordinates.isInvertible_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0))
    (hi : L.IsInvertible) : (transverseBlock L).IsInvertible := by
  let e :=
    (LinearEquiv.ofBijective (transverseBlock L).toLinearMap
        (bijective_transverseBlock L hL hi.bijective)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

private theorem Degree.AxisCoordinates.derivative_fixes_axis {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : (ℝ × V) → (ℝ × V)} {s : ℝ} (hF : ContDiffAt ℝ ∞ F (s, 0))
    (heq : (fun r : ℝ => F (r, 0)) =ᶠ[𝓝 s] (fun r => (r, (0 : V)))) :
    fderiv ℝ F (s, 0) (1, 0) = (1, 0) := by
  have ha : HasDerivAt (fun r : ℝ => (r, (0 : V))) (1, 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s 0)
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s ha
  exact hd.deriv.symm.trans (heq.deriv_eq.trans ha.deriv)

private theorem Degree.AxisCoordinates.exists_native_axis_transition_data {V E M : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) {s₀ : ℝ}
    (hΦ : (s₀, (0 : V)) ∈ Φ.source) (hΨ : (s₀, (0 : V)) ∈ Ψ.source)
    (haxis : (fun s : ℝ => Φ (s, 0)) =ᶠ[𝓝 s₀] (fun s => Ψ (s, 0))) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        s₀ ∈ U ∧
          (∀ s ∈ U, (s, (0 : V)) ∈ (Φ.trans Ψ.symm).source) ∧
            (∀ s ∈ U, Ψ.symm (Φ (s, 0)) = (s, 0)) ∧
              ContDiffOn ℝ ∞ (fun s => tangentShear (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) U ∧
                ContDiffOn ℝ ∞ (fun s => transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) U ∧
                  (∀ s ∈ U, (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))).IsInvertible) ∧
                    ∀ s ∈ U,
                      fderiv ℝ (Ψ.symm ∘ Φ) (s, 0) =
                        Smale.FrameField.shearedBlock
                          (tangentShear (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0)))
                          (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) := by
  let R := Φ.trans Ψ.symm
  have hR0 : (s₀, (0 : V)) ∈ R.source := by
    refine ⟨hΦ, ?_⟩
    change Φ (s₀, 0) ∈ Ψ.target
    rw [haxis.eq_of_nhds]
    exact Ψ.map_source' hΨ
  have hRsource : ∀ᶠ s in 𝓝 s₀, (s, (0 : V)) ∈ R.source :=
    (continuous_id.prodMk continuous_const).continuousAt (R.open_source.mem_nhds hR0)
  have hΨsource : ∀ᶠ s in 𝓝 s₀, (s, (0 : V)) ∈ Ψ.source :=
    (continuous_id.prodMk continuous_const).continuousAt (Ψ.open_source.mem_nhds hΨ)
  have hRaxis : ∀ᶠ s in 𝓝 s₀, R (s, (0 : V)) = (s, 0) := by
    filter_upwards [haxis, hΨsource] with s hs hsΨ
    change Ψ.symm (Φ (s, 0)) = (s, 0)
    rw [hs]
    exact Ψ.left_inv' hsΨ
  obtain ⟨U, hUN, hU, hs₀⟩ := mem_nhds_iff.mp (hRsource.and hRaxis)
  have hdf : ContDiffOn ℝ ∞ (fun s : ℝ => fderiv ℝ R (s, (0 : V))) U :=
    (R.contMDiffOn_toFun.contDiffOn.fderiv_of_isOpen R.open_source (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun s hs => (hUN hs).1)
  have hfix (s : ℝ) (hs : s ∈ U) : fderiv ℝ R (s, (0 : V)) (1, 0) = (1, 0) := by
    apply
      derivative_fixes_axis
        (R.contMDiffOn_toFun.contDiffOn.contDiffAt (R.open_source.mem_nhds (hUN hs).1))
    filter_upwards [hU.mem_nhds hs] with r hr
    exact (hUN hr).2
  refine
    ⟨U, hU, hs₀, fun s hs => (hUN hs).1, fun s hs => (hUN hs).2,
      (contDiff_tangentShear (V := V)).contDiffOn.comp hdf (fun _ _ => Set.mem_univ _),
      (contDiff_transverseBlock (V := V)).contDiffOn.comp hdf (fun _ _ => Set.mem_univ _), ?_, ?_⟩
  · intro s hs
    have hl : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ R (s, 0) :=
      ⟨R, (hUN hs).1, fun _ _ => rfl⟩
    have hi : (fderiv ℝ R (s, 0)).IsInvertible := by
      refine ⟨hl.mfderivToContinuousLinearEquiv (by simp), ?_⟩
      have he := hl.mfderivToContinuousLinearEquiv_coe (by simp)
      rw [mfderiv_eq_fderiv] at he
      exact he
    exact isInvertible_transverseBlock _ (hfix s hs) hi
  · intro s hs
    exact axis_block_eq _ (hfix s hs)

private theorem Smale.exists_smooth_open_curve_with_germ {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (S : TopologicalSpace.Opens B) {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ∈ S) :
    ∃ f : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧ (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → S := fun t => if h : a t ∈ S then ⟨a t, h⟩ else ⟨a t₀, ha0⟩
  let V := U ∩ a ⁻¹' (S : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU S.isOpen
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hsS : a s ∈ S := hs.2
    simp only [Function.comp_apply, A, dite_eq_left hsS]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt := (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff S A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, heq⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [heq, hval htV] with t ht hta
  exact (congrArg Subtype.val ht).trans hta

private theorem
    Smale.exists_smooth_open_curve_with_endpoint_germs {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (S : TopologicalSpace.Opens B) {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ∈ S) (hb1 : b 1 ∈ S)
    (γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S)) :
    ∃ f : ℝ → B, ContDiff ℝ ∞ f ∧ (∀ t, f t ∈ S) ∧ (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_open_curve_with_germ S ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_open_curve_with_germ S hb hV h1V hb1
  have hstart : a' 0 = (⟨a 0, ha0⟩ : S) := Subtype.ext heqa.eq_of_nhds
  have hend : b' 1 = (⟨b 1, hb1⟩ : S) := Subtype.ext heqb.eq_of_nhds
  obtain ⟨f, hf, hfa, hfb⟩ :=
    exists_smooth_curve_with_endpoint_germs a' b' ha' hb' (γ.cast hstart hend)
  refine
    ⟨fun t => (f t : B), ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := S)).comp hf).contDiff,
      fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb

private def Degree.LinearFramePaths.matrixCoordinates {D ι : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ D) : (D →L[ℝ] D) ≃L[ℝ] Matrix ι ι ℝ :=
  (LinearMap.toContinuousLinearMap.symm.trans (LinearMap.toMatrix b b)).toContinuousLinearEquiv

private theorem Degree.LinearFramePaths.det_matrixCoordinates {D ι : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ D)
    (A : D →L[ℝ] D) : Matrix.det (matrixCoordinates b A) = A.toLinearMap.det :=
  LinearMap.det_toMatrix b A.toLinearMap

private def
    Degree.LinearFramePaths.operatorComponent {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (σ : ℝ) : TopologicalSpace.Opens (D →L[ℝ] D) :=
  ⟨{A | 0 < σ * A.toLinearMap.det},
    isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩

private theorem
    Degree.LinearFramePaths.joined_operatorComponent {D ι : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Nontrivial ι] [Finite ι] (b : Module.Basis ι ℝ D)
    {σ : ℝ} (A B : operatorComponent (D := D) σ) : Joined A B := by
  classical
  let _ := Fintype.ofFinite ι
  let e := matrixCoordinates b
  let A' : determinantComponent (ι := ι) σ :=
    ⟨e A, by
      change 0 < σ * Matrix.det (matrixCoordinates b A)
      rw [det_matrixCoordinates]
      exact A.property⟩
  let B' : determinantComponent (ι := ι) σ :=
    ⟨e B, by
      change 0 < σ * Matrix.det (matrixCoordinates b B)
      rw [det_matrixCoordinates]
      exact B.property⟩
  let ψ : determinantComponent (ι := ι) σ → operatorComponent (D := D) σ := fun C =>
    ⟨e.symm C, by
      have hd := det_matrixCoordinates b (e.symm C)
      change Matrix.det (e (e.symm C)) = (e.symm C).toLinearMap.det at hd
      rw [e.apply_symm_apply] at hd
      change 0 < σ * (e.symm C).toLinearMap.det
      rw [← hd]
      exact C.property⟩
  have hψ : Continuous ψ := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  have hA : ψ A' = A := Subtype.ext (e.symm_apply_apply A)
  have hB : ψ B' = B := Subtype.ext (e.symm_apply_apply B)
  have h := (joined_determinantComponent A' B').map hψ
  rwa [hA, hB] at h

private theorem Degree.LinearFramePaths.exists_smooth_invertible_frame_join {D ι : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Nontrivial ι] [Finite ι]
    (basis : Module.Basis ι ℝ D) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ} (ha : ContDiffOn ℝ ∞ a U)
    (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U)
    (h1V : (1 : ℝ) ∈ V) (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  let S := operatorComponent (D := D) σ
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have ha0 : a 0 ∈ S := mul_self_pos.mpr ha0ne
  have hb1 : b 1 ∈ S := hsign
  let γ := (joined_operatorComponent basis (⟨a 0, ha0⟩ : S) ⟨b 1, hb1⟩).somePath
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    Smale.exists_smooth_open_curve_with_endpoint_germs S ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := hmem t
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  have hdet : (L t).toLinearMap.det ≠ 0 := by
    intro hz
    have hp := hpositive t
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  have hker : (L t).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hi : Function.Injective (L t) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

private theorem Degree.AxisCoordinates.exists_smooth_sheared_frame_join {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Finite ι] [Nontrivial ι]
    (basis : Module.Basis ι ℝ V) {A₀ A₁ : ℝ → (V →L[ℝ] ℝ)} {T₀ T₁ : ℝ → (V →L[ℝ] V)}
    {U₀ U₁ : Set ℝ} (hA₀ : ContDiffOn ℝ ∞ A₀ U₀) (hA₁ : ContDiffOn ℝ ∞ A₁ U₁)
    (hT₀ : ContDiffOn ℝ ∞ T₀ U₀) (hT₁ : ContDiffOn ℝ ∞ T₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0 : (0 : ℝ) ∈ U₀) (h1 : (1 : ℝ) ∈ U₁)
    (hsign : 0 < (T₀ 0).toLinearMap.det * (T₁ 1).toLinearMap.det) :
    ∃ A : ℝ → (V →L[ℝ] ℝ),
      ∃ T : ℝ → (V →L[ℝ] V),
        ContDiff ℝ ∞ A ∧
          ContDiff ℝ ∞ T ∧
            (∀ s, (T s).IsInvertible) ∧
              (∀ s, (Smale.FrameField.shearedBlock (A s) (T s)).IsInvertible) ∧
                (A =ᶠ[𝓝 (0 : ℝ)] A₀) ∧
                  (A =ᶠ[𝓝 (1 : ℝ)] A₁) ∧ (T =ᶠ[𝓝 (0 : ℝ)] T₀) ∧ (T =ᶠ[𝓝 (1 : ℝ)] T₁) := by
  let S : TopologicalSpace.Opens (V →L[ℝ] ℝ) := ⟨Set.univ, isOpen_univ⟩
  let γ : Path (⟨A₀ 0, Set.mem_univ _⟩ : S) ⟨A₁ 1, Set.mem_univ _⟩ :=
    { toFun := fun t => ⟨(1 - (t : ℝ)) • A₀ 0 + (t : ℝ) • A₁ 1, Set.mem_univ _⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
  obtain ⟨A, hA, -, ha₀, ha₁⟩ :=
    Smale.exists_smooth_open_curve_with_endpoint_germs S hA₀ hA₁ hU₀ hU₁ h0 h1 (Set.mem_univ _)
      (Set.mem_univ _) γ
  obtain ⟨T, hT, hi, -, ht₀, ht₁⟩ :=
    Degree.LinearFramePaths.exists_smooth_invertible_frame_join basis hT₀ hT₁ hU₀ hU₁ h0 h1 hsign
  have hTi (s : ℝ) : (T s).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (T s).toLinearMap (hi s)).toContinuousLinearEquiv, rfl⟩
  exact
    ⟨A, T, hA, hT, hTi, fun s => Smale.FrameField.isInvertible_shearedBlock (A s) (T s) (hTi s),
      ha₀, ha₁, ht₀, ht₁⟩

private theorem Degree.AxisCoordinates.exists_smooth_sheared_frame_join_at {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Finite ι] [Nontrivial ι]
    (basis : Module.Basis ι ℝ V) {p q : ℝ} (hpq : p < q) {A₀ A₁ : ℝ → (V →L[ℝ] ℝ)}
    {T₀ T₁ : ℝ → (V →L[ℝ] V)} {U₀ U₁ : Set ℝ} (hA₀ : ContDiffOn ℝ ∞ A₀ U₀)
    (hA₁ : ContDiffOn ℝ ∞ A₁ U₁) (hT₀ : ContDiffOn ℝ ∞ T₀ U₀) (hT₁ : ContDiffOn ℝ ∞ T₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hp : p ∈ U₀) (hq : q ∈ U₁)
    (hsign : 0 < (T₀ p).toLinearMap.det * (T₁ q).toLinearMap.det) :
    ∃ A : ℝ → (V →L[ℝ] ℝ),
      ∃ T : ℝ → (V →L[ℝ] V),
        ContDiff ℝ ∞ A ∧
          ContDiff ℝ ∞ T ∧
            (∀ s, (T s).IsInvertible) ∧
              (∀ s, (Smale.FrameField.shearedBlock (A s) (T s)).IsInvertible) ∧
                (A =ᶠ[𝓝 p] A₀) ∧ (A =ᶠ[𝓝 q] A₁) ∧ (T =ᶠ[𝓝 p] T₀) ∧ (T =ᶠ[𝓝 q] T₁) := by
  let ξ : ℝ → ℝ := fun t => p + (q - p) * t
  let ζ : ℝ → ℝ := fun s => (s - p) / (q - p)
  have hn : q - p ≠ 0 := ne_of_gt (sub_pos.mpr hpq)
  have hξ : ContDiff ℝ ∞ ξ := by dsimp [ξ]; fun_prop
  have hζ : ContDiff ℝ ∞ ζ := by dsimp [ζ]; fun_prop
  have hξ0 : ξ 0 = p := by simp [ξ]
  have hξ1 : ξ 1 = q := by simp [ξ]
  have hζp : ζ p = 0 := by simp [ζ]
  have hζq : ζ q = 1 := by simp [ζ, hn]
  have hξζ (s : ℝ) : ξ (ζ s) = s := by
    dsimp [ξ, ζ]
    field_simp
    ring
  have h0 : (0 : ℝ) ∈ ξ ⁻¹' U₀ := by simpa only [Set.mem_preimage, hξ0] using hp
  have h1 : (1 : ℝ) ∈ ξ ⁻¹' U₁ := by simpa only [Set.mem_preimage, hξ1] using hq
  have hsgn : 0 < ((T₀ ∘ ξ) 0).toLinearMap.det * ((T₁ ∘ ξ) 1).toLinearMap.det := by
    simpa only [Function.comp_apply, hξ0, hξ1] using hsign
  obtain ⟨A, T, hA, hT, hi, hb, ha₀, ha₁, ht₀, ht₁⟩ :=
    exists_smooth_sheared_frame_join basis (hA₀.comp hξ.contDiffOn (fun _ hs => hs))
      (hA₁.comp hξ.contDiffOn (fun _ hs => hs)) (hT₀.comp hξ.contDiffOn (fun _ hs => hs))
      (hT₁.comp hξ.contDiffOn (fun _ hs => hs)) (hU₀.preimage hξ.continuous)
      (hU₁.preimage hξ.continuous) h0 h1 hsgn
  have hζ0 : Filter.Tendsto ζ (𝓝 p) (𝓝 0) := by
    simpa only [hζp] using hζ.continuous.continuousAt.tendsto (x := p)
  have hζ1 : Filter.Tendsto ζ (𝓝 q) (𝓝 1) := by
    simpa only [hζq] using hζ.continuous.continuousAt.tendsto (x := q)
  refine
    ⟨A ∘ ζ, T ∘ ζ, hA.comp hζ, hT.comp hζ, fun s => hi (ζ s), fun s => hb (ζ s), ?_, ?_, ?_, ?_⟩
  · filter_upwards [hζ0 ha₀] with s hs
    exact hs.trans (congrArg A₀ (hξζ s))
  · filter_upwards [hζ1 ha₁] with s hs
    exact hs.trans (congrArg A₁ (hξζ s))
  · filter_upwards [hζ0 ht₀] with s hs
    exact hs.trans (congrArg T₀ (hξζ s))
  · filter_upwards [hζ1 ht₁] with s hs
    exact hs.trans (congrArg T₁ (hξζ s))

private theorem
    Degree.AxisCoordinates.exists_flat_local_correction {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H R : E → F} {K U : Set E} {x : E} (hH : ContDiff ℝ ∞ H) (hR : ContDiffOn ℝ ∞ R U)
    (hU : IsOpen U) (hx : x ∈ U) (hvalue : ∀ y ∈ K ∩ U, R y = H y)
    (hderiv : ∀ y ∈ K ∩ U, fderiv ℝ R y = fderiv ℝ H y) :
    ∃ G : E → F,
      ContDiff ℝ ∞ G ∧
        (G =ᶠ[𝓝 x] R) ∧
          (∀ y ∉ U, G =ᶠ[𝓝 y] H) ∧ Set.EqOn G H K ∧ Set.EqOn (fderiv ℝ G) (fderiv ℝ H) K := by
  obtain ⟨β, hβ, -, hsupp, hone, -⟩ :=
    Smale.exists_compact_smooth_cutoff (isCompact_singleton : IsCompact ({ x } : Set E)) hU
      (Set.singleton_subset_iff.mpr hx)
  let G : E → F := fun y => H y + β y • (R y - H y)
  have hoff (y : E) (hy : y ∉ tsupport β) : G =ᶠ[𝓝 y] H := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp only [G, hz, Pi.zero_apply, zero_smul, add_zero]
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport β
    · exact
        hH.contDiffAt.add
          (hβ.contDiffAt.smul ((hR.contDiffAt (hU.mem_nhds (hsupp hy))).sub hH.contDiffAt))
    · exact hH.contDiffAt.congr_of_eventuallyEq (hoff y hy)
  have hGeq (y : E) (hy : y ∈ K) : G y = H y := by
    by_cases hb : y ∈ tsupport β
    · simp only [G, hvalue y ⟨hy, hsupp hb⟩, sub_self, smul_zero, add_zero]
    · exact (hoff y hb).eq_of_nhds
  refine ⟨G, hG, ?_, fun y hy => hoff y (fun h => hy (hsupp h)), hGeq, ?_⟩
  · have hone' : ∀ᶠ y in 𝓝 x, β y = 1 := by simpa only [nhdsSet_singleton] using hone
    filter_upwards [hone'] with y hy
    simp only [G, hy, one_smul]
    abel
  · intro y hy
    by_cases hb : y ∈ tsupport β
    · have hr := (hR.contDiffAt (hU.mem_nhds (hsupp hb))).differentiableAt (by simp)
      have hh := hH.differentiable (by simp) y
      have hd : HasFDerivAt (fun z => R z - H z) (0 : E →L[ℝ] F) y := by
        simpa only [hderiv y ⟨hy, hsupp hb⟩, sub_self, Pi.sub_def] using
          hr.hasFDerivAt.sub hh.hasFDerivAt
      have hc : HasFDerivAt (fun z => β z • (R z - H z)) (0 : E →L[ℝ] F) y := by
        simpa only [hvalue y ⟨hy, hsupp hb⟩, sub_self, smul_zero,
          ContinuousLinearMap.smulRight_zero, add_zero, Pi.smul_def'] using
          (hβ.differentiable (by simp) y).hasFDerivAt.smul hd
      simpa only [add_zero, Pi.add_def, G] using (hh.hasFDerivAt.add hc).fderiv
    · exact (hoff y hb).fderiv_eq

private theorem
    Degree.AxisCoordinates.exists_axis_germ_correction {V F : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H R₀ R₁ : (ℝ × V) → F} {U₀ U₁ : Set (ℝ × V)} {p q : ℝ} (hpq : p < q) (hH : ContDiff ℝ ∞ H)
    (hR₀ : ContDiffOn ℝ ∞ R₀ U₀) (hR₁ : ContDiffOn ℝ ∞ R₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0 : (p, (0 : V)) ∈ U₀) (h1 : (q, (0 : V)) ∈ U₁)
    (hv₀ : (fun s : ℝ => R₀ (s, 0)) =ᶠ[𝓝 p] (fun s => H (s, 0)))
    (hv₁ : (fun s : ℝ => R₁ (s, 0)) =ᶠ[𝓝 q] (fun s => H (s, 0)))
    (hd₀ : (fun s : ℝ => fderiv ℝ R₀ (s, 0)) =ᶠ[𝓝 p] (fun s => fderiv ℝ H (s, 0)))
    (hd₁ : (fun s : ℝ => fderiv ℝ R₁ (s, 0)) =ᶠ[𝓝 q] (fun s => fderiv ℝ H (s, 0))) :
    ∃ G : (ℝ × V) → F,
      ContDiff ℝ ∞ G ∧
        (∀ s : ℝ, G (s, 0) = H (s, 0)) ∧
          (∀ s : ℝ, fderiv ℝ G (s, 0) = fderiv ℝ H (s, 0)) ∧
            (G =ᶠ[𝓝 (p, (0 : V))] R₀) ∧ (G =ᶠ[𝓝 (q, (0 : V))] R₁) := by
  obtain ⟨I₀, hI₀sub, hI₀, h0I⟩ := mem_nhds_iff.mp (hv₀.and hd₀)
  obtain ⟨I₁, hI₁sub, hI₁, h1I⟩ := mem_nhds_iff.mp (hv₁.and hd₁)
  let W₀ := U₀ ∩ Prod.fst ⁻¹' (I₀ ∩ Set.Iio ((p + q) / 2))
  let W₁ := U₁ ∩ Prod.fst ⁻¹' (I₁ ∩ Set.Ioi ((p + q) / 2))
  have hW₀ : IsOpen W₀ := hU₀.inter ((hI₀.inter isOpen_Iio).preimage continuous_fst)
  have hW₁ : IsOpen W₁ := hU₁.inter ((hI₁.inter isOpen_Ioi).preimage continuous_fst)
  have h0W : (p, (0 : V)) ∈ W₀ := ⟨h0, h0I, by change p < (p + q) / 2; linarith⟩
  have h1W : (q, (0 : V)) ∈ W₁ := ⟨h1, h1I, by change (p + q) / 2 < q; linarith⟩
  let K : Set (ℝ × V) := Set.univ ×ˢ {0}
  have hv0 (y : ℝ × V) (hy : y ∈ K ∩ W₀) : R₀ y = H y := by
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₀sub hy.2.2.1).1
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  have hd0 (y : ℝ × V) (hy : y ∈ K ∩ W₀) : fderiv ℝ R₀ y = fderiv ℝ H y := by
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₀sub hy.2.2.1).2
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  obtain ⟨G₀, hG₀, hg₀, -, hvG₀, hdG₀⟩ :=
    exists_flat_local_correction hH (hR₀.mono Set.inter_subset_left) hW₀ h0W hv0 hd0
  have hv1 (y : ℝ × V) (hy : y ∈ K ∩ W₁) : R₁ y = G₀ y := by
    rw [hvG₀ hy.1]
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₁sub hy.2.2.1).1
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  have hd1 (y : ℝ × V) (hy : y ∈ K ∩ W₁) : fderiv ℝ R₁ y = fderiv ℝ G₀ y := by
    rw [hdG₀ hy.1]
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₁sub hy.2.2.1).2
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  obtain ⟨G, hG, hg₁, hoff, hvG, hdG⟩ :=
    exists_flat_local_correction hG₀ (hR₁.mono Set.inter_subset_left) hW₁ h1W hv1 hd1
  have h0not : (p, (0 : V)) ∉ W₁ := by
    intro hh
    have hbad : (p + q) / 2 < p := hh.2.2
    linarith
  refine ⟨G, hG, ?_, ?_, (hoff _ h0not).trans hg₀, hg₁⟩
  · intro s
    have hs : (s, (0 : V)) ∈ K := ⟨Set.mem_univ s, rfl⟩
    exact (hvG hs).trans (hvG₀ hs)
  · intro s
    have hs : (s, (0 : V)) ∈ K := ⟨Set.mem_univ s, rfl⟩
    exact (hdG hs).trans (hdG₀ hs)

private theorem
    Smale.FrameField.exists_sheared_tubular_chart {X Z F E M : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Ψ : PartialDiffeomorph 𝓘(ℝ, X × F) 𝓘(ℝ, E) (X × F) M ∞) {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hzero : K ×ˢ {(0 : F)} ⊆ Ψ.source) {A : X → (Z →L[ℝ] X)}
    {T : X → (Z →L[ℝ] F)} (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U)
    (hi : ∀ x ∈ K, (T x).IsInvertible) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, E) (X × Z) M ∞,
          K ×ˢ Metric.closedBall (0 : Z) ε ⊆ Φ.source ∧
            (∀ p, Φ p = Ψ (shearedMap A T p)) ∧
              Φ.target ⊆ Ψ.target ∧
                (∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] shearedMap A T) ∧
                  ∀ x ∈ K, HasFDerivAt (Ψ.symm ∘ Φ) (shearedBlock (A x) (T x)) (x, 0) := by
  obtain ⟨χ, hzeroχ, -, hχ⟩ := exists_sheared_frame_chart hK hU hKU hA hT hi
  let Φ := χ.trans Ψ
  have hzeroΦ : K ×ˢ {(0 : Z)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hx, rfl⟩, ?_⟩
    change χ (x, 0) ∈ Ψ.source
    rw [hχ, shearedMap_zero]
    exact hzero ⟨hx, rfl⟩
  obtain ⟨ε, hε, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hzeroΦ
  have hgerm : ∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] shearedMap A T := by
    intro x hx
    filter_upwards [Φ.open_source.mem_nhds (hzeroΦ ⟨hx, rfl⟩)] with p hp
    change Ψ.symm (Ψ (χ p)) = shearedMap A T p
    have hpΨ : χ p ∈ Ψ.source := hp.2
    exact (Ψ.left_inv' hpΨ).trans (congrFun hχ p)
  refine ⟨ε, hε, Φ, hprod, ?_, fun _ hy => hy.1, hgerm, ?_⟩
  · intro p
    change Ψ (χ p) = Ψ (shearedMap A T p)
    rw [hχ]
  · intro x hx
    apply (hgerm x hx).hasFDerivAt_iff.mpr
    exact
      hasFDerivAt_shearedMap_zero
        ((hA.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
        ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))

private theorem
    Degree.AxisCoordinates.exists_native_axis_chart_with_endpoint_germs {V E M ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Finite ι] [Nontrivial ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (basis : Module.Basis ι ℝ V) (Ψ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    {p q : ℝ} (hpq : p < q) {K : Set ℝ} (hK : IsCompact K) (hzero : K ×ˢ {(0 : V)} ⊆ Ψ.source)
    (hΨ₀ : (p, (0 : V)) ∈ Ψ.source) (hΨ₁ : (q, (0 : V)) ∈ Ψ.source)
    (hΦ₀ : (p, (0 : V)) ∈ Φ₀.source) (hΦ₁ : (q, (0 : V)) ∈ Φ₁.source)
    (haxis₀ : (fun s : ℝ => Φ₀ (s, 0)) =ᶠ[𝓝 p] (fun s => Ψ (s, 0)))
    (haxis₁ : (fun s : ℝ => Φ₁ (s, 0)) =ᶠ[𝓝 q] (fun s => Ψ (s, 0)))
    (hsign :
      0 <
        (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det *
          (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₁) (q, 0))).toLinearMap.det) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞,
          K ×ˢ Metric.closedBall (0 : V) ε ⊆ Φ.source ∧
            Φ.target ⊆ Ψ.target ∧
              (∀ s : ℝ, Φ (s, 0) = Ψ (s, 0)) ∧
                ((Φ : (ℝ × V) → M) =ᶠ[𝓝 (p, (0 : V))] Φ₀) ∧
                  ((Φ : (ℝ × V) → M) =ᶠ[𝓝 (q, (0 : V))] Φ₁) := by
  let R₀ := Φ₀.trans Ψ.symm
  let R₁ := Φ₁.trans Ψ.symm
  obtain ⟨U₀, hU₀, h0U, hs₀, hx₀, ha₀, ht₀, -, hb₀⟩ :=
    exists_native_axis_transition_data Φ₀ Ψ hΦ₀ hΨ₀ haxis₀
  obtain ⟨U₁, hU₁, h1U, hs₁, hx₁, ha₁, ht₁, -, hb₁⟩ :=
    exists_native_axis_transition_data Φ₁ Ψ hΦ₁ hΨ₁ haxis₁
  obtain ⟨A, T, hA, hT, -, hinv, hA₀, hA₁, hT₀, hT₁⟩ :=
    exists_smooth_sheared_frame_join_at basis hpq ha₀ ha₁ ht₀ ht₁ hU₀ hU₁ h0U h1U hsign
  let H := Smale.FrameField.shearedMap A T
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_fst.add ((hA.comp contDiff_fst).clm_apply contDiff_snd)).prodMk
      ((hT.comp contDiff_fst).clm_apply contDiff_snd)
  have hHd (s : ℝ) : fderiv ℝ H (s, (0 : V)) = Smale.FrameField.shearedBlock (A s) (T s) :=
    (Smale.FrameField.hasFDerivAt_shearedMap_zero (hA.differentiable (by simp) s)
        (hT.differentiable (by simp) s)).fderiv
  have hv₀ : (fun s : ℝ => R₀ (s, (0 : V))) =ᶠ[𝓝 p] (fun s => H (s, 0)) := by
    filter_upwards [hU₀.mem_nhds h0U] with s hs
    exact (hx₀ s hs).trans (Smale.FrameField.shearedMap_zero A T s).symm
  have hv₁ : (fun s : ℝ => R₁ (s, (0 : V))) =ᶠ[𝓝 q] (fun s => H (s, 0)) := by
    filter_upwards [hU₁.mem_nhds h1U] with s hs
    exact (hx₁ s hs).trans (Smale.FrameField.shearedMap_zero A T s).symm
  have hd₀ : (fun s : ℝ => fderiv ℝ R₀ (s, (0 : V))) =ᶠ[𝓝 p] (fun s => fderiv ℝ H (s, 0)) := by
    filter_upwards [hU₀.mem_nhds h0U, hA₀, hT₀] with s hs ha ht
    change fderiv ℝ (Ψ.symm ∘ Φ₀) (s, 0) = _
    rw [hb₀ s hs, hHd s, ha, ht]
  have hd₁ : (fun s : ℝ => fderiv ℝ R₁ (s, (0 : V))) =ᶠ[𝓝 q] (fun s => fderiv ℝ H (s, 0)) := by
    filter_upwards [hU₁.mem_nhds h1U, hA₁, hT₁] with s hs ha ht
    change fderiv ℝ (Ψ.symm ∘ Φ₁) (s, 0) = _
    rw [hb₁ s hs, hHd s, ha, ht]
  obtain ⟨G, hG, hvG, hdG, hg₀, hg₁⟩ :=
    exists_axis_germ_correction hpq hH R₀.contMDiffOn_toFun.contDiffOn
      R₁.contMDiffOn_toFun.contDiffOn R₀.open_source R₁.open_source (hs₀ p h0U) (hs₁ q h1U) hv₀
      hv₁ hd₀ hd₁
  have hGaxis (s : ℝ) : G (s, (0 : V)) = (s, 0) :=
    (hvG s).trans (Smale.FrameField.shearedMap_zero A T s)
  have hGi : Set.InjOn G (K ×ˢ {(0 : V)}) := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩ ⟨t, w⟩ ⟨ht, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    simpa only [hGaxis] using heq
  have hGl : ∀ p ∈ K ×ˢ {(0 : V)}, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ G p := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      Smale.isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ _)
        hG.contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv, hdG s, hHd s]
    exact hinv s
  have hGO : K ×ˢ {(0 : V)} ⊆ G ⁻¹' Ψ.source := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change G (s, 0) ∈ Ψ.source
    rw [hGaxis]
    exact hzero ⟨hs, rfl⟩
  obtain ⟨χ, hχzero, hχsub, hχ⟩ :=
    Smale.exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hGi hGl
      (Ψ.open_source.preimage hG.continuous) hGO
  let Φ := χ.trans Ψ
  have hΦzero : K ×ˢ {(0 : V)} ⊆ Φ.source := by
    intro p hp
    refine ⟨hχzero hp, ?_⟩
    change χ p ∈ Ψ.source
    rw [hχ]
    exact hχsub (hχzero hp)
  obtain ⟨ε, hε, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hΦzero
  have hformula (p : ℝ × V) : Φ p = Ψ (G p) := by
    change Ψ (χ p) = Ψ (G p)
    rw [hχ]
  refine ⟨ε, hε, Φ, hprod, fun _ hy => hy.1, ?_, ?_, ?_⟩
  · intro s
    rw [hformula, hGaxis]
  · filter_upwards [hg₀, R₀.open_source.mem_nhds (hs₀ p h0U)] with p hp hs
    rw [hformula, hp]
    exact Ψ.right_inv' hs.2
  · filter_upwards [hg₁, R₁.open_source.mem_nhds (hs₁ q h1U)] with p hp hs
    rw [hformula, hp]
    exact Ψ.right_inv' hs.2

private def
    MorseCancel.linearTransverseChart {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞ :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toDiffeomorph.toPartialDiffeomorph.trans Φ

private theorem MorseCancel.linearTransverseChart_axis {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    (t : ℝ) : linearTransverseChart C Φ (t, 0) = Φ (t, 0) := by
  change Φ (t, C 0) = Φ (t, 0)
  rw [map_zero]

private theorem MorseCancel.linearTransverseChart_axis_source {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    (t : ℝ) : (t, (0 : V)) ∈ (linearTransverseChart C Φ).source ↔ (t, (0 : V)) ∈ Φ.source := by
  change (t, (0 : V)) ∈ Set.univ ∧ (t, C 0) ∈ Φ.source ↔ _
  simp only [Set.mem_univ, map_zero, true_and]

private theorem MorseCancel.transverseBlock_comp_linear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (C : V ≃L[ℝ] V) (L : (ℝ × V) →L[ℝ] (ℝ × V)) :
    Degree.AxisCoordinates.transverseBlock
        (L.comp ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toContinuousLinearMap) =
      (Degree.AxisCoordinates.transverseBlock L).comp C.toContinuousLinearMap := by
  ext z
  rfl

private theorem
    MorseCancel.det_transition_linearTransverseChart {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    {t : ℝ} (ht : (t, (0 : V)) ∈ (Φ.trans Ψ.symm).source) :
    (Degree.AxisCoordinates.transverseBlock
          (fderiv ℝ (Ψ.symm ∘ linearTransverseChart C Φ) (t, 0))).toLinearMap.det =
      (Degree.AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (t, 0))).toLinearMap.det *
        C.toLinearMap.det := by
  let P := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C
  have hP (s : ℝ) : P (s, (0 : V)) = (s, 0) := by
    change (s, C 0) = (s, 0)
    rw [map_zero]
  have hr : DifferentiableAt ℝ (Ψ.symm ∘ Φ) (t, (0 : V)) :=
    ((Φ.trans Ψ.symm).contMDiffOn_toFun.contDiffOn.contDiffAt
          ((Φ.trans Ψ.symm).open_source.mem_nhds ht)).differentiableAt
      (by simp)
  have hre : DifferentiableAt ℝ (Ψ.symm ∘ Φ) (P (t, (0 : V))) := by
    rw [hP]
    exact hr
  have heq : (Ψ.symm ∘ linearTransverseChart C Φ) = (Ψ.symm ∘ Φ) ∘ P := rfl
  rw [heq, fderiv_comp _ hre P.differentiableAt, P.fderiv, hP, transverseBlock_comp_linear]
  exact LinearMap.det_comp _ _

private theorem MorseCancel.det_ne_zero_of_isInvertible {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (T : V →L[ℝ] V) (hT : T.IsInvertible) : T.toLinearMap.det ≠ 0 := by
  obtain ⟨e, he⟩ := hT
  rw [← he]
  exact e.toLinearEquiv.isUnit_det'.ne_zero

private theorem MorseCancel.exists_compatible_sheet_endpoint_orientation {A B E M ι : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (basis : Module.Basis ι ℝ B) (i : ι)
    (Ψ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (A × B)) 𝓘(ℝ, E) (ℝ × (A × B)) M ∞) {p q : ℝ}
    (hΨ₀ : (p, (0 : A × B)) ∈ Ψ.source) (hΨ₁ : (q, (0 : A × B)) ∈ Ψ.source)
    (hΦ₀ : (p, (0 : A × B)) ∈ Φ₀.source) (hΦ₁ : (q, (0 : A × B)) ∈ Φ₁.source)
    (haxis₀ : (fun s : ℝ => Φ₀ (s, 0)) =ᶠ[𝓝 p] (fun s => Ψ (s, 0)))
    (haxis₁ : (fun s : ℝ => Φ₁ (s, 0)) =ᶠ[𝓝 q] (fun s => Ψ (s, 0))) :
    ∃ R : B ≃L[ℝ] B,
      0 <
        (Degree.AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det *
          (Degree.AxisCoordinates.transverseBlock
              (fderiv ℝ
                (Ψ.symm ∘ linearTransverseChart ((ContinuousLinearEquiv.refl ℝ A).prodCongr R) Φ₁)
                (q, 0))).toLinearMap.det := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨U₀, -, hp, -, -, -, -, hi₀, -⟩ :=
    Degree.AxisCoordinates.exists_native_axis_transition_data Φ₀ Ψ hΦ₀ hΨ₀ haxis₀
  obtain ⟨U₁, -, hq, hs₁, -, -, -, hi₁, -⟩ :=
    Degree.AxisCoordinates.exists_native_axis_transition_data Φ₁ Ψ hΦ₁ hΨ₁ haxis₁
  let d₀ :=
    (Degree.AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det
  let d₁ :=
    (Degree.AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₁) (q, 0))).toLinearMap.det
  have h₀ : d₀ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₀ p hp)
  have h₁ : d₁ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₁ q hq)
  obtain ⟨R, hR⟩ :=
    Degree.SupportedGerms.exists_linearEquiv_with_det basis i (inv_ne_zero (mul_ne_zero h₀ h₁))
  refine ⟨R, ?_⟩
  rw [det_transition_linearTransverseChart _ Φ₁ Ψ (hs₁ q hq)]
  have hdet : ((ContinuousLinearEquiv.refl ℝ A).prodCongr R).toLinearMap.det = (d₀ * d₁)⁻¹ := by
    change ((LinearMap.id : A →ₗ[ℝ] A).prodMap R.toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul, hR]
  rw [hdet]
  change 0 < d₀ * (d₁ * (d₀ * d₁)⁻¹)
  have hone : d₀ * (d₁ * (d₀ * d₁)⁻¹) = 1 := by
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero h₀ h₁)]
  rw [hone]
  exact zero_lt_one

private theorem
    MorseCancel.exists_sheet_arc_tube {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {a : ℝ → M} (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a)
    (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart
                      ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr R)
                      Φ₁) ∧
                  Φ.target ⊆ O := by
  have h0K : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1K : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨r, hr, Ξ, hΞprod, hΞaxis, hΞO⟩ :=
    Smale.exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero ha
      CompactIccSpace.isCompact_Icc h0K ((convex_Icc (0 : ℝ) 1).starConvex h0K) hinj hi 4
      (by rw [Module.finrank_self, hdim]) hO haO
  let L :
    ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])
  let P := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L).toDiffeomorph
  let Ψ := P.toPartialDiffeomorph.trans Ξ
  have hΨaxis (t : ℝ) : Ψ (t, 0) = a t := by
    change Ξ (t, L 0) = a t
    rw [map_zero, hΞaxis]
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change
      (t, (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Set.univ ∧
        (t, L 0) ∈ Ξ.source
    rw [map_zero]
    exact ⟨Set.mem_univ _, hΞprod ⟨ht, Metric.mem_closedBall_self hr.le⟩⟩
  have hΨ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Ψ.source :=
    hzero ⟨h0K, rfl⟩
  have hΨ₁ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Ψ.source :=
    hzero ⟨h1K, rfl⟩
  have haxis₀ : (fun t : ℝ => Φ₀ (t, 0)) =ᶠ[𝓝 (0 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hleft] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  have haxis₁ : (fun t : ℝ => Φ₁ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  obtain ⟨R, hsign⟩ :=
    exists_compatible_sheet_endpoint_orientation (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 2)))
      ⟨0, by simp only [finrank_euclideanSpace_fin]; norm_num⟩ Ψ Φ₀ Φ₁ hΨ₀ hΨ₁ hΦ₀ hΦ₁ haxis₀
      haxis₁
  let C := (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr R
  let Φ₂ := linearTransverseChart C Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source C Φ₁ 1).mpr hΦ₁
  have haxis₂ : (fun t : ℝ => Φ₂ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [haxis₁] with t ht
    exact (linearTransverseChart_axis C Φ₁ t).trans ht
  let _ :
    Nontrivial
      (Fin (Module.finrank ℝ ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) :=
    Fin.nontrivial_iff_two_le.mpr
      (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
        norm_num)
  obtain ⟨ε, hε, Φ, hprod, htarget, haxis, hgl, hgr⟩ :=
    Degree.AxisCoordinates.exists_native_axis_chart_with_endpoint_germs
      (Module.finBasis ℝ ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) Ψ Φ₀ Φ₂
      zero_lt_one CompactIccSpace.isCompact_Icc hzero hΨ₀ hΨ₁ hΦ₀ hΦ₂ haxis₀ haxis₂ hsign
  exact
    ⟨R, ε, hε, Φ, hprod, fun t => (haxis t).trans (hΨaxis t), hgl, hgr, fun z hz =>
      hΞO (htarget hz).1⟩

private theorem
    MorseCancel.exists_open_tube_sheet_recognition {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) {K : Set ℝ}
    (hKsource : K ×ˢ {(0 : V)} ⊆ Φ.source) {S : Set M} (hS : IsClosed S) (p : ℝ) (N : Set V)
    (hlocal : ∀ᶠ z in 𝓝 (p, (0 : V)), Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N)
    (haway : ∀ t ∈ K, t ≠ p → Φ (t, 0) ∉ S) :
    ∃ W : Set (ℝ × V),
      IsOpen W ∧ K ×ˢ {(0 : V)} ⊆ W ∧ W ⊆ Φ.source ∧ ∀ z ∈ W, Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N := by
  obtain ⟨U, hUgood, hU, hpU⟩ := _root_.mem_nhds_iff.mp hlocal
  let A : Set (ℝ × V) := (Φ.source ∩ Φ ⁻¹' Sᶜ) ∩ {z | z.1 ≠ p}
  have hA : IsOpen A :=
    (Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hS.isOpen_compl).inter
      (isOpen_ne_fun continuous_fst continuous_const)
  let W := Φ.source ∩ (U ∪ A)
  refine ⟨W, Φ.open_source.inter (hU.union hA), ?_, Set.inter_subset_left, ?_⟩
  · rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hKsource ⟨ht, rfl⟩, ?_⟩
    by_cases htp : t = p
    · subst t
      exact Or.inl hpU
    · exact Or.inr ⟨⟨hKsource ⟨ht, rfl⟩, haway t ht htp⟩, htp⟩
  · intro z hz
    rcases hz.2 with hzU | hzA
    · exact hUgood hzU
    · constructor
      · intro h
        exact (hzA.1.2 h).elim
      · rintro ⟨h, -⟩
        exact (hzA.2 h).elim

private theorem
    MorseCancel.exists_clean_axis_tube_restriction {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) {K : Set ℝ} (hK : IsCompact K)
    (hKsource : K ×ˢ {(0 : V)} ⊆ Φ.source) {S T : Set M} (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℝ) (N P : Set V) (hlocalS : ∀ᶠ z in 𝓝 (p, (0 : V)), Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N)
    (hlocalT : ∀ᶠ z in 𝓝 (q, (0 : V)), Φ z ∈ T ↔ z.1 = q ∧ z.2 ∈ P)
    (hawayS : ∀ t ∈ K, t ≠ p → Φ (t, 0) ∉ S) (hawayT : ∀ t ∈ K, t ≠ q → Φ (t, 0) ∉ T) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞,
          K ×ˢ Metric.closedBall (0 : V) ε ⊆ Ψ.source ∧
            (∀ z, Ψ z = Φ z) ∧
              Ψ.target ⊆ Φ.target ∧
                (∀ z ∈ Ψ.source, Ψ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N) ∧
                  (∀ z ∈ Ψ.source, Ψ z ∈ T ↔ z.1 = q ∧ z.2 ∈ P) := by
  obtain ⟨U, hU, hKU, -, hSU⟩ :=
    exists_open_tube_sheet_recognition Φ hKsource hS p N hlocalS hawayS
  obtain ⟨W, hW, hKW, -, hTW⟩ :=
    exists_open_tube_sheet_recognition Φ hKsource hT q P hlocalT hawayT
  let Ψ := Smale.PartialChart.restrictSource Φ (hU.inter hW)
  have hzero : K ×ˢ {(0 : V)} ⊆ Ψ.source := fun z hz => ⟨hKsource hz, hKU hz, hKW hz⟩
  obtain ⟨ε, hε, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hzero
  exact
    ⟨ε, hε, Ψ, hprod, fun _ => rfl, fun _ hz => hz.1, fun z hz => hSU z hz.2.1, fun z hz =>
      hTW z hz.2.2⟩

private theorem MorseCancel.exists_tube_support_box {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    (haxis : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Φ.source) :
    ∃ l u r : ℝ, l < 0 ∧ 1 < u ∧ 0 < r ∧ Set.Icc l u ×ˢ Metric.closedBall (0 : V) r ⊆ Φ.source := by
  let U : Set ℝ := (fun t : ℝ => (t, (0 : V))) ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage (continuous_id.prodMk continuous_const)
  have h0U : (0 : ℝ) ∈ U := haxis ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have h1U : (1 : ℝ) ∈ U := haxis ⟨⟨zero_le_one, le_rfl⟩, rfl⟩
  obtain ⟨a, ha, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h0U)
  obtain ⟨b, hb, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h1U)
  have hwide : Set.Icc (-a) (1 + b) ⊆ U := by
    intro t ht
    by_cases ht0 : t < 0
    · apply hball0
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_neg ht0]
      linarith [ht.1]
    · by_cases ht1 : 1 < t
      · apply hball1
        rw [Metric.mem_closedBall, Real.dist_eq, abs_of_pos (sub_pos.mpr ht1)]
        linarith [ht.2]
      · exact haxis ⟨⟨le_of_not_gt ht0, le_of_not_gt ht1⟩, rfl⟩
  have hwideAxis : Set.Icc (-a) (1 + b) ×ˢ {(0 : V)} ⊆ Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hwide ht
  obtain ⟨r, hr, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc
      Φ.open_source hwideAxis
  exact ⟨-a, 1 + b, r, by linarith, by linarith, hr, hprod⟩

private def
    Degree.RegularHeightCoordinates.heightMap {V : Type*} (F : ℝ × V → ℝ) (p : ℝ × V) : ℝ × V :=
  (F p, p.2)

private theorem
    Degree.RegularHeightCoordinates.linear_decomposition {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℝ × V →L[ℝ] ℝ) (s : ℝ) (z : V) : L (s, z) = s * L (1, 0) + L (0, z) := by
  have he : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [he, map_add, map_smul]
  rfl

private theorem
    Degree.RegularHeightCoordinates.triangular_bijective {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    Function.Bijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)) := by
  constructor
  · rintro ⟨s, z⟩ ⟨t, w⟩ h
    have hzw : z = w := congrArg Prod.snd h
    subst w
    have he : L (s, z) = L (t, z) := congrArg Prod.fst h
    rw [linear_decomposition L s z, linear_decomposition L t z] at he
    have hst : s = t := (mul_right_cancel₀ hL) (by linarith)
    exact Prod.ext hst rfl
  · rintro ⟨s, z⟩
    refine ⟨((s - L (0, z)) / L (1, 0), z), ?_⟩
    apply Prod.ext
    · change L ((s - L (0, z)) / L (1, 0), z) = s
      rw [linear_decomposition L, div_mul_cancel₀ _ hL]
      ring
    · rfl

private def Degree.RegularHeightCoordinates.triangularEquiv {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    (ℝ × V) ≃L[ℝ] (ℝ × V) :=
  (LinearEquiv.ofBijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)).toLinearMap
      (triangular_bijective L hL)).toContinuousLinearEquiv

private theorem
    Degree.RegularHeightCoordinates.contDiff_heightMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (heightMap F) :=
  hF.prodMk contDiff_snd

private theorem Degree.RegularHeightCoordinates.fderiv_heightMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (p : ℝ × V) :
    fderiv ℝ (heightMap F) p = (fderiv ℝ F p).prod (ContinuousLinearMap.snd ℝ ℝ V) :=
  (((hF.differentiable (by simp) p).hasFDerivAt).prodMk
      (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt).fderiv

private theorem Degree.RegularHeightCoordinates.heightMap_localDiffeomorph {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {F : ℝ × V → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : ℝ × V} (hreg : fderiv ℝ F p (1, 0) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap F) p := by
  have hinv : (fderiv ℝ (heightMap F) p).IsInvertible := by
    refine ⟨triangularEquiv (fderiv ℝ F p) hreg, ?_⟩
    rw [fderiv_heightMap hF]
    rfl
  obtain ⟨Φ, hp, _, hΦ⟩ :=
    NoExotic.exists_partialDiffeomorph_of_contDiffOn isOpen_univ (Set.mem_univ p)
      (contDiff_heightMap hF).contDiffOn hinv
  exact ⟨Φ, hp, fun _ _ => congrFun hΦ.symm _⟩

private def
    Degree.RegularHeightCoordinates.displacedHeight {V : Type*} (u : ℝ × V → ℝ) (p : ℝ × V) : ℝ :=
  p.1 + u p

private theorem Degree.RegularHeightCoordinates.contDiff_displacedHeight {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (displacedHeight u) :=
  contDiff_fst.add hu

private theorem Degree.RegularHeightCoordinates.scalar_derivative {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) (z : V) :
    HasDerivAt (fun t : ℝ => F (t, z)) (fderiv ℝ F (s, z) (1, 0)) s :=
  ((hF.differentiable (by simp) (s, z)).hasFDerivAt).comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

private theorem Degree.RegularHeightCoordinates.heightMap_injective_of_positive {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ p, 0 < fderiv ℝ F p (1, 0)) : Function.Injective (heightMap F) := by
  have hmono (z : V) : StrictMono (fun s : ℝ => F (s, z)) :=
    strictMono_of_deriv_pos (fun s => by rw [(scalar_derivative hF s z).deriv]; exact hpos _)
  rintro ⟨s, z⟩ ⟨t, w⟩ he
  have hzw : z = w := congrArg Prod.snd he
  subst w
  have hst : s = t := (hmono z).injective (congrArg Prod.fst he)
  exact Prod.ext hst rfl

private theorem Degree.RegularHeightCoordinates.heightMap_surjective_of_bounded {V : Type*}
    [NormedAddCommGroup V] {u : ℝ × V → ℝ} (hu : Continuous u) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, |u p| ≤ C) : Function.Surjective (heightMap (displacedHeight u)) := by
  rintro ⟨r, z⟩
  let a := r - (C + 1)
  let b := r + (C + 1)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hs : Continuous (fun s : ℝ => displacedHeight u (s, z)) :=
    continuous_id.add (hu.comp (continuous_id.prodMk continuous_const))
  have hlo : displacedHeight u (a, z) ≤ r := by
    have h := (abs_le.mp (hbound (a, z))).2
    dsimp [displacedHeight, a] at *
    linarith
  have hhi : r ≤ displacedHeight u (b, z) := by
    have h := (abs_le.mp (hbound (b, z))).1
    dsimp [displacedHeight, b] at *
    linarith
  obtain ⟨s, _, he⟩ := intermediate_value_Icc hab hs.continuousOn ⟨hlo, hhi⟩
  exact ⟨(s, z), Prod.ext he rfl⟩

private theorem Degree.RegularHeightCoordinates.heightMap_surjective_of_compactSupport {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : Function.Surjective (heightMap (displacedHeight u)) := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hu.continuous).isBounded.exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg (u 0)).trans (hC _ ⟨0, rfl⟩)
  exact
    heightMap_surjective_of_bounded hu.continuous C hC0
      (fun p => by simpa only [Real.norm_eq_abs] using hC _ ⟨p, rfl⟩)

private def
    Degree.RegularHeightCoordinates.longitudinalDiffeomorph {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hpos : ∀ p, 0 < fderiv ℝ (displacedHeight u) p (1, 0)) :
    (ℝ × V) ≃ₘ⟮𝓘(ℝ, ℝ × V), 𝓘(ℝ, ℝ × V)⟯ (ℝ × V) := by
  have hs := contDiff_displacedHeight hu
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap (displacedHeight u)) :=
    fun p => heightMap_localDiffeomorph hs (hpos p).ne'
  exact
    hloc.diffeomorphOfBijective
      ⟨heightMap_injective_of_positive hs hpos, heightMap_surjective_of_compactSupport hu hc⟩

private def Degree.MorseRearrangement.IntervalTranslation (a b x y : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
    (∀ z, z ∉ Set.Ioo a b → D z = z) ∧ D =ᶠ[𝓝 x] fun z => z + (y - x)

private theorem
    Degree.MorseRearrangement.translation_germ_apply (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    {x y : ℝ} (hD : D =ᶠ[𝓝 x] fun z => z + (y - x)) : D x = y := by
  have h := hD.self_of_nhds
  linarith

private theorem Degree.MorseRearrangement.intervalTranslation_refl (a b x : ℝ) :
    IntervalTranslation a b x x := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞, fun _ _ => rfl, Filter.Eventually.of_forall ?_⟩
  intro z
  change z = z + (x - x)
  ring

private theorem Degree.MorseRearrangement.intervalTranslation_symm {a b x y : ℝ}
    (h : IntervalTranslation a b x y) : IntervalTranslation a b y x := by
  obtain ⟨D, hfix, hgerm⟩ := h
  have hxy := translation_germ_apply D hgerm
  have hback : D.symm y = x := by rw [← hxy, D.symm_apply_apply]
  have ht : Filter.Tendsto D.symm (𝓝 y) (𝓝 x) := hback ▸ D.symm.continuous.continuousAt.tendsto
  refine ⟨D.symm, ?_, ?_⟩
  · intro z hz
    have hh := D.symm_apply_apply z
    rwa [hfix z hz] at hh
  · filter_upwards [hgerm.comp_tendsto ht] with z hz
    change D (D.symm z) = D.symm z + (y - x) at hz
    rw [D.apply_symm_apply] at hz
    linarith

private theorem Degree.MorseRearrangement.intervalTranslation_trans {a b x y z : ℝ}
    (hxy : IntervalTranslation a b x y) (hyz : IntervalTranslation a b y z) :
    IntervalTranslation a b x z := by
  obtain ⟨D, hDfix, hD⟩ := hxy
  obtain ⟨G, hGfix, hG⟩ := hyz
  have hxy := translation_germ_apply D hD
  have ht : Filter.Tendsto D (𝓝 x) (𝓝 y) := hxy ▸ D.continuous.continuousAt.tendsto
  refine ⟨D.trans G, ?_, ?_⟩
  · intro w hw
    change G (D w) = w
    rw [hDfix w hw, hGfix w hw]
  · filter_upwards [hD, hG.comp_tendsto ht] with w hwD hwG
    change G (D w) = w + (z - x)
    change G (D w) = D w + (z - y) at hwG
    rw [hwG, hwD]
    ring

private theorem Degree.MorseRearrangement.exists_local_interval_translation {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) : ∃ ε, 0 < ε ∧ ∀ y, Dist.dist y x < ε → IntervalTranslation a b x y := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds hx)
  let β : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsupp : tsupport (fun z : ℝ => β z) ⊆ Set.Ioo a b := by
    rw [β.tsupport_eq]
    intro z hz
    apply hsub
    have hh : Dist.dist z x ≤ r / 2 := hz
    change Dist.dist z x < r
    linarith
  have hcompact : HasCompactSupport (fun z : ℝ => β z) := by
    change IsCompact (tsupport (fun z : ℝ => β z))
    rw [β.tsupport_eq]
    exact ProperSpace.isCompact_closedBall _ _
  obtain ⟨ε, hε, hmove⟩ :=
    Smale.SmallPerturbation.exists_radius_bumpTranslation β.contDiff hcompact
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hnorm : ‖y - x‖ < ε := by simpa only [dist_eq_norm] using hy
  obtain ⟨D, hD, hfix⟩ := hmove (y - x) hnorm
  refine ⟨D, fun z hz => hfix z (fun h => hz (hsupp h)), ?_⟩
  filter_upwards [Metric.ball_mem_nhds x β.rIn_pos] with z hz
  rw [hD, β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_smul]

private theorem Degree.MorseRearrangement.exists_supported_interval_translation {a b x y : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) : IntervalTranslation a b x y := by
  let U := Set.Ioo a b
  let P : U → Prop := fun z => IntervalTranslation a b x z
  have hlocal : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro z
    obtain ⟨ε, hε, hmove⟩ := exists_local_interval_translation z.property
    filter_upwards [Metric.ball_mem_nhds z hε] with w hw
    have hzw : IntervalTranslation a b z w := hmove w hw
    apply propext
    exact
      ⟨fun hw => intervalTranslation_trans hw (intervalTranslation_symm hzw), fun hz =>
        intervalTranslation_trans hz hzw⟩
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have heq : P ⟨x, hx⟩ = P ⟨y, hy⟩ := hlocal.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  have hstart : P ⟨x, hx⟩ := intervalTranslation_refl a b x
  have hfinish : P ⟨y, hy⟩ := heq ▸ hstart
  exact hfinish

private theorem Degree.MorseRearrangement.strictMono_of_fixed_exterior
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) {a b : ℝ} (hfix : ∀ z, z ∉ Set.Ioo a b → D z = z) :
    StrictMono D := by
  rcases D.continuous.strictMono_of_inj D.injective with hm | ha
  · exact hm
  · have hanti := ha (show b < b + 1 by linarith)
    rw [hfix b (fun h => (lt_irrefl b) h.2), hfix (b + 1) (fun h => by linarith [h.2])] at hanti
    linarith

private theorem Degree.MorseRearrangement.deriv_pos_of_strictMono_diffeomorph
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (hm : StrictMono D) (x : ℝ) : 0 < deriv D x := by
  have hd := (D.mdifferentiable (by simp) x).differentiableAt.hasDerivAt
  have hi := (D.symm.mdifferentiable (by simp) (D x)).differentiableAt.hasDerivAt
  have hc := hi.comp x hd
  have heq : D.symm ∘ D = id := funext D.symm_apply_apply
  rw [heq] at hc
  have hh := hc.unique (hasDerivAt_id x)
  have hn : deriv D x ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.mul_zero] at hh
    norm_num at hh
  exact lt_of_le_of_ne hm.monotone.deriv_nonneg (Ne.symm hn)

private theorem Degree.MorseRearrangement.exists_increasing_interval_translation {a b x y : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Set.Ioo a b → D z = z) ∧
        (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧ D x = y ∧ StrictMono D ∧ ∀ z, 0 < deriv D z := by
  obtain ⟨D, hfix, hgerm⟩ := exists_supported_interval_translation hx hy
  have hm := strictMono_of_fixed_exterior D hfix
  exact
    ⟨D, hfix, hgerm, translation_germ_apply D hgerm, hm, deriv_pos_of_strictMono_diffeomorph D hm⟩

private theorem Degree.MorseRearrangement.exists_increasing_interval_translation_with_exterior_germs
    {a b x y : ℝ} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Set.Ioo a b → D z = z) ∧
        (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧
          D x = y ∧ StrictMono D ∧ (∀ z, 0 < deriv D z) ∧ ∀ z, z ∉ Set.Ioo a b → D =ᶠ[𝓝 z] id := by
  obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hx.1 hy.1)
  obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hx.2 hy.2)
  have hx' : x ∈ Set.Ioo a' b' := ⟨ha'.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb'⟩
  have hy' : y ∈ Set.Ioo a' b' :=
    ⟨ha'.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb'⟩
  obtain ⟨D, hfix, hgerm, hpoint, hmono, hderiv⟩ := exists_increasing_interval_translation hx' hy'
  have hsub : Set.Icc a' b' ⊆ Set.Ioo a b := fun z hz => ⟨haa'.trans_le hz.1, hz.2.trans_lt hb'b⟩
  have hout (z : ℝ) (hz : z ∉ Set.Ioo a b) : D =ᶠ[𝓝 z] id := by
    have hz' : z ∈ (Set.Icc a' b')ᶜ := fun h => hz (hsub h)
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hz'] with w hw
    exact hfix w (fun h => hw ⟨h.1.le, h.2.le⟩)
  exact ⟨D, fun z hz => (hout z hz).self_of_nhds, hgerm, hpoint, hmono, hderiv, hout⟩

private def Degree.MorseRearrangement.blendHeight (θ : ℝ) (P Q : ℝ → ℝ) (s : ℝ) : ℝ :=
  θ * P s + (1 - θ) * Q s

private theorem Degree.MorseRearrangement.blendHeight_zero (P Q : ℝ → ℝ) (s : ℝ) :
    blendHeight 0 P Q s = Q s := by simp [blendHeight]

private theorem Degree.MorseRearrangement.blendHeight_one (P Q : ℝ → ℝ) (s : ℝ) :
    blendHeight 1 P Q s = P s := by simp [blendHeight]

private theorem Degree.MorseRearrangement.blendHeight_fixed {P Q : ℝ → ℝ} {s : ℝ} (hP : P s = s)
    (hQ : Q s = s) (θ : ℝ) : blendHeight θ P Q s = s := by
  rw [blendHeight, hP, hQ]
  ring

private theorem Degree.MorseRearrangement.positive_blended_slope {θ a b : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < θ * a + (1 - θ) * b := by
  by_cases hzero : θ = 0
  · simpa only [hzero, MulZeroClass.zero_mul, sub_zero, one_mul, zero_add] using hb
  · exact
      add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hθ.1 (Ne.symm hzero)) ha)
        (mul_nonneg (sub_nonneg.mpr hθ.2) hb.le)

private theorem
    Degree.MorseRearrangement.hasDerivAt_blended_height {f θ P Q : ℝ → ℝ} {t f' p' q' : ℝ}
    (hf : HasDerivAt f f' t) (hθ : HasDerivAt θ 0 t) (hP : HasDerivAt P p' (f t))
    (hQ : HasDerivAt Q q' (f t)) :
    HasDerivAt (fun s => blendHeight (θ s) P Q (f s)) ((θ t * p' + (1 - θ t) * q') * f') t := by
  convert!
    (hθ.mul (hP.comp t hf)).add (((hasDerivAt_const t (1 : ℝ)).sub hθ).mul (hQ.comp t hf)) using 1
  simp only [Pi.sub_apply]
  ring

private def
    MorseCancel.longitudinalBlendDisplacement {V : Type*} (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (t : ℝ) (p : ℝ × V) : ℝ :=
  η t * β p.2 * (D p.1 - p.1)

private def MorseCancel.longitudinalBlend {V : Type*} (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (p : ℝ × (ℝ × V)) : ℝ × V :=
  (p.2.1 + longitudinalBlendDisplacement D β η p.1 p.2, p.2.2)

private theorem MorseCancel.longitudinalBlendDisplacement_smooth {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (t : ℝ) : ContDiff ℝ ∞ (longitudinalBlendDisplacement D β η t) :=
  (contDiff_const.mul (hβ.comp contDiff_snd)).mul ((hD.comp contDiff_fst).sub contDiff_fst)

private theorem
    MorseCancel.longitudinalBlend_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hβ : ContDiff ℝ ∞ β)
    (hη : ContDiff ℝ ∞ η) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, ℝ × V) ∞ (longitudinalBlend D β η) := by
  have hs : ContMDiff 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ) ∞ Prod.fst := contDiff_fst.contMDiff
  have hz : ContMDiff 𝓘(ℝ, ℝ × V) 𝓘(ℝ, V) ∞ Prod.snd := contDiff_snd.contMDiff
  have hs' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × (ℝ × V) => p.2.1) :=
    hs.comp contMDiff_snd
  have hz' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, V) ∞ (fun p : ℝ × (ℝ × V) => p.2.2) :=
    hz.comp contMDiff_snd
  exact
    (hs'.add
          (((hη.contMDiff.comp contMDiff_fst).mul (hβ.contMDiff.comp hz')).mul
            ((hD.contMDiff.comp hs').sub hs'))).prodMk_space
      hz'

private theorem
    MorseCancel.longitudinalBlend_zero {V : Type*}
    {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hη : η 0 = 0) (p : ℝ × V) :
    longitudinalBlend D β η (0, p) = p := by
  simp only [longitudinalBlend, longitudinalBlendDisplacement, hη, MulZeroClass.zero_mul,
    add_zero]

private theorem
    MorseCancel.longitudinalBlendDisplacement_zero_outside {V : Type*} [NormedAddCommGroup V]
     {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) {l u : ℝ}
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (t : ℝ) (p : ℝ × V) (hp : p ∉ Set.Icc l u ×ˢ tsupport β) :
    longitudinalBlendDisplacement D β η t p = 0 := by
  by_cases hs : p.1 ∈ Set.Icc l u
  · have hb : β p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp ⟨hs, h⟩)
    simp only [longitudinalBlendDisplacement, hb, MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  · have hd := hfix p.1 (fun h => hs ⟨h.1.le, h.2.le⟩)
    simp only [longitudinalBlendDisplacement, hd, sub_self, MulZeroClass.mul_zero]

private theorem MorseCancel.longitudinalBlend_fixed_outside {V : Type*} [NormedAddCommGroup V]
     {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) {l u : ℝ}
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (t : ℝ) (p : ℝ × V) (hp : p ∉ Set.Icc l u ×ˢ tsupport β) :
    longitudinalBlend D β η (t, p) = p := by
  rw [longitudinalBlend, longitudinalBlendDisplacement_zero_outside η hfix t p hp, add_zero]

private theorem MorseCancel.longitudinalBlend_derivative_positive {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (hDpos : ∀ s, 0 < deriv D s) (hβrange : ∀ z, β z ∈ Set.Icc (0 : ℝ) 1)
    (hηrange : ∀ t, η t ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) (p : ℝ × V) :
    0 <
      fderiv ℝ
        (Degree.RegularHeightCoordinates.displacedHeight (longitudinalBlendDisplacement D β η t))
        p (1, 0) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hscalar :=
    Degree.RegularHeightCoordinates.scalar_derivative
      (Degree.RegularHeightCoordinates.contDiff_displacedHeight hu) p.1 p.2
  have hd :=
    (hasDerivAt_id p.1).add
      (((hD.differentiable (by simp) p.1).hasDerivAt.sub (hasDerivAt_id p.1)).const_mul
        (η t * β p.2))
  have hrate :
    fderiv ℝ
        (Degree.RegularHeightCoordinates.displacedHeight (longitudinalBlendDisplacement D β η t))
        p (1, 0) =
      1 + (η t * β p.2) * (deriv D p.1 - 1) :=
    hscalar.deriv.symm.trans hd.deriv
  rw [hrate]
  have hweight : η t * β p.2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hηrange t).1 (hβrange p.2).1,
      mul_le_one₀ (hηrange t).2 (hβrange p.2).1 (hβrange p.2).2⟩
  have hpos := Degree.MorseRearrangement.positive_blended_slope hweight (hDpos p.1) zero_lt_one
  nlinarith

private theorem
    MorseCancel.longitudinalBlend_slices {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} {l u : ℝ} (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β) (hDpos : ∀ s, 0 < deriv D s)
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (hβrange : ∀ z, β z ∈ Set.Icc (0 : ℝ) 1)
    (hηrange : ∀ t, η t ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ∃ d : Diffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) (ℝ × V) (ℝ × V) ∞,
      ∀ p, d p = longitudinalBlend D β η (t, p) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hcompact : HasCompactSupport (longitudinalBlendDisplacement D β η t) :=
    HasCompactSupport.intro (CompactIccSpace.isCompact_Icc.prod hc.isCompact)
      (longitudinalBlendDisplacement_zero_outside η hfix t)
  exact
    ⟨Degree.RegularHeightCoordinates.longitudinalDiffeomorph hu hcompact
        (longitudinalBlend_derivative_positive hD hβ hDpos hβrange hηrange t),
      fun _ => rfl⟩

private theorem MorseCancel.expNegInvGlue_hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t

private theorem MorseCancel.smoothTransition_deriv_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < deriv Real.smoothTransition t := by
  let a := expNegInvGlue t
  let b := expNegInvGlue (1 - t)
  let a' := t⁻¹ ^ 2 * a
  let b' := (1 - t)⁻¹ ^ 2 * b
  have ha : 0 < a := expNegInvGlue.pos_of_pos ht.1
  have hb : 0 < b := expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2)
  have ha' : 0 < a' := mul_pos (sq_pos_of_ne_zero (inv_ne_zero ht.1.ne')) ha
  have hb' : 0 < b' := mul_pos (sq_pos_of_ne_zero (inv_ne_zero (sub_pos.mpr ht.2).ne')) hb
  have hA : HasDerivAt expNegInvGlue a' t := expNegInvGlue_hasDerivAt t
  have hB : HasDerivAt (fun s : ℝ => expNegInvGlue (1 - s)) (-b') t := by
    convert!
      (expNegInvGlue_hasDerivAt (1 - t)).comp t
        ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) using
      1
    dsimp only [b', b]
    ring
  have hd := hA.div (hA.add hB) (Real.smoothTransition.pos_denom t).ne'
  change HasDerivAt Real.smoothTransition ((a' * (a + b) - a * (a' + -b')) / (a + b) ^ 2) t at hd
  rw [hd.deriv]
  apply div_pos
  · have he : a' * (a + b) - a * (a' + -b') = a' * b + a * b' := by ring
    rw [he]
    exact add_pos (mul_pos ha' hb) (mul_pos ha hb')
  · exact sq_pos_of_pos (add_pos ha hb)

private theorem MorseCancel.smoothTransition_strictMonoOn :
    StrictMonoOn Real.smoothTransition (Set.Icc (0 : ℝ) 1) := by
  apply
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) Real.smoothTransition.continuous.continuousOn
  intro t ht
  apply smoothTransition_deriv_pos
  simpa only [interior_Icc] using ht

private theorem
    MorseCancel.exists_unique_smoothTransition_time {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ τ : ℝ,
      τ ∈ Set.Ioo (0 : ℝ) 1 ∧
        Real.smoothTransition τ = c ∧
          0 < deriv Real.smoothTransition τ ∧
            ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.smoothTransition t = c ↔ t = τ := by
  have hc' : c ∈ Set.Icc (Real.smoothTransition 0) (Real.smoothTransition 1) := by
    rw [Real.smoothTransition.zero, Real.smoothTransition.one]
    exact ⟨hc.1.le, hc.2.le⟩
  obtain ⟨τ, hτ, heq⟩ :=
    intermediate_value_Icc zero_le_one Real.smoothTransition.continuous.continuousOn hc'
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, Real.smoothTransition.zero] at heq
    linarith [hc.1]
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, Real.smoothTransition.one] at heq
    linarith [hc.2]
  have hτI : τ ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hτ.1 (Ne.symm hτ0), lt_of_le_of_ne hτ.2 hτ1⟩
  refine ⟨τ, hτI, heq, smoothTransition_deriv_pos hτI, ?_⟩
  intro t ht
  exact ⟨fun h => smoothTransition_strictMonoOn.injOn ht hτ (h.trans heq.symm), fun h => h ▸ heq⟩

private structure MorseCancel.LongitudinalTubeMotion {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) where
  profile : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
  cutoff : V → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_germ : cutoff =ᶠ[𝓝 (0 : V)] fun _ => 1
  cutoff_zero : cutoff 0 = 1
  destination : ℝ
  destination_gt_one : 1 < destination
  profile_zero : profile 0 = destination
  profile_germ : (profile : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] fun s => s + destination
  time : ℝ
  time_mem : time ∈ Set.Ioo (0 : ℝ) 1
  time_value : Real.smoothTransition time * destination = 1
  time_rate : 0 < deriv Real.smoothTransition time * destination
  unique_time : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.smoothTransition t * destination = 1 ↔ t = time
  family : ℝ × M → M
  support : Set M
  compact_support : IsCompact support
  support_subset : support ⊆ Φ.target
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ family
  zero : ∀ y, family (0, y) = y
  slices : ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, d y = family (t, y)
  fixedOutside : ∀ t y, y ∉ support → family (t, y) = y
  model_source :
    ∀ t z, z ∈ Φ.source → longitudinalBlend profile cutoff Real.smoothTransition (t, z) ∈ Φ.source
  formula :
    ∀ t z,
      z ∈ Φ.source →
        family (t, Φ z) = Φ (longitudinalBlend profile cutoff Real.smoothTransition (t, z))

private theorem MorseCancel.nonempty_longitudinalTubeMotion {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ V]
    [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    (haxis : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Φ.source) : Nonempty (LongitudinalTubeMotion Φ) := by
  obtain ⟨l, u, r, hl, hu, hr, hbox⟩ := exists_tube_support_box Φ haxis
  let c : ℝ := (1 + u) / 2
  have hc : 1 < c := by dsimp only [c]; linarith
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcu : c < u := by dsimp only [c]; linarith
  have h0I : (0 : ℝ) ∈ Set.Ioo l u := ⟨hl, zero_lt_one.trans hu⟩
  have hcI : c ∈ Set.Ioo l u := ⟨hl.trans hcpos, hcu⟩
  obtain ⟨D, hDfix, hDgerm, hD0, -, hDpos⟩ :=
    Degree.MorseRearrangement.exists_increasing_interval_translation h0I hcI
  let β : ContDiffBump (0 : V) :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hβgerm : (β : V → ℝ) =ᶠ[𝓝 (0 : V)] fun _ => 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : V) β.rIn_pos] with z hz
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  have hβrange : ∀ z : V, β z ∈ Set.Icc (0 : ℝ) 1 := fun _ => ⟨β.nonneg, β.le_one⟩
  have hηrange : ∀ t : ℝ, Real.smoothTransition t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hmodel :=
    longitudinalBlend_smooth D.contMDiff.contDiff β.contDiff
      (Real.smoothTransition.contDiff (n := ⊤))
  have hsource : Set.Icc l u ×ˢ tsupport (β : V → ℝ) ⊆ Φ.source := by
    rw [β.tsupport_eq]
    exact hbox
  obtain ⟨F, K, hK, hKΦ, hF, hF0, hFd, hFfix, hsrc, hformula⟩ :=
    Smale.SupportedDiffeomorph.exists_supported_isotopy_extension Φ hmodel
      (longitudinalBlend_zero Real.smoothTransition.zero)
      (longitudinalBlend_slices D.contMDiff.contDiff β.contDiff β.hasCompactSupport hDpos hDfix
        hβrange hηrange)
      (CompactIccSpace.isCompact_Icc.prod β.hasCompactSupport.isCompact) hsource
      (longitudinalBlend_fixed_outside Real.smoothTransition hDfix)
  have hcInv : 1 / c ∈ Set.Ioo (0 : ℝ) 1 := ⟨one_div_pos.mpr hcpos, (div_lt_one hcpos).mpr hc⟩
  obtain ⟨τ, hτ, hτvalue, hτrate, hτunique⟩ := exists_unique_smoothTransition_time hcInv
  refine
    ⟨{  profile := D
        cutoff := β
        cutoff_smooth := β.contDiff
        cutoff_germ := hβgerm
        cutoff_zero := hβgerm.self_of_nhds
        destination := c
        destination_gt_one := hc
        profile_zero := hD0
        profile_germ := by simpa only [sub_zero] using hDgerm
        time := τ
        time_mem := hτ
        time_value := (eq_div_iff hcpos.ne').mp hτvalue
        time_rate := mul_pos hτrate hcpos
        unique_time := ?_
        family := F
        support := K
        compact_support := hK
        support_subset := hKΦ
        smooth := hF
        zero := hF0
        slices := hFd
        fixedOutside := hFfix
        model_source := hsrc
        formula := hformula }⟩
  intro t ht
  rw [← eq_div_iff hcpos.ne']
  exact hτunique t ht

private theorem
    MorseCancel.LongitudinalTubeMotion.model_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (t : ℝ) :
    MorseCancel.longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, (0, 0)) =
      (Real.smoothTransition t * A.destination, 0) := by
  simp only [MorseCancel.longitudinalBlend, MorseCancel.longitudinalBlendDisplacement,
    A.cutoff_zero, A.profile_zero, mul_one, sub_zero, zero_add]

private theorem
    MorseCancel.LongitudinalTubeMotion.model_germ {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (t : ℝ) :
    MorseCancel.longitudinalBlend A.profile A.cutoff Real.smoothTransition =ᶠ[𝓝 (t, (0, 0))]
      fun p : ℝ × (ℝ × V) => (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : Filter.Tendsto (fun p : ℝ × (ℝ × V) => p.2.1) (𝓝 (t, (0, 0))) (𝓝 0) :=
    continuous_fst.continuousAt.comp continuous_snd.continuousAt
  have hz : Filter.Tendsto (fun p : ℝ × (ℝ × V) => p.2.2) (𝓝 (t, (0, 0))) (𝓝 0) :=
    continuous_snd.continuousAt.comp continuous_snd.continuousAt
  filter_upwards [hs.eventually A.profile_germ, hz.eventually A.cutoff_germ] with p hp hβ
  simp only [MorseCancel.longitudinalBlend, MorseCancel.longitudinalBlendDisplacement, hp, hβ,
    mul_one, add_sub_cancel_left]

private theorem
    MorseCancel.LongitudinalTubeMotion.native_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    A.family (t, Φ 0) = Φ (Real.smoothTransition t * A.destination, 0) := by
  rw [A.formula t 0 h0]
  exact congrArg Φ (A.model_axis t)

private theorem
    MorseCancel.LongitudinalTubeMotion.native_germ {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    (fun p : ℝ × (ℝ × V) => A.family (p.1, Φ p.2)) =ᶠ[𝓝 (t, 0)] fun p =>
      Φ (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : ∀ᶠ p : ℝ × (ℝ × V) in 𝓝 (t, 0), p.2 ∈ Φ.source :=
    continuous_snd.continuousAt.eventually (Φ.open_source.mem_nhds h0)
  filter_upwards [A.model_germ t, hs] with p hp hs
  rw [A.formula p.1 p.2 hs, hp]

private theorem MorseCancel.LongitudinalTubeMotion.fixed_outside_target {V E H M : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (t : ℝ) (y : M) (hy : y ∉ Φ.target) : A.family (t, y) = y :=
  A.fixedOutside t y (fun h => hy (A.support_subset h))

private theorem
    MorseCancel.LongitudinalTubeMotion.crossing_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) : A.family (A.time, Φ 0) = Φ (1, 0) := by
  rw [A.native_axis h0, A.time_value]

private theorem MorseCancel.LongitudinalTubeMotion.whole_sheet_crossing_iff {U V E H M X Y : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M}
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hdisj : Disjoint (Set.range f) (Set.range g))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) (x₀ : X) (y₀ : Y)
    (hx₀ : Φ 0 = f x₀) (hy₀ : Φ (1, 0) = g y₀) (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : X) (y : Y) :
    A.family (t, f x) = g y ↔ t = A.time ∧ x = x₀ ∧ y = y₀ := by
  constructor
  · intro he
    have htarget : f x ∈ Φ.target := by
      by_contra hn
      have hxy : f x = g y := (A.fixed_outside_target t (f x) hn).symm.trans he
      exact (Set.disjoint_left.mp hdisj) ⟨x, rfl⟩ ⟨y, hxy.symm⟩
    let z := Φ.symm (f x)
    have hz : z ∈ Φ.source := Φ.map_target htarget
    have hzfx : Φ z = f x := Φ.right_inv htarget
    have hfz := (hrecf z hz).mp ⟨x, hzfx.symm⟩
    let w := MorseCancel.longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, z)
    have hw : w ∈ Φ.source := A.model_source t z hz
    have hwgy : Φ w = g y := by
      calc
        Φ w = A.family (t, Φ z) := (A.formula t z hz).symm
        _ = A.family (t, f x) := (congrArg (fun p => A.family (t, p)) hzfx)
        _ = g y := he
    have hgw := (hrecg w hw).mp ⟨y, hwgy.symm⟩
    have hu : z.2.1 = 0 := hgw.2
    have hz0 : z = 0 := Prod.ext hfz.1 (Prod.ext hu hfz.2)
    have hwaxis : w = (Real.smoothTransition t * A.destination, 0) := by
      dsimp only [w]
      rw [hz0]
      exact A.model_axis t
    have htimevalue : Real.smoothTransition t * A.destination = 1 :=
      (congrArg Prod.fst hwaxis).symm.trans hgw.1
    have htτ : t = A.time := (A.unique_time t ht).mp htimevalue
    have hx : x = x₀ := hfi (hzfx.symm.trans ((congrArg Φ hz0).trans hx₀))
    have hwy : Φ w = g y₀ := by
      rw [hwaxis, htimevalue]
      exact hy₀
    exact ⟨htτ, hx, hgi (hwgy.symm.trans hwy)⟩
  · rintro ⟨ht, hx, hy⟩
    rw [ht, hx, hy]
    calc
      A.family (A.time, f x₀) = A.family (A.time, Φ 0) :=
        congrArg (fun p => A.family (A.time, p)) hx₀.symm
      _ = Φ (1, 0) := (A.crossing_axis h0)
      _ = g y₀ := hy₀

private theorem
    MorseCancel.surjective_sheet_coordinate_mfderiv {U W H X : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (P : W →L[ℝ] U) (Q : U →L[ℝ] W) (b : W) {a : X → W} {x : X}
    (ha : MDifferentiableAt I 𝓘(ℝ, W) a x) (hi : Function.Injective (mfderiv I 𝓘(ℝ, W) a x))
    (hgerm : a =ᶠ[𝓝 x] fun y => Q (P (a y)) + b) :
    Function.Surjective (mfderiv I 𝓘(ℝ, U) (P ∘ a) x) := by
  have hP : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, U) P (a x) := P.differentiableAt.mdifferentiableAt
  have hα := hP.comp x ha
  have hQ : HasMFDerivAt 𝓘(ℝ, U) 𝓘(ℝ, W) (fun u => Q u + b) (P (a x)) Q :=
    (Q.hasFDerivAt.add_const b).hasMFDerivAt
  have heq : (mfderiv I 𝓘(ℝ, W) a x : U →L[ℝ] W) = Q.comp (mfderiv I 𝓘(ℝ, U) (P ∘ a) x) :=
    hgerm.mfderiv_eq.trans (hQ.comp x hα.hasMFDerivAt).mfderiv
  let D : U →L[ℝ] U := mfderiv I 𝓘(ℝ, U) (P ∘ a) x
  change Function.Surjective D
  apply (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mp
  intro u v huv
  apply hi
  rw [heq]
  exact congrArg Q huv

private theorem MorseCancel.native_coordinate_plane_trace_transverse {U H X : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X] {V H' Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] {α : X → U} {β : Y → V} {x : X} {y : Y} {η : ℝ → ℝ}
    {τ κ : ℝ} (hα : MDifferentiableAt I 𝓘(ℝ, U) α x) (hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y)
    (hαs : Function.Surjective (mfderiv I 𝓘(ℝ, U) α x))
    (hβs : Function.Surjective (mfderiv I' 𝓘(ℝ, V) β y)) (hη : HasDerivAt η κ τ) (hκ : κ ≠ 0) :
    Smale.NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, ℝ × (U × V))
      (fun p : ℝ × X => (η p.1, (α p.2, 0))) (fun q : Y => (1, (0, β q))) (τ, x) y := by
  let D : U →L[ℝ] U := mfderiv I 𝓘(ℝ, U) α x
  let E : V →L[ℝ] V := mfderiv I' 𝓘(ℝ, V) β y
  let C : (ℝ × U) →L[ℝ] ℝ :=
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).comp (ContinuousLinearMap.fst ℝ ℝ U)
  let L : (ℝ × U) →L[ℝ] ℝ × (U × V) := C.prod ((D.comp (ContinuousLinearMap.snd ℝ ℝ U)).prod 0)
  let R : V →L[ℝ] ℝ × (U × V) := (0 : V →L[ℝ] ℝ).prod ((0 : V →L[ℝ] U).prod E)
  have htime :=
    hη.hasFDerivAt.hasMFDerivAt.comp (τ, x) (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hcoord := hα.hasMFDerivAt.comp (τ, x) (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hzero : HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) (fun _ : ℝ × X => (0 : V)) (τ, x) 0 :=
    hasMFDerivAt_const _ _
  have hT :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × (U × V)) (fun p : ℝ × X => (η p.1, (α p.2, (0 : V))))
      (τ, x) L := by convert! htime.prodMk (hcoord.prodMk hzero) using 1
  have hone : HasMFDerivAt I' 𝓘(ℝ, ℝ) (fun _ : Y => (1 : ℝ)) y 0 := hasMFDerivAt_const _ _
  have hz : HasMFDerivAt I' 𝓘(ℝ, U) (fun _ : Y => (0 : U)) y 0 := hasMFDerivAt_const _ _
  have hB : HasMFDerivAt I' 𝓘(ℝ, ℝ × (U × V)) (fun q : Y => ((1 : ℝ), ((0 : U), β q))) y R := by
    convert! hone.prodMk (hz.prodMk hβ.hasMFDerivAt) using 1
  intro _
  rw [hT.mfderiv, hB.mfderiv]
  change Function.Surjective (L.coprod R)
  rintro ⟨s, u, v⟩
  obtain ⟨a, ha⟩ := hαs u
  obtain ⟨b, hb⟩ := hβs v
  refine ⟨((s / κ, a), b), ?_⟩
  apply Prod.ext
  · change s / κ * κ + 0 = s
    rw [add_zero, div_mul_cancel₀ s hκ]
  · change (D a + 0, 0 + E b) = (u, v)
    rw [add_zero, zero_add]
    exact Prod.ext ha hb

private theorem
    MorseCancel.LongitudinalTubeMotion.whole_sheet_transverse {U V E HU HV H M X Y : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace H] {I : ModelWithCorners ℝ U HU}
    {I' : ModelWithCorners ℝ V HV} {J : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y]
    [ChartedSpace HV Y] {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hfi : Function.Injective (mfderiv I J f x)) (hgi : Function.Injective (mfderiv I' J g y))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) (hx : Φ 0 = f x)
    (hy : Φ (1, 0) = g y) (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) :
    Smale.NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' J (fun p : ℝ × X => A.family (p.1, f p.2)) g
      (A.time, x) y := by
  let W := ℝ × (U × V)
  let a : X → W := Φ.symm ∘ f
  let b : Y → W := Φ.symm ∘ g
  let P : W →L[ℝ] U := (ContinuousLinearMap.fst ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let Q : U →L[ℝ] W := (0 : U →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ U).prod (0 : U →L[ℝ] V))
  let R : W →L[ℝ] V := (ContinuousLinearMap.snd ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let S : V →L[ℝ] W := (0 : V →L[ℝ] ℝ).prod ((0 : V →L[ℝ] U).prod (ContinuousLinearMap.id ℝ V))
  have h1 : ((1 : ℝ), (0 : U × V)) ∈ Φ.source := by
    have hh := A.model_source A.time ((0 : ℝ), (0 : U × V)) h0
    rw [A.model_axis, A.time_value] at hh
    exact hh
  have hfx : f x ∈ Φ.target := hx ▸ Φ.map_source h0
  have hgy : g y ∈ Φ.target := hy ▸ Φ.map_source h1
  have ha : MDifferentiableAt I 𝓘(ℝ, W) a x := (Φ.symm.mdifferentiableAt (by simp) hfx).comp x hf
  have hb : MDifferentiableAt I' 𝓘(ℝ, W) b y := (Φ.symm.mdifferentiableAt (by simp) hgy).comp y hg
  have hai : Function.Injective (mfderiv I 𝓘(ℝ, W) a x) := by
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hfx) hf]
    exact (Smale.PartialChart.bijective_mfderiv Φ.symm hfx).injective.comp hfi
  have hbi : Function.Injective (mfderiv I' 𝓘(ℝ, W) b y) := by
    rw [mfderiv_comp y (Φ.symm.mdifferentiableAt (by simp) hgy) hg]
    exact (Smale.PartialChart.bijective_mfderiv Φ.symm hgy).injective.comp hgi
  have ha0 : a x = 0 := (congrArg Φ.symm hx).symm.trans (Φ.left_inv h0)
  have hb1 : b y = (1, 0) := (congrArg Φ.symm hy).symm.trans (Φ.left_inv h1)
  have hfn : ∀ᶠ q in 𝓝 x, f q ∈ Φ.target :=
    hf.continuousAt.eventually (Φ.open_target.mem_nhds hfx)
  have hgn : ∀ᶠ q in 𝓝 y, g q ∈ Φ.target :=
    hg.continuousAt.eventually (Φ.open_target.mem_nhds hgy)
  have hca : ∀ᶠ q in 𝓝 x, (a q).1 = 0 ∧ (a q).2.2 = 0 := by
    filter_upwards [hfn] with q hq
    exact (hrecf (a q) (Φ.map_target hq)).mp ⟨q, (Φ.right_inv hq).symm⟩
  have hcb : ∀ᶠ q in 𝓝 y, (b q).1 = 1 ∧ (b q).2.1 = 0 := by
    filter_upwards [hgn] with q hq
    exact (hrecg (b q) (Φ.map_target hq)).mp ⟨q, (Φ.right_inv hq).symm⟩
  have hagerm : a =ᶠ[𝓝 x] fun q => Q (P (a q)) + (0 : W) := by
    filter_upwards [hca] with q hq
    change a q = (0, ((a q).2.1, 0)) + (0 : W)
    rw [add_zero]
    exact Prod.ext hq.1 (Prod.ext rfl hq.2)
  have hbgerm : b =ᶠ[𝓝 y] fun q => S (R (b q)) + ((1 : ℝ), (0 : U × V)) := by
    filter_upwards [hcb] with q hq
    change b q = (0, (0, (b q).2.2)) + ((1 : ℝ), (0 : U × V))
    apply Prod.ext
    · change (b q).1 = 0 + 1
      simpa only [zero_add] using hq.1
    · apply Prod.ext
      · change (b q).2.1 = 0 + 0
        simpa only [zero_add] using hq.2
      · change (b q).2.2 = (b q).2.2 + 0
        exact (add_zero _).symm
  let α : X → U := P ∘ a
  let β : Y → V := R ∘ b
  have hα : MDifferentiableAt I 𝓘(ℝ, U) α x := P.differentiableAt.mdifferentiableAt.comp x ha
  have hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y := R.differentiableAt.mdifferentiableAt.comp y hb
  have hαs := MorseCancel.surjective_sheet_coordinate_mfderiv P Q 0 ha hai hagerm
  have hβs := MorseCancel.surjective_sheet_coordinate_mfderiv R S (1, 0) hb hbi hbgerm
  let η : ℝ → ℝ := fun t => Real.smoothTransition t * A.destination
  have hη : HasDerivAt η (deriv Real.smoothTransition A.time * A.destination) A.time :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
          A.time).hasDerivAt.mul_const
      _
  let T : ℝ × X → W := fun p => (η p.1, (α p.2, 0))
  let B : Y → W := fun q => (1, (0, β q))
  have hT : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, W) T (A.time, x) :=
    (hη.differentiableAt.mdifferentiableAt.comp (A.time, x) mdifferentiableAt_fst).prodMk_space
      ((hα.comp (A.time, x) mdifferentiableAt_snd).prodMk_space mdifferentiableAt_const)
  have hB : MDifferentiableAt I' 𝓘(ℝ, W) B y :=
    mdifferentiableAt_const.prodMk_space (mdifferentiableAt_const.prodMk_space hβ)
  have hT0 : T (A.time, x) = (1, 0) := by
    change (η A.time, (P (a x), (0 : V))) = (1, 0)
    rw [ha0, map_zero]
    exact Prod.ext A.time_value rfl
  have hB0 : B y = (1, 0) := by
    change ((1 : ℝ), ((0 : U), R (b y))) = (1, 0)
    rw [hb1]
    rfl
  have hmodel : Smale.NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, W) T B (A.time, x) y :=
    MorseCancel.native_coordinate_plane_trace_transverse hα hβ hαs hβs hη A.time_rate.ne'
  have hnative :=
    (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff Φ hT hB
          (hB0.trans hT0.symm) (hT0 ▸ h1)).mp
      hmodel
  have hq :
    Filter.Tendsto (fun p : ℝ × X => (p.1, a p.2)) (𝓝 (A.time, x)) (𝓝 (A.time, (0 : W))) := by
    have hcont : ContinuousAt (fun p : ℝ × X => (p.1, a p.2)) (A.time, x) :=
      continuousAt_fst.prodMk
        (ContinuousAt.comp (g := a) (f := fun p : ℝ × X => p.2) ha.continuousAt continuousAt_snd)
    simpa only [ha0] using hcont.tendsto
  have hFgerm : (fun p : ℝ × X => A.family (p.1, f p.2)) =ᶠ[𝓝 (A.time, x)] (Φ ∘ T) := by
    filter_upwards [hq.eventually (A.native_germ h0 A.time),
      continuous_snd.continuousAt.eventually hfn, continuous_snd.continuousAt.eventually hca] with
      p hmove hp hplane
    have hpoint : Φ (a p.2) = f p.2 := Φ.right_inv hp
    calc
      A.family (p.1, f p.2) = A.family (p.1, Φ (a p.2)) :=
        congrArg (fun z => A.family (p.1, z)) hpoint.symm
      _ = Φ ((a p.2).1 + η p.1, (a p.2).2) := hmove
      _ = (Φ ∘ T) p := by
        apply congrArg Φ
        change ((a p.2).1 + η p.1, (a p.2).2) = (η p.1, ((a p.2).2.1, 0))
        rw [hplane.1, zero_add]
        exact Prod.ext rfl (Prod.ext rfl hplane.2)
  have hGgerm : g =ᶠ[𝓝 y] (Φ ∘ B) := by
    filter_upwards [hgn, hcb] with q hq hplane
    calc
      g q = Φ (b q) := (Φ.right_inv hq).symm
      _ = (Φ ∘ B) q := congrArg Φ (Prod.ext hplane.1 (Prod.ext hplane.2 rfl))
  intro _
  rw [hFgerm.mfderiv_eq, hGgerm.mfderiv_eq]
  exact hnative (congrArg Φ (hB0.trans hT0.symm))

private theorem
    MorseCancel.exists_clean_two_sheet_arc_avoiding {E M X Y Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    {f : X → M} {g : Y → M} {b : Z → M} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g) (hfe : Topology.IsEmbedding f)
    (hge : Topology.IsEmbedding g) (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hx : f x ∉ Set.range g) (hy : g y ∉ Set.range f) (hbx : f x ∉ Set.range b)
    (hby : g y ∉ Set.range b) (γ : Path (f x) (g y)) :
    ∃ Φ Ψ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source ∧
        ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source ∧
          Φ 0 = f x ∧
            Ψ (1, 0) = g y ∧
              (∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                (∀ z ∈ Ψ.source, Ψ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                  ∃ a : C(ℝ, M),
                    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
                      (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
                        (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
                          Topology.IsClosedEmbedding (fun t : unitInterval => a t) ∧
                            (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range f ↔ t = 0) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range g ↔ t = 1) ∧
                                  Set.MapsTo a (Set.Icc (0 : ℝ) 1) (Set.range b)ᶜ := by
  obtain ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec, -⟩ :=
    exists_clean_two_sheet_arc hf hg hfe hge hfi hgi hdim x y hx hy γ
  let o : C((X ⊕ Y) ⊕ Z, M) :=
    ⟨Sum.elim (Sum.elim f g) b, (hf.continuous.sumElim hg.continuous).sumElim hb.continuous⟩
  have ho : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ o := (hf.sumElim hg).sumElim hb
  have horange : Set.range o = (Set.range f ∪ Set.range g) ∪ Set.range b := by
    ext z
    constructor
    · rintro ⟨(a | c) | d, he⟩
      · exact Or.inl (Or.inl ⟨a, he⟩)
      · exact Or.inl (Or.inr ⟨c, he⟩)
      · exact Or.inr ⟨d, he⟩
    · rintro ((⟨a, he⟩ | ⟨c, he⟩) | ⟨d, he⟩)
      · exact ⟨Sum.inl (Sum.inl a), he⟩
      · exact ⟨Sum.inl (Sum.inr c), he⟩
      · exact ⟨Sum.inr d, he⟩
  have hoclosed : IsClosed (Set.range o) := by
    rw [horange]
    exact
      ((isCompact_range hf.continuous).isClosed.union
            (isCompact_range hg.continuous).isClosed).union
        hbc
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨V, hV, h1V, hVΨ, hc, hic⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hnear0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∉ Set.range b :=
    (ha.contMDiffAt (hU.mem_nhds h0U)).continuousAt.eventually
      (hbc.isOpen_compl.mem_nhds (by change Φ 0 ∉ Set.range b; rw [hΦx]; exact hbx))
  have hnear1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∉ Set.range b :=
    (hc.contMDiffAt (hV.mem_nhds h1V)).continuousAt.eventually
      (hbc.isOpen_compl.mem_nhds (by change Ψ (1, 0) ∉ Set.range b; rw [hΨy]; exact hby))
  have hclean0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 0 := by
    filter_upwards [hU.mem_nhds h0U, hnear0] with t ht hb'
    rw [horange]
    rintro ((h | h) | h)
    · exact ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
    · exact (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
    · exact (hb' h).elim
  have hclean1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 1 := by
    filter_upwards [hV.mem_nhds h1V, hnear1] with t ht hb'
    rw [horange]
    rintro ((h | h) | h)
    · exact (hΨavoid (Ψ.map_source' (hVΨ t ht)) h).elim
    · exact ((hΨrec (t, 0) (hVΨ t ht)).mp h).1
    · exact (hb' h).elim
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact fun h => hx ⟨y, h.symm⟩
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid⟩ :=
    exists_clean_arc_with_local_endpoint_germs ha hc hU hV h0U h1V hia hic (γ.cast hΦx hΨy) hends
      (by omega) o ho hoclosed (by rw [finrank_euclideanSpace_fin, hdim]; norm_num) hclean0
      hclean1
  have ha0 : a 0 = f x := hleft.eq_of_nhds.trans hΦx
  have ha1 : a 1 = g y := hright.eq_of_nhds.trans hΨy
  refine ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦrec, hΨrec, a, ha', hleft, hright, hemb, hi, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inl (Or.inl h))
    · intro he
      subst t
      rw [ha0]
      exact Set.mem_range_self x
  · intro t ht
    constructor
    · intro h
      by_contra ht1
      have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at h; exact hx h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inl (Or.inr h))
    · intro he
      subst t
      rw [ha1]
      exact Set.mem_range_self y
  · intro t ht htb
    have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at htb; exact hbx htb
    have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at htb; exact hby htb
    exact
      havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
        (horange.symm ▸ Or.inr htb)

private theorem
    AdaptedWindows.exists_forward_basin_smooth_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∃ r : ℝ,
      0 < r ∧
        (∀ n : ℕ,
            ContMDiffOn 𝓘(ℝ, (S.data p).chart.PositiveCoordinates) 𝓘(ℝ, E) ∞
              (fun v => S.flow (-(n : ℝ)) ((S.data p).chart.splitChart.symm (0, v)))
              (Metric.ball 0 r)) ∧
          {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} =
            ⋃ n : ℕ,
              (fun v => S.flow (-(n : ℝ)) ((S.data p).chart.splitChart.symm (0, v))) ''
                Metric.ball (0 : (S.data p).chart.PositiveCoordinates) r := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancel.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have htarget (v : c.PositiveCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    (0, v) ∈ c.splitChart.target :=
    hblock
      ⟨Metric.mem_closedBall_self hr.le,
        Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r)
          (Metric.ball_subset_closedBall hv)⟩
  have hlocal :
    ContMDiffOn 𝓘(ℝ, c.PositiveCoordinates) 𝓘(ℝ, E) ∞ (fun v => c.splitChart.symm (0, v))
      (Metric.ball 0 (r / 2)) :=
    c.splitChart.contMDiffOn_invFun.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
      htarget
  have hpoint (v : c.PositiveCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    Filter.Tendsto (fun t => S.flow t (c.splitChart.symm (0, v))) Filter.atTop (𝓝 p.val) := by
    have ht := htarget v hv
    have hs : c.splitChart.symm (0, v) ∈ c.splitChart.source := c.splitChart.map_target' ht
    have he : c.splitChart (c.splitChart.symm (0, v)) = (0, v) := c.splitChart.right_inv' ht
    apply ((hbasin (c.splitChart.symm (0, v)) hs ?_ ?_).1).mpr
    · rw [he]
    · rw [he]
      simpa using hr
    · rw [he]
      exact (mem_ball_zero_iff.mp hv).trans (half_lt_self hr)
  refine ⟨r / 2, half_pos hr, ?_, ?_⟩
  · intro n
    exact
      (Degree.SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
            (-(n : ℝ))).contMDiff.comp_contMDiffOn
        hlocal
  · ext x
    constructor
    · intro hx
      have hlim := hx.comp tendsto_natCast_atTop_atTop
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually
            (MorseCancel.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (MorseCancel.flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
      have hz : (c.splitChart (S.flow (n : ℝ) x)).1 = 0 :=
        ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp'.trans (half_lt_self hr))).1).mp hnew
      refine
        Set.mem_iUnion.mpr ⟨n, (c.splitChart (S.flow (n : ℝ) x)).2, mem_ball_zero_iff.mpr hp', ?_⟩
      have he : (0, (c.splitChart (S.flow (n : ℝ) x)).2) = c.splitChart (S.flow (n : ℝ) x) :=
        Prod.ext hz.symm rfl
      change S.flow (-(n : ℝ)) (c.splitChart.symm (0, (c.splitChart (S.flow (n : ℝ) x)).2)) = x
      rw [he]
      have hi : c.splitChart.symm (c.splitChart (S.flow (n : ℝ) x)) = S.flow (n : ℝ) x :=
        c.splitChart.left_inv' hs
      rw [hi, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]
    · intro hx
      obtain ⟨n, v, hv, rfl⟩ := Set.mem_iUnion.mp hx
      exact
        (MorseCancel.flow_time_atTop_limit_iff S.flow (-(n : ℝ)) (c.splitChart.symm (0, v))
              p.val).mpr
          (hpoint v hv)

private theorem
    AdaptedWindows.exists_backward_basin_smooth_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∃ r : ℝ,
      0 < r ∧
        (∀ n : ℕ,
            ContMDiffOn 𝓘(ℝ, (S.data p).chart.NegativeCoordinates) 𝓘(ℝ, E) ∞
              (fun v => S.flow (n : ℝ) ((S.data p).chart.splitChart.symm (v, 0)))
              (Metric.ball 0 r)) ∧
          {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)} =
            ⋃ n : ℕ,
              (fun v => S.flow (n : ℝ) ((S.data p).chart.splitChart.symm (v, 0))) ''
                Metric.ball (0 : (S.data p).chart.NegativeCoordinates) r := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancel.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have htarget (v : c.NegativeCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    (v, 0) ∈ c.splitChart.target :=
    hblock
      ⟨Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r)
          (Metric.ball_subset_closedBall hv),
        Metric.mem_closedBall_self hr.le⟩
  have hlocal :
    ContMDiffOn 𝓘(ℝ, c.NegativeCoordinates) 𝓘(ℝ, E) ∞ (fun v => c.splitChart.symm (v, 0))
      (Metric.ball 0 (r / 2)) :=
    c.splitChart.contMDiffOn_invFun.comp (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn
      htarget
  have hpoint (v : c.NegativeCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    Filter.Tendsto (fun t => S.flow t (c.splitChart.symm (v, 0))) Filter.atBot (𝓝 p.val) := by
    have ht := htarget v hv
    have hs : c.splitChart.symm (v, 0) ∈ c.splitChart.source := c.splitChart.map_target' ht
    have he : c.splitChart (c.splitChart.symm (v, 0)) = (v, 0) := c.splitChart.right_inv' ht
    apply ((hbasin (c.splitChart.symm (v, 0)) hs ?_ ?_).2).mpr
    · rw [he]
    · rw [he]
      exact (mem_ball_zero_iff.mp hv).trans (half_lt_self hr)
    · rw [he]
      simpa using hr
  refine ⟨r / 2, half_pos hr, ?_, ?_⟩
  · intro n
    exact
      (Degree.SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
            (n : ℝ)).contMDiff.comp_contMDiffOn
        hlocal
  · ext x
    constructor
    · intro hx
      have hlim : Filter.Tendsto (fun n : ℕ => S.flow (-(n : ℝ)) x) Filter.atTop (𝓝 p.val) :=
        hx.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually
            (MorseCancel.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (MorseCancel.flow_time_atBot_limit_iff S.flow (-(n : ℝ)) x p.val).mpr hx
      have hz : (c.splitChart (S.flow (-(n : ℝ)) x)).2 = 0 :=
        ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp'.trans (half_lt_self hr))).2).mp hnew
      refine
        Set.mem_iUnion.mpr
          ⟨n, (c.splitChart (S.flow (-(n : ℝ)) x)).1, mem_ball_zero_iff.mpr hn, ?_⟩
      have he :
        ((c.splitChart (S.flow (-(n : ℝ)) x)).1, 0) = c.splitChart (S.flow (-(n : ℝ)) x) :=
        Prod.ext rfl hz.symm
      change S.flow (n : ℝ) (c.splitChart.symm ((c.splitChart (S.flow (-(n : ℝ)) x)).1, 0)) = x
      rw [he]
      have hi : c.splitChart.symm (c.splitChart (S.flow (-(n : ℝ)) x)) = S.flow (-(n : ℝ)) x :=
        c.splitChart.left_inv' hs
      rw [hi, ← S.flow.map_add, add_neg_cancel, S.flow.map_zero_apply]
    · intro hx
      obtain ⟨n, v, hv, rfl⟩ := Set.mem_iUnion.mp hx
      exact
        (MorseCancel.flow_time_atBot_limit_iff S.flow (n : ℝ) (c.splitChart.symm (v, 0))
              p.val).mpr
          (hpoint v hv)

private theorem MorseCancel.exists_smooth_ball_parametrization {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ} (hd : Module.finrank ℝ V ≤ d) {r : ℝ}
    (hr : 0 < r) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) → V, ContDiff ℝ ∞ ψ ∧ Set.range ψ = Metric.ball 0 r := by
  let W := EuclideanSpace ℝ (Fin (d - Module.finrank ℝ V))
  let L : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (V × W) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin, W]
        omega)
  let π : EuclideanSpace ℝ (Fin d) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V W).comp L.toContinuousLinearMap
  have hπ : Function.Surjective π := by
    intro v
    refine ⟨L.symm (v, 0), ?_⟩
    change (L (L.symm (v, 0))).1 = v
    rw [L.apply_symm_apply]
  let B := OpenPartialHomeomorph.univBall (0 : V) r
  let ψ : EuclideanSpace ℝ (Fin d) → V := B ∘ π
  have hψ : ContDiff ℝ ∞ ψ := OpenPartialHomeomorph.contDiff_univBall.comp π.contDiff
  refine ⟨ψ, hψ, ?_⟩
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    have hm : π z ∈ B.source := by rw [OpenPartialHomeomorph.univBall_source]; trivial
    have hh := B.map_source hm
    rwa [OpenPartialHomeomorph.univBall_target _ hr] at hh
  · intro hv
    have hvt : v ∈ B.target := by rw [OpenPartialHomeomorph.univBall_target _ hr]; exact hv
    obtain ⟨z, hz⟩ := hπ (B.symm v)
    refine ⟨z, ?_⟩
    change B (π z) = v
    rw [hz]
    exact B.right_inv hvt

private theorem MorseCancel.exists_global_smooth_image_of_ball {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {d : ℕ} (hd : Module.finrank ℝ V ≤ d) {r : ℝ} (hr : 0 < r) {f : V → M}
    (hf : ContMDiffOn 𝓘(ℝ, V) I ∞ f (Metric.ball 0 r)) :
    ∃ g : EuclideanSpace ℝ (Fin d) → M,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I ∞ g ∧ Set.range g = f '' Metric.ball 0 r := by
  obtain ⟨ψ, hψ, hrange⟩ := exists_smooth_ball_parametrization hd hr
  refine ⟨f ∘ ψ, ?_, ?_⟩
  · intro x
    have hx : ψ x ∈ Metric.ball (0 : V) r := hrange ▸ Set.mem_range_self x
    exact (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)).comp x hψ.contMDiff.contMDiffAt
  · rw [Set.range_comp, hrange]

private theorem Degree.FlowCancellation.native_flow_eq_on_positive_halfline {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W) {x : M}
    (hagrees : ∀ t : ℝ, 0 ≤ t → W (G t x) = V (G t x)) : ∀ t : ℝ, 0 ≤ t → G t x = F t x := by
  intro t ht
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]
  · have hc : IsMIntegralCurveOn (fun s => G s x) V (Set.Ioo (0 : ℝ) t) := by
      intro s hs
      have hd := hG x s
      rw [hagrees s hs.1.le] at hd
      exact hd.hasMFDerivWithinAt
    have hh :=
      Degree.FlowSuspension.native_flow_segment_endpoints hV F hF ht
        (hG x).continuous.continuousOn hc
    simpa only [sub_zero, G.map_zero_apply] using hh.symm

private theorem Degree.FlowCancellation.native_flow_eq_on_negative_halfline {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W) {x : M}
    (hagrees : ∀ t : ℝ, t ≤ 0 → W (G t x) = V (G t x)) : ∀ t : ℝ, t ≤ 0 → G t x = F t x := by
  intro t ht
  rcases ht.lt_or_eq with ht | ht
  · have hc : IsMIntegralCurveOn (fun s => G s x) V (Set.Ioo t (0 : ℝ)) := by
      intro s hs
      have hd := hG x s
      rw [hagrees s hs.2.le] at hd
      exact hd.hasMFDerivWithinAt
    have hh :=
      Degree.FlowSuspension.native_flow_segment_endpoints hV F hF ht
        (hG x).continuous.continuousOn hc
    have he := congrArg (F t) hh
    simpa only [zero_sub, ← F.map_add, add_neg_cancel, F.map_zero_apply, G.map_zero_apply] using
      he
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]

public
theorem Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {x p q : X}
    (hp : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 q)) {c : ℝ} (hpc : c < f p)
    (hqc : f q < c) : ∃ t, f (F t x) = c := by
  have htop : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f q)) :=
    hf.continuousAt.tendsto.comp hq
  have hbot : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hp
  obtain ⟨s, hs⟩ := (htop.eventually (eventually_lt_nhds hqc)).exists
  obtain ⟨t, ht⟩ := (hbot.eventually (eventually_gt_nhds hpc)).exists
  exact
    mem_range_of_exists_le_of_exists_ge (hf.comp (F.continuous continuous_id continuous_const))
      ⟨s, hs.le⟩ ⟨t, ht.le⟩

private def MorseCancel.forwardHighBasins {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (a : ℝ) : Set M :=
  {x |
    ∃ p : Smale.ManifoldMorse.criticalPoints E f,
      a ≤ f p ∧ Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)}

private def MorseCancel.backwardLowBasins {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (a : ℝ) : Set M :=
  {x |
    ∃ p : Smale.ManifoldMorse.criticalPoints E f,
      f p ≤ a ∧ Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)}

private theorem MorseCancel.forwardHighBasins_eq_inter {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : forwardHighBasins S a = ⋂ t : ℝ, {x | a ≤ f (S.flow t x)} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact hp.trans (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t)
  · intro hbound
    obtain ⟨-, -, q, hq, -, hlim, -⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    refine ⟨⟨q, hq⟩, ?_, hlim⟩
    exact
      ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
        (Filter.Eventually.of_forall hbound)

private theorem MorseCancel.backwardLowBasins_eq_inter {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : backwardLowBasins S a = ⋂ t : ℝ, {x | f (S.flow t x) ≤ a} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t).trans hp
  · intro hbound
    obtain ⟨p, hp, -, -, hlim, -, -⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    refine ⟨⟨p, hp⟩, ?_, hlim⟩
    exact
      le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
        (Filter.Eventually.of_forall hbound)

private theorem MorseCancel.isClosed_endpoint_obstruction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : IsClosed (forwardHighBasins S a ∪ backwardLowBasins S a) := by
  rw [forwardHighBasins_eq_inter S hf, backwardLowBasins_eq_inter S hf]
  apply IsClosed.union
  · exact
      isClosed_iInter
        (fun t =>
          isClosed_le continuous_const
            (hf.continuous.comp (S.flow.continuous continuous_const continuous_id)))
  · exact
      isClosed_iInter
        (fun t =>
          isClosed_le (hf.continuous.comp (S.flow.continuous continuous_const continuous_id))
            continuous_const)

private theorem
    MorseCancel.levelBasin_compl_eq_endpoint_obstruction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    (Degree.FlowCancellation.levelBasin S.flow f a)ᶜ =
      forwardHighBasins S a ∪ backwardLowBasins S a := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, q, hq, hback, hforward, -⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    by_cases hqa : a ≤ f q
    · exact Or.inl ⟨⟨q, hq⟩, hqa, hforward⟩
    by_cases hpa : f p ≤ a
    · exact Or.inr ⟨⟨p, hp⟩, hpa, hback⟩
    exact
      False.elim
        (hx
          (Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
            hback hforward (lt_of_not_ge hpa) (lt_of_not_ge hqa)))
  · intro hx hcross
    obtain ⟨t, ht⟩ := hcross
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    rcases hx with ⟨p, hp, hlim⟩ | ⟨p, hp, hlim⟩
    · have hh := hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hh hp) p.property
    · have hh := hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hp hh) p.property

private theorem
    AdaptedWindows.exists_forward_basin_global_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hd : Module.finrank ℝ E - MorseCancel.nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
        {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} =
          ⋃ n, Set.range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_forward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.PositiveCoordinates ≤ d := by
    have hh := (S.data p).chart.finrank_negative_add_positive
    rw [MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart] at hd
    omega
  choose g hg hrange using
    (fun n => MorseCancel.exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact Set.iUnion_congr (fun n => (hrange n).symm)

private theorem
    AdaptedWindows.exists_backward_basin_global_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hd : MorseCancel.nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
        {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)} =
          ⋃ n, Set.range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_backward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.NegativeCoordinates ≤ d := by
    rwa [MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart] at hd
  choose g hg hrange using
    (fun n => MorseCancel.exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact Set.iUnion_congr (fun n => (hrange n).symm)

private abbrev MorseCancel.EndpointBasinIndex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} (a : ℝ) :=
  ({ p : Smale.ManifoldMorse.criticalPoints E f // a ≤ f p.val } × ℕ) ⊕
    ({ p : Smale.ManifoldMorse.criticalPoints E f // f p.val ≤ a } × ℕ)

private theorem MorseCancel.endpointBasinIndex_countable {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (a : ℝ) : Countable (EndpointBasinIndex (E := E) (f := f) a) := by
  let _ := S.finite.fintype
  unfold EndpointBasinIndex
  infer_instance

private theorem AdaptedWindows.exists_endpoint_obstruction_global_images {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) {d : ℕ}
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancel.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d) :
    ∃ g : MorseCancel.EndpointBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
        MorseCancel.forwardHighBasins S a ∪ MorseCancel.backwardLowBasins S a =
          ⋃ i, Set.range (g i) := by
  choose gF hgF hF using
    (fun p : { p : Smale.ManifoldMorse.criticalPoints E f // a ≤ f p.val } =>
      S.exists_forward_basin_global_images hf p.val (hhigh p.val p.property))
  choose gB hgB hB using
    (fun p : { p : Smale.ManifoldMorse.criticalPoints E f // f p.val ≤ a } =>
      S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  let g : MorseCancel.EndpointBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M :=
    Sum.elim (fun i => gF i.1 i.2) (fun i => gB i.1 i.2)
  refine ⟨g, ?_, ?_⟩
  · intro i
    rcases i with ⟨p, n⟩ | ⟨p, n⟩
    · exact hgF p n
    · exact hgB p n
  · ext x
    constructor
    · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
      · have hh : x ∈ ⋃ n, Set.range (gF ⟨p, hp⟩ n) := (hF ⟨p, hp⟩) ▸ hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨Sum.inl (⟨p, hp⟩, n), hn⟩
      · have hh : x ∈ ⋃ n, Set.range (gB ⟨p, hp⟩ n) := (hB ⟨p, hp⟩) ▸ hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨p, hp⟩, n), hn⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rcases i with ⟨p, n⟩ | ⟨p, n⟩
      · have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val.val)} :=
          by
          rw [hF p]
          exact Set.mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inl ⟨p.val, p.property, hh⟩
      · have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val.val)} :=
          by
          rw [hB p]
          exact Set.mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inr ⟨p.val, p.property, hh⟩

private theorem MorseCancel.isClosed_backwardLowBasins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) : IsClosed (backwardLowBasins S a) := by
  rw [backwardLowBasins_eq_inter S hf]
  exact
    isClosed_iInter
      (fun t =>
        isClosed_le (hf.continuous.comp (S.flow.continuous continuous_const continuous_id))
          continuous_const)

private abbrev
    MorseCancel.LowBackwardBasinIndex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} (a : ℝ) :=
  { p : Smale.ManifoldMorse.criticalPoints E f // f p.val ≤ a } × ℕ

private theorem MorseCancel.lowBackwardBasinIndex_countable {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (a : ℝ) : Countable (LowBackwardBasinIndex (E := E) (f := f) a) := by
  let _ := S.finite.fintype
  unfold LowBackwardBasinIndex
  infer_instance

private theorem
    AdaptedWindows.exists_low_backward_obstruction_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) {d : ℕ}
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d) :
    ∃ g : MorseCancel.LowBackwardBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
        MorseCancel.backwardLowBasins S a = ⋃ i, Set.range (g i) := by
  choose g hg hcover using
    (fun p : { p : Smale.ManifoldMorse.criticalPoints E f // f p.val ≤ a } =>
      S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  refine ⟨fun i => g i.1 i.2, fun i => hg i.1 i.2, ?_⟩
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    have hh : x ∈ ⋃ n, Set.range (g ⟨p, hp⟩ n) := (hcover ⟨p, hp⟩) ▸ hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
    exact Set.mem_iUnion.mpr ⟨(⟨p, hp⟩, n), hn⟩
  · intro hx
    obtain ⟨⟨p, n⟩, hn⟩ := Set.mem_iUnion.mp hx
    have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val.val)} := by
      rw [hcover p]
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    exact ⟨p.val, p.property, hh⟩

private theorem MorseCancel.contMDiff_discrete_family {ι V E H M : Type*} [TopologicalSpace ι]
    [DiscreteTopology ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] (f : ι → V → M) (hf : ∀ i, ContMDiff 𝓘(ℝ, V) I ∞ (f i)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) ι := ChartedSpace.ofDiscreteTopology
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun p : ι × V => f p.1 p.2) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) ι := ChartedSpace.ofDiscreteTopology
  change ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun p : ι × V => f p.1 p.2)
  intro p
  have hg :
    ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun q : ι × V => f p.1 q.2)
      p :=
    (hf p.1).contMDiffAt.comp p contMDiffAt_snd
  apply hg.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : ι × V in 𝓝 p, q.1 ∈ ({ p.1 } : Set ι) :=
    ((isOpen_discrete ({ p.1 } : Set ι)).preimage continuous_fst).mem_nhds (Set.mem_singleton _)
  filter_upwards [hnear] with q hq
  rw [Set.mem_singleton_iff.mp hq]

private theorem MorseCancel.range_discrete_family {ι V M : Type*}
    (f : ι → V → M) : Set.range (fun p : ι × V => f p.1 p.2) = ⋃ i, Set.range (f i) := by
  ext x
  constructor
  · rintro ⟨⟨i, v⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, v, rfl⟩
  · intro hx
    obtain ⟨i, v, hv⟩ := Set.mem_iUnion.mp hx
    exact ⟨(i, v), hv⟩

private theorem MorseCancel.joinedIn_sublevel_of_forward_limit {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {x p : X} {a : ℝ} (hx : f x ≤ a)
    (hp : f p < a) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    JoinedIn {y : X | f y ≤ a} x p := by
  have hU : {y : X | f y < a} ∈ 𝓝 p := (isOpen_lt hf continuous_const).mem_nhds hp
  have hC := pathComponentIn_mem_nhds hU
  obtain ⟨T, hT, hFT⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and (hlim.eventually hC)).exists
  have htail : JoinedIn {y : X | f y ≤ a} (F T x) p :=
    (show JoinedIn {y : X | f y < a} p (F T x) from hFT).symm.mono
      (fun y hy => (show f y < a from hy).le)
  have hsegment : JoinedIn {y : X | f y ≤ a} x (F T x) := by
    let γ : Path x (F T x) :=
      { toFun := fun u => F ((u : ℝ) * T) x
        continuous_toFun := F.continuous (continuous_subtype_val.mul_const T) continuous_const
        source' := by simp
        target' := by simp }
    refine ⟨γ, fun u => ?_⟩
    have htime : 0 ≤ (u : ℝ) * T := mul_nonneg u.property.1 hT
    have hh := hmono x htime
    have hh' : f (F ((u : ℝ) * T) x) ≤ f x := by simpa only [F.map_zero_apply] using hh
    exact hh'.trans hx
  exact hsegment.trans htail

private theorem MorseCancel.joined_sublevel_of_common_forward_limit {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {a : ℝ} (x y : { z : X // f z ≤ a }) {p : X}
    (hp : f p < a) (hx : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hy : Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) : Joined x y := by
  exact
    ((joinedIn_sublevel_of_forward_limit F hf hmono x.property hp hx).trans
        (joinedIn_sublevel_of_forward_limit F hf hmono y.property hp hy).symm).joined_subtype

private theorem MorseCancel.joinedIn_open_forward_basin {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) (p : X)
    (hopen : IsOpen {x : X | Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)})
    (hp : Filter.Tendsto (fun t => F t p) Filter.atTop (𝓝 p)) {x : X}
    (hx : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    JoinedIn {y : X | Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)} x p := by
  let B : Set X := {y | Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)}
  have hC := pathComponentIn_mem_nhds (hopen.mem_nhds hp)
  obtain ⟨T, hT⟩ := (hx.eventually hC).exists
  have htail : JoinedIn B (F T x) p := (show JoinedIn B p (F T x) from hT).symm
  let γ : Path x (F T x) :=
    { toFun := fun u => F ((u : ℝ) * T) x
      continuous_toFun := F.continuous (continuous_subtype_val.mul_const T) continuous_const
      source' := by simp
      target' := by simp }
  have hsegment : JoinedIn B x (F T x) := by
    refine ⟨γ, fun u => ?_⟩
    exact (flow_time_atTop_limit_iff F ((u : ℝ) * T) x p).mpr hx
  exact hsegment.trans htail

private theorem AdaptedWindows.joinedIn_minimum_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 0) {x y : M}
    (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val))
    (hy : Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val)) :
    JoinedIn {z : M | Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val)} x y := by
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  have hpp : Filter.Tendsto (fun t => S.flow t p.val) Filter.atTop (𝓝 p.val) := by
    have heq : (fun t => S.flow t p.val) = fun _ => p.val :=
      funext
        (fun t =>
          Smale.FlowConstruction.flow_fixed_of_zero (S.smooth.of_le (by simp)) S.flow S.integral
            (S.zero p p.property) t)
    rw [heq]
    exact tendsto_const_nhds
  have hopen := S.isOpen_minimum_forward_basin hf p hp
  exact
    (MorseCancel.joinedIn_open_forward_basin S.flow p.val hopen hpp hx).trans
      (MorseCancel.joinedIn_open_forward_basin S.flow p.val hopen hpp hy).symm

private theorem Degree.SmoothODE.scalar_partial_invertible {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {F : P × ℝ → ℝ} {p : P} {t v : ℝ} (hF : ContDiffAt ℝ ∞ F (p, t))
    (htime : HasDerivAt (fun s : ℝ => F (p, s)) v t) (hv : v ≠ 0) :
    ((fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inr ℝ P ℝ)).IsInvertible := by
  have hd :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp t
      ((hasFDerivAt_const p t).prodMk (hasFDerivAt_id t))
  change
    HasFDerivAt (fun s : ℝ => F (p, s)) ((fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inr ℝ P ℝ))
      t at hd
  have heq := hd.unique htime.hasFDerivAt
  let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ v hv).toContinuousLinearEquiv
  refine ⟨L, ?_⟩
  rw [heq]
  apply ContinuousLinearMap.ext
  intro r
  change v * r = r * v
  exact mul_comm v r

private theorem Degree.SmoothODE.exists_smooth_scalar_time_germ {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] {F : P × ℝ → ℝ} {p : P} {t c v : ℝ}
    (hF : ContDiffAt ℝ ∞ F (p, t)) (hlevel : F (p, t) = c)
    (htime : HasDerivAt (fun s : ℝ => F (p, s)) v t) (hv : v ≠ 0) :
    ∃ θ : P → ℝ, θ p = t ∧ ContDiffAt ℝ ∞ θ p ∧ ∀ᶠ q in 𝓝 p, F (q, θ q) = c := by
  have hinv := scalar_partial_invertible hF htime hv
  let θ := hF.implicitFunction (by simp) hinv
  refine
    ⟨θ, hF.implicitFunction_apply_self (by simp) hinv,
      hF.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  filter_upwards [hF.eventually_apply_implicitFunction (by simp) hinv] with q hq
  exact hq.trans hlevel

private theorem Degree.FlowCancellation.exists_native_smooth_time_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {H : M × ℝ → ℝ} {p : M} {t c v : ℝ}
    (hH : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (p, t)) (hlevel : H (p, t) = c)
    (htime : HasDerivAt (fun s : ℝ => H (p, s)) v t) (hv : v ≠ 0) :
    ∃ θ : M → ℝ, θ p = t ∧ ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧ ∀ᶠ q in 𝓝 p, H (q, θ q) = c := by
  let e := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) p
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hz : e p ∈ e.target := e.map_source' hp
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e p :=
    (e.contMDiffOn p hp).contMDiffAt (e.open_source.mem_nhds hp)
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e p) :=
    (e.symm.contMDiffOn (e p) hz).contMDiffAt (e.open_target.mem_nhds hz)
  let B (q : E × ℝ) : M × ℝ := (e.symm q.1, q.2)
  let F : E × ℝ → ℝ := H ∘ B
  have hleft : e.symm (e p) = p := e.left_inv' hp
  have hB : ContMDiffAt 𝓘(ℝ, E × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞ B (e p, t) := by
    have hfst : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞ (Prod.fst : E × ℝ → E) (e p, t) :=
      contDiffAt_fst.contMDiffAt
    have hfirst := hi.comp (e p, t) hfst
    exact hfirst.prodMk contDiffAt_snd.contMDiffAt
  have hB0 : B (e p, t) = (p, t) := Prod.ext hleft rfl
  have hH' : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (B (e p, t)) := by
    rw [hB0]
    exact hH
  have hF : ContDiffAt ℝ ∞ F (e p, t) := (hH'.comp (e p, t) hB).contDiffAt
  have hFtime : (fun s : ℝ => F (e p, s)) = fun s => H (p, s) := by
    funext s
    change H (e.symm (e p), s) = H (p, s)
    rw [hleft]
  have hFt : HasDerivAt (fun s : ℝ => F (e p, s)) v t := by rw [hFtime]; exact htime
  have hFc : F (e p, t) = c := by
    change H (B (e p, t)) = c
    rw [hB0]
    exact hlevel
  obtain ⟨θ, hθ, hsmooth, hroot⟩ := Degree.SmoothODE.exists_smooth_scalar_time_germ hF hFc hFt hv
  refine ⟨θ ∘ e, hθ, hsmooth.contMDiffAt.comp p he, ?_⟩
  filter_upwards [e.open_source.mem_nhds hp, he.continuousAt hroot] with q hq hrootq
  have hqleft : e.symm (e q) = q := e.left_inv' hq
  change H (e.symm (e q), θ (e q)) = c at hrootq
  change H (q, θ (e q)) = c
  rwa [hqleft] at hrootq

private theorem
    Degree.FlowCancellation.smooth_signed_level_time {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (levelBasin F f c) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (signedLevelTime F f c) (levelBasin F f c) ∧
        ∀ x ∈ levelBasin F f c,
          ∀ s : ℝ, signedLevelTime F f c (F s x) = signedLevelTime F f c x - s := by
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hH : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : M × ℝ => f (F q.2 q.1)) :=
    hf.comp (Degree.SmoothODE.contMDiff_native_flow hV F hcurve)
  have hgerm (p : M) (hp : p ∈ levelBasin F f c) :
    ∃ θ : M → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧ ∀ᶠ q in 𝓝 p, f (F (θ q) q) = c := by
    let t := signedLevelTime F f c p
    have hhit : f (F t p) = c := signedLevelTime_hits F f c hp
    obtain ⟨θ, -, hθ, heq⟩ :=
      exists_native_smooth_time_germ hH.contMDiffAt hhit (hder p t) (hboundary (F t p) hhit).ne
    exact ⟨θ, hθ, heq⟩
  have hB : IsOpen (levelBasin F f c) := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    obtain ⟨θ, -, heq⟩ := hgerm p hp
    exact heq.mono (fun q hq => ⟨θ q, hq⟩)
  refine ⟨hB, ?_, ?_⟩
  · intro p hp
    obtain ⟨θ, hθ, heq⟩ := hgerm p hp
    apply ContMDiffAt.contMDiffWithinAt
    apply hθ.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    exact signedLevelTime_eq_of_level F hf.continuous hD hder hboundary hq
  · intro x hx s
    exact signedLevelTime_flow F hf.continuous hD hder hboundary hx s

private theorem Degree.FlowCancellation.exists_native_level_flow_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c : ℝ} (hreg : ∀ x, f x = c → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) (z : { x : M // f x = c }) :
    letI := Smale.RegularLevel.chartedSpace hf hreg
    ∃ Φ :
      PartialDiffeomorph (𝓘(ℝ, Smale.RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({ x : M // f x = c } × ℝ) M ∞,
      Φ.source = Set.univ ∧
        Φ.target = levelBasin F f c ∧
          (∀ p, Φ p = F p.2 p.1) ∧ ∀ x ∈ Φ.target, (Φ.symm x).2 = -signedLevelTime F f c x := by
  classical
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let L := { x : M // f x = c }
  let B := levelBasin F f c
  let θ := signedLevelTime F f c
  obtain ⟨hB, hθ, htranslate⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  let r : M → L := fun x => if hx : x ∈ B then ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ else z
  let φ : L × ℝ → M := fun p => F p.2 p.1
  let ψ : M → L × ℝ := fun x => (r x, -θ x)
  have hflow := Degree.SmoothODE.contMDiff_native_flow hV F hcurve
  have hφ : ContMDiff (𝓘(ℝ, Smale.RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ φ :=
    hflow.comp
      (((Smale.RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_fst).prodMk contMDiff_snd)
  have hψ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, Smale.RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) ∞ ψ B := by
    intro x hx
    have hθx := (hθ x hx).contMDiffAt (hB.mem_nhds hx)
    have hr : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ r x := by
      apply (Smale.RegularLevel.contMDiffAt_iff_inclusion hf hreg 𝓘(ℝ, E) r x).mpr
      apply (hflow.contMDiffAt.comp x (contMDiffAt_id.prodMk hθx)).congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds hx] with y hy
      change (r y : M) = F (θ y) y
      have hyB : y ∈ B := hy
      simp only [r, dite_eq_left hyB]
    exact (hr.prodMk hθx.neg).contMDiffWithinAt
  have hD : Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) :=
    (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) :=
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hlevel (x : L) : (x : M) ∈ B := ⟨0, by simpa only [F.map_zero_apply] using x.property⟩
  have hφB (p : L × ℝ) : φ p ∈ B := (levelBasin_flow_iff F f c p.2 p.1).mpr (hlevel p.1)
  have hclock (p : L × ℝ) : θ (φ p) = -p.2 := by
    have hh := htranslate p.1 (hlevel p.1) p.2
    rw [signedLevelTime_eq_zero F hf.continuous hD hder hboundary p.1.property, zero_sub] at hh
    exact hh
  have hleft (p : L × ℝ) : ψ (φ p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      change (r (φ p) : M) = p.1
      rw [show r (φ p) = ⟨F (θ (φ p)) (φ p), signedLevelTime_hits F f c (hφB p)⟩ by
          simp only [r, dite_eq_left (hφB p)] ]
      change F (θ (φ p)) (F p.2 p.1) = p.1
      rw [hclock, ← F.map_add, neg_add_cancel, F.map_zero_apply]
    · change -θ (φ p) = p.2
      rw [hclock, neg_neg]
  have hright (x : M) (hx : x ∈ B) : φ (ψ x) = x := by
    change F (-θ x) (r x) = x
    rw [show r x = ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ by simp only [r, dite_eq_left hx] ]
    change F (-θ x) (F (θ x) x) = x
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  let Φ :
    PartialDiffeomorph (𝓘(ℝ, Smale.RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (L × ℝ) M ∞ :=
    { toFun := φ
      invFun := ψ
      source := Set.univ
      target := B
      map_source' := fun p _ => hφB p
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun p _ => hleft p
      right_inv' := hright
      open_source := isOpen_univ
      open_target := hB
      contMDiffOn_toFun := hφ.contMDiffOn
      contMDiffOn_invFun := hψ }
  exact ⟨Φ, rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩

private theorem AdaptedWindows.joinedIn_regular_level_of_endpoint_dimensions {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancel.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxa : f x = a) (hya : f y = a) (γ : Path x y) :
    JoinedIn {z : M | f z = a} x y := by
  let _ := S.finite.fintype
  let K := MorseCancel.EndpointBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancel.endpointBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun z : K × V => g z.1 z.2) :=
    MorseCancel.contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : Set.range G = (Degree.FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [MorseCancel.levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact MorseCancel.range_discrete_family g
  have hclosed : IsClosed (Set.range G) := by
    rw [hrange, MorseCancel.levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact MorseCancel.isClosed_endpoint_obstruction S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : f z = a) : z ∉ Set.range G := by
    rw [hrange, Set.mem_compl_iff, Classical.not_not]
    exact ⟨0, by simpa only [S.flow.map_zero_apply] using hz⟩
  obtain ⟨η, -, havoid⟩ :=
    MorseCancel.exists_smooth_path_avoiding_closed_image γ G hG hclosed hdim' (hnot x hxa)
      (hnot y hya)
  have hcross (t : unitInterval) : η t ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
    have hh := havoid t
    simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using hh
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let xL : { z : M // f z = a } := ⟨x, hxa⟩
  let yL : { z : M // f z = a } := ⟨y, hya⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
      (fun z hz => S.descent z (hreg z hz)) xL
  have hcont : Continuous (fun t : unitInterval => Φ.symm (η t)) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous η.continuous
      (fun t => htarget.symm ▸ hcross t)
  have hinverse (z : { w : M // f w = a }) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let ξ : Path x y :=
    { toFun := fun t => (Φ.symm (η t)).1.val
      continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
      source' := by
        rw [η.source]
        exact congrArg (fun z : { w : M // f w = a } × ℝ => z.1.val) (hinverse xL)
      target' := by
        rw [η.target]
        exact congrArg (fun z : { w : M // f w = a } × ℝ => z.1.val) (hinverse yL) }
  exact ⟨ξ, fun t => (Φ.symm (η t)).1.property⟩

private theorem AdaptedWindows.pathConnectedSpace_regular_level_of_endpoint_dimensions {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancel.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) (z₀ : { z : M // f z = a }) :
    PathConnectedSpace { z : M // f z = a }
    where
  nonempty := ⟨z₀⟩
  joined x
    y :=
    (S.joinedIn_regular_level_of_endpoint_dimensions hf hreg hhigh hlow hdim x.property y.property
        (PathConnectedSpace.somePath x.val y.val)).joined_subtype

private theorem AdaptedWindows.pathConnectedSpace_middle_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PathConnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → 3 ≤ MorseCancel.nativeMorseIndex E f p)
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ 3)
    (z₀ : { z : M // f z = a }) : PathConnectedSpace { z : M // f z = a } :=
  S.pathConnectedSpace_regular_level_of_endpoint_dimensions hf hreg
    (fun p hp => by have hh := hhigh p hp; omega) hlow (by omega) z₀

private theorem AdaptedWindows.pathConnectedSpace_index_three_upper_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (p : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 3)
    (z₀ : (S.data p).UpperLevel) : PathConnectedSpace (S.data p).UpperLevel := by
  apply S.pathConnectedSpace_middle_level hf hdim (S.data p).upper_regular (z₀ := z₀)
  · intro r hr
    have hpr : f p < f r := (S.toSurgeryWindows.value_lt_upper p).trans_le hr
    simpa only [hp] using horder p r hpr
  · intro r hr
    rcases lt_trichotomy (f r) (f p) with h | h | h
    · simpa only [hp] using horder r p h
    · have he : r = p := Subtype.ext (S.distinct r.property p.property h)
      rw [he, hp]
    · have hsep := S.separated p r h
      have hlow := S.toSurgeryWindows.lower_lt_value r
      exact ((not_lt_of_ge hr) (hsep.trans hlow)).elim

private theorem
    Degree.MorseRearrangement.native_transverse_dimension_bound {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {f : X → N} {g : Y → N} {x : X} {y : Y}
    (ht : Smale.NativeTransversality.At I I' J f g x y) (hxy : g y = f x) :
    Module.finrank ℝ G ≤ Module.finrank ℝ D + Module.finrank ℝ Z := by
  let L : (D × Z) →L[ℝ] G := by
    exact (mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G)
  have hL : Function.Surjective L := ht hxy
  have hh := LinearMap.finrank_le_finrank_of_surjective (f := L.toLinearMap) hL
  simpa only [Module.finrank_prod] using hh

private theorem Degree.MorseRearrangement.disjoint_ranges_of_native_transverse_dimension
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] {f : X → N} {g : Y → N}
    (ht : ∀ x y, Smale.NativeTransversality.At I I' J f g x y)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    Disjoint (Set.range f) (Set.range g) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  exact (not_le_of_gt hdim) (native_transverse_dimension_bound (ht x y) (hy.trans hx.symm))

private theorem
    Degree.MorseRearrangement.native_transverse_of_ignored_factor {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {R H'' W : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [TopologicalSpace H'']
    {I'' : ModelWithCorners ℝ R H''} [TopologicalSpace W] [ChartedSpace H'' W] {f : X → N}
    {g : Y → N} {x : X} {y : Y} (w : W) (hf : MDifferentiableAt I J f x)
    (ht : Smale.NativeTransversality.At (I.prod I'') I' J (f ∘ Prod.fst) g (x, w) y) :
    Smale.NativeTransversality.At I I' J f g x y := by
  intro hxy
  have hsurj := ht hxy
  have hd :
    (mfderiv (I.prod I'') J (f ∘ Prod.fst) (x, w) : (D × R) →L[ℝ] G) =
      (mfderiv I J f x : D →L[ℝ] G).comp (ContinuousLinearMap.fst ℝ D R) := by
    rw [mfderiv_comp (x, w) hf mdifferentiableAt_fst, mfderiv_fst]
    rfl
  change
    Function.Surjective
      ((mfderiv (I.prod I'') J (f ∘ Prod.fst) (x, w) : (D × R) →L[ℝ] G).coprod
        (mfderiv I' J g y : Z →L[ℝ] G)) at hsurj
  rw [hd] at hsurj
  intro v
  obtain ⟨⟨⟨a, b⟩, c⟩, hh⟩ := hsurj v
  exact ⟨(a, c), hh⟩

private theorem Smale.ChartMapPerturbation.exists_ambient_transverse_plateau
    {D Z G F H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N]
    [ChartedSpace K N] [T2Space N] [LindelofSpace (X × Y)]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {β : F → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ c.target)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        ∃ e : Diffeomorph J J N N ∞,
          (∀ y, e y = Smale.SupportedDiffeomorph.bumpFamily c.symm β (a, y)) ∧
            (∀ y ∉ c.symm '' tsupport β, e y = y) ∧
              Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
                ∀ x,
                  f x ∈ c.source →
                    (β =ᶠ[𝓝 (c (f x))] fun _ => 1) →
                      ∀ y,
                        g y = e (f x) →
                          Function.Surjective
                            ((mfderiv I J (e ∘ f) x : D →L[ℝ] G).coprod
                              (mfderiv I' J g y : Z →L[ℝ] G)) := by
  let U : Set X := f ⁻¹' c.source
  let V : Set Y := g ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have hV : IsOpen V := c.open_source.preimage hg.continuous
  have hcf : ContMDiffOn I 𝓘(ℝ, F) ∞ (c ∘ f) U :=
    c.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ hx => hx)
  have hcg : ContMDiffOn I' 𝓘(ℝ, F) ∞ (c ∘ g) V :=
    c.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
  have hdense := Smale.TransverseCoordinates.dense_native_translations hU hV hcf hcg hdim
  obtain ⟨δ, hδ, hdiff, -, hsource⟩ :=
    Smale.SupportedDiffeomorph.exists_radius_ambient_bumpFamily c.symm hβ hcompact hsupport
  obtain ⟨η, hη, hisotopy⟩ :=
    Smale.SupportedDiffeomorph.exists_radius_bumpFamily_isotopy c.symm hβ hcompact hsupport
  obtain ⟨a, ha, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε (lt_min hδ hη))
  have hn : ‖a‖ < Min.min ε (Min.min δ η) := by simpa only [dist_zero_left] using hnorm
  have haδ := (lt_min_iff.mp (lt_min_iff.mp hn).2).1
  have haη := (lt_min_iff.mp (lt_min_iff.mp hn).2).2
  obtain ⟨e, he⟩ := hdiff a haδ
  have hsrc := hsource a haδ
  refine ⟨a, (lt_min_iff.mp hn).1, e, he, ?_, hisotopy a haη e he, ?_⟩
  · intro y hy
    rw [he]
    exact Smale.SupportedDiffeomorph.bumpFamily_fixed_outside c.symm β a hy
  · intro x hfx hx y hxy
    have hnew : e (f x) ∈ c.source := by
      rw [he]
      exact Smale.SupportedDiffeomorph.bumpFamily_mem_target c.symm β a hsrc hfx
    have hgy : g y ∈ c.source := hxy ▸ hnew
    have hcfAt := hcf.contMDiffAt (hU.mem_nhds hfx)
    have hevent : c ∘ (e ∘ f) =ᶠ[𝓝 x] fun z => c (f z) + a := by
      filter_upwards [hU.mem_nhds hfx, hx.comp_tendsto hcfAt.continuousAt] with z hz hβz
      change β (c (f z)) = 1 at hβz
      change c (e (f z)) = c (f z) + a
      rw [he]
      have hh := Smale.SupportedDiffeomorph.bumpFamily_coordinates c.symm β a hsrc hz
      change
        c (Smale.SupportedDiffeomorph.bumpFamily c.symm β (a, f z)) =
          c (f z) + β (c (f z)) • a at hh
      exact hh.trans (by rw [hβz, one_smul])
    have hcross : (c ∘ g) y = (c ∘ f) x + a := by
      change c (g y) = c (f x) + a
      rw [hxy]
      exact hevent.eq_of_nhds
    have ht := ha x hfx y hgy hcross
    have hderiv := mfderiv_eq_of_translation_germ (hcfAt.mdifferentiableAt (by simp)) hevent
    apply
      transverse_of_chart c ((e.contMDiff.comp hf).mdifferentiableAt (by simp))
        (hg.mdifferentiableAt (by simp)) hxy hnew
    rw [hderiv]
    exact ht

private structure Smale.NativeTransversality.Patch {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] (J : ModelWithCorners ℝ G K) [TopologicalSpace N]
    [ChartedSpace K N] (X : Type*) [TopologicalSpace X] where
  core : Set X
  core_compact : IsCompact core
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : G → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ chart.target
  plateau : Set N
  plateau_open : IsOpen plateau
  plateau_source : plateau ⊆ chart.source
  plateau_one : ∀ y ∈ plateau, cutoff =ᶠ[𝓝 (chart y)] fun _ => 1

private def Smale.NativeTransversality.Patch.Compatible {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] {X : Type*} [TopologicalSpace X]
    (p : Smale.NativeTransversality.Patch J X (N := N)) (f : X → N) : Prop :=
  Set.MapsTo f p.core p.plateau

private theorem Smale.NativeTransversality.exists_patch_at {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] {X : Type*} [TopologicalSpace X] [FiniteDimensional ℝ G] [J.Boundaryless]
    [IsManifold J ∞ N] [CompactSpace X] [T2Space X] {f : X → N} (hf : Continuous f) (x : X) :
    ∃ p : Patch J X (N := N), p.Compatible f ∧ x ∈ interior p.core := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  have hcx : f x ∈ c.source := mem_extChartAt_source _
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source' hcx))
  obtain ⟨β, hβ, hsupport, W, hW, hcenter, -, hone⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed (K := {c (f x)}) (U :=
      Metric.ball (c (f x)) r) isClosed_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have hcompact : HasCompactSupport β :=
    (ProperSpace.isCompact_closedBall (c (f x)) r).of_isClosed_subset (isClosed_tsupport β)
      (hsupport.trans Metric.ball_subset_closedBall)
  let O : Set N := c.source ∩ c ⁻¹' W
  have hO : IsOpen O := c.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_source hW
  have hfx : f x ∈ O := ⟨hcx, hcenter (Set.mem_singleton _)⟩
  obtain ⟨C, hC, -, hxC, hCO⟩ :=
    exists_compact_closed_between (isCompact_singleton (x := x)) (hO.preimage hf)
      (Set.singleton_subset_iff.mpr hfx)
  let p : Patch J X (N := N) :=
    { core := C
      core_compact := hC
      chart := c
      cutoff := β
      cutoff_smooth := hβ
      cutoff_compact := hcompact
      cutoff_support := hsupport.trans hball
      plateau := O
      plateau_open := hO
      plateau_source := Set.inter_subset_left
      plateau_one := by
        intro y hy
        filter_upwards [hW.mem_nhds hy.2] with z hz
        exact hone hz }
  exact ⟨p, hCO, hxC (Set.mem_singleton x)⟩

private theorem Smale.NativeTransversality.exists_patch_step {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] (p : ι → Patch J X (N := N)) (i : ι)
    {f : X → N} {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {C : Set X}
    (hC : IsCompact C) (htrans : ∀ x ∈ C, ∀ y, At I I' J f g x y) :
    ∃ e : Diffeomorph J J N N ∞,
      (∀ j, (p j).Compatible (e ∘ f)) ∧
        (∀ x ∈ C ∪ (p i).core, ∀ y, At I I' J (e ∘ f) g x y) ∧
          (∀ y ∉ (p i).chart.symm '' tsupport (p i).cutoff, e y = y) ∧
            Smale.SupportedDiffeomorph.IsotopicToIdentity e := by
  let A : G × X → N := fun q =>
    Smale.SupportedDiffeomorph.bumpFamily (p i).chart.symm (p i).cutoff (q.1, f q.2)
  have hkeep : ∀ᶠ a in 𝓝 (0 : G), ∀ j, (p j).Compatible (fun x => A (a, x)) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open (p i).chart.symm
        (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hf.continuous
        (p j).core_compact (p j).plateau_open (hcompatible j)
  obtain ⟨δ, hδ, -, hsmooth, -⟩ :=
    Smale.SupportedDiffeomorph.exists_radius_ambient_bumpFamily (p i).chart.symm
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support
  have hA : ContMDiffOn (𝓘(ℝ, G).prod I) J ∞ A (Metric.ball (0 : G) δ ×ˢ Set.univ) := by
    intro q hq
    have hsmall : ‖q.1‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hq.1
    have hpair :
      ContMDiffAt (𝓘(ℝ, G).prod I) (𝓘(ℝ, G).prod J) ∞ (fun r : G × X => (r.1, f r.2)) q :=
      contMDiffAt_fst.prodMk (hf.comp contMDiff_snd).contMDiffAt
    exact ((hsmooth (q.1, f q.2) hsmall).comp q hpair).contMDiffWithinAt
  have hzero : (fun x => A (0, x)) = f := by
    funext x
    exact Smale.SupportedDiffeomorph.bumpFamily_zero _ _ _
  have hregular :
    ∀ᶠ a in 𝓝 (0 : G), ∀ z ∈ C ×ˢ (Set.univ : Set Y), At I I' J (fun x => A (a, x)) g z.1 z.2 := by
    apply
      eventually_on_compact Metric.isOpen_ball hA hg hdim (hC.prod isCompact_univ)
        (Metric.mem_ball_self hδ)
    intro z hz
    rw [hzero]
    exact htrans z.1 hz.1 z.2
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp (hkeep.and hregular)
  obtain ⟨a, ha, e, he, hfixed, hisotopy, hnew⟩ :=
    Smale.ChartMapPerturbation.exists_ambient_transverse_plateau (p i).chart hf hg
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hdim hε
  have hgood :=
    hsmall
      (show a ∈ Metric.ball (0 : G) ε by simpa only [Metric.mem_ball, dist_zero_right] using ha)
  have heq : (fun x => A (a, x)) = e ∘ f := funext (fun x => (he (f x)).symm)
  refine ⟨e, ?_, ?_, hfixed, hisotopy⟩
  · intro j
    exact heq ▸ hgood.1 j
  · intro x hx y
    rcases hx with hx | hx
    · exact heq ▸ hgood.2 (x, y) ⟨hx, Set.mem_univ y⟩
    · intro hxy
      have hplateau := hcompatible i hx
      exact hnew x ((p i).plateau_source hplateau) ((p i).plateau_one _ hplateau) y hxy

private theorem
    Smale.NativeTransversality.exists_finite_patch_diffeomorph {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] (p : ι → Patch J X (N := N)) {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) (s : Finset ι) :
    ∃ e : Diffeomorph J J N N ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
        (∀ j, (p j).Compatible (e ∘ f)) ∧
          ∀ j ∈ s, ∀ x ∈ (p j).core, ∀ y, At I I' J (e ∘ f) g x y := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    refine
      ⟨Diffeomorph.refl J N ∞, Smale.SupportedDiffeomorph.isotopicToIdentity_refl, hcompatible,
        ?_⟩
    intro j hj
    simp at hj
  | @insert i s _ ih =>
    obtain ⟨e₁, hiso₁, hc₁, ht₁⟩ := ih
    let C : Set X := ⋃ j ∈ s, (p j).core
    have hC : IsCompact C := s.isCompact_biUnion (fun j _ => (p j).core_compact)
    have htrans : ∀ x ∈ C, ∀ y, At I I' J (e₁ ∘ f) g x y := by
      intro x hx y
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact ht₁ j hj x hxj y
    obtain ⟨e₂, hc₂, ht₂, -, hiso₂⟩ :=
      exists_patch_step p i (e₁.contMDiff.comp hf) hg hc₁ hdim hC htrans
    refine ⟨e₁.trans e₂, hiso₁.trans hiso₂, hc₂, ?_⟩
    intro j hj x hx y
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact ht₂ x (Or.inr hx) y
    · exact ht₂ x (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hjs, hx⟩)) y

private theorem Smale.NativeTransversality.exists_ambient_transverse_diffeomorph
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [CompactSpace X] [T2Space X] {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧ ∀ x y, At I I' J (e ∘ f) g x y := by
  classical
  choose p hp hx using fun x : X => exists_patch_at (J := J) hf.continuous x
  have hcover : (Set.univ : Set X) ⊆ ⋃ x : X, interior (p x).core := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover (fun x : X => interior (p x).core)
      (fun _ => isOpen_interior) hcover
  obtain ⟨e, hisotopy, -, ht⟩ :=
    exists_finite_patch_diffeomorph (fun i : s => p i.1) hf hg (fun i => hp i.1) hdim Finset.univ
  refine ⟨e, hisotopy, ?_⟩
  intro x y
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ht ⟨i, hi⟩ (Finset.mem_univ _) x (interior_subset hxi) y

private theorem Degree.MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
        Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  classical
  let d := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let f' : X × Smale.Hemisphere.Sphere d → N := f ∘ Prod.fst
  have hf' : ContMDiff (I.prod (𝓡 d)) J ∞ f' := hf.comp contMDiff_fst
  have hdim' :
    Module.finrank ℝ (D × EuclideanSpace ℝ (Fin d)) + Module.finrank ℝ Z = Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    dsimp [d]
    omega
  obtain ⟨e, he, ht⟩ :=
    Smale.NativeTransversality.exists_ambient_transverse_diffeomorph hf' hg hdim'
  have htrans : ∀ x y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Smale.Hemisphere.Sphere d := Smale.Hemisphere.point Bool.true ⟨0, by simp []⟩
    apply
      native_transverse_of_ignored_factor (I'' := 𝓡 d) w
        ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, he, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩

private def Degree.PassageHomology.twoPunctureSet {X : Type} (a b : X) : Set X :=
  ({ a }ᶜ : Set X) ∩ { b }ᶜ

private def
    Degree.PassageHomology.firstPunctureInclusion {X : Type} [TopologicalSpace X] (a b : X) :
    C(twoPunctureSet a b, ({ a }ᶜ : Set X)) :=
  ContinuousMap.inclusion Set.inter_subset_left

private def
    Degree.PassageHomology.secondPunctureInclusion {X : Type} [TopologicalSpace X] (a b : X) :
    C(twoPunctureSet a b, ({ b }ᶜ : Set X)) :=
  ContinuousMap.inclusion Set.inter_subset_right

private theorem
    Degree.PassageHomology.homology_ext_of_ambient_vanishing {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology X (n + 1))]
    {a b : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n}
    (hfirst :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a =
        SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n b)
    (hsecond :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n a =
        SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n b) :
    a = b := by
  have hz : SingularMayerVietoris.connectingHomomorphism U V hU hV hc n = 0 := by
    apply LinearMap.ext
    intro c
    have hc0 : c = 0 := Subsingleton.elim _ _
    rw [hc0, map_zero]
    rfl
  have hi : Function.Injective (SingularMayerVietoris.leftHomologyMap U V n) := by
    apply LinearMap.ker_eq_bot.mp
    rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hc n, hz, LinearMap.range_zero]
  apply hi
  rw [SingularMayerVietoris.leftHomologyMap_apply, SingularMayerVietoris.leftHomologyMap_apply,
    hfirst, hsecond]

private theorem Degree.PassageHomology.two_puncture_homology_ext {X : Type} [TopologicalSpace X]
    [T1Space X] [ContractibleSpace X] {p q : X} (hpq : p ≠ q) (n : ℕ)
    {a b : SingularMayerVietoris.SingularHomology (twoPunctureSet p q) n}
    (hfirst :
      SingularMayerVietoris.singularHomologyMap (firstPunctureInclusion p q) n a =
        SingularMayerVietoris.singularHomologyMap (firstPunctureInclusion p q) n b)
    (hsecond :
      SingularMayerVietoris.singularHomologyMap (secondPunctureInclusion p q) n a =
        SingularMayerVietoris.singularHomologyMap (secondPunctureInclusion p q) n b) :
    a = b := by
  have hc : ({ p }ᶜ : Set X) ∪ { q }ᶜ = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hz : z = p
    · exact Or.inr (fun hq => hpq (hz.symm.trans hq))
    · exact Or.inl hz
  let _ :=
    PeriodTorusHigherHomology.contractible_homology_subsingleton X (n + 1) (Nat.succ_ne_zero n)
  exact
    homology_ext_of_ambient_vanishing _ _ isOpen_compl_singleton isOpen_compl_singleton hc n
      hfirst hsecond

private theorem Degree.PassageHomology.affine_sphere_ne_of_norm_ne {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p c : E} {r : ℝ} (hr : 0 ≤ r) (h : ‖c - p‖ ≠ r)
    (u : Metric.sphere (0 : E) 1) : c + r • u.val ≠ p := by
  intro he
  apply h
  have hvalue : r • u.val = p - c := by rw [← he, add_sub_cancel_left]
  calc
    ‖c - p‖ = ‖p - c‖ := norm_sub_rev c p
    _ = ‖r • u.val‖ := (congrArg Norm.norm hvalue.symm)
    _ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mem_sphere_zero_iff_norm.mp u.property,
        mul_one]

private def
    Degree.PassageHomology.puncturedSphereMap {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p c : E) (r : ℝ) (h : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ p) :
    C(Metric.sphere (0 : E) 1, ({ p }ᶜ : Set E))
    where
  toFun u := ⟨c + r • u.val, h u⟩
  continuous_toFun :=
    (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _

private theorem Degree.PassageHomology.puncturedSphereMap_homotopic_of_family {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : E) (c : C(unitInterval, E))
    (r : C(unitInterval, ℝ)) {c₀ c₁ : E} {r₀ r₁ : ℝ} (hc₀ : c 0 = c₀) (hc₁ : c 1 = c₁)
    (hr₀ : r 0 = r₀) (hr₁ : r 1 = r₁)
    (h : ∀ t, ∀ u : Metric.sphere (0 : E) 1, c t + r t • u.val ≠ p)
    (h₀ : ∀ u : Metric.sphere (0 : E) 1, c₀ + r₀ • u.val ≠ p)
    (h₁ : ∀ u : Metric.sphere (0 : E) 1, c₁ + r₁ • u.val ≠ p) :
    (puncturedSphereMap p c₀ r₀ h₀).Homotopic (puncturedSphereMap p c₁ r₁ h₁) := by
  refine
    ⟨{  toFun := fun z => ⟨c z.1 + r z.1 • z.2.val, h z.1 z.2⟩
        continuous_toFun :=
          ((c.continuous.comp continuous_fst).add
                ((r.continuous.comp continuous_fst).smul
                  (continuous_subtype_val.comp continuous_snd))).subtype_mk
            _
        map_zero_left := ?_
        map_one_left := ?_ }⟩
  · intro u
    apply Subtype.ext
    change c 0 + r 0 • u.val = c₀ + r₀ • u.val
    rw [hc₀, hr₀]
  · intro u
    apply Subtype.ext
    change c 1 + r 1 • u.val = c₁ + r₁ • u.val
    rw [hc₁, hr₁]

private theorem Degree.PassageHomology.puncturedSphereMap_radius_homotopic {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : E) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (h₀ : ∀ u : Metric.sphere (0 : E) 1, p + r₀ • u.val ≠ p)
    (h₁ : ∀ u : Metric.sphere (0 : E) 1, p + r₁ • u.val ≠ p) :
    (puncturedSphereMap p p r₀ h₀).Homotopic (puncturedSphereMap p p r₁ h₁) := by
  let r : C(unitInterval, ℝ) :=
    ⟨fun t => (1 - (t : ℝ)) * r₀ + (t : ℝ) * r₁,
      ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
        (continuous_subtype_val.mul continuous_const)⟩
  apply
    puncturedSphereMap_homotopic_of_family p (ContinuousMap.const _ p) r rfl rfl (by simp [r])
      (by simp [r]) _ h₀ h₁
  intro t u
  have hrt : 0 < r t := by
    change 0 < (1 - (t : ℝ)) * r₀ + (t : ℝ) * r₁
    exact
      (convex_Ioi (0 : ℝ)) hr₀ hr₁ (sub_nonneg.mpr t.property.2) t.property.1
        (sub_add_cancel 1 (t : ℝ))
  exact affine_sphere_ne_of_norm_ne hrt.le (by simpa using hrt.ne) u

private theorem Degree.PassageHomology.puncturedSphereMap_center_homotopic {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p c : E) {r : ℝ} (hinside : ‖c - p‖ < r)
    (h₀ : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ p)
    (h₁ : ∀ u : Metric.sphere (0 : E) 1, p + r • u.val ≠ p) :
    (puncturedSphereMap p c r h₀).Homotopic (puncturedSphereMap p p r h₁) := by
  let cpath : C(unitInterval, E) :=
    ⟨fun t => p + (1 - (t : ℝ)) • (c - p),
      continuous_const.add ((continuous_const.sub continuous_subtype_val).smul continuous_const)⟩
  have hc0 : cpath 0 = c := by simp [cpath]
  have hc1 : cpath 1 = p := by simp [cpath]
  apply
    puncturedSphereMap_homotopic_of_family p cpath (ContinuousMap.const _ r) hc0 hc1 rfl rfl _ h₀
      h₁
  intro t u
  have hn : ‖cpath t - p‖ ≤ ‖c - p‖ := by
    change ‖(p + (1 - (t : ℝ)) • (c - p)) - p‖ ≤ _
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ t.property.1)
  exact
    affine_sphere_ne_of_norm_ne ((norm_nonneg _).trans_lt hinside).le (hn.trans_lt hinside).ne u

private theorem Degree.PassageHomology.puncturedSphereMap_outside_nullhomotopic {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p c : E) {r : ℝ} (hr : 0 ≤ r)
    (houtside : r < ‖c - p‖) (h : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ p) :
    ∃ q : ({ p }ᶜ : Set E), (puncturedSphereMap p c r h).Homotopic (ContinuousMap.const _ q) := by
  have hcp : c ≠ p := by
    intro he
    rw [he, sub_self, norm_zero] at houtside
    exact (not_lt_of_ge hr) houtside
  have hzero : ∀ u : Metric.sphere (0 : E) 1, c + (0 : ℝ) • u.val ≠ p := by
    intro u
    simpa only [zero_smul, add_zero] using hcp
  let rpath : C(unitInterval, ℝ) :=
    ⟨fun t => (1 - (t : ℝ)) * r,
      (continuous_const.sub continuous_subtype_val).mul continuous_const⟩
  have H :=
    puncturedSphereMap_homotopic_of_family p (ContinuousMap.const _ c) rpath rfl rfl
      (by simp [rpath]) (by simp [rpath]) (h₀ := h) (h₁ := hzero)
      (by
        intro t u
        have hrt : 0 ≤ rpath t := mul_nonneg (sub_nonneg.mpr t.property.2) hr
        have hle : rpath t ≤ r := mul_le_of_le_one_left hr (sub_le_self _ t.property.1)
        exact affine_sphere_ne_of_norm_ne hrt (hle.trans_lt houtside).ne' u)
  have he :
    puncturedSphereMap p c 0 hzero = ContinuousMap.const _ (⟨c, hcp⟩ : ({ p }ᶜ : Set E)) := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    change c + (0 : ℝ) • u.val = c
    rw [zero_smul, add_zero]
  exact ⟨⟨c, hcp⟩, he ▸ H⟩

private def Degree.PassageHomology.twoPunctureSphereMap {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p q c : E) (r : ℝ) (hp : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ p)
    (hq : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ q) :
    C(Metric.sphere (0 : E) 1, twoPunctureSet p q)
    where
  toFun u := ⟨c + r • u.val, hp u, hq u⟩
  continuous_toFun :=
    (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _

private def
    Degree.PassageHomology.innerSphere {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : E)
    (r : ℝ) (hr : 0 < r) (hrb : r < ‖b‖) : C(Metric.sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b 0 r
    (affine_sphere_ne_of_norm_ne hr.le (by simpa only [sub_self, norm_zero] using hr.ne))
    (affine_sphere_ne_of_norm_ne hr.le (by simpa only [zero_sub, norm_neg] using hrb.ne'))

private def
    Degree.PassageHomology.outerSphere {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : E)
    (R : ℝ) (hbR : ‖b‖ < R) : C(Metric.sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b 0 R
    (affine_sphere_ne_of_norm_ne ((norm_nonneg b).trans_lt hbR).le
      (by simpa only [sub_self, norm_zero] using ((norm_nonneg b).trans_lt hbR).ne))
    (affine_sphere_ne_of_norm_ne ((norm_nonneg b).trans_lt hbR).le
      (by simpa only [zero_sub, norm_neg] using hbR.ne))

private def Degree.PassageHomology.linkingSphere {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E) (ε : ℝ) (hε : 0 < ε) (hεb : ε < ‖b‖) :
    C(Metric.sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b b ε
    (affine_sphere_ne_of_norm_ne hε.le (by simpa only [sub_zero] using hεb.ne'))
    (affine_sphere_ne_of_norm_ne hε.le (by simpa only [sub_self, norm_zero] using hε.ne))

private theorem
    Degree.PassageHomology.radial_sphere_homology_relation {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : E) {r R ε : ℝ} (hr : 0 < r) (hrb : r < ‖b‖) (hbR : ‖b‖ < R)
    (hε : 0 < ε) (hεb : ε < ‖b‖) (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (outerSphere b R hbR) n =
      SingularMayerVietoris.singularHomologyMap (innerSphere b r hr hrb) n +
        SingularMayerVietoris.singularHomologyMap (linkingSphere b ε hε hεb) n := by
  have hb : b ≠ 0 := norm_pos_iff.mp (hr.trans hrb)
  have hR : 0 < R := (norm_nonneg b).trans_lt hbR
  let i := firstPunctureInclusion (0 : E) b
  let j := secondPunctureInclusion (0 : E) b
  let inner := innerSphere b r hr hrb
  let outer := outerSphere b R hbR
  let link := linkingSphere b ε hε hεb
  have hio : (i.comp outer).Homotopic (i.comp inner) :=
    puncturedSphereMap_radius_homotopic 0 hR hr (fun u => (outer u).property.1)
      (fun u => (inner u).property.1)
  have hil : (i.comp link).Nullhomotopic :=
    puncturedSphereMap_outside_nullhomotopic 0 b hε.le (by simpa only [sub_zero] using hεb)
      (fun u => (link u).property.1)
  have hji : (j.comp inner).Nullhomotopic :=
    puncturedSphereMap_outside_nullhomotopic b 0 hr.le
      (by simpa only [zero_sub, norm_neg] using hrb) (fun u => (inner u).property.2)
  have hcenter : ∀ u : Metric.sphere (0 : E) 1, b + R • u.val ≠ b :=
    affine_sphere_ne_of_norm_ne hR.le (by simpa only [sub_self, norm_zero] using hR.ne)
  let center := puncturedSphereMap b b R hcenter
  have hoc : (j.comp outer).Homotopic center :=
    puncturedSphereMap_center_homotopic b 0 (by simpa only [zero_sub, norm_neg] using hbR)
      (fun u => (outer u).property.2) hcenter
  have hcl : center.Homotopic (j.comp link) :=
    puncturedSphereMap_radius_homotopic b hR hε hcenter (fun u => (link u).property.2)
  have hjo := hoc.trans hcl
  have hioMap := PeriodTorusHigherHomology.homotopic_homologyMap hio n
  have hjoMap := PeriodTorusHigherHomology.homotopic_homologyMap hjo n
  have hilMap :=
    CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic (i.comp link) hil n hn
  have hjiMap :=
    CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic (j.comp inner) hji n hn
  apply LinearMap.ext
  intro a
  change
    SingularMayerVietoris.singularHomologyMap outer n a =
      SingularMayerVietoris.singularHomologyMap inner n a +
        SingularMayerVietoris.singularHomologyMap link n a
  apply two_puncture_homology_ext hb.symm n
  · change
      SingularMayerVietoris.singularHomologyMap i n
          (SingularMayerVietoris.singularHomologyMap outer n a) =
        _
    rw [map_add]
    have ho :
      SingularMayerVietoris.singularHomologyMap i n
          (SingularMayerVietoris.singularHomologyMap outer n a) =
        SingularMayerVietoris.singularHomologyMap i n
          (SingularMayerVietoris.singularHomologyMap inner n a) := by
      simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply] using
        LinearMap.congr_fun hioMap a
    have hl :
      SingularMayerVietoris.singularHomologyMap i n
          (SingularMayerVietoris.singularHomologyMap link n a) =
        0 := by
      simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
        LinearMap.zero_apply] using LinearMap.congr_fun hilMap a
    rw [ho, hl, add_zero]
  · change
      SingularMayerVietoris.singularHomologyMap j n
          (SingularMayerVietoris.singularHomologyMap outer n a) =
        _
    rw [map_add]
    have ho :
      SingularMayerVietoris.singularHomologyMap j n
          (SingularMayerVietoris.singularHomologyMap outer n a) =
        SingularMayerVietoris.singularHomologyMap j n
          (SingularMayerVietoris.singularHomologyMap link n a) := by
      simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply] using
        LinearMap.congr_fun hjoMap a
    have hi :
      SingularMayerVietoris.singularHomologyMap j n
          (SingularMayerVietoris.singularHomologyMap inner n a) =
        0 := by
      simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
        LinearMap.zero_apply] using LinearMap.congr_fun hjiMap a
    rw [ho, hi, zero_add]

private def Degree.PassageHomology.radialCylinderHomeomorph (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : (ℝ × Metric.sphere (0 : E) 1) ≃ₜ ({0}ᶜ : Set E) :=
  ((Homeomorph.prodComm ℝ (Metric.sphere (0 : E) 1)).trans
        ((Homeomorph.refl (Metric.sphere (0 : E) 1)).prodCongr
          Real.expOrderIso.toHomeomorph)).trans
    (homeomorphUnitSphereProd E).symm

private def
    Degree.PassageHomology.cylinderPuncture {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : ℝ) (u : Metric.sphere (0 : E) 1) : E :=
  Real.exp τ • u.val

private theorem Degree.PassageHomology.norm_cylinderPuncture {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (τ : ℝ) (u : Metric.sphere (0 : E) 1) :
    ‖cylinderPuncture τ u‖ = Real.exp τ := by
  rw [cylinderPuncture, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos τ),
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

private def Degree.PassageHomology.puncturedCylinderHomeomorph {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (τ : ℝ) (u : Metric.sphere (0 : E) 1) :
    ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)) ≃ₜ twoPunctureSet 0 (cylinderPuncture τ u)
    where
  toFun
    p := by
    refine
      ⟨(radialCylinderHomeomorph E p.val).val, (radialCylinderHomeomorph E p.val).property, ?_⟩
    intro h
    have he : radialCylinderHomeomorph E p.val = radialCylinderHomeomorph E (τ, u) :=
      Subtype.ext h
    exact p.property ((radialCylinderHomeomorph E).injective he)
  invFun
    z :=
    ⟨(radialCylinderHomeomorph E).symm ⟨z.val, z.property.1⟩,
      by
      intro h
      have hh := congrArg (radialCylinderHomeomorph E) h
      rw [(radialCylinderHomeomorph E).apply_symm_apply] at hh
      exact z.property.2 (congrArg Subtype.val hh)⟩
  left_inv
    p := by
    apply Subtype.ext
    change (radialCylinderHomeomorph E).symm (radialCylinderHomeomorph E p.val) = p.val
    exact (radialCylinderHomeomorph E).symm_apply_apply p.val
  right_inv
    z := by
    apply Subtype.ext
    change
      ((radialCylinderHomeomorph E)
            ((radialCylinderHomeomorph E).symm ⟨z.val, z.property.1⟩)).val =
        z.val
    exact
      congrArg (fun w : ({0}ᶜ : Set E) => w.val)
        ((radialCylinderHomeomorph E).apply_symm_apply ⟨z.val, z.property.1⟩)
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((radialCylinderHomeomorph E).continuous.comp continuous_subtype_val)).subtype_mk
      _
  continuous_invFun := by
    have hc :
      Continuous
        (fun z : twoPunctureSet 0 (cylinderPuncture τ u) =>
          (⟨z.val, z.property.1⟩ : ({0}ᶜ : Set E))) :=
      continuous_subtype_val.subtype_mk _
    exact ((radialCylinderHomeomorph E).symm.continuous.comp hc).subtype_mk _

private def Degree.PassageHomology.cylinderSlice {E : Type} [NormedAddCommGroup E] (τ : ℝ)
    (u : Metric.sphere (0 : E) 1) (t : ℝ) (ht : t ≠ τ) :
    C(Metric.sphere (0 : E) 1, ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)))
    where
  toFun v := ⟨(t, v), fun h => ht (congrArg Prod.fst h)⟩
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _

private def Degree.PassageHomology.cylinderLink {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : ℝ) (u : Metric.sphere (0 : E) 1) (ε : ℝ) (hε : 0 < ε) (hεu : ε < Real.exp τ) :
    C(Metric.sphere (0 : E) 1, ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1))) :=
  ((puncturedCylinderHomeomorph τ u).symm : C(_, _)).comp
    (linkingSphere (cylinderPuncture τ u) ε hε (by rwa [norm_cylinderPuncture]))

private theorem Degree.PassageHomology.punctured_cylinder_endpoint_relation {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (u : Metric.sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε) (hεu : ε < Real.exp τ) (n : ℕ)
    (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (cylinderSlice τ u 1 hτ.2.ne') n =
      SingularMayerVietoris.singularHomologyMap (cylinderSlice τ u 0 hτ.1.ne) n +
        SingularMayerVietoris.singularHomologyMap (cylinderLink τ u ε hε hεu) n := by
  let b := cylinderPuncture τ u
  have hrb : (1 : ℝ) < ‖b‖ := by
    rw [norm_cylinderPuncture]
    exact Real.one_lt_exp_iff.mpr hτ.1
  have hbR : ‖b‖ < Real.exp 1 := by
    rw [norm_cylinderPuncture]
    exact Real.exp_lt_exp.mpr hτ.2
  have hεb : ε < ‖b‖ := by rwa [norm_cylinderPuncture]
  let inner := innerSphere b 1 zero_lt_one hrb
  let outer := outerSphere b (Real.exp 1) hbR
  let link := linkingSphere b ε hε hεb
  let e := puncturedCylinderHomeomorph τ u
  let e' : C(twoPunctureSet 0 b, ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1))) := e.symm
  have hinner : e'.comp inner = cylinderSlice τ u 0 hτ.1.ne := by
    apply ContinuousMap.ext
    intro v
    apply e.injective
    change e (e.symm (inner v)) = e (cylinderSlice τ u 0 hτ.1.ne v)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (0 : E) + 1 • v.val = Real.exp 0 • v.val
    rw [Real.exp_zero, one_smul, zero_add]
  have houter : e'.comp outer = cylinderSlice τ u 1 hτ.2.ne' := by
    apply ContinuousMap.ext
    intro v
    apply e.injective
    change e (e.symm (outer v)) = e (cylinderSlice τ u 1 hτ.2.ne' v)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (0 : E) + Real.exp 1 • v.val = Real.exp 1 • v.val
    rw [zero_add]
  have H :
    SingularMayerVietoris.singularHomologyMap (e'.comp outer) n =
      SingularMayerVietoris.singularHomologyMap (e'.comp inner) n +
        SingularMayerVietoris.singularHomologyMap (e'.comp link) n := by
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
      PeriodTorusHigherHomology.singularHomologyMap_comp,
      PeriodTorusHigherHomology.singularHomologyMap_comp]
    have hrel := radial_sphere_homology_relation b zero_lt_one hrb hbR hε hεb n hn
    change
      (SingularMayerVietoris.singularHomologyMap e' n).comp
          (SingularMayerVietoris.singularHomologyMap outer n) =
        _
    rw [hrel, LinearMap.comp_add]
  rw [hinner, houter] at H
  exact H

private theorem
    Degree.PassageHomology.punctured_cylinder_trace_relation {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Y : Type} [TopologicalSpace Y] {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (u : Metric.sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε) (hεu : ε < Real.exp τ)
    (F : C(({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)), Y)) (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (F.comp (cylinderSlice τ u 1 hτ.2.ne')) n =
      SingularMayerVietoris.singularHomologyMap (F.comp (cylinderSlice τ u 0 hτ.1.ne)) n +
        SingularMayerVietoris.singularHomologyMap (F.comp (cylinderLink τ u ε hε hεu)) n := by
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    punctured_cylinder_endpoint_relation hτ u hε hεu n hn, LinearMap.comp_add]

private def Degree.PassageHomology.clampTime : C(ℝ, ℝ) :=
  ⟨fun t => Max.max 0 (Min.min 1 t), continuous_const.max (continuous_const.min continuous_id)⟩

private theorem Degree.PassageHomology.clampTime_mem (t : ℝ) : clampTime t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private theorem Degree.PassageHomology.clampTime_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    clampTime t = t := by
  change Max.max 0 (Min.min 1 t) = t
  rw [min_eq_right ht.2, max_eq_right ht.1]

private theorem
    Degree.PassageHomology.clampTime_eq_interior_iff {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) : clampTime t = τ ↔ t = τ := by
  constructor
  · intro he
    by_cases ht0 : t ≤ 0
    · have hc : clampTime t = 0 := by
        change Max.max 0 (Min.min 1 t) = 0
        rw [min_eq_right (ht0.trans zero_le_one), max_eq_left ht0]
      exact (hτ.1.ne (hc.symm.trans he)).elim
    by_cases ht1 : 1 ≤ t
    · have hc : clampTime t = 1 := by
        change Max.max 0 (Min.min 1 t) = 1
        rw [min_eq_left ht1, max_eq_right zero_le_one]
      exact (hτ.2.ne' (hc.symm.trans he)).elim
    exact (clampTime_of_mem ⟨(lt_of_not_ge ht0).le, (lt_of_not_ge ht1).le⟩).symm.trans he
  · intro he
    subst t
    exact clampTime_of_mem ⟨hτ.1.le, hτ.2.le⟩

private def Degree.PassageHomology.puncturedPassageTrace {E X : Type} [NormedAddCommGroup E]
    [TopologicalSpace X] (H : C(ℝ × Metric.sphere (0 : E) 1, X)) (S : Set X) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (u : Metric.sphere (0 : E) 1)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v : Metric.sphere (0 : E) 1, H (t, v) ∈ S ↔ t = τ ∧ v = u) :
    C(({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)), (Sᶜ : Set X))
    where
  toFun
    p :=
    ⟨H (clampTime p.val.1, p.val.2), by
      intro hp
      have he := (hcross _ (clampTime_mem _) p.val.2).mp hp
      exact p.property (Prod.ext ((clampTime_eq_interior_iff hτ _).mp he.1) he.2)⟩
  continuous_toFun := by
    have ht :
      Continuous (fun p : ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)) => clampTime p.val.1) :=
      clampTime.continuous.comp (continuous_fst.comp continuous_subtype_val)
    have hv : Continuous (fun p : ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)) => p.val.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (H.continuous.comp (ht.prodMk hv)).subtype_mk _

private theorem Degree.PassageHomology.puncturedPassageTrace_on_interval {E X : Type}
    [NormedAddCommGroup E] [TopologicalSpace X]
    (H : C(ℝ × Metric.sphere (0 : E) 1, X)) (S : Set X) {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (u : Metric.sphere (0 : E) 1)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v : Metric.sphere (0 : E) 1, H (t, v) ∈ S ↔ t = τ ∧ v = u)
    (p : ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1))) (hp : p.val.1 ∈ Set.Icc (0 : ℝ) 1) :
    (puncturedPassageTrace H S hτ u hcross p).val = H p.val := by
  change H (clampTime p.val.1, p.val.2) = H p.val
  rw [clampTime_of_mem hp]

private theorem
    MorseCancel.exists_native_open_curve_with_germ {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] (S : TopologicalSpace.Opens N) {a : ℝ → N} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ∈ S) :
    ∃ g : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ (Subtype.val ∘ g) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → S := fun t => if h : a t ∈ S then ⟨a t, h⟩ else ⟨a t₀, ha0⟩
  let V := U ∩ a ⁻¹' (S : Set N)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU S.isOpen
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hsS : a s ∈ S := hs.2
    simp only [Function.comp_apply, A, dite_eq_left hsS]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ A V := by
    intro t ht
    have hvalAt := (ha.contMDiffAt (hU.mem_nhds ht.1)).congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff S A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨g, hg, heq⟩ := Smale.exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨g, hg, ?_⟩
  filter_upwards [heq, hval htV] with t ht hta
  exact (congrArg Subtype.val ht).trans hta

private theorem MorseCancel.exists_embedded_native_open_arc_with_local_germs {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] [FiniteDimensional ℝ G] [J.Boundaryless]
    [IsManifold J ∞ N] [T2Space N] (S : TopologicalSpace.Opens N) {a b : ℝ → N} {U V : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V) (hU : IsOpen U)
    (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ∈ S) (hb1 : b 1 ∈ S)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1))
    (γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] a) ∧
          ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
              ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨a', ha', heqa⟩ := exists_native_open_curve_with_germ S ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_native_open_curve_with_germ S hb hV h1V hb1
  have hstart : a' 0 = (⟨a 0, ha0⟩ : S) := Subtype.ext heqa.eq_of_nhds
  have hend : b' 1 = (⟨b 1, hb1⟩ : S) := Subtype.ext heqb.eq_of_nhds
  have hia' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a' 0) := by
    have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (Subtype.val ∘ a') 0) := by
      rw [heqa.mfderiv_eq]
      exact hia
    rw [mfderiv_comp 0
        ((contMDiff_subtype_val (I := J) (U := S) (n := ∞)).mdifferentiableAt (by simp))
        (ha'.mdifferentiableAt (by simp))] at hi
    intro x y hxy
    exact hi (congrArg (mfderiv J J (Subtype.val : S → N) (a' 0)) hxy)
  have hib' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b' 1) := by
    have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (Subtype.val ∘ b') 1) := by
      rw [heqb.mfderiv_eq]
      exact hib
    rw [mfderiv_comp 1
        ((contMDiff_subtype_val (I := J) (U := S) (n := ∞)).mdifferentiableAt (by simp))
        (hb'.mdifferentiableAt (by simp))] at hi
    intro x y hxy
    exact hi (congrArg (mfderiv J J (Subtype.val : S → N) (b' 1)) hxy)
  have hxy' : a' 0 ≠ b' 1 := by
    intro h
    exact hxy (heqa.eq_of_nhds.symm.trans ((congrArg Subtype.val h).trans heqb.eq_of_nhds))
  obtain ⟨g, hg, hga, hgb, hemb, hi, -⟩ :=
    Smale.exists_embedded_arc_with_endpoint_germs a' b' ha' hb' hia' hib' (γ.cast hstart hend)
      hxy' hdim (S := ∅) Set.finite_empty
  refine ⟨g, hg, ?_, ?_, hemb, hi⟩
  · filter_upwards [hga, heqa] with t hta hta'
    exact (congrArg Subtype.val hta).trans hta'
  · filter_upwards [hgb, heqb] with t htb htb'
    exact (congrArg Subtype.val htb).trans htb'

private theorem MorseCancel.injective_mfderiv_curve_translate {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {α : ℝ → N} {s c : ℝ} (hα : MDifferentiableAt 𝓘(ℝ, ℝ) J α (s + c))
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α (s + c))) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => α (t + c)) s) := by
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s :=
    (contMDiff_id.add (contMDiff_const (c := c)) :
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => t + c)).mdifferentiableAt
      (by simp)
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s = ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun t : ℝ => id t + c) s = _
    rw [fderiv_add_const, fderiv_id]
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (α ∘ (fun t : ℝ => t + c)) s)
  rw [mfderiv_comp s hα ht]
  intro x y hxy
  apply hi
  have hdx : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s x = x :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L x) hd
  have hdy : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s y = y :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L y) hd
  change
    mfderiv 𝓘(ℝ, ℝ) J α (s + c) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s x) =
      mfderiv 𝓘(ℝ, ℝ) J α (s + c) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s y) at hxy
  rw [hdx, hdy] at hxy
  exact hxy

private theorem
    MorseCancel.exists_embedded_return_arc_inside_open {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]
    (S : TopologicalSpace.Opens N) {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hinj : Set.InjOn α (Set.Icc (-R) R))
    (hderiv : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s)) (hplus : α r ∈ S)
    (hminus : α (-r) ∈ S) (γ : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) ∧
          ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
              ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let a : ℝ → N := fun t => α (t + r)
  let b : ℝ → N := fun t => α (t + (-1 - r))
  let U : Set ℝ := (fun t : ℝ => t + r) ⁻¹' Set.Ioo (-R) R
  let V : Set ℝ := (fun t : ℝ => t + (-1 - r)) ⁻¹' Set.Ioo (-R) R
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_id.add continuous_const)
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_id.add continuous_const)
  have hp : r ∈ Set.Ioo (-R) R := ⟨by linarith, hrR⟩
  have hm : -r ∈ Set.Ioo (-R) R := ⟨by linarith, by linarith⟩
  have h0U : (0 : ℝ) ∈ U := by simpa only [U, Set.mem_preimage, zero_add] using hp
  have h1V : (1 : ℝ) ∈ V := by
    change 1 + (-1 - r) ∈ Set.Ioo (-R) R
    simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using hm
  have ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U :=
    hα.comp (contMDiff_id.add contMDiff_const).contMDiffOn (fun _ ht => ht)
  have hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V :=
    hα.comp (contMDiff_id.add contMDiff_const).contMDiffOn (fun _ ht => ht)
  have ha0 : a 0 = α r := by dsimp [a]; rw [zero_add]
  have hb1 : b 1 = α (-r) := by dsimp [b]; congr 1; ring
  have hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0) := by
    apply injective_mfderiv_curve_translate
    · simpa only [zero_add] using
        (hα.contMDiffAt (Ioo_mem_nhds hp.1 hp.2)).mdifferentiableAt (by simp)
    · exact (zero_add r).symm ▸ hderiv r hp
  have hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1) := by
    apply injective_mfderiv_curve_translate
    · simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using
        (hα.contMDiffAt (Ioo_mem_nhds hm.1 hm.2)).mdifferentiableAt (by simp)
    · exact (show (1 : ℝ) + (-1 - r) = -r by ring).symm ▸ hderiv (-r) hm
  have haS : a 0 ∈ S := ha0.symm ▸ hplus
  have hbS : b 1 ∈ S := hb1.symm ▸ hminus
  have hpath : Path (⟨a 0, haS⟩ : S) (⟨b 1, hbS⟩ : S) :=
    γ.cast (Subtype.ext ha0) (Subtype.ext hb1)
  have hxy : a 0 ≠ b 1 := by
    rw [ha0, hb1]
    intro hh
    have heq := hinj ⟨hp.1.le, hp.2.le⟩ ⟨hm.1.le, hm.2.le⟩ hh
    linarith
  exact
    exists_embedded_native_open_arc_with_local_germs S ha hb hU hV h0U h1V haS hbS hia hib hpath
      hxy hdim

private theorem
    MorseCancel.exists_clean_return_endpoint_neighborhood {N : Type*}
    {α β : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R) (hinj : Set.InjOn α (Set.Icc (-R) R))
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    ∃ C : Set ℝ,
      IsClosed C ∧
        ({0, 1} : Set ℝ) ⊆ interior C ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → β t ∉ α '' Set.Icc (-r) r := by
  have hp : r ∈ Set.Ioo (-R) R := ⟨by linarith, hrR⟩
  have hm : -r ∈ Set.Ioo (-R) R := ⟨by linarith, by linarith⟩
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), β t = α (t + r) ∧ t + r ∈ Set.Ioo (-R) R := by
    have hn : ∀ᶠ t in 𝓝 (0 : ℝ), t + r ∈ Set.Ioo (-R) R :=
      ((continuous_id.add continuous_const).continuousAt.tendsto
        (show Set.Ioo (-R) R ∈ 𝓝 ((0 : ℝ) + r) by
          simpa only [zero_add] using Ioo_mem_nhds hp.1 hp.2))
    exact h0.and hn
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), β t = α (t + (-1 - r)) ∧ t + (-1 - r) ∈ Set.Ioo (-R) R := by
    have hn : ∀ᶠ t in 𝓝 (1 : ℝ), t + (-1 - r) ∈ Set.Ioo (-R) R :=
      ((continuous_id.add continuous_const).continuousAt.tendsto
        (show Set.Ioo (-R) R ∈ 𝓝 ((1 : ℝ) + (-1 - r)) by
          simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using Ioo_mem_nhds hm.1 hm.2))
    exact h1.and hn
  obtain ⟨δ₀, hδ₀, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear0
  obtain ⟨δ₁, hδ₁, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear1
  let C : Set ℝ := Metric.closedBall 0 δ₀ ∪ Metric.closedBall 1 δ₁
  have h0C : C ∈ 𝓝 (0 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ₀)
      (fun _ ht => Or.inl (Metric.ball_subset_closedBall ht))
  have h1C : C ∈ 𝓝 (1 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 1 hδ₁)
      (fun _ ht => Or.inr (Metric.ball_subset_closedBall ht))
  refine ⟨C, Metric.isClosed_closedBall.union Metric.isClosed_closedBall, ?_, ?_⟩
  · intro t ht
    rcases ht with rfl | ht
    · exact mem_interior_iff_mem_nhds.mpr h0C
    · have ht1 : t = 1 := ht
      subst t
      exact mem_interior_iff_mem_nhds.mpr h1C
  · intro t ht htB
    rintro ⟨s, hs, heq⟩
    have hsR : s ∈ Set.Icc (-R) R := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rcases ht.2 with ht0 | ht1
    · have hg := hball0 ht0
      have hts := hinj ⟨hg.2.1.le, hg.2.2.le⟩ hsR (hg.1.symm.trans heq.symm)
      have htne : t ≠ 0 := fun h => htB (Or.inl h)
      have htpos : 0 < t := lt_of_le_of_ne ht.1.1 htne.symm
      linarith [hs.2]
    · have hg := hball1 ht1
      have hts := hinj ⟨hg.2.1.le, hg.2.2.le⟩ hsR (hg.1.symm.trans heq.symm)
      have htne : t ≠ 1 := fun h => htB (Or.inr h)
      have htlt : t < 1 := lt_of_le_of_ne ht.1.2 htne
      linarith [hs.1]

private theorem Smale.ManifoldImmersion.exists_relative_embedded_avoidance_in_open_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (U : TopologicalSpace.Opens N) (f : C(E, U)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hclosed : IsClosed (Set.range g))
    (hsourceDim : Module.finrank ℝ E = 2) (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ Set.range g) :
    ∃ f' : C(E, U),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, (f' x : N) ∉ Set.range g := by
  have hclean' : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range (Smale.OpenObstacle.restrict g U) := by
    intro x hx hxB hmem
    exact hclean x hx hxB ((Smale.OpenObstacle.mem_range_restrict_iff g U (f x)).mp hmem)
  obtain ⟨f', hf', hhom, hemb, hderiv', havoid⟩ :=
    exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range f
      (Smale.OpenObstacle.restrict g U) hf (Smale.OpenObstacle.contMDiff_restrict g U hg)
      (Smale.OpenObstacle.isClosed_range_restrict g U hclosed) hsourceDim hdim hobstacle hK hC hBC
      hinj hderiv hclean'
  refine ⟨f', hf', hhom, hemb, hderiv', ?_⟩
  intro x hx hmem
  exact havoid x hx ((Smale.OpenObstacle.mem_range_restrict_iff g U (f' x)).mpr hmem)

private theorem
    Smale.ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (U : TopologicalSpace.Opens N) (f : C(E, U)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g) (hclosed : IsClosed (g '' A))
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ g '' A) {O : Set U} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, U),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              Set.MapsTo f' K O ∧ ∀ x ∈ K \ B, (f' x : N) ∉ g '' A := by
  let A' : Set (Smale.OpenObstacle.source g U) := Subtype.val ⁻¹' A
  have hclean' : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Smale.OpenObstacle.restrict g U '' A' := by
    intro x hx hxB hmem
    rw [Smale.OpenObstacle.image_restrict] at hmem
    exact hclean x hx hxB hmem
  obtain ⟨f', hf', hhom, hemb, hd, hmaps', havoid⟩ :=
    exists_embedded_image_avoidance_relative_neighborhood f (Smale.OpenObstacle.restrict g U) A'
      hf (Smale.OpenObstacle.contMDiff_restrict g U hg)
      (Smale.OpenObstacle.isClosed_image_restrict g U A hclosed) hself hobstacle hK hC hBC hinj
      hderiv hclean' hO hmaps
  refine ⟨f', hf', hhom, hemb, hd, hmaps', ?_⟩
  intro x hx hmem
  apply havoid x hx
  rw [Smale.OpenObstacle.image_restrict]
  exact hmem

private theorem Smale.ManifoldImmersion.exists_relative_embedded_avoidance_in_open
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] [CompactSpace Y]
    [SecondCountableTopology H'] (U : TopologicalSpace.Opens N) (f : C(E, U)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ Set.range g) :
    ∃ f' : C(E, U),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, (f' x : N) ∉ Set.range g := by
  let : SecondCountableTopology Y := ChartedSpace.secondCountable_of_sigmaCompact H' Y
  exact
    exists_relative_embedded_avoidance_in_open_of_isClosed_range U f g hf hg
      (isCompact_range g.continuous).isClosed hsourceDim hdim hobstacle hK hC hBC hinj hderiv
      hclean

private theorem
    MorseCancel.exists_disjoint_embedded_return_arc {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (S : TopologicalSpace.Opens N) {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hinj : Set.InjOn α (Set.Icc (-R) R))
    (hderiv : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s)) (hplus : α r ∈ S)
    (hminus : α (-r) ∈ S) (γ : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) ∧
          ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)) ∧
                ∀ t ∈ Set.Ioo (0 : ℝ) 1, (g t : N) ∉ α '' Set.Icc (-r) r := by
  obtain ⟨β, hβ, hβ0, hβ1, hemb, hβd⟩ :=
    exists_embedded_return_arc_inside_open S hr hrR hα hinj hderiv hplus hminus γ hdim
  obtain ⟨C, hC, hBC, hclean⟩ := exists_clean_return_endpoint_neighborhood hr hrR hinj hβ0 hβ1
  let Q : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-R) R, isOpen_Ioo⟩
  let q : C(Q, N) :=
    ⟨fun s => α s,
      continuous_iff_continuousAt.mpr
        (fun s =>
          (hα.continuousOn.continuousAt (isOpen_Ioo.mem_nhds s.property)).comp
            continuous_subtype_val.continuousAt)⟩
  have hq : ContMDiff 𝓘(ℝ, ℝ) J ∞ q := by
    intro s
    exact
      (hα.contMDiffAt (isOpen_Ioo.mem_nhds s.property)).comp s
        (contMDiff_subtype_val (n := ∞)).contMDiffAt
  let A : Set Q := {s | (s : ℝ) ∈ Set.Icc (-r) r}
  have hsub : Set.Icc (-r) r ⊆ Set.Ioo (-R) R := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have himage : q '' A = α '' Set.Icc (-r) r := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hsub hs⟩, hs, rfl⟩
  have hclosed : IsClosed (q '' A) := by
    rw [himage]
    exact
      (CompactIccSpace.isCompact_Icc.image_of_continuousOn (hα.continuousOn.mono hsub)).isClosed
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobstacle : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hβinj : Set.InjOn β (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hclean' : ∀ t ∈ Set.Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → (β t : N) ∉ q '' A := by
    intro t ht htB
    rw [himage]
    exact hclean t ht htB
  obtain ⟨g, hg, hhom, hembg, hdg, -, havoid⟩ :=
    Smale.ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open S β q A
      hβ hq hclosed hself hobstacle CompactIccSpace.isCompact_Icc hC hBC hβinj hβd hclean'
      isOpen_univ (fun _ _ => Set.mem_univ _)
  have h0C : C ∈ 𝓝 (0 : ℝ) := mem_interior_iff_mem_nhds.mp (hBC (Or.inl rfl))
  have h1C : C ∈ 𝓝 (1 : ℝ) := mem_interior_iff_mem_nhds.mp (hBC (Or.inr rfl))
  refine ⟨g, hg, ?_, ?_, hembg, hdg, ?_⟩
  · filter_upwards [h0C, hβ0] with t ht ht0
    exact (congrArg Subtype.val (hhom.fst_eq_snd ht)).symm.trans ht0
  · filter_upwards [h1C, hβ1] with t ht ht1
    exact (congrArg Subtype.val (hhom.fst_eq_snd ht)).symm.trans ht1
  · intro t ht hmem
    have htB : t ∉ ({0, 1} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ne_of_gt ht.1, ne_of_lt ht.2⟩
    exact havoid t ⟨⟨ht.1.le, ht.2.le⟩, htB⟩ (himage.symm ▸ hmem)

private def
    Degree.CircleGluing.periodicExtension {N : Type*} {T : ℝ} (hT : 0 < T) (f : ℝ → N) (t : ℝ) :
    N :=
  f (toIcoMod hT 0 t)

private theorem Degree.CircleGluing.periodicExtension_periodic {N : Type*} {T : ℝ} (hT : 0 < T)
    (f : ℝ → N) : Function.Periodic (periodicExtension hT f) T := fun t =>
  congrArg f (toIcoMod_add_right hT 0 t)

private theorem
    Degree.CircleGluing.periodicExtension_germ_in_fundamental_interval {N : Type*} {T : ℝ}
    (hT : 0 < T) {f : ℝ → N} (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) T) : periodicExtension hT f =ᶠ[𝓝 x] f := by
  by_cases hx0 : x = 0
  · subst x
    filter_upwards [hmatch, Ioo_mem_nhds (neg_lt_zero.mpr hT) hT] with t ht htn
    change f (toIcoMod hT 0 t) = f t
    by_cases ht0 : 0 ≤ t
    · rw [(toIcoMod_eq_self hT).mpr ⟨ht0, by simpa only [zero_add] using htn.2⟩]
    · have hmod : toIcoMod hT 0 t = t + T := by
        apply (toIcoMod_eq_iff hT).mpr
        refine ⟨⟨by linarith [htn.1], by linarith⟩, -1, ?_⟩
        simp
      rw [hmod]
      exact ht
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    filter_upwards [Ioo_mem_nhds hxpos hx.2] with t ht
    change f (toIcoMod hT 0 t) = f t
    rw [(toIcoMod_eq_self hT).mpr ⟨ht.1.le, by simpa only [zero_add] using ht.2⟩]

private theorem
    Degree.CircleGluing.periodicExtension_germ {N : Type*} {T : ℝ} (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f) (x : ℝ) :
    ∃ c : ℝ, x + c ∈ Set.Ico (0 : ℝ) T ∧ periodicExtension hT f =ᶠ[𝓝 x] (fun t => f (t + c)) := by
  let n : ℤ := toIcoDiv hT 0 x
  let c : ℝ := -(n • T)
  have hx : x + c = toIcoMod hT 0 x := by
    change x - n • T = toIcoMod hT 0 x
    rfl
  have hxc : x + c ∈ Set.Ico (0 : ℝ) T := by
    rw [hx]
    simpa only [zero_add] using toIcoMod_mem_Ico hT 0 x
  have hg := periodicExtension_germ_in_fundamental_interval hT hmatch hxc
  have ht : Filter.Tendsto (fun t : ℝ => t + c) (𝓝 x) (𝓝 (x + c)) :=
    (continuous_id.add continuous_const).continuousAt
  refine ⟨c, hxc, ?_⟩
  filter_upwards [hg.comp_tendsto ht] with t ht
  have heq : periodicExtension hT f (t + c) = periodicExtension hT f t :=
    congrArg f (toIcoMod_sub_zsmul hT 0 t n)
  exact heq.symm.trans ht

private theorem Degree.CircleGluing.periodicExtension_contMDiff {N : Type*} {T : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    (hf : ∀ t ∈ Set.Ico (0 : ℝ) T, ContMDiffAt 𝓘(ℝ, ℝ) J ∞ f t) :
    ContMDiff 𝓘(ℝ, ℝ) J ∞ (periodicExtension hT f) := by
  intro x
  obtain ⟨c, hc, heq⟩ := periodicExtension_germ hT hmatch x
  exact
    ((hf (x + c) hc).comp x (contMDiff_id.add contMDiff_const).contMDiffAt).congr_of_eventuallyEq
      heq

private theorem Degree.CircleGluing.periodicExtension_derivative_injective {N : Type*} {T : ℝ}
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    (hf : ∀ t ∈ Set.Ico (0 : ℝ) T, MDifferentiableAt 𝓘(ℝ, ℝ) J f t)
    (hi : ∀ t ∈ Set.Ico (0 : ℝ) T, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (x : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (periodicExtension hT f) x) := by
  obtain ⟨c, hc, heq⟩ := periodicExtension_germ hT hmatch x
  rw [heq.mfderiv_eq]
  exact MorseCancel.injective_mfderiv_curve_translate (hf (x + c) hc) (hi (x + c) hc)

attribute [local instance 100] Classical.propDecidable in
private def Degree.CircleGluing.joinedArc {N : Type*} (α β : ℝ → N) (r t : ℝ) : N :=
  if t ≤ 2 * r then α (t + (-r)) else β (t + (-2 * r))

private theorem
    Degree.CircleGluing.joinedArc_left {N : Type*} {α β : ℝ → N} {r t : ℝ} (ht : t ≤ 2 * r) :
    joinedArc α β r t = α (t + (-r)) :=
  ite_eq_left ht

private theorem
    Degree.CircleGluing.joinedArc_right {N : Type*} {α β : ℝ → N} {r t : ℝ} (ht : 2 * r < t) :
    joinedArc α β r t = β (t + (-2 * r)) :=
  ite_eq_right (not_le.mpr ht)

private theorem Degree.CircleGluing.joinedArc_left_germ {N : Type*} {α β : ℝ → N} {r t : ℝ}
    (ht : t < 2 * r) : joinedArc α β r =ᶠ[𝓝 t] (fun s => α (s + (-r))) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact joinedArc_left hs.le

private theorem Degree.CircleGluing.joinedArc_right_germ {N : Type*} {α β : ℝ → N} {r t : ℝ}
    (ht : 2 * r < t) : joinedArc α β r =ᶠ[𝓝 t] (fun s => β (s + (-2 * r))) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact joinedArc_right hs

private theorem Degree.CircleGluing.joinedArc_seam_germ {N : Type*} {α β : ℝ → N} {r : ℝ}
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) :
    joinedArc α β r =ᶠ[𝓝 (2 * r)] (fun s => α (s + (-r))) := by
  have ht : Filter.Tendsto (fun t : ℝ => t + (-2 * r)) (𝓝 (2 * r)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t + (-2 * r)) := continuous_id.add continuous_const
    simpa only [show 2 * r + (-2 * r) = 0 by ring] using hc.continuousAt.tendsto (x := 2 * r)
  filter_upwards [h0.comp_tendsto ht] with t ht
  change β (t + (-2 * r)) = α (t + (-2 * r) + r) at ht
  by_cases htr : t ≤ 2 * r
  · exact joinedArc_left htr
  · rw [joinedArc_right (lt_of_not_ge htr), ht]
    congr 1
    ring

private theorem
    Degree.CircleGluing.joinedArc_periodic_germ {N : Type*} {α β : ℝ → N} {r : ℝ} (hr : 0 < r)
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    (fun t => joinedArc α β r (t + (2 * r + 1))) =ᶠ[𝓝 (0 : ℝ)] joinedArc α β r := by
  have ht : Filter.Tendsto (fun t : ℝ => t + 1) (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => t + 1) := continuous_id.add continuous_const
    simpa only [zero_add] using hc.continuousAt.tendsto (x := 0)
  filter_upwards [h1.comp_tendsto ht,
    Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show 0 < 2 * r by linarith)] with t ht htn
  change β (t + 1) = α (t + 1 + (-1 - r)) at ht
  rw [joinedArc_right (by linarith [htn.1]), joinedArc_left htn.2.le,
    show t + (2 * r + 1) + (-2 * r) = t + 1 by ring, ht]
  congr 1
  ring

private theorem Degree.CircleGluing.joinedArc_injOn {N : Type*} {α β : ℝ → N} {r : ℝ}
    (hα : Set.InjOn α (Set.Icc (-r) r)) (hβ : Set.InjOn β (Set.Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, β t ∉ α '' Set.Icc (-r) r) :
    Set.InjOn (joinedArc α β r) (Set.Ico (0 : ℝ) (2 * r + 1)) := by
  intro x hx y hy hxy
  have hleft {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) (hle : t ≤ 2 * r) :
    t + (-r) ∈ Set.Icc (-r) r := ⟨by linarith [ht.1], by linarith⟩
  have hright {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) (hlt : 2 * r < t) :
    t + (-2 * r) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
  by_cases hxl : x ≤ 2 * r <;> by_cases hyl : y ≤ 2 * r
  · rw [joinedArc_left hxl, joinedArc_left hyl] at hxy
    have heq := hα (hleft hx hxl) (hleft hy hyl) hxy
    linarith
  · rw [joinedArc_left hxl, joinedArc_right (lt_of_not_ge hyl)] at hxy
    exact False.elim (havoid _ (hright hy (lt_of_not_ge hyl)) ⟨_, hleft hx hxl, hxy⟩)
  · rw [joinedArc_right (lt_of_not_ge hxl), joinedArc_left hyl] at hxy
    exact False.elim (havoid _ (hright hx (lt_of_not_ge hxl)) ⟨_, hleft hy hyl, hxy.symm⟩)
  · rw [joinedArc_right (lt_of_not_ge hxl), joinedArc_right (lt_of_not_ge hyl)] at hxy
    have heq :=
      hβ (Set.Ioo_subset_Icc_self (hright hx (lt_of_not_ge hxl)))
        (Set.Ioo_subset_Icc_self (hright hy (lt_of_not_ge hyl))) hxy
    linarith

private theorem
    Degree.CircleGluing.joinedArc_contMDiffAt {N : Type*} {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {α β : ℝ → N} {R r : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) :
    ContMDiffAt 𝓘(ℝ, ℝ) J ∞ (joinedArc α β r) t := by
  by_cases htle : t ≤ 2 * r
  · have htα : t + (-r) ∈ Set.Ioo (-R) R := ⟨by linarith [ht.1], by linarith⟩
    have hs :=
      (hα.contMDiffAt (Ioo_mem_nhds htα.1 htα.2)).comp t
        (contMDiff_id.add contMDiff_const).contMDiffAt
    apply hs.congr_of_eventuallyEq
    rcases htle.eq_or_lt with rfl | hlt
    · exact joinedArc_seam_germ h0
    · exact joinedArc_left_germ hlt
  · exact
      (hβ.comp (contMDiff_id.add contMDiff_const)).contMDiffAt.congr_of_eventuallyEq
        (joinedArc_right_germ (lt_of_not_ge htle))

private theorem Degree.CircleGluing.joinedArc_derivative_injective {N : Type*} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {α β : ℝ → N} {R r : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (hiα : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hiβ : ∀ s ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J β s)) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (joinedArc α β r) t) := by
  by_cases htle : t ≤ 2 * r
  · have htα : t + (-r) ∈ Set.Ioo (-R) R := ⟨by linarith [ht.1], by linarith⟩
    have heq : joinedArc α β r =ᶠ[𝓝 t] (fun s => α (s + (-r))) := by
      rcases htle.eq_or_lt with rfl | hlt
      · exact joinedArc_seam_germ h0
      · exact joinedArc_left_germ hlt
    rw [heq.mfderiv_eq]
    exact
      MorseCancel.injective_mfderiv_curve_translate
        ((hα.contMDiffAt (Ioo_mem_nhds htα.1 htα.2)).mdifferentiableAt (by simp)) (hiα _ htα)
  · have htβ : t + (-2 * r) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
    rw [(joinedArc_right_germ (α := α) (β := β) (lt_of_not_ge htle)).mfderiv_eq]
    exact
      MorseCancel.injective_mfderiv_curve_translate (hβ.mdifferentiableAt (by simp)) (hiβ _ htβ)

private def Degree.CircleGluing.joinedLoop {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) : ℝ → N :=
  periodicExtension (show 0 < 2 * r + 1 by linarith) (joinedArc α β r)

private theorem
    Degree.CircleGluing.joinedLoop_periodic {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) :
    Function.Periodic (joinedLoop hr α β) (2 * r + 1) :=
  periodicExtension_periodic _ _

private theorem
    Degree.CircleGluing.joinedLoop_left {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) {s : ℝ}
    (hs : s ∈ Set.Icc (-r) r) : joinedLoop hr α β (s + r) = α s := by
  change joinedArc α β r (toIcoMod _ 0 (s + r)) = α s
  rw [(toIcoMod_eq_self _).mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩,
    joinedArc_left (by linarith [hs.2])]
  congr 1
  ring

private theorem Degree.CircleGluing.joinedLoop_right {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (h0 : β 0 = α r) (h1 : β 1 = α (-r)) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    joinedLoop hr α β (2 * r + s) = β s := by
  by_cases hs1 : s = 1
  · subst s
    have hper := (joinedLoop_periodic hr α β) 0
    rw [zero_add] at hper
    have hz : joinedLoop hr α β 0 = α (-r) := by
      simpa only [neg_add_cancel] using joinedLoop_left hr α β (s := -r) ⟨le_rfl, by linarith⟩
    exact hper.trans (hz.trans h1.symm)
  · change joinedArc α β r (toIcoMod _ 0 (2 * r + s)) = β s
    rw [(toIcoMod_eq_self _).mpr
        ⟨by linarith [hs.1], by
          have hlt : s < 1 := lt_of_le_of_ne hs.2 hs1
          linarith⟩]
    by_cases hs0 : s = 0
    · subst s
      rw [add_zero, joinedArc_left le_rfl]
      simpa only [show 2 * r + (-r) = r by ring] using h0.symm
    · rw [joinedArc_right
          (by
            have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
            linarith)]
      congr 1
      ring

private theorem Degree.CircleGluing.joinedLoop_range {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (h0 : β 0 = α r) (h1 : β 1 = α (-r)) :
    Set.range (joinedLoop hr α β) = α '' Set.Icc (-r) r ∪ β '' Set.Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    let q := toIcoMod (show 0 < 2 * r + 1 by linarith) 0 t
    have hq : q ∈ Set.Ico (0 : ℝ) (2 * r + 1) := by
      simpa only [zero_add] using toIcoMod_mem_Ico (show 0 < 2 * r + 1 by linarith) 0 t
    change joinedArc α β r q ∈ _
    by_cases hqr : q ≤ 2 * r
    · rw [joinedArc_left hqr]
      exact Or.inl ⟨_, ⟨by linarith [hq.1], by linarith⟩, rfl⟩
    · rw [joinedArc_right (lt_of_not_ge hqr)]
      exact Or.inr ⟨_, ⟨by linarith, by linarith [hq.2]⟩, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨s + r, joinedLoop_left hr α β hs⟩
    · exact ⟨2 * r + s, joinedLoop_right hr h0 h1 hs⟩

private theorem Degree.CircleGluing.joinedLoop_injOn {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (hα : Set.InjOn α (Set.Icc (-r) r)) (hβ : Set.InjOn β (Set.Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, β t ∉ α '' Set.Icc (-r) r) :
    Set.InjOn (joinedLoop hr α β) (Set.Ico (0 : ℝ) (2 * r + 1)) := by
  intro x hx y hy hxy
  apply joinedArc_injOn hα hβ havoid hx hy
  change joinedArc α β r (toIcoMod _ 0 x) = joinedArc α β r (toIcoMod _ 0 y) at hxy
  rw [(toIcoMod_eq_self _).mpr (by simpa only [zero_add] using hx),
    (toIcoMod_eq_self _).mpr (by simpa only [zero_add] using hy)] at hxy
  exact hxy

private theorem Degree.CircleGluing.joinedLoop_contMDiff {N : Type*} {r : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hr : 0 < r) {α β : ℝ → N} {R : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    ContMDiff 𝓘(ℝ, ℝ) J ∞ (joinedLoop hr α β) :=
  periodicExtension_contMDiff _ (joinedArc_periodic_germ hr h1)
    (fun _ ht => joinedArc_contMDiffAt hrR hα hβ h0 ht)

private theorem
    Degree.CircleGluing.joinedLoop_derivative_injective {N : Type*} {r : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hr : 0 < r) {α β : ℝ → N} {R : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r))))
    (hiα : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hiβ : ∀ s ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J β s)) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (joinedLoop hr α β) t) :=
  periodicExtension_derivative_injective _ (joinedArc_periodic_germ hr h1)
    (fun _ ht => (joinedArc_contMDiffAt hrR hα hβ h0 ht).mdifferentiableAt (by simp))
    (fun _ ht => joinedArc_derivative_injective hrR hα hβ h0 hiα hiβ ht) t

private theorem Degree.CircleGluing.circleExp_derivative_injective (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  have hd :
    HasDerivAt (fun s : ℝ => (Circle.exp s : ℂ)) (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)
      t := by
    simpa only [Circle.coe_exp, Complex.real_smul, id_eq, one_mul] using
      ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).cexp.comp_ofReal
  have hdne : (Complex.exp ((t : ℂ) * Complex.I) * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
  have hi0 : Function.Injective (fderiv ℝ (fun s : ℝ => (Circle.exp s : ℂ)) t) := by
    rw [hd.hasFDerivAt.fderiv]
    exact smul_left_injective ℝ hdne
  let c : Circle → ℂ := fun z => (z : ℂ)
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ c := contMDiff_coe_sphere
  have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (c ∘ (fun s : ℝ => Circle.exp s)) t) := by
    rw [mfderiv_eq_fderiv]
    exact hi0
  rw [mfderiv_comp t (hc.mdifferentiableAt (by simp))
      ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hi
  intro x y hxy
  exact hi (congrArg (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) c (Circle.exp t)) hxy)

private theorem Degree.CircleGluing.circleExp_localDiffeomorph (t : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp t := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have hi : Function.Injective L := circleExp_derivative_injective t
  have hs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) (by simp)).mp
      hi
  apply
    Smale.isLocalDiffeomorphAt_boundaryless isOpen_univ (Set.mem_univ t)
      (contMDiff_circleExp (m := ∞)).contMDiffOn
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

private theorem
    Degree.CircleGluing.contMDiff_of_comp_circleExp {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff 𝓘(ℝ, ℝ) J ∞ (γ ∘ Circle.exp)) :
    ContMDiff (𝓡 1) J ∞ γ := by
  intro z
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  let h := circleExp_localDiffeomorph t
  have hs : ContMDiffAt (𝓡 1) J ∞ ((γ ∘ Circle.exp) ∘ h.localInverse) (Circle.exp t) :=
    (hγ.contMDiffAt (x := h.localInverse (Circle.exp t))).comp _ h.localInverse_contMDiffAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [h.localInverse_eventuallyEq_right] with y hy
  exact (congrArg γ hy).symm

private def Degree.CircleGluing.periodicCircle {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) (z : Circle) : N :=
  hper.lift ((AddCircle.homeomorphCircle hT).symm z)

private theorem Degree.CircleGluing.periodicCircle_exp {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) (t : ℝ) :
    periodicCircle hT hper (Circle.exp (2 * Real.pi / T * t)) = f t := by
  have heq : Circle.exp (2 * Real.pi / T * t) = AddCircle.homeomorphCircle hT (t : AddCircle T) :=
    by rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  rw [heq, periodicCircle, Homeomorph.symm_apply_apply, Function.Periodic.lift_coe]

private theorem
    Degree.CircleGluing.periodicCircle_comp_exp {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) :
    periodicCircle hT hper ∘ Circle.exp = (fun t => f (T / (2 * Real.pi) * t)) := by
  funext t
  have heq : 2 * Real.pi / T * (T / (2 * Real.pi) * t) = t := by field_simp [hT, Real.pi_ne_zero]
  have hh := periodicCircle_exp hT hper (T / (2 * Real.pi) * t)
  rw [heq] at hh
  exact hh

private theorem
    Degree.CircleGluing.periodicCircle_injective {N : Type*} {T : ℝ} {f : ℝ → N} (hT : 0 < T)
    (hper : Function.Periodic f T) (hi : Set.InjOn f (Set.Ico (0 : ℝ) T)) :
    Function.Injective (periodicCircle hT.ne' hper) := by
  let _ : Fact (0 < T) := ⟨hT⟩
  let e := AddCircle.homeomorphCircle hT.ne'
  intro z w hzw
  let x := AddCircle.equivIco T 0 (e.symm z)
  let y := AddCircle.equivIco T 0 (e.symm w)
  have hx : (x.val : AddCircle T) = e.symm z := AddCircle.coe_equivIco
  have hy : (y.val : AddCircle T) = e.symm w := AddCircle.coe_equivIco
  have hval : f x.val = f y.val := by
    change hper.lift (e.symm z) = hper.lift (e.symm w) at hzw
    rw [← hx, ← hy, Function.Periodic.lift_coe, Function.Periodic.lift_coe] at hzw
    exact hzw
  have hxy : x.val = y.val :=
    hi (by simpa only [zero_add] using x.property) (by simpa only [zero_add] using y.property)
      hval
  apply e.symm.injective
  rw [← hx, ← hy, hxy]

private theorem
    Degree.CircleGluing.periodicCircle_range {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) : Set.range (periodicCircle hT hper) = Set.range f := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective w
    have hh := congrFun (periodicCircle_comp_exp hT hper) t
    exact ⟨T / (2 * Real.pi) * t, hh.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Circle.exp (2 * Real.pi / T * t), periodicCircle_exp hT hper t⟩

private theorem
    Degree.CircleGluing.periodicCircle_contMDiff {N : Type*} {T : ℝ} {f : ℝ → N} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hT : T ≠ 0) (hper : Function.Periodic f T)
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) : ContMDiff (𝓡 1) J ∞ (periodicCircle hT hper) := by
  apply contMDiff_of_comp_circleExp
  rw [periodicCircle_comp_exp]
  exact hf.comp (contDiff_const.mul contDiff_id).contMDiff

private theorem Degree.CircleGluing.injective_mfderiv_curve_const_mul {N : Type*} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {α : ℝ → N} {s a : ℝ} (ha : a ≠ 0)
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) J α (a * s))
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α (a * s))) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => α (a * t)) s) := by
  have hd : HasDerivAt (fun t : ℝ => a * t) a s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul a
  have hmul : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => a * t) s) := by
    rw [mfderiv_eq_fderiv]
    have hh : Function.Injective (fderiv ℝ (fun t : ℝ => a * t) s) := by
      rw [hd.hasFDerivAt.fderiv]
      exact smul_left_injective ℝ ha
    exact hh
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (α ∘ (fun t : ℝ => a * t)) s)
  rw [mfderiv_comp s hα hd.differentiableAt.mdifferentiableAt]
  intro x y hxy
  exact hmul (hi hxy)

private theorem
    Degree.CircleGluing.periodicCircle_derivative_injective {N : Type*} {T : ℝ} {f : ℝ → N}
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] (hT : T ≠ 0)
    (hper : Function.Periodic f T) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hi : ∀ t, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (z : Circle) :
    Function.Injective (mfderiv (𝓡 1) J (periodicCircle hT hper) z) := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  have hc : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (periodicCircle hT hper ∘ Circle.exp) t) := by
    rw [periodicCircle_comp_exp]
    exact
      injective_mfderiv_curve_const_mul
        (div_ne_zero hT (mul_ne_zero (by norm_num) Real.pi_ne_zero))
        (hf.mdifferentiableAt (by simp)) (hi _)
  rw [mfderiv_comp t ((periodicCircle_contMDiff hT hper hf).mdifferentiableAt (by simp))
      ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hc
  have hs := ((circleExp_localDiffeomorph t).mfderivToContinuousLinearEquiv (by simp)).surjective
  intro x y hxy
  obtain ⟨u, hu⟩ := hs x
  obtain ⟨v, hv⟩ := hs y
  have hux : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t u = x := hu
  have hvy : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t v = y := hv
  have huv : u = v :=
    hc
      (by
        change
          mfderiv (𝓡 1) J (periodicCircle hT hper) (Circle.exp t)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t u) =
            mfderiv (𝓡 1) J (periodicCircle hT hper) (Circle.exp t)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t v)
        rw [hux, hvy]
        exact hxy)
  exact hux.symm.trans ((congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) huv).trans hvy)

private theorem Smale.NativeOpenSubmanifold.injective_mfderiv_subtype_val {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (U : TopologicalSpace.Opens M) (p : U) :
    Function.Injective (mfderiv I I (Subtype.val : U → M) p) := by
  classical
  let g : M → U := fun x => if hx : x ∈ U then ⟨x, hx⟩ else p
  have hval : (Subtype.val ∘ g) =ᶠ[𝓝 (p : M)] id := by
    apply Filter.mem_of_superset (U.isOpen.mem_nhds p.property)
    intro x hx
    change x ∈ U at hx
    change (g x : M) = x
    dsimp [g]
    rw [dite_eq_left hx]
  have hg : ContMDiffAt I I ∞ g (p : M) := by
    apply (ContMDiffAt.subtypeVal_comp_iff U g (p : M)).mp
    exact contMDiffAt_id.congr_of_eventuallyEq hval
  have hv : ContMDiff I I ∞ (Subtype.val : U → M) := contMDiff_subtype_val
  have hleft : g ∘ (Subtype.val : U → M) = id := by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, g, dite_eq_left x.property, id_eq]
  have heq := mfderiv_comp p (hg.mdifferentiableAt (by simp)) (hv.mdifferentiableAt (by simp))
  rw [hleft, mfderiv_id] at heq
  intro v w hvw
  have hh := congrArg (mfderiv I I g (p : M)) hvw
  have hv' := congrArg (fun L => L v) heq
  have hw' := congrArg (fun L => L w) heq
  exact hv'.trans (hh.trans hw'.symm)

private theorem
    MorseCancel.exists_embedded_circle_through_arc {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (S : TopologicalSpace.Opens N) {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hinj : Set.InjOn α (Set.Icc (-R) R))
    (hderiv : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s)) (hplus : α r ∈ S)
    (hminus : α (-r) ∈ S) (η : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ γ : C(Circle, N),
      ContMDiff (𝓡 1) J ∞ γ ∧
        Function.Injective γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) J γ z)) ∧
            (∀ s ∈ Set.Icc (-r) r, γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) = α s) ∧
              Set.range γ ⊆ α '' Set.Icc (-r) r ∪ (S : Set N) := by
  obtain ⟨b, hb, hb0, hb1, hemb, hbd, havoid⟩ :=
    exists_disjoint_embedded_return_arc S hr hrR hα hinj hderiv hplus hminus η hdim
  let β : ℝ → N := Subtype.val ∘ b
  have hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β := contMDiff_subtype_val.comp hb
  have hβi : Set.InjOn β (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hbx : b x = b y := Subtype.ext hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hbx)
  have hβd : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J β t) := by
    intro t ht
    rw [show β = Subtype.val ∘ b from rfl,
      mfderiv_comp t ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
        (hb.mdifferentiableAt (by simp))]
    exact (Smale.NativeOpenSubmanifold.injective_mfderiv_subtype_val S (b t)).comp (hbd t ht)
  have h0 : β 0 = α r := by simpa only [zero_add] using hb0.eq_of_nhds
  have h1 : β 1 = α (-r) := by
    simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using hb1.eq_of_nhds
  let F := Degree.CircleGluing.joinedLoop hr α β
  have hF : ContMDiff 𝓘(ℝ, ℝ) J ∞ F :=
    Degree.CircleGluing.joinedLoop_contMDiff hr hrR hα hβ hb0 hb1
  have hFd : ∀ t, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J F t) :=
    Degree.CircleGluing.joinedLoop_derivative_injective hr hrR hα hβ hb0 hb1 hderiv hβd
  have hsub : Set.Icc (-r) r ⊆ Set.Icc (-R) R := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hαi : Set.InjOn α (Set.Icc (-r) r) := hinj.mono hsub
  have hFi : Set.InjOn F (Set.Ico (0 : ℝ) (2 * r + 1)) :=
    Degree.CircleGluing.joinedLoop_injOn hr hαi hβi havoid
  have hT : 0 < 2 * r + 1 := by linarith
  have hper : Function.Periodic F (2 * r + 1) := Degree.CircleGluing.joinedLoop_periodic hr α β
  let Γ := Degree.CircleGluing.periodicCircle hT.ne' hper
  have hΓ : ContMDiff (𝓡 1) J ∞ Γ := Degree.CircleGluing.periodicCircle_contMDiff hT.ne' hper hF
  refine
    ⟨⟨Γ, hΓ.continuous⟩, hΓ, Degree.CircleGluing.periodicCircle_injective hT hper hFi,
      Degree.CircleGluing.periodicCircle_derivative_injective hT.ne' hper hF hFd, ?_, ?_⟩
  · intro s hs
    exact
      (Degree.CircleGluing.periodicCircle_exp hT.ne' hper (s + r)).trans
        (Degree.CircleGluing.joinedLoop_left hr α β hs)
  · intro z hz
    change z ∈ Set.range Γ at hz
    rw [Degree.CircleGluing.periodicCircle_range,
      Degree.CircleGluing.joinedLoop_range hr h0 h1] at hz
    rcases hz with hz | ⟨t, -, rfl⟩
    · exact Or.inl hz
    · exact Or.inr (b t).property

private theorem MorseCancel.dense_section_of_flow_cylinder {N X : Type*} [TopologicalSpace N]
    [TopologicalSpace X] (A : OpenPartialHomeomorph (N × ℝ) X) (hsource : A.source = Set.univ)
    (F : Flow ℝ X) (ι : N → X) (hformula : ∀ z, A z = F z.2 (ι z.1)) {B : Set X} (hB : Dense B)
    (hinv : ∀ t x, F t x ∈ B ↔ x ∈ B) : Dense (ι ⁻¹' B) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  have hdom : U ×ˢ (Set.univ : Set ℝ) ⊆ A.source := by rw [hsource]; exact Set.subset_univ _
  have hopen : IsOpen (A '' (U ×ˢ (Set.univ : Set ℝ))) :=
    A.isOpen_image_of_subset_source (hU.prod isOpen_univ) hdom
  obtain ⟨z, hz⟩ := hne
  have himage : (A '' (U ×ˢ (Set.univ : Set ℝ))).Nonempty :=
    ⟨A (z, 0), (z, 0), ⟨hz, Set.mem_univ _⟩, rfl⟩
  obtain ⟨x, hx, hxB⟩ := hB.inter_open_nonempty _ hopen himage
  obtain ⟨⟨w, t⟩, ⟨hw, -⟩, rfl⟩ := hx
  refine ⟨w, hw, ?_⟩
  apply (hinv t (ι w)).mp
  rwa [hformula] at hxB

private theorem
    AdaptedWindows.dense_regular_level_minimum_basins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    Dense
      {x : { y : M // f y = a } |
        ∃ p : Smale.ManifoldMorse.criticalPoints E f,
          MorseCancel.nativeMorseIndex E f p = 0 ∧
            Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let L := { y : M // f y = a }
  rcases isEmpty_or_nonempty L with h | h
  · exact fun x => isEmptyElim x
  · let _ := Smale.RegularLevel.chartedSpace hf hreg
    obtain ⟨A, hsource, -, hformula, -⟩ :=
      Degree.FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
        (fun x hx => S.descent x (hreg x hx)) (Classical.arbitrary L)
    apply
      MorseCancel.dense_section_of_flow_cylinder A.toOpenPartialHomeomorph hsource S.flow
        Subtype.val hformula (S.dense_minimum_forward_basins hf)
    intro t x
    constructor
    · rintro ⟨p, hp, hlim⟩
      exact ⟨p, hp, (MorseCancel.flow_time_atTop_limit_iff S.flow t x p.val).mp hlim⟩
    · rintro ⟨p, hp, hlim⟩
      exact ⟨p, hp, (MorseCancel.flow_time_atTop_limit_iff S.flow t x p.val).mpr hlim⟩

private abbrev Degree.Handle.Space {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P] :=
  Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P

private def Degree.Handle.denominator {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    (z : Space (N := N) (P := P)) : ℝ :=
  Max.max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)

private theorem Degree.Handle.half_le_denominator {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) : (1 / 2 : ℝ) ≤ denominator z := by
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have hd := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  change (1 / 2 : ℝ) ≤ Max.max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  linarith

private theorem
    Degree.Handle.denominator_pos {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    (z : Space (N := N) (P := P)) : 0 < denominator z :=
  lt_of_lt_of_le (by norm_num) (half_le_denominator z)

private theorem Degree.Handle.denominator_le_one {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) : denominator z ≤ 1 := by
  apply max_le (mem_closedBall_zero_iff.mp z.1.property)
  linarith [norm_nonneg (z.2 : P)]

private def
    Degree.Handle.positiveMultiplier {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    (z : Space (N := N) (P := P)) : ℝ :=
  (2 * denominator z + ‖(z.2 : P)‖ - 2) / (‖(z.2 : P)‖ * denominator z)

private theorem Degree.Handle.positiveMultiplier_nonneg {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) : 0 ≤ positiveMultiplier z := by
  apply div_nonneg
  · have hd := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
    change 0 ≤ 2 * Max.max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2) + ‖(z.2 : P)‖ - 2
    linarith
  · exact mul_nonneg (norm_nonneg _) (denominator_pos z).le

private theorem Degree.Handle.positiveMultiplier_le_one {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) : positiveMultiplier z ≤ 1 := by
  by_cases hv : (z.2 : P) = 0
  · simp [positiveMultiplier, hv]
  · apply (div_le_one (mul_pos (norm_pos_iff.mpr hv) (denominator_pos z))).mpr
    have hb : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
    have hprod :=
      mul_nonneg (sub_nonneg.mpr (denominator_le_one z)) (show 0 ≤ 2 - ‖(z.2 : P)‖ by linarith)
    nlinarith

private def Degree.Handle.negative {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [NormedSpace ℝ N] (z : Space (N := N) (P := P)) : N :=
  (denominator z)⁻¹ • (z.1 : N)

private def Degree.Handle.positive {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [NormedSpace ℝ P] (z : Space (N := N) (P := P)) : P :=
  positiveMultiplier z • (z.2 : P)

private theorem Degree.Handle.norm_negative_le_one {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ N] (z : Space (N := N) (P := P)) : ‖negative z‖ ≤ 1 := by
  rw [negative, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (denominator_pos z).le)]
  have h :=
    mul_le_mul_of_nonneg_left (le_max_left ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2))
      (inv_nonneg.mpr (denominator_pos z).le)
  exact h.trans_eq (inv_mul_cancel₀ (denominator_pos z).ne')

private theorem
    Degree.Handle.norm_positive_le {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [NormedSpace ℝ P] (z : Space (N := N) (P := P)) : ‖positive z‖ ≤ ‖(z.2 : P)‖ := by
  rw [positive, norm_smul, Real.norm_of_nonneg (positiveMultiplier_nonneg z)]
  exact
    (mul_le_mul_of_nonneg_right (positiveMultiplier_le_one z) (norm_nonneg _)).trans_eq
      (one_mul _)

private theorem Degree.Handle.positive_eq_zero_of_snd_eq_zero {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) (hz : (z.2 : P) = 0) :
    positive z = 0 := by simp only [positive, hz, smul_zero]

private theorem Degree.Handle.denominator_eq_one_of_snd_eq_zero {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) (hz : (z.2 : P) = 0) :
    denominator z = 1 := by
  simp only [denominator, hz, norm_zero, zero_div, sub_zero]
  exact max_eq_right (mem_closedBall_zero_iff.mp z.1.property)

private theorem Degree.Handle.continuous_denominator {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] : Continuous (denominator (N := N) (P := P)) := by
  unfold denominator
  fun_prop

private theorem
    Degree.Handle.continuous_negative {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] : Continuous (negative (N := N) (P := P)) :=
  (continuous_denominator.inv₀ (fun z => (denominator_pos z).ne')).smul
    (continuous_subtype_val.comp continuous_fst)

private theorem Degree.Handle.continuous_positive {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] : Continuous (positive (N := N) (P := P)) := by
  have hv : Continuous (fun z : Space (N := N) (P := P) => (z.2 : P)) :=
    continuous_subtype_val.comp continuous_snd
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : (z.2 : P) = 0
  · change Filter.Tendsto positive (𝓝 z) (𝓝 (positive z))
    rw [positive_eq_zero_of_snd_eq_zero z hz]
    apply squeeze_zero_norm norm_positive_le
    simpa only [hz, norm_zero] using hv.norm.continuousAt.tendsto (x := z)
  · have hn :
      Continuous (fun w : Space (N := N) (P := P) => 2 * denominator w + ‖(w.2 : P)‖ - 2) :=
      ((continuous_const.mul continuous_denominator).add hv.norm).sub continuous_const
    have hd : Continuous (fun w : Space (N := N) (P := P) => ‖(w.2 : P)‖ * denominator w) :=
      hv.norm.mul continuous_denominator
    exact
      (hn.continuousAt.div hd.continuousAt
            (mul_ne_zero (norm_ne_zero_iff.mpr hz) (denominator_pos z).ne')).smul
        hv.continuousAt

private def Degree.Handle.retraction {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] : C(Space (N := N) (P := P), Space (N := N) (P := P))
    where
  toFun
    z :=
    (⟨negative z, mem_closedBall_zero_iff.mpr (norm_negative_le_one z)⟩,
      ⟨positive z,
        mem_closedBall_zero_iff.mpr
          ((norm_positive_le z).trans (mem_closedBall_zero_iff.mp z.2.property))⟩)
  continuous_toFun := (continuous_negative.subtype_mk _).prodMk (continuous_positive.subtype_mk _)

private def Degree.Handle.faceCore {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P] :
    Set (Space (N := N) (P := P)) :=
  {z | ‖(z.1 : N)‖ = 1 ∨ (z.2 : P) = 0}

private theorem Degree.Handle.retraction_mem_faceCore {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) :
    retraction z ∈ faceCore := by
  by_cases hz : 1 - ‖(z.2 : P)‖ / 2 ≤ ‖(z.1 : N)‖
  · left
    change ‖negative z‖ = 1
    have hd : denominator z = ‖(z.1 : N)‖ := max_eq_left hz
    rw [negative, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (denominator_pos z).le)]
    rw [← hd, inv_mul_cancel₀ (denominator_pos z).ne']
  · right
    change positive z = 0
    have hd : denominator z = 1 - ‖(z.2 : P)‖ / 2 := max_eq_right (le_of_not_ge hz)
    have hn : 2 * denominator z + ‖(z.2 : P)‖ - 2 = 0 := by rw [hd]; ring
    simp only [positive, positiveMultiplier, hn, zero_div, zero_smul]

private theorem
    Degree.Handle.retraction_eq_self {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) (hz : z ∈ faceCore) :
    retraction z = z := by
  have hd : denominator z = 1 := by
    rcases hz with hu | hv
    · unfold denominator
      rw [hu]
      apply max_eq_left
      linarith [norm_nonneg (z.2 : P)]
    · exact denominator_eq_one_of_snd_eq_zero z hv
  apply Prod.ext
  · apply Subtype.ext
    change negative z = (z.1 : N)
    simp only [negative, hd, inv_one, one_smul]
  · apply Subtype.ext
    change positive z = (z.2 : P)
    by_cases hv : (z.2 : P) = 0
    · simp only [positive, hv, smul_zero]
    · have hm : positiveMultiplier z = 1 := by
        unfold positiveMultiplier
        rw [hd]
        field_simp
        ring
      rw [positive, hm, one_smul]

private abbrev Degree.DiskCylinder.Disk {E : Type*} [NormedAddCommGroup E] :=
  Metric.closedBall (0 : E) 1

private abbrev Degree.DiskCylinder.Sphere {E : Type*} [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

private def Degree.DiskCylinder.toHandle {E : Type*} [NormedAddCommGroup E] :
    C((unitInterval) × Disk (E := E), Degree.Handle.Space (N := E) (P := ℝ))
    where
  toFun
    p :=
    (p.2,
      ⟨p.1.val,
        mem_closedBall_zero_iff.mpr
          (by
            rw [Real.norm_of_nonneg p.1.property.1]
            exact p.1.property.2)⟩)
  continuous_toFun :=
    continuous_snd.prodMk ((continuous_subtype_val.comp continuous_fst).subtype_mk _)

private def Degree.DiskCylinder.retractedTime {E : Type*} [NormedAddCommGroup E]
    (p : (unitInterval) × Disk (E := E)) : (unitInterval) :=
  ⟨Degree.Handle.positiveMultiplier (toHandle p) * p.1.val,
    mul_nonneg (Degree.Handle.positiveMultiplier_nonneg _) p.1.property.1,
    (by
      have h :=
        mul_le_mul_of_nonneg_right (Degree.Handle.positiveMultiplier_le_one (toHandle p))
          p.1.property.1
      exact (h.trans_eq (one_mul p.1.val)).trans p.1.property.2)⟩

private theorem Degree.DiskCylinder.continuous_retractedTime {E : Type*} [NormedAddCommGroup E] :
    Continuous (retractedTime (E := E)) :=
  (Degree.Handle.continuous_positive.comp toHandle.continuous).subtype_mk _

private def Degree.DiskCylinder.retractedDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : (unitInterval) × Disk (E := E)) : Disk (E := E) :=
  (Degree.Handle.retraction (toHandle p)).1

private theorem Degree.DiskCylinder.continuous_retractedDisk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (retractedDisk (E := E)) :=
  continuous_fst.comp (Degree.Handle.retraction.continuous.comp toHandle.continuous)

private def Degree.DiskCylinder.bottomOrSide {E : Type*} [NormedAddCommGroup E] :
    Set ((unitInterval) × Disk (E := E)) :=
  {p | p.1 = 0 ∨ ‖(p.2 : E)‖ = 1}

private theorem Degree.DiskCylinder.retracted_mem_bottomOrSide {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : (unitInterval) × Disk (E := E)) :
    (retractedTime p, retractedDisk p) ∈ bottomOrSide := by
  rcases Degree.Handle.retraction_mem_faceCore (toHandle p) with hp | hp
  · exact Or.inr hp
  · apply Or.inl
    apply Subtype.ext
    exact hp

private def Degree.DiskCylinder.retraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C((unitInterval) × Disk (E := E), bottomOrSide (E := E)) :=
  ⟨fun p => ⟨(retractedTime p, retractedDisk p), retracted_mem_bottomOrSide p⟩,
    (continuous_retractedTime.prodMk continuous_retractedDisk).subtype_mk _⟩

private theorem
    Degree.DiskCylinder.retraction_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : (unitInterval) × Disk (E := E)) (hp : p ∈ bottomOrSide) : (retraction p).val = p := by
  have hh : toHandle p ∈ Degree.Handle.faceCore := by
    rcases hp with ht | hx
    · exact Or.inr (congrArg Subtype.val ht)
    · exact Or.inl hx
  have hr := Degree.Handle.retraction_eq_self (toHandle p) hh
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : Degree.Handle.Space (N := E) (P := ℝ) => (z.2 : ℝ)) hr
  · exact congrArg Prod.fst hr

private def Degree.DiskCylinder.boundaryToDisk {E : Type*} [NormedAddCommGroup E] :
    C(Sphere (E := E), Disk (E := E)) :=
  ⟨fun u => ⟨u.val, Metric.sphere_subset_closedBall u.property⟩,
    continuous_subtype_val.subtype_mk _⟩

private def Degree.DiskCylinder.bottomMap {E : Type*} [NormedAddCommGroup E] :
    C(Disk (E := E), bottomOrSide (E := E)) :=
  ⟨fun u => ⟨(0, u), Or.inl rfl⟩, (continuous_const.prodMk continuous_id).subtype_mk _⟩

private def Degree.DiskCylinder.sideMap {E : Type*} [NormedAddCommGroup E] :
    C((unitInterval) × Sphere (E := E), bottomOrSide (E := E)) :=
  ⟨fun p => ⟨(p.1, boundaryToDisk p.2), Or.inr (mem_sphere_zero_iff_norm.mp p.2.property)⟩,
    (continuous_fst.prodMk (boundaryToDisk.continuous.comp continuous_snd)).subtype_mk _⟩

private def Degree.DiskCylinder.bottomSideQuotient {E : Type*} [NormedAddCommGroup E] :
    C(Disk (E := E) ⊕ ((unitInterval) × Sphere (E := E)), bottomOrSide (E := E)) :=
  ⟨Sum.elim bottomMap sideMap, bottomMap.continuous.sumElim sideMap.continuous⟩

private theorem
    Degree.DiskCylinder.bottomSideQuotient_surjective {E : Type*} [NormedAddCommGroup E] :
    Function.Surjective (bottomSideQuotient (E := E)) := by
  rintro ⟨⟨t, u⟩, ht | hu⟩
  · change t = 0 at ht
    subst t
    exact ⟨.inl u, rfl⟩
  · exact ⟨.inr (t, ⟨u.val, mem_sphere_zero_iff_norm.mpr hu⟩), rfl⟩

private theorem
    Degree.DiskCylinder.bottomSideQuotient_isQuotientMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Topology.IsQuotientMap (bottomSideQuotient (E := E)) :=
  .of_surjective_continuous bottomSideQuotient_surjective bottomSideQuotient.continuous

private def Degree.DiskCylinder.bottomSideData {E : Type*} [NormedAddCommGroup E] {X : Type*}
    [TopologicalSpace X] (f : C(Disk (E := E), X)) (G : C((unitInterval) × Sphere (E := E), X)) :
    C(Disk (E := E) ⊕ ((unitInterval) × Sphere (E := E)), X) :=
  ⟨Sum.elim f G, f.continuous.sumElim G.continuous⟩

private theorem
    Degree.DiskCylinder.bottomSideData_constant_on_fibres {E : Type*} [NormedAddCommGroup E]
    {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))
    (a b : Disk (E := E) ⊕ ((unitInterval) × Sphere (E := E)))
    (h : bottomSideQuotient a = bottomSideQuotient b) :
    bottomSideData f G a = bottomSideData f G b := by
  have he := congrArg Subtype.val h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg f (congrArg Prod.snd he)
    | inr b =>
      have ht : (0 : (unitInterval)) = b.1 := congrArg Prod.fst he
      have hu : a = boundaryToDisk b.2 := congrArg Prod.snd he
      exact (congrArg f hu).trans ((h0 b.2).symm.trans (congrArg G (Prod.ext ht rfl)))
  | inr a =>
    cases b with
    | inl b =>
      change G a = f b
      have ht : a.1 = (0 : (unitInterval)) := congrArg Prod.fst he
      have hu : boundaryToDisk a.2 = b := congrArg Prod.snd he
      have ha : a = (0, a.2) := Prod.ext ht rfl
      exact (congrArg G ha).trans ((h0 a.2).trans (congrArg f hu))
    | inr b =>
      change G a = G b
      have ht : a.1 = b.1 := congrArg (fun p : (unitInterval) × Disk (E := E) => p.1) he
      have hu : a.2.val = b.2.val :=
        congrArg (fun p : (unitInterval) × Disk (E := E) => p.2.val) he
      exact congrArg G (Prod.ext ht (Subtype.ext hu))

private def Degree.DiskCylinder.gluedBottomSide {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) :
    C(bottomOrSide (E := E), X) :=
  bottomSideQuotient_isQuotientMap.lift (bottomSideData f G)
    (bottomSideData_constant_on_fibres f G h0)

@[simp]
private theorem Degree.DiskCylinder.gluedBottomSide_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (f : C(Disk (E := E), X)) (G : C((unitInterval) × Sphere (E := E), X))
    (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))
    (z : Disk (E := E) ⊕ ((unitInterval) × Sphere (E := E))) :
    gluedBottomSide f G h0 (bottomSideQuotient z) = bottomSideData f G z :=
  ContinuousMap.congr_fun
    (bottomSideQuotient_isQuotientMap.lift_comp (bottomSideData f G)
      (bottomSideData_constant_on_fibres f G h0))
    z

@[simp]
private theorem Degree.DiskCylinder.gluedBottomSide_bottom {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (f : C(Disk (E := E), X)) (G : C((unitInterval) × Sphere (E := E), X))
    (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) (u : Disk (E := E)) :
    gluedBottomSide f G h0 (bottomMap u) = f u :=
  gluedBottomSide_apply f G h0 (.inl u)

@[simp]
private theorem Degree.DiskCylinder.gluedBottomSide_side {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (f : C(Disk (E := E), X)) (G : C((unitInterval) × Sphere (E := E), X))
    (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) (p : (unitInterval) × Sphere (E := E)) :
    gluedBottomSide f G h0 (sideMap p) = G p :=
  gluedBottomSide_apply f G h0 (.inr p)

private theorem
    Degree.DiskCylinder.retraction_bottom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Disk (E := E)) : retraction (0, u) = bottomMap u :=
  Subtype.ext (retraction_fixed (0, u) (Or.inl rfl))

private theorem
    Degree.DiskCylinder.retraction_side {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : (unitInterval) × Sphere (E := E)) : retraction (p.1, boundaryToDisk p.2) = sideMap p :=
  Subtype.ext
    (retraction_fixed (p.1, boundaryToDisk p.2)
      (Or.inr (mem_sphere_zero_iff_norm.mp p.2.property)))

private def Degree.DiskCylinder.extend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) :
    C((unitInterval) × Disk (E := E), X) :=
  (gluedBottomSide f G h0).comp retraction

@[simp]
private theorem
    Degree.DiskCylinder.extend_bottom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))
    (u : Disk (E := E)) : Degree.DiskCylinder.extend f G h0 (0, u) = f u := by
  change gluedBottomSide f G h0 (retraction (0, u)) = f u
  rw [retraction_bottom, gluedBottomSide_bottom]

@[simp]
private theorem Degree.DiskCylinder.extend_side {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))
    (t : (unitInterval)) (u : Sphere (E := E)) :
    Degree.DiskCylinder.extend f G h0 (t, boundaryToDisk u) = G (t, u) := by
  change gluedBottomSide f G h0 (retraction (t, boundaryToDisk u)) = G (t, u)
  rw [retraction_side (t, u), gluedBottomSide_side]

private def
    Degree.DiskCylinder.extensionEndpoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) :
    C(Disk (E := E), X) :=
  (Degree.DiskCylinder.extend f G h0).comp
    ⟨fun u => (1, u), continuous_const.prodMk continuous_id⟩

private def
    Degree.DiskCylinder.extensionHomotopy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) :
    f.Homotopy (extensionEndpoint f G h0)
    where
  toContinuousMap := Degree.DiskCylinder.extend f G h0
  map_zero_left := extend_bottom f G h0
  map_one_left _ := rfl

private def Degree.DiskCone.radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C((unitInterval) × Degree.DiskCylinder.Sphere (E := E), Degree.DiskCylinder.Disk (E := E))
    where
  toFun
    p :=
    ⟨p.1.val • p.2.val,
      mem_closedBall_zero_iff.mpr
        (by
          rw [norm_smul, Real.norm_of_nonneg p.1.property.1,
            mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
          exact p.1.property.2)⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _

private theorem Degree.DiskCone.radial_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : (unitInterval) × Degree.DiskCylinder.Sphere (E := E)) : ‖(radial p : E)‖ = p.1.val := by
  change ‖p.1.val • p.2.val‖ = p.1.val
  rw [norm_smul, Real.norm_of_nonneg p.1.property.1, mem_sphere_zero_iff_norm.mp p.2.property,
    mul_one]

@[simp]
private theorem Degree.DiskCone.radial_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Degree.DiskCylinder.Sphere (E := E)) :
    radial (1, s) = Degree.DiskCylinder.boundaryToDisk s :=
  Subtype.ext (one_smul ℝ s.val)

@[simp]
private theorem Degree.DiskCone.radial_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Degree.DiskCylinder.Sphere (E := E)) :
    radial (0, s) = (⟨0, by simp⟩ : Degree.DiskCylinder.Disk (E := E)) :=
  Subtype.ext (zero_smul ℝ s.val)

private theorem
    Degree.DiskCone.radial_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s0 : Degree.DiskCylinder.Sphere (E := E)) : Function.Surjective (radial (E := E)) := by
  intro z
  by_cases hz : z.val = 0
  · exact ⟨(0, s0), (radial_zero s0).trans (Subtype.ext hz.symm)⟩
  · let t : (unitInterval) := ⟨‖z.val‖, norm_nonneg _, mem_closedBall_zero_iff.mp z.property⟩
    let s : Degree.DiskCylinder.Sphere (E := E) :=
      ⟨NormedSpace.normalize z.val, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hz)⟩
    exact ⟨(t, s), Subtype.ext (NormedSpace.norm_smul_normalize z.val)⟩

private theorem Degree.DiskCone.radial_eq_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : (unitInterval) × Degree.DiskCylinder.Sphere (E := E)) :
    radial p = radial q ↔ p = q ∨ p.1 = 0 ∧ q.1 = 0 := by
  constructor
  · intro h
    have ht : p.1 = q.1 :=
      Subtype.ext
        ((radial_norm p).symm.trans
          ((congrArg (fun z : Degree.DiskCylinder.Disk (E := E) => ‖(z : E)‖) h).trans
            (radial_norm q)))
    by_cases hp : p.1 = 0
    · exact Or.inr ⟨hp, ht.symm.trans hp⟩
    · left
      apply Prod.ext ht
      apply Subtype.ext
      have hn : p.1.val ≠ 0 := fun he => hp (Subtype.ext he)
      have hv : p.1.val • p.2.val = q.1.val • q.2.val := congrArg Subtype.val h
      rw [← ht] at hv
      exact (smul_right_inj hn).mp hv
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · change radial (p.1, p.2) = radial (q.1, q.2)
      rw [hp, hq, radial_zero, radial_zero]

private theorem
    Degree.DiskCone.radial_isQuotientMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s0 : Degree.DiskCylinder.Sphere (E := E)) :
    Topology.IsQuotientMap (radial (E := E)) :=
  .of_surjective_continuous (radial_surjective s0) radial.continuous

private theorem Degree.DiskCone.constant_on_radial_fibres {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : Type*} [TopologicalSpace X]
    (G : C((unitInterval) × Degree.DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) (p q : (unitInterval) × Degree.DiskCylinder.Sphere (E := E))
    (h : radial p = radial q) : G p = G q := by
  rcases (radial_eq_iff p q).mp h with rfl | ⟨hp, hq⟩
  · rfl
  · change G (p.1, p.2) = G (q.1, q.2)
    rw [hp, hq, hG, hG]

private def Degree.DiskCone.extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (s0 : Degree.DiskCylinder.Sphere (E := E))
    (G : C((unitInterval) × Degree.DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) : C(Degree.DiskCylinder.Disk (E := E), X) :=
  (radial_isQuotientMap s0).lift G (constant_on_radial_fibres G x hG)

private theorem
    Degree.DiskCone.extension_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (s0 : Degree.DiskCylinder.Sphere (E := E))
    (G : C((unitInterval) × Degree.DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) (t : (unitInterval)) (s : Degree.DiskCylinder.Sphere (E := E)) :
    extension s0 G x hG (radial (t, s)) = G (t, s) :=
  ContinuousMap.congr_fun
    ((radial_isQuotientMap s0).lift_comp G (constant_on_radial_fibres G x hG)) (t, s)

private theorem
    Degree.DiskCone.extension_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (s0 : Degree.DiskCylinder.Sphere (E := E))
    (G : C((unitInterval) × Degree.DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) (s : Degree.DiskCylinder.Sphere (E := E)) :
    extension s0 G x hG (Degree.DiskCylinder.boundaryToDisk s) = G (1, s) := by
  rw [← radial_one, extension_radial]

private theorem
    Degree.DiskCone.extension_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (s0 : Degree.DiskCylinder.Sphere (E := E))
    (G : C((unitInterval) × Degree.DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) : extension s0 G x hG ⟨0, by simp⟩ = x := by
  rw [← radial_zero s0, extension_radial, hG]

private theorem Degree.UnitSphereEquiv.vector_ne_zero {E : Type*} [NormedAddCommGroup E]
    (u : Degree.DiskCylinder.Sphere (E := E)) : u.val ≠ 0 := by
  intro h
  have hn := mem_sphere_zero_iff_norm.mp u.property
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

private theorem Degree.UnitSphereEquiv.image_ne_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F)
    (u : Degree.DiskCylinder.Sphere (E := E)) : L u.val ≠ 0 := by
  intro h
  exact vector_ne_zero u (L.injective (h.trans (L.map_zero).symm))

private def Degree.UnitSphereEquiv.map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) :
    C(Degree.DiskCylinder.Sphere (E := E), Degree.DiskCylinder.Sphere (E := F))
    where
  toFun
    u :=
    ⟨NormedSpace.normalize (L u.val),
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (image_ne_zero L u))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (((L.continuous.comp continuous_subtype_val).norm.inv₀
            (fun u => norm_ne_zero_iff.mpr (image_ne_zero L u))).smul
        (L.continuous.comp continuous_subtype_val))

private theorem
    Degree.UnitSphereEquiv.map_inverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F)
    (u : Degree.DiskCylinder.Sphere (E := E)) :
    Degree.UnitSphereEquiv.map L.symm (Degree.UnitSphereEquiv.map L u) = u := by
  apply Subtype.ext
  change NormedSpace.normalize (L.symm (‖L u.val‖⁻¹ • L u.val)) = u.val
  rw [map_smul, L.symm_apply_apply,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr (image_ne_zero L u)))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp u.property)

private def Degree.UnitSphereEquiv.homeomorph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) :
    Degree.DiskCylinder.Sphere (E := E) ≃ₜ Degree.DiskCylinder.Sphere (E := F)
    where
  toFun := Degree.UnitSphereEquiv.map L
  invFun := Degree.UnitSphereEquiv.map L.symm
  left_inv := map_inverse L
  right_inv := map_inverse L.symm
  continuous_toFun := (Degree.UnitSphereEquiv.map L).continuous
  continuous_invFun := (Degree.UnitSphereEquiv.map L.symm).continuous

private theorem
    MorseCancel.unitSphere_eq_two_points_of_finrank_one {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 1)
    (u v : Metric.sphere (0 : V) 1) (huv : u ≠ v) (w : Metric.sphere (0 : V) 1) : w = u ∨ w = v :=
  by
  obtain ⟨L⟩ :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hdim)
  let e := Degree.UnitSphereEquiv.homeomorph L
  have hpoint (z : Metric.sphere (0 : V) 1) : (e z : ℝ) = 1 ∨ (e z : ℝ) = -1 := by
    have hz : |(e z : ℝ)| = |(1 : ℝ)| := by
      simpa only [Real.norm_eq_abs, abs_one] using mem_sphere_zero_iff_norm.mp (e z).property
    exact abs_eq_abs.mp hz
  have hne : (e u : ℝ) ≠ (e v : ℝ) := fun h => huv (e.injective (Subtype.ext h))
  have heq : (e w : ℝ) = (e u : ℝ) ∨ (e w : ℝ) = (e v : ℝ) := by
    rcases hpoint u with hu | hu <;> rcases hpoint v with hv | hv <;>
        rcases hpoint w with hw | hw <;>
      simp_all
  exact
    heq.elim (fun h => Or.inl (e.injective (Subtype.ext h)))
      (fun h => Or.inr (e.injective (Subtype.ext h)))

private theorem MorseCancel.exists_positive_height_rescaling {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ) (hχrange : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hdesc : ∀ x ∈ tsupport χ, mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    ∃ ρ : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ ∧
        (∀ x, 0 < ρ x) ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
              (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
              (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) < 0) ∧
                (∀ x, χ x = 1 → mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) = -1) ∧
                  ∀ x ∉ tsupport χ, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let ρ (x : M) := 1 - χ x + χ x / (-D x)
  have hD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D := contMDiff_directionalDerivative hf hV
  have hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_const.sub hχ).add
      (contMDiff_supported_division hχ hD.neg (fun x hx => neg_ne_zero.mpr (hdesc x hx).ne))
  have hpos (x : M) : 0 < ρ x := by
    by_cases hx : x ∈ tsupport χ
    · have hdx : 0 < -D x := neg_pos.mpr (hdesc x hx)
      by_cases he : χ x = 1
      · simpa only [ρ, he, sub_self, zero_add] using one_div_pos.mpr hdx
      · exact
          add_pos_of_pos_of_nonneg (sub_pos.mpr (lt_of_le_of_ne (hχrange x).2 he))
            (div_nonneg (hχrange x).1 hdx.le)
    · simp only [ρ, image_eq_zero_of_notMem_tsupport hx, sub_zero, zero_div, add_zero]
      exact zero_lt_one
  refine ⟨ρ, hρ, hpos, hρ.smul_section hV, ?_, ?_, ?_, ?_⟩
  · intro x
    exact smul_eq_zero.trans (or_iff_right (hpos x).ne')
  · intro x hx
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (hpos x) hx
  · intro x hx
    have hs : x ∈ tsupport χ := subset_tsupport χ (by simp [Function.mem_support, hx])
    have hd : D x ≠ 0 := (hdesc x hs).ne
    rw [map_smul, smul_eq_mul]
    change (1 - χ x + χ x / (-D x)) * D x = -1
    rw [hx]
    field_simp
    ring
  · intro x hx
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [ρ, image_eq_zero_of_notMem_tsupport hy, sub_zero, zero_div, add_zero]

private theorem MorseCancel.exists_positive_band_normalization {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {a b : ℝ} (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ (ρ : M → ℝ) (U : Set ℝ),
      IsOpen U ∧
        Set.Icc a b ⊆ U ∧
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ ∧
            (∀ x, 0 < ρ x) ∧
              ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                  (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
                  (∀ x,
                      x ∉ Smale.ManifoldMorse.criticalPoints E f →
                        mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) < 0) ∧
                    (∀ x, f x ∈ U → mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) = -1) ∧
                      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let B := f '' Smale.ManifoldMorse.criticalPoints E f
  have hB : IsClosed B :=
    ((Smale.ManifoldMorse.criticalPoints_isClosed hf).isCompact.image hf.continuous).isClosed
  have hAB : Set.Icc a b ⊆ Bᶜ := by
    rintro y hy ⟨x, hx, rfl⟩
    exact hband x hy hx
  obtain ⟨φ, hφ, hsupp, U, hU, hAU, -, hφU⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed isClosed_Icc hB.isOpen_compl hAB
  let χ := Real.smoothTransition ∘ φ ∘ f
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ :=
    (Real.smoothTransition.contDiff.comp hφ).contMDiff.comp hf
  have hχsupport : tsupport χ ⊆ (Smale.ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    have hp := tsupport_comp_subset Real.smoothTransition.zero (φ ∘ f) hx
    exact hsupp (tsupport_comp_subset_preimage φ hf.continuous hp) ⟨x, hcrit, rfl⟩
  obtain ⟨ρ, hρ, hpos, hW, hzero, hneg, hspeed, hgerm⟩ :=
    exists_positive_height_rescaling hf hV hχ
      (fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
      (fun x hx => hdesc x (hχsupport hx))
  refine ⟨ρ, U, hU, hAU, hρ, hpos, hW, hzero, fun x hx => hneg x (hdesc x hx), ?_, ?_⟩
  · intro x hx
    apply hspeed
    simp only [χ, Function.comp_apply, hφU hx, Real.smoothTransition.one]
  · intro x hx
    exact hgerm x (fun h => hχsupport h hx)

private theorem
    Degree.FlowTimeChange.local_affine_height_germ {γ : ℝ → ℝ} (hγ : Continuous γ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ t, γ t ∈ U → HasDerivAt γ (-1) t) {t : ℝ} (ht : γ t ∈ U) :
    ∀ᶠ s in 𝓝 t, γ s + s = γ t + t := by
  obtain ⟨l, u, htu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ((hU.preimage hγ).mem_nhds ht)
  have hder (s : ℝ) (hs : s ∈ Set.Ioo l u) : HasDerivAt (fun r => γ r + r) 0 s := by
    convert! (hd s (hsub hs)).add (hasDerivAt_id s) using 1
    norm_num
  filter_upwards [Ioo_mem_nhds htu.1 htu.2] with s hs
  exact
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hder r hr).deriv) hs htu

private theorem
    Degree.FlowTimeChange.scalar_local_height_translation {γ : ℝ → ℝ} (hγ : Continuous γ)
    {U : Set ℝ} (hU : IsOpen U) {a b c t : ℝ} (hIU : Set.Icc a b ⊆ U)
    (hd : ∀ s, γ s ∈ U → HasDerivAt γ (-1) s) (hzero : γ 0 = c) (hc : c ∈ Set.Icc a b)
    (ht : c - t ∈ Set.Icc a b) : γ t = c - t := by
  let J := Set.Icc (c - b) (c - a)
  let _ : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let P : J → Prop := fun s => γ s = c - s
  have hloc : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro s
    by_cases hs : P s
    · have hsU : γ s ∈ U := by
        rw [show γ s = c - s from hs]
        exact hIU ⟨by linarith [s.property.2], by linarith [s.property.1]⟩
      have heq := local_affine_height_germ hγ hU hd hsU
      filter_upwards [continuous_subtype_val.continuousAt heq] with r hr
      apply propext
      constructor
      · intro _
        exact hs
      · intro _
        change γ r = c - r
        change γ s = c - s at hs
        change γ r + r = γ s + s at hr
        linarith
    · have hn : (s : ℝ) ∈ {r : ℝ | γ r = c - r}ᶜ := hs
      have hopen : IsOpen {r : ℝ | γ r = c - r}ᶜ :=
        (isClosed_eq hγ ((continuous_const (y := c)).sub continuous_id)).isOpen_compl
      filter_upwards [continuous_subtype_val.continuousAt (hopen.mem_nhds hn)] with r hr
      exact propext ⟨fun h => (hr h).elim, fun h => (hs h).elim⟩
  let s₀ : J := ⟨0, ⟨by linarith [hc.2], by linarith [hc.1]⟩⟩
  let s₁ : J := ⟨t, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  have hinit : P s₀ := by simpa only [P, s₀, sub_zero] using hzero
  have heq : P s₀ = P s₁ := hloc.apply_eq_of_preconnectedSpace s₀ s₁
  have hfinish : P s₁ := heq ▸ hinit
  exact hfinish

private theorem
    Degree.FlowTimeChange.native_local_height_translation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {U : Set ℝ} (hU : IsOpen U)
    {a b : ℝ} (hIU : Set.Icc a b ⊆ U) (hspeed : ∀ x, f x ∈ U → mvfderiv 𝓘(ℝ, E) f x (V x) = -1)
    (x : M) (t : ℝ) (hx : f x ∈ Set.Icc a b) (ht : f x - t ∈ Set.Icc a b) : f (F t x) = f x - t :=
  by
  apply
    scalar_local_height_translation
      (hf.continuous.comp (F.continuous continuous_id continuous_const)) hU hIU (γ := fun s =>
      f (F s x)) ?_ (by rw [F.map_zero_apply]) hx ht
  intro s hs
  have hd := Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) s
  rw [hspeed (F s x) hs] at hd
  exact hd

private theorem Degree.FlowTimeChange.normalized_flow_level_image {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Set.Icc a b → f x - t ∈ Set.Icc a b → f (F t x) = f x - t) :
    F (a - b) '' {x : X | f x = a} = {x : X | f x = b} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change f x = a at hx
    have hh :=
      hshift x (a - b) (by rw [hx]; exact ⟨le_rfl, hab⟩) (by rw [hx]; constructor <;> linarith)
    change f (F (a - b) x) = b
    linarith
  · intro hy
    change f y = b at hy
    have hh :=
      hshift y (b - a) (by rw [hy]; exact ⟨hab, le_rfl⟩) (by rw [hy]; constructor <;> linarith)
    refine ⟨F (b - a) y, ?_, ?_⟩
    · change f (F (b - a) y) = a
      linarith
    · rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]

private theorem Degree.FlowTimeChange.normalized_flow_sublevel_iff {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Set.Icc a b → f x - t ∈ Set.Icc a b → f (F t x) = f x - t) (x : X) :
    f (F (a - b) x) ≤ b ↔ f x ≤ a := by
  let γ : ℝ → ℝ := fun s => f (F (-s) x) - (a + s)
  have hγ : Continuous γ :=
    (hf.comp (F.continuous ContinuousNeg.continuous_neg continuous_const)).sub
      (continuous_const.add continuous_id)
  have hstart : γ 0 = f x - a := by simp only [γ, neg_zero, F.map_zero_apply, add_zero]
  have hend : γ (b - a) = f (F (a - b) x) - b := by
    dsimp [γ]
    rw [neg_sub, show a + (b - a) = b by ring]
  have hzero (s : ℝ) (hs : s ∈ Set.Icc 0 (b - a)) (hgs : γ s = 0) : f x = a := by
    have hz : f (F (-s) x) = a + s := by dsimp [γ] at hgs; linarith
    have hh :=
      hshift (F (-s) x) s (by rw [hz]; constructor <;> linarith [hs.1, hs.2])
        (by rw [hz]; constructor <;> linarith)
    rw [← F.map_add, add_neg_cancel, F.map_zero_apply] at hh
    linarith
  have hzeroEnd (hx : f x = a) : γ (b - a) = 0 := by
    have hh :=
      hshift x (a - b) (by rw [hx]; exact ⟨le_rfl, hab⟩) (by rw [hx]; constructor <;> linarith)
    rw [hend]
    linarith
  constructor
  · intro hy
    by_contra hx
    have hx' : a < f x := lt_of_not_ge hx
    obtain ⟨s, hs, hgs⟩ :=
      intermediate_value_Icc' (sub_nonneg.mpr hab) hγ.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (γ (b - a)) (γ 0) by rw [hstart, hend]; constructor <;> linarith)
    linarith [hzero s hs hgs]
  · intro hx
    by_contra hy
    have hy' : b < f (F (a - b) x) := lt_of_not_ge hy
    obtain ⟨s, hs, hgs⟩ :=
      intermediate_value_Icc (sub_nonneg.mpr hab) hγ.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (γ 0) (γ (b - a)) by rw [hstart, hend]; constructor <;> linarith)
    have hh := hzeroEnd (hzero s hs hgs)
    rw [hend] at hh
    linarith

private theorem
    Degree.FlowTimeChange.normalized_flow_sublevel_image {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Set.Icc a b → f x - t ∈ Set.Icc a b → f (F t x) = f x - t) :
    F (a - b) '' {x : X | f x ≤ a} = {x : X | f x ≤ b} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (normalized_flow_sublevel_iff F hf hab hshift x).mpr hx
  · intro hy
    have hi : F (a - b) (F (b - a) y) = y := by
      rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]
    refine ⟨F (b - a) y, ?_, hi⟩
    apply (normalized_flow_sublevel_iff F hf hab hshift _).mp
    rw [hi]
    exact hy

private theorem Degree.FlowTimeChange.exists_positive_integral_clock {a : ℝ → ℝ} (ha : Continuous a)
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ t, δ ≤ a t) :
    ∃ c : ℝ ≃o ℝ,
      c 0 = 0 ∧
        (∀ t, c t = ∫ s in (0 : ℝ)..t, a s) ∧
          (∀ t, HasDerivAt c (a t) t) ∧ ∀ t, HasDerivAt c.symm (a (c.symm t))⁻¹ t := by
  let g : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s
  have hd (t : ℝ) : HasDerivAt g (a t) t :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
      ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hg : Differentiable ℝ g := fun t => (hd t).differentiableAt
  have hzero : g 0 = 0 := by simp [g]
  have hmono : StrictMono g := strictMono_of_hasDerivAt_pos hd (fun t => hδ.trans_le (hlower t))
  have hbound {s t : ℝ} (hst : s ≤ t) : δ * (t - s) ≤ g t - g s :=
    mul_sub_le_image_sub_of_le_deriv hg (fun t => by rw [(hd t).deriv]; exact hlower t) hst
  have hsurj : Function.Surjective g := by
    intro y
    apply mem_range_of_exists_le_of_exists_ge hg.continuous
    · refine ⟨Min.min 0 (y / δ), ?_⟩
      have hh := hbound (min_le_left 0 (y / δ))
      have hm : δ * Min.min 0 (y / δ) ≤ y := by
        calc
          δ * Min.min 0 (y / δ) ≤ δ * (y / δ) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le
          _ = y := by field_simp
      rw [hzero] at hh
      linarith
    · refine ⟨Max.max 0 (y / δ), ?_⟩
      have hh := hbound (le_max_left 0 (y / δ))
      have hm : y ≤ δ * Max.max 0 (y / δ) := by
        calc
          y = δ * (y / δ) := by field_simp
          _ ≤ δ * Max.max 0 (y / δ) := mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le
      rw [hzero] at hh
      linarith
  let c : ℝ ≃o ℝ := hmono.orderIsoOfSurjective g hsurj
  refine ⟨c, hzero, fun _ => rfl, hd, ?_⟩
  intro t
  exact
    HasDerivAt.of_local_left_inverse c.symm.continuous.continuousAt (hd (c.symm t))
      (ne_of_gt (hδ.trans_le (hlower _))) (Filter.Eventually.of_forall c.apply_symm_apply)

private theorem Degree.FlowTimeChange.native_curve_positive_reparametrization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ρ : M → ℝ} {γ : ℝ → M} (hγ : IsMIntegralCurve γ V)
    {c : ℝ → ℝ} (hc : ∀ t, HasDerivAt c (ρ (γ (c t))) t) :
    IsMIntegralCurve (γ ∘ c) (fun x => ρ x • V x) := by
  intro t
  have hh := (hγ (c t)).comp t (hc t).hasFDerivAt.hasMFDerivAt
  have he :
    (1 : ℝ →L[ℝ] ℝ).smulRight (ρ (γ (c t)) • V (γ (c t))) =
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ (c t)))).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (ρ (γ (c t)))) := by
    ext
    simp [smul_smul, mul_comm]
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ c) t ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (γ (c t)) • V (γ (c t))))
  rw [he]
  exact hh

private theorem
    Degree.FlowTimeChange.exists_native_flow_time_change {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] {ρ : M → ℝ} (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (hW :
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) (fun y => ρ y • V y)) (x : M) :
    ∃ c : ℝ ≃o ℝ,
      c 0 = 0 ∧
        (∀ t, c t = ∫ s in (0 : ℝ)..t, (ρ (F s x))⁻¹) ∧
          (∀ t, HasDerivAt c.symm (ρ (F (c.symm t) x)) t) ∧ ∀ t, G t x = F (c.symm t) x := by
  obtain ⟨R, hR⟩ := (isCompact_univ.image hρ).bddAbove
  have hbound (y : M) : ρ y ≤ R := hR ⟨y, Set.mem_univ _, rfl⟩
  have hRpos : 0 < R := (hρpos x).trans_le (hbound x)
  have ha : Continuous (fun t => (ρ (F t x))⁻¹) :=
    (hρ.comp (F.continuous continuous_id continuous_const)).inv₀ (fun t => (hρpos _).ne')
  have hlower (t : ℝ) : R⁻¹ ≤ (ρ (F t x))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (hρpos (F t x)) (hbound (F t x))
  obtain ⟨c, hc0, hcint, -, hcinv⟩ := exists_positive_integral_clock ha (inv_pos.mpr hRpos) hlower
  have hcinv' (t : ℝ) : HasDerivAt c.symm (ρ (F (c.symm t) x)) t := by
    simpa only [inv_inv] using hcinv t
  have hcurve := native_curve_positive_reparametrization (hF x) hcinv'
  have hc0' : c.symm 0 = 0 := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact hc0.symm
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hW (hG x) hcurve (t₀ := 0)
      (by simp only [Function.comp_apply, hc0', F.map_zero_apply, G.map_zero_apply])
  exact ⟨c, hc0, hcint, hcinv', fun t => congrFun heq t⟩

end Mathoverflow1973

end
