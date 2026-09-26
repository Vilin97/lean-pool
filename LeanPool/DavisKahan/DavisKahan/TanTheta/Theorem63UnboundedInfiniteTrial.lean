/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module


public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrial
public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63Unbounded

/-! # Theorem63Unbounded Infinite Trial -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Theorem 6.3 for an unbounded operator and an arbitrary trial space

Davis--Kahan's Appendix removes the finite-dimensional trial-space hypothesis from the
single-angle tangent theorem by finite-projector approximation.  Two halves of that
argument already existed separately:

* `Theorem63Unbounded.lean` proves the printed unbounded theorem for a finite trial space;
* `Theorem63InfiniteTrial.lean` proves the Appendix finite-projector passage for a bounded
  ambient operator and an arbitrary complete trial space.

The finite-projector passage only uses bounded trial-block data: the self-adjoint Ritz
compression, the residual, and the action on the trial space.  Those are precisely the
fields of `Theorem63TrialData`, including for an `BoundedCompressionTrialBlock`.  This module lifts
the Appendix argument to that data abstraction and then instantiates it at the unbounded
trial block.

No doubled-angle theorem enters this proof.  The only approximation operator used to find
finite almost-invariant subspaces is the bounded self-adjoint Ritz compression.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open TanTheta
open Module (finrank)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## Infinite-trial passage over abstract trial-block data -/

namespace Theorem63TrialData

variable {Z V : Submodule ℂ H}
  [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]

omit [CompleteSpace H] [CompleteSpace Z] in
/-- The residual of restricted trial-block data is the old residual restricted to the
smaller trial space plus the leakage of the old compression out of that space. -/
theorem restrict_residual_apply_eq
    (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] (f : F) :
    (data.restrict F hFZ).residual f =
      data.residual (inclCLM hFZ f) +
        (((data.compression (inclCLM hFZ f) : Z) : H) -
          F.starProjection ((data.compression (inclCLM hFZ f) : Z) : H)) := by
  have hresF : data.residual (inclCLM hFZ f) ∈ Fᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    exact data.inner_residual_left (inclCLM hFZ f) ⟨y, hFZ hy⟩
  have hprojres : F.starProjection (data.residual (inclCLM hFZ f)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff F).mpr hresF
  change data.action (inclCLM hFZ f) -
      F.starProjection (data.action (inclCLM hFZ f)) = _
  rw [data.action_eq, map_add, hprojres]
  simp only [add_zero]
  abel

omit [CompleteSpace ↥Z] in
/-- Restricting trial-block data to `F ≤ Z` costs at most `k * ε` in the `k`-th Ky Fan
approximation gauge when the Ritz compression leaks from `F` by at most `ε`. -/
theorem kyFanApproximationGauge_restrict_residual_le_add
    (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z)
    [F.HasOrthogonalProjection] [CompleteSpace F]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hleak : ∀ f : F,
      ‖((data.compression (inclCLM hFZ f) : Z) : H) -
          F.starProjection ((data.compression (inclCLM hFZ f) : Z) : H)‖ ≤
        ε * ‖(f : H)‖)
    (k : ℕ) :
    kyFanApproximationGauge k (data.restrict F hFZ).residual ≤
      kyFanApproximationGauge k data.residual + (k : ℝ) * ε := by
  classical
  set J : F →L[ℂ] Z := inclCLM hFZ with hJ_def
  have hJnorm : ‖J‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    change ‖((x : F) : H)‖ ≤ 1 * ‖x‖
    simp
  set G : F →L[ℂ] H :=
    Z.subtypeL ∘L data.compression ∘L J -
      F.starProjection ∘L Z.subtypeL ∘L data.compression ∘L J with hG_def
  have hGnorm : ‖G‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε fun f => ?_
    have hGf : G f =
        ((data.compression (inclCLM hFZ f) : Z) : H) -
          F.starProjection ((data.compression (inclCLM hFZ f) : Z) : H) := by
      rfl
    rw [hGf]
    exact hleak f
  have hsplit : (data.restrict F hFZ).residual = data.residual ∘L J + G := by
    apply ContinuousLinearMap.ext
    intro f
    rw [restrict_residual_apply_eq data F hFZ f]
    rfl
  calc
    kyFanApproximationGauge k (data.restrict F hFZ).residual =
        kyFanApproximationGauge k (data.residual ∘L J + G) := by rw [hsplit]
    _ ≤ kyFanApproximationGauge k (data.residual ∘L J) +
        kyFanApproximationGauge k G :=
      kyFanApproximationGauge_add_le_complex k _ _
    _ ≤ kyFanApproximationGauge k data.residual + (k : ℝ) * ε := by
      have h1 : kyFanApproximationGauge k (data.residual ∘L J) ≤
          kyFanApproximationGauge k data.residual := by
        have h := kyFanApproximationGauge_comp_le k
          (ContinuousLinearMap.id ℂ H) data.residual J
        rw [ContinuousLinearMap.id_comp] at h
        refine h.trans ?_
        have hid : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        have hnn := kyFanApproximationGauge_nonneg k data.residual
        calc
          ‖ContinuousLinearMap.id ℂ H‖ * kyFanApproximationGauge k data.residual * ‖J‖ ≤
              1 * kyFanApproximationGauge k data.residual * ‖J‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg J)
            exact mul_le_mul_of_nonneg_right hid hnn
          _ ≤ 1 * kyFanApproximationGauge k data.residual * 1 := by
            apply mul_le_mul_of_nonneg_left hJnorm
            simpa using hnn
          _ = kyFanApproximationGauge k data.residual := by ring
      have h2 : kyFanApproximationGauge k G ≤ (k : ℝ) * ε := by
        refine (kyFanApproximationGauge_le_nat_mul_opNorm k G).trans ?_
        exact mul_le_mul_of_nonneg_left hGnorm (Nat.cast_nonneg k)
      linarith

omit [CompleteSpace H] in
/-- A finite-dimensional enlargement inside `Z` that is almost invariant for the bounded
self-adjoint Ritz compression carried by the trial data. -/
theorem exists_finiteDimensional_superset_compression_leak
    (data : Theorem63TrialData Z V)
    (F₀ : Submodule ℂ H) (hF₀Z : F₀ ≤ Z) [FiniteDimensional ℂ F₀]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Submodule ℂ H) (_ : FiniteDimensional ℂ F)
      (_ : F₀ ≤ F) (hFZ : F ≤ Z),
      ∀ f : F, ∃ y ∈ F,
        ‖((data.compression (inclCLM hFZ f) : Z) : H) - y‖ ≤
          ε * ‖(f : H)‖ := by
  classical
  have hMsa : IsSelfAdjoint data.compression :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr data.compression_isSymmetric
  have : FiniteDimensional ℂ (F₀.comap Z.subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hF₀Z).symm
  obtain ⟨F', hF'fin, hF₀'F', hleak'⟩ :=
    TauCeti.BorelCalculus.exists_finiteDimensional_le_almostInvariant hMsa
      (F₀.comap Z.subtype) hε
  have := hF'fin
  let F : Submodule ℂ H := F'.map Z.subtype
  have hFZ : F ≤ Z := Submodule.map_subtype_le Z F'
  refine ⟨F, inferInstance, ?_, hFZ, ?_⟩
  · have hmapeq : (F₀.comap Z.subtype).map Z.subtype = F₀ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.mpr hF₀Z
    rw [← hmapeq]
    exact Submodule.map_mono hF₀'F'
  · intro f
    obtain ⟨x, hxF', hxf⟩ := (Submodule.mem_map).mp f.2
    have hxJ : inclCLM hFZ f = x := by
      apply Subtype.ext
      exact hxf.symm
    obtain ⟨y, hyF', hy⟩ := hleak' x hxF'
    have hyH : (y : H) ∈ F := Submodule.mem_map_of_mem hyF'
    refine ⟨(y : H), hyH, ?_⟩
    have hxnorm : ‖x‖ = ‖(f : H)‖ := by
      change ‖Z.subtype x‖ = ‖(f : H)‖
      exact congrArg norm hxf
    have hnorm :
        ‖((data.compression (inclCLM hFZ f) : Z) : H) - (y : H)‖ =
          ‖data.compression x - y‖ := by
      rw [hxJ]
      rfl
    calc
      ‖((data.compression (inclCLM hFZ f) : Z) : H) - (y : H)‖ =
          ‖data.compression x - y‖ := hnorm
      _ ≤ ε * ‖x‖ := hy
      _ = ε * ‖(f : H)‖ := by rw [hxnorm]

omit [CompleteSpace ↥Z] in
omit [CompleteSpace H] in
/-- The finite-dimensional no-pole fact over abstract trial-block data, stated with
approximation numbers rather than finite-source indices. -/
theorem approximationSingularValue_sineBlock_lt_one_of_finiteData
    (data : Theorem63TrialData Z V) [FiniteDimensional ℂ Z]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock Z V) < 1 := by
  by_cases hn : n < finrank ℂ Z
  · have hlt := data.sine_lt_one_of_formBounds hdelta hMupper hcross ⟨n, hn⟩
    have hb := approximationSingularValue_eq_finiteSourceSingularValue
      (theorem63DirectedSineBlock Z V) ⟨n, hn⟩
    simpa using hb ▸ hlt
  · have h0 := approximationSingularValue_eq_zero_of_finrank_le_complex
      (Z := Z) (theorem63DirectedSineBlock Z V) (le_of_not_gt hn)
    rw [h0]
    exact one_pos

section InfiniteCore

variable (data : Theorem63TrialData Z V)

omit [CompleteSpace ↥Z] in
/-- The finite Appendix step over abstract trial-block data. -/
private theorem finite_leak_step
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (k' : ℕ) (F : Submodule ℂ H) (hFZ : F ≤ Z)
    [F.HasOrthogonalProjection] [CompleteSpace F] [FiniteDimensional ℂ F]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hleak : ∀ f : F,
      ‖((data.compression (inclCLM hFZ f) : Z) : H) -
          F.starProjection ((data.compression (inclCLM hFZ f) : Z) : H)‖ ≤
        ε * ‖(f : H)‖) :
    delta * ∑ n ∈ Finset.range k', Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V))) ≤
      kyFanApproximationGauge k' data.residual + (k' : ℝ) * ε := by
  let dataF := data.restrict F hFZ
  have hMupperF := data.restrict_compression_upper F hFZ hMupper
  have hcrossF := data.restrict_crossed_lower F hFZ hcross
  have hlt : ∀ i : Fin (finrank ℂ F),
      finiteSourceSingularValue (theorem63DirectedSineBlock F V) i < 1 :=
    dataF.sine_lt_one_of_formBounds hdelta hMupperF hcrossF
  have htan := hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent
    F V hlt
  have hcore := dataF.all_kyFan_core_of_formBounds hdelta hMupperF hcrossF
    (theorem63DirectedTangent F V) htan k'
  have hKyTan : kyFanApproximationGauge k' (theorem63DirectedTangent F V) =
      ∑ n ∈ Finset.range k', Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := htan n
    unfold approximationSingularValue at h
    exact h
  calc
    delta * ∑ n ∈ Finset.range k', Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V))) =
        delta * kyFanApproximationGauge k' (theorem63DirectedTangent F V) := by
      rw [hKyTan]
    _ ≤ kyFanApproximationGauge k' dataF.residual := hcore
    _ ≤ kyFanApproximationGauge k' data.residual + (k' : ℝ) * ε :=
      data.kyFanApproximationGauge_restrict_residual_le_add F hFZ hε hleak k'

/-- Under the printed form gap, every approximation singular value of the directed sine
block is strictly below one at arbitrary trial dimension. -/
theorem approximationSingularValue_sineBlock_lt_one_infiniteData
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock Z V) < 1 := by
  classical
  by_contra hcon
  have ha_le : approximationSingularValue n (theorem63DirectedSineBlock Z V) ≤ 1 := by
    refine (approximationSingularValue_le_opNorm _ _).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [one_mul]
    exact theorem63DirectedSineBlock_apply_norm_le Z V z
  have haeq : approximationSingularValue n (theorem63DirectedSineBlock Z V) = 1 :=
    le_antisymm ha_le (le_of_not_gt fun h => hcon h)
  set B' : ℝ := kyFanApproximationGauge (n + 1) data.residual with hB'_def
  have hB'0 : 0 ≤ B' := kyFanApproximationGauge_nonneg _ _
  set C : ℝ := B' / delta + 1 with hC_def
  have hC0 : 0 ≤ C := by positivity
  set c : ℝ := Real.sin (Real.arctan C) with hc_def
  have hc0 : 0 ≤ c := Real.sin_arctan_nonneg.mpr hC0
  have hclt : c < approximationSingularValue n (theorem63DirectedSineBlock Z V) := by
    rw [haeq]
    exact TanArcsin.sin_arctan_lt_one C
  obtain ⟨F₁, hF₁fin, hF₁Z, hF₁⟩ :=
    exists_finiteDimensional_le_lt_approximationSingularValue
      (Vᗮ.starProjection) Z n hc0 hclt
  have := hF₁fin
  have hεp : (0 : ℝ) < delta / (2 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨F, hFfin, hF₁F, hFZ, hleak₀⟩ :=
    data.exists_finiteDimensional_superset_compression_leak F₁ hF₁Z hεp
  let : FiniteDimensional ℂ F := hFfin
  have : F.HasOrthogonalProjection := inferInstance
  have hleak : ∀ f : F,
      ‖((data.compression (inclCLM hFZ f) : Z) : H) -
          F.starProjection ((data.compression (inclCLM hFZ f) : Z) : H)‖ ≤
        delta / (2 * ((n : ℝ) + 1)) * ‖(f : H)‖ := by
    intro f
    obtain ⟨y, hyF, hy⟩ := hleak₀ f
    exact (norm_sub_starProjection_le_of_mem _ hyF).trans hy
  have hmono : approximationSingularValue n (theorem63DirectedSineBlock F₁ V) ≤
      approximationSingularValue n (theorem63DirectedSineBlock F V) :=
    approximationSingularValue_restrict_mono (Vᗮ.starProjection) n hF₁F
  have hcF : c < approximationSingularValue n (theorem63DirectedSineBlock F V) :=
    lt_of_lt_of_le hF₁ hmono
  let dataF := data.restrict F hFZ
  have hMupperF := data.restrict_compression_upper F hFZ hMupper
  have hcrossF := data.restrict_crossed_lower F hFZ hcross
  have hFlt1 : approximationSingularValue n (theorem63DirectedSineBlock F V) < 1 :=
    dataF.approximationSingularValue_sineBlock_lt_one_of_finiteData
      hdelta hMupperF hcrossF n
  have hgc : Real.tan (Real.arcsin c) ≤ Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlock F V))) :=
    TanArcsin.tanArcsin_le_tanArcsin hc0 hcF.le hFlt1
  have hsum : Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlock F V))) ≤
      ∑ m ∈ Finset.range (n + 1), Real.tan (Real.arcsin
        (approximationSingularValue m (theorem63DirectedSineBlock F V))) := by
    refine Finset.single_le_sum
      (f := fun m => Real.tan (Real.arcsin
        (approximationSingularValue m (theorem63DirectedSineBlock F V))))
      (fun m _ => TanArcsin.tanArcsin_nonneg (approximationSingularValue_nonneg _ _))
      (Finset.self_mem_range_succ n)
  have hfinal := finite_leak_step data hdelta hMupper hcross
    (n + 1) F hFZ hεp.le hleak
  have hCval : Real.tan (Real.arcsin c) = C := TanArcsin.tanArcsin_sin_arctan C
  have hchain : delta * C ≤ B' + delta / 2 := by
    have h1 : delta * Real.tan (Real.arcsin c) ≤
        delta * ∑ m ∈ Finset.range (n + 1), Real.tan (Real.arcsin
          (approximationSingularValue m (theorem63DirectedSineBlock F V))) :=
      mul_le_mul_of_nonneg_left (hgc.trans hsum) hdelta.le
    have h2 : ((n : ℝ) + 1) * (delta / (2 * ((n : ℝ) + 1))) = delta / 2 := by
      field_simp
    rw [hCval] at h1
    calc
      delta * C ≤ delta * ∑ m ∈ Finset.range (n + 1), Real.tan (Real.arcsin
          (approximationSingularValue m (theorem63DirectedSineBlock F V))) := h1
      _ ≤ B' + ((n : ℝ) + 1) * (delta / (2 * ((n : ℝ) + 1))) := by
        push_cast at hfinal ⊢
        linarith
      _ = B' + delta / 2 := by rw [h2]
  have hCeq : delta * C = B' + delta := by
    rw [hC_def]
    field_simp
  linarith

/-- **The Appendix Ky Fan passage over arbitrary complete trial-block data.**

This is the dimension-removal theorem needed for the unbounded source scope.  It only
uses the bounded self-adjoint Ritz compression carried by `data`; the ambient action may
come from an unbounded operator. -/
theorem all_kyFan_core_of_formBounds_infinite
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (k : ℕ) :
    delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
      kyFanApproximationGauge k data.residual := by
  classical
  have ha_lt_one : ∀ n, approximationSingularValue n
      (theorem63DirectedSineBlock Z V) < 1 := fun n =>
    data.approximationSingularValue_sineBlock_lt_one_infiniteData
      hdelta hMupper hcross n
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    exact kyFanApproximationGauge_nonneg _ _
  refine le_of_forall_pos_le_add fun κ hκ => ?_
  have hk0R : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkpos
  set κ' : ℝ := κ / (2 * delta * (k : ℝ)) with hκ'_def
  have hκ'0 : 0 < κ' := by positivity
  have hkey : ∀ n ∈ Finset.range k, ∃ Fn : Submodule ℂ H,
      FiniteDimensional ℂ Fn ∧ Fn ≤ Z ∧
      ∀ (F : Submodule ℂ H), Fn ≤ F → F ≤ Z →
        ∀ [F.HasOrthogonalProjection] [FiniteDimensional ℂ F],
        Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
        Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock F V))) + κ' := by
    intro n _
    set an : ℝ := approximationSingularValue n (theorem63DirectedSineBlock Z V)
      with han_def
    have han0 : 0 ≤ an := approximationSingularValue_nonneg _ _
    rcases eq_or_lt_of_le han0 with hzero | hpos
    · refine ⟨⊥, inferInstance, bot_le, ?_⟩
      intro F _ hFZ _ _
      have h0 : Real.tan (Real.arcsin an) = 0 := by
        rw [← hzero, Real.arcsin_zero, Real.tan_zero]
      rw [h0]
      have := TanArcsin.tanArcsin_nonneg
        (approximationSingularValue_nonneg n (theorem63DirectedSineBlock F V))
      linarith
    · have hcont := TanArcsin.continuousAt_tanArcsin han0 (ha_lt_one n)
      obtain ⟨d, hd0, hd⟩ := Metric.continuousAt_iff.mp hcont κ' hκ'0
      set cn : ℝ := max (an - d / 2) 0 with hcn_def
      have hcn0 : 0 ≤ cn := le_max_right _ _
      have hcnlt : cn < an := by
        rcases le_or_gt (an - d / 2) 0 with hle | hgt
        · rw [hcn_def, max_eq_right hle]
          exact hpos
        · rw [hcn_def, max_eq_left hgt.le]
          linarith
      have hcnnear : dist cn an < d := by
        rw [Real.dist_eq, abs_lt]
        constructor
        · rcases le_or_gt (an - d / 2) 0 with hle | hgt
          · rw [hcn_def, max_eq_right hle]
            simp only [zero_sub, neg_lt_neg_iff]
            linarith
          · rw [hcn_def, max_eq_left hgt.le]
            linarith
        · linarith [hcnlt]
      have hnear := hd hcnnear
      rw [Real.dist_eq, abs_lt] at hnear
      obtain ⟨Fn, hFnfin, hFnZ, hFn⟩ :=
        exists_finiteDimensional_le_lt_approximationSingularValue
          (Vᗮ.starProjection) Z n hcn0 hcnlt
      refine ⟨Fn, hFnfin, hFnZ, ?_⟩
      intro F hFnF hFZ _ _
      have := hFnfin
      have hmono : approximationSingularValue n (theorem63DirectedSineBlock Fn V) ≤
          approximationSingularValue n (theorem63DirectedSineBlock F V) :=
        approximationSingularValue_restrict_mono (Vᗮ.starProjection) n hFnF
      have hcF : cn ≤ approximationSingularValue n (theorem63DirectedSineBlock F V) :=
        (lt_of_lt_of_le hFn hmono).le
      let dataF := data.restrict F hFZ
      have hMupperF := data.restrict_compression_upper F hFZ hMupper
      have hcrossF := data.restrict_crossed_lower F hFZ hcross
      have hFlt1 : approximationSingularValue n (theorem63DirectedSineBlock F V) < 1 :=
        dataF.approximationSingularValue_sineBlock_lt_one_of_finiteData
          hdelta hMupperF hcrossF n
      have hgmono : Real.tan (Real.arcsin cn) ≤ Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock F V))) :=
        TanArcsin.tanArcsin_le_tanArcsin hcn0 hcF hFlt1
      linarith [hnear.1, hnear.2]
  choose Fn hFnfin hFnZ hFnbound using hkey
  set F₀ : Submodule ℂ H :=
    (Finset.range k).attach.sup (fun p => Fn p.1 p.2) with hF₀_def
  have : ∀ p : { x // x ∈ Finset.range k }, FiniteDimensional ℂ (Fn p.1 p.2) :=
    fun p => hFnfin p.1 p.2
  have hF₀fin : FiniteDimensional ℂ F₀ :=
    Submodule.finiteDimensional_finset_sup _ _
  have hF₀Z : F₀ ≤ Z := Finset.sup_le fun p _ => hFnZ p.1 p.2
  have hεp : (0 : ℝ) < κ / (2 * (k : ℝ)) := by positivity
  obtain ⟨F, hFfin, hF₀F, hFZ, hleak₀⟩ :=
    data.exists_finiteDimensional_superset_compression_leak F₀ hF₀Z hεp
  let : FiniteDimensional ℂ F := hFfin
  have : F.HasOrthogonalProjection := inferInstance
  have hleak : ∀ f : F,
      ‖((data.compression (inclCLM hFZ f) : Z) : H) -
          F.starProjection ((data.compression (inclCLM hFZ f) : Z) : H)‖ ≤
        κ / (2 * (k : ℝ)) * ‖(f : H)‖ := by
    intro f
    obtain ⟨y, hyF, hy⟩ := hleak₀ f
    exact (norm_sub_starProjection_le_of_mem _ hyF).trans hy
  have hperterm : ∀ n ∈ Finset.range k,
      Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
      Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V))) + κ' := by
    intro n hn
    have hFnF : Fn n hn ≤ F := by
      refine le_trans ?_ hF₀F
      exact Finset.le_sup (f := fun p : { x // x ∈ Finset.range k } => Fn p.1 p.2)
        (Finset.mem_attach _ ⟨n, hn⟩)
    exact hFnbound n hn F hFnF hFZ
  have hsumbound : ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
      (∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V)))) +
        (k : ℝ) * κ' := by
    calc
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
          ∑ n ∈ Finset.range k, (Real.tan (Real.arcsin
            (approximationSingularValue n (theorem63DirectedSineBlock F V))) + κ') :=
        Finset.sum_le_sum hperterm
      _ = (∑ n ∈ Finset.range k, Real.tan (Real.arcsin
            (approximationSingularValue n (theorem63DirectedSineBlock F V)))) +
          (k : ℝ) * κ' := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfinstep := finite_leak_step data hdelta hMupper hcross
    k F hFZ hεp.le hleak
  have hδκ' : delta * ((k : ℝ) * κ') = κ / 2 := by
    rw [hκ'_def]
    field_simp
  have hkε : (k : ℝ) * (κ / (2 * (k : ℝ))) = κ / 2 := by
    field_simp
  calc
    delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
        delta * ((∑ n ∈ Finset.range k, Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock F V)))) +
            (k : ℝ) * κ') :=
      mul_le_mul_of_nonneg_left hsumbound hdelta.le
    _ = delta * (∑ n ∈ Finset.range k, Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock F V)))) +
        delta * ((k : ℝ) * κ') := by ring
    _ ≤ (kyFanApproximationGauge k data.residual +
          (k : ℝ) * (κ / (2 * (k : ℝ)))) + delta * ((k : ℝ) * κ') := by
      linarith [hfinstep]
    _ = kyFanApproximationGauge k data.residual + κ := by
      rw [hkε, hδκ']
      ring

/-- Fan-dominance endpoint for arbitrary complete trial-block data. -/
theorem ideal_of_formBounds_infinite
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem data.residual) :
    N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge data.residual := by
  refine ExactSinTheta.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N.toFanDominantIdealFamily hdelta hResidual fun k => ?_
  have hcore := data.all_kyFan_core_of_formBounds_infinite hdelta hMupper hcross k
  have hKyTan : kyFanApproximationGauge k tanTheta0 =
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := htan n
    unfold approximationSingularValue at h
    exact h
  rw [hKyTan]
  exact hcore

/-- Unconditional infinite-trial endpoint over abstract trial-block data: the tangent
representative is constructed with exactly the approximation numbers prescribed by the
paper. -/
theorem ideal_of_formBounds_infinite_exists
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (hResidual : N.Mem data.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge data.residual := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V
      (fun n => data.approximationSingularValue_sineBlock_lt_one_infiniteData
        hdelta hMupper hcross n)
  obtain ⟨hmem, hbound⟩ := data.ideal_of_formBounds_infinite N hdelta
    hMupper hcross tanTheta0 htan hResidual
  exact ⟨tanTheta0, htan, hmem, hbound⟩

end InfiniteCore

end Theorem63TrialData

/-! ## The Appendix endpoint for an unbounded self-adjoint operator -/

/-- **Davis--Kahan Theorem 6.3, unbounded ambient operator and arbitrary complete trial
space, under the printed reducing-subspace hypotheses.**

This is the Appendix dimension-removal endpoint.  There is no finite-dimensionality or
compactness hypothesis on `Z`.  The tangent representative is exhibited, and every
Fan-dominant unitarily invariant ideal gauge satisfies the printed residual bound. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  let data := Theorem63TrialData.ofUnbounded D V
  exact data.ideal_of_formBounds_infinite_exists N hdelta hCompression
    (crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted) hResidual

/-- Same arbitrary-trial unbounded theorem when a tangent representative with the paper's
approximation numbers is supplied explicitly. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_of_reducing
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  let data := Theorem63TrialData.ofUnbounded D V
  exact data.ideal_of_formBounds_infinite N hdelta hCompression
    (crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted)
    tanTheta0 htan hResidual

/-- Spectral-gap specialization of the arbitrary-trial unbounded theorem. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_exists
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z
        (selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  let V := selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic
  let data := Theorem63TrialData.ofUnbounded D V
  exact data.ideal_of_formBounds_infinite_exists N hdelta hCompression
    (crossed_lower_of_spectralGap A hA D hgap) hResidual

/-- Spectral-gap specialization with the tangent representative supplied explicitly.

`theorem6_3_unbounded_infiniteTrial_ideal_exists` produces a representative; a
source-facing statement at an arbitrary unitarily invariant norm cannot use that
form, because the existential would hand back a possibly different witness at
each Ky Fan index.  Taking the representative as a parameter is what lets the
paper-norm promotion quantify one operator over all indices. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z
      (selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  let V := selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic
  let data := Theorem63TrialData.ofUnbounded D V
  exact data.ideal_of_formBounds_infinite N hdelta hCompression
    (crossed_lower_of_spectralGap A hA D hgap) tanTheta0 htan hResidual

end TanTheta
end DavisKahan
end TauCeti
