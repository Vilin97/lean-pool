/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Conjugation
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.Stone

/-!
# Strong continuity of a conjugation flow on the Hilbert–Schmidt space

The Sylvester flow `W t Z = U_A t ∘ Z ∘ (U_B t)⋆` is a one-parameter unitary
group on the Hilbert–Schmidt operators.  Unitarity is
`HilbertSchmidtConjugation`; this module supplies the analytic half, strong
continuity, whose whole content is the estimate proved here:

`tendsto_energy_sub_comp` — for a Hilbert–Schmidt `S` and a strongly continuous
family of isometries `W` with `W 0 = 1`, the Hilbert–Schmidt energy of
`(W t - 1) ∘ S` tends to `0`.

Strong continuity of a *bounded* operator flow would be immediate; it is
Hilbert–Schmidt convergence that has content, because the columns must go to
zero **together**.  The argument is the usual `ε`-split: a finite set of columns
carries all but `ε/5` of the energy, the remaining columns are controlled
uniformly in `t` by `‖W t x - x‖ ≤ 2 ‖x‖`, and the finite part is a finite sum
of continuous functions vanishing at `t = 0`.

It is carried out in `ℝ≥0∞` rather than in `ℝ` on purpose: there the sum splits
unconditionally (`ENNReal.sum_add_tsum_compl`) and the tail estimate
(`ENNReal.tendsto_tsum_compl_atTop_zero`) needs no summability side condition,
so no part of the bookkeeping is spent on convergence hypotheses.

## Provenance

*New.*  The donor obtains strong continuity from the tensor-product functor
applied to the two factor groups; nothing of that is used.

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterGroup.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Group.lean` — the eighth and last
of those moves, held back while another agent held a claim on
this file read `in progress`.  Path change and repointing of imports only — no
statement, signature, proof, attribute, declaration name or namespace changed.
-/

public section

open scoped ENNReal NNReal
open Filter Topology

namespace TauCeti
namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A displacement by an isometry is at most twice the vector. -/
theorem enorm_sub_sq_le (W : E →L[𝕜] E) (hW : ∀ x : E, ‖W x‖ = ‖x‖) (x : E) :
    ‖W x - x‖ₑ ^ 2 ≤ 4 * ‖x‖ₑ ^ 2 := by
  have hle : ‖W x - x‖ₑ ≤ 2 * ‖x‖ₑ := by
    refine le_trans enorm_sub_le ?_
    have : ‖W x‖ₑ = ‖x‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      exact congrArg _ (NNReal.coe_injective (hW x))
    rw [this, two_mul]
  calc ‖W x - x‖ₑ ^ 2 ≤ (2 * ‖x‖ₑ) ^ 2 := by gcongr
    _ = 4 * ‖x‖ₑ ^ 2 := by ring

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Hilbert–Schmidt energy of `(W t - 1) ∘ S` vanishes as `t → 0`.**

This is the estimate behind strong continuity of any conjugation flow on the
Hilbert–Schmidt space.  Note what is *not* assumed: `W` need not be a group, and
no relation between different `t` is used — only that each `W t` is an isometry,
that `t ↦ W t x` is continuous for each fixed `x`, and that `W 0 = 1`. -/
theorem tendsto_energy_sub_comp (b : HilbertBasis ι 𝕜 F) (S : F →L[𝕜] E)
    (hS : S.hilbertSchmidtEnergy b ≠ ⊤)
    (W : ℝ → (E →L[𝕜] E)) (hiso : ∀ (t : ℝ) (x : E), ‖W t x‖ = ‖x‖)
    (hcont : ∀ x : E, Continuous fun t : ℝ => W t x) (hzero : ∀ x : E, W 0 x = x) :
    Tendsto (fun t : ℝ => ∑' i, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hEdef : ∑' i, ‖S (b i)‖ₑ ^ 2 ≠ ⊤ := by
    rw [← ContinuousLinearMap.hilbertSchmidtEnergy_def]; exact hS
  set δ : ℝ≥0∞ := ε / 5 with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact ENNReal.div_pos hε.ne' (by norm_num)
  -- A finite set of columns carrying all but `δ` of the energy.
  obtain ⟨s, hs⟩ :=
    ((tendsto_order.1 (ENNReal.tendsto_tsum_compl_atTop_zero hEdef)).2 δ hδ).exists
  -- The tail is uniformly small in `t`.
  have htail : ∀ t : ℝ,
      ∑' i : ↥((s : Set ι))ᶜ, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2 ≤ 4 * δ := by
    intro t
    calc ∑' i : ↥((s : Set ι))ᶜ, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2
        ≤ ∑' i : ↥((s : Set ι))ᶜ, 4 * ‖S (b i)‖ₑ ^ 2 :=
          ENNReal.tsum_le_tsum fun i => enorm_sub_sq_le (W t) (hiso t) _
      _ = 4 * ∑' i : ↥((s : Set ι))ᶜ, ‖S (b i)‖ₑ ^ 2 := ENNReal.tsum_mul_left
      _ ≤ 4 * δ := by gcongr; exact hs.le
  -- The finite part is a finite sum of continuous functions vanishing at `0`.
  have hfin : Tendsto (fun t : ℝ => ∑ i ∈ s, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
    have hterm : ∀ i ∈ s,
        Tendsto (fun t : ℝ => ‖W t (S (b i)) - S (b i)‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
      intro i _
      have heq : ∀ t : ℝ, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2
          = ENNReal.ofReal (‖W t (S (b i)) - S (b i)‖ ^ 2) := by
        intro t
        rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
      simp_rw [heq]
      have hc : Continuous fun t : ℝ => ENNReal.ofReal (‖W t (S (b i)) - S (b i)‖ ^ 2) :=
        ENNReal.continuous_ofReal.comp (((hcont _).sub continuous_const).norm.pow 2)
      have := hc.tendsto (0 : ℝ)
      simpa [hzero] using this
    simpa using tendsto_finsetSum s hterm
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hfin) δ hδ] with t ht
  calc ∑' i, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2
      = ∑ i ∈ s, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2
        + ∑' i : ↥((s : Set ι))ᶜ, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2 :=
        (ENNReal.sum_add_tsum_compl s _).symm
    _ ≤ δ + 4 * δ := add_le_add ht (htail t)
    _ = 5 * δ := by ring
    _ = ε := by rw [hδdef, ENNReal.mul_div_cancel' (by norm_num) (by norm_num)]

/-! ### Representing a Hilbert–Schmidt operator in `ℓ²` -/

omit [CompleteSpace F] in
/-- The `ℓ²` column family of an operator of finite Hilbert–Schmidt energy. -/
noncomputable def ofOperator (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E)
    (hT : T.hilbertSchmidtEnergy b ≠ ⊤) : lp (fun _ : ι => E) 2 :=
  ⟨columns b T, (memLp_columns_iff b T).mpr hT⟩

omit [CompleteSpace F] in
/-- Rebuilding an operator from its columns is the identity. -/
@[simp] theorem ofLp_ofOperator (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E)
    (hT : T.hilbertSchmidtEnergy b ≠ ⊤) : ofLp b (ofOperator b T hT) = T :=
  ofLp_columns b T _

omit [CompleteSpace F] in
/-- **From energy convergence to norm convergence.**  The `ℓ²` norm is the square
root of the real part of the energy, so a family of column vectors whose
energies vanish has vanishing norms. -/
theorem tendsto_norm_of_tendsto_energy {α : Type*} {l : Filter α} (b : HilbertBasis ι 𝕜 F)
    (g : α → lp (fun _ : ι => E) 2)
    (h : Tendsto (fun a => (ofLp b (g a)).hilbertSchmidtEnergy b) l (𝓝 0)) :
    Tendsto (fun a => ‖g a‖) l (𝓝 0) := by
  have hsq : ∀ a, ‖g a‖ = Real.sqrt (((ofLp b (g a)).hilbertSchmidtEnergy b).toReal) := by
    intro a
    rw [energy_ofLp, ENNReal.toReal_ofReal (by positivity), Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hsq]
  have h1 : Tendsto (fun a => ((ofLp b (g a)).hilbertSchmidtEnergy b).toReal) l (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp)).comp h
  simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1

omit [CompleteSpace E] [CompleteSpace F] in
/-- The energy of `W ∘ S - S`, written out columnwise. -/
theorem energy_sub_comp_eq (b : HilbertBasis ι 𝕜 F) (S : F →L[𝕜] E) (W : E →L[𝕜] E) :
    (W.comp S - S).hilbertSchmidtEnergy b = ∑' i, ‖W (S (b i)) - S (b i)‖ₑ ^ 2 := by
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_def]
  refine tsum_congr fun i => ?_
  rw [sub_apply, ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `W ∘ S - S` is Hilbert–Schmidt whenever `S` is and `W` is an isometry. -/
theorem energy_sub_comp_ne_top (b : HilbertBasis ι 𝕜 F) (S : F →L[𝕜] E) (W : E →L[𝕜] E)
    (hW : ∀ x : E, ‖W x‖ = ‖x‖) (hS : S.hilbertSchmidtEnergy b ≠ ⊤) :
    (W.comp S - S).hilbertSchmidtEnergy b ≠ ⊤ := by
  rw [energy_sub_comp_eq]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun i => enorm_sub_sq_le W hW (S (b i)))
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top (by norm_num) ?_
  rw [← ContinuousLinearMap.hilbertSchmidtEnergy_def]
  exact hS

/-! ### The Sylvester conjugation flow -/

section Sylvester

open TauCeti.OneParameterUnitaryGroup

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (U : OneParameterUnitaryGroup E) (V : OneParameterUnitaryGroup F)
variable (b : HilbertBasis ι ℂ F)

/-- The adjoint of a reversed group element is the forward one. -/
theorem adjoint_U_neg (t : ℝ) : (V.U (-t)).adjoint = V.U t := by
  have h := inverse_eq_adjoint V (-t)
  rw [neg_neg] at h
  exact h.symm

/-- The Sylvester flow on operators: `Z ↦ U t ∘ Z ∘ (V t)⋆`. -/
@[expose]
noncomputable def conjOp (t : ℝ) (f : lp (fun _ : ι => E) 2) : F →L[ℂ] E :=
  ((U.U t).comp (ofLp b f)).comp (V.U (-t))

/-- **The Sylvester flow preserves Hilbert--Schmidt energy.**  Both conjugating factors are
isometries, and the energy is invariant under composition with an isometry on either side.  This
is what makes the flow a group of *unitaries* on `HS(F, E)`. -/
theorem energy_conjOp (t : ℝ) (f : lp (fun _ : ι => E) 2) :
    (conjOp U V b t f).hilbertSchmidtEnergy b = (ofLp b f).hilbertSchmidtEnergy b := by
  rw [conjOp, hilbertSchmidtEnergy_comp_isometry _ b (V.U (-t))
      (fun x => by rw [adjoint_U_neg]; exact norm_preserving V t x),
    hilbertSchmidtEnergy_isometry_comp _ b (U.U t) (norm_preserving U t)]

/-- The flow keeps the energy finite, so its image stays inside the Hilbert--Schmidt class. -/
theorem energy_conjOp_ne_top (t : ℝ) (f : lp (fun _ : ι => E) 2) :
    (conjOp U V b t f).hilbertSchmidtEnergy b ≠ ⊤ := by
  rw [energy_conjOp, energy_ofLp]; exact ENNReal.ofReal_ne_top

/-- The Sylvester flow, transported to the `ℓ²` model. -/
noncomputable def sylvesterFun (t : ℝ) (f : lp (fun _ : ι => E) 2) : lp (fun _ : ι => E) 2 :=
  ofOperator b (conjOp U V b t f) (energy_conjOp_ne_top U V b t f)

/-- The Sylvester flow, seen through the operator model. -/
@[simp] theorem ofLp_sylvesterFun (t : ℝ) (f : lp (fun _ : ι => E) 2) :
    ofLp b (sylvesterFun U V b t f) = conjOp U V b t f :=
  ofLp_ofOperator _ _ _

/-- The Sylvester flow is norm-preserving on the `lp` model. -/
theorem norm_sylvesterFun (t : ℝ) (f : lp (fun _ : ι => E) 2) :
    ‖sylvesterFun U V b t f‖ = ‖f‖ :=
  norm_conj_eq b f (U.U t) (norm_preserving U t) (V.U (-t))
    (fun x => by rw [adjoint_U_neg]; exact norm_preserving V t x)
    _ (ofLp_sylvesterFun U V b t f)

/-- The Sylvester flow is additive. -/
theorem sylvesterFun_add (t : ℝ) (f g : lp (fun _ : ι => E) 2) :
    sylvesterFun U V b t (f + g) = sylvesterFun U V b t f + sylvesterFun U V b t g := by
  refine ofLp_injective b ?_
  rw [ofLp_add, ofLp_sylvesterFun, ofLp_sylvesterFun, ofLp_sylvesterFun]
  simp only [conjOp, ofLp_add]
  ext x
  simp

/-- The Sylvester flow is complex-linear.  Note it is linear, not conjugate-linear, even though
the right factor is an adjoint: the scalar passes through `Z ↦ U t ∘ Z ∘ (V t)⋆` untouched. -/
theorem sylvesterFun_smul (t : ℝ) (c : ℂ) (f : lp (fun _ : ι => E) 2) :
    sylvesterFun U V b t (c • f) = c • sylvesterFun U V b t f := by
  refine ofLp_injective b ?_
  rw [ofLp_smul, ofLp_sylvesterFun, ofLp_sylvesterFun]
  simp only [conjOp, ofLp_smul]
  ext x
  simp

/-- At time zero the flow is the identity -- the group identity law. -/
theorem sylvesterFun_zero (f : lp (fun _ : ι => E) 2) : sylvesterFun U V b 0 f = f := by
  refine ofLp_injective b ?_
  rw [ofLp_sylvesterFun]
  simp only [conjOp, neg_zero, U.identity, V.identity]
  ext x
  simp

/-- The flow composes additively in time.  With `sylvesterFun_zero` this is the one-parameter
group law. -/
theorem sylvesterFun_add_time (s t : ℝ) (f : lp (fun _ : ι => E) 2) :
    sylvesterFun U V b (s + t) f = sylvesterFun U V b s (sylvesterFun U V b t f) := by
  refine ofLp_injective b ?_
  rw [ofLp_sylvesterFun, ofLp_sylvesterFun]
  simp only [conjOp, ofLp_sylvesterFun]
  rw [U.group_law s t, show -(s + t) = -t + -s by ring, V.group_law (-t) (-s)]
  ext x
  simp

/-- The Sylvester flow as a bounded operator on the `ℓ²` model. -/
noncomputable def sylvesterOp (t : ℝ) :
    lp (fun _ : ι => E) 2 →L[ℂ] lp (fun _ : ι => E) 2 :=
  LinearMap.mkContinuous
    { toFun := sylvesterFun U V b t
      map_add' := sylvesterFun_add U V b t
      map_smul' := fun c f => sylvesterFun_smul U V b t c f } 1
    (fun f => by rw [one_mul]; exact le_of_eq (norm_sylvesterFun U V b t f))

/-- The bundled Sylvester operator acts as `sylvesterFun`. -/
@[simp] theorem sylvesterOp_apply (t : ℝ) (f : lp (fun _ : ι => E) 2) :
    sylvesterOp U V b t f = sylvesterFun U V b t f := (rfl)

/-! ### Strong continuity -/

/-- **Strong continuity at zero**: `‖U(r) f - f‖ → 0` as `r → 0`.  Strong
continuity at every other time follows from this by the group law, which is why
only the origin is proved. -/
theorem tendsto_norm_sylvesterFun_sub_zero (f : lp (fun _ : ι => E) 2) :
    Tendsto (fun r : ℝ => ‖sylvesterFun U V b r f - f‖) (𝓝 0) (𝓝 0) := by
  classical
  obtain ⟨w, c, -⟩ := exists_hilbertBasis ℂ E
  set T := ofLp b f with hT
  have hTtop : T.hilbertSchmidtEnergy b ≠ ⊤ := by rw [hT, energy_ofLp]; exact ENNReal.ofReal_ne_top
  have hTadjtop : T.adjoint.hilbertSchmidtEnergy c ≠ ⊤ := by
    rw [← ContinuousLinearMap.hilbertSchmidtEnergy_adjoint T b c]; exact hTtop
  -- the two pieces of the displacement
  have h1top : ∀ r : ℝ,
      (((U.U r).comp T - T).comp (V.U (-r))).hilbertSchmidtEnergy b ≠ ⊤ := by
    intro r
    rw [hilbertSchmidtEnergy_comp_isometry _ b (V.U (-r))
      (fun x => by rw [adjoint_U_neg]; exact norm_preserving V r x)]
    exact energy_sub_comp_ne_top b T (U.U r) (norm_preserving U r) hTtop
  have h2top : ∀ r : ℝ, (T.comp (V.U (-r)) - T).hilbertSchmidtEnergy b ≠ ⊤ := by
    intro r
    rw [ContinuousLinearMap.hilbertSchmidtEnergy_adjoint _ b c, map_sub,
      ContinuousLinearMap.adjoint_comp, adjoint_U_neg]
    exact energy_sub_comp_ne_top c T.adjoint (V.U r) (norm_preserving V r) hTadjtop
  set g₁ : ℝ → lp (fun _ : ι => E) 2 :=
    fun r => ofOperator b (((U.U r).comp T - T).comp (V.U (-r))) (h1top r) with hg₁
  set g₂ : ℝ → lp (fun _ : ι => E) 2 :=
    fun r => ofOperator b (T.comp (V.U (-r)) - T) (h2top r) with hg₂
  have hsplit : ∀ r : ℝ, sylvesterFun U V b r f - f = g₁ r + g₂ r := by
    intro r
    refine ofLp_injective b ?_
    simp only [ofLp_sub, ofLp_sylvesterFun, ofLp_add, hg₁, hg₂, ofLp_ofOperator, conjOp]
    ext x
    simp [hT]
  -- each piece tends to zero
  have h1 : Tendsto (fun r : ℝ => ‖g₁ r‖) (𝓝 0) (𝓝 0) := by
    refine tendsto_norm_of_tendsto_energy b g₁ ?_
    have hrw : ∀ r : ℝ, (ofLp b (g₁ r)).hilbertSchmidtEnergy b
        = ∑' i, ‖U.U r (T (b i)) - T (b i)‖ₑ ^ 2 := by
      intro r
      rw [hg₁, ofLp_ofOperator, hilbertSchmidtEnergy_comp_isometry _ b (V.U (-r))
        (fun x => by rw [adjoint_U_neg]; exact norm_preserving V r x), energy_sub_comp_eq]
    simp_rw [hrw]
    exact tendsto_energy_sub_comp b T hTtop (fun r => U.U r) (fun r => norm_preserving U r)
      (fun x => U.strong_continuous x) (fun x => by rw [U.identity]; rfl)
  have h2 : Tendsto (fun r : ℝ => ‖g₂ r‖) (𝓝 0) (𝓝 0) := by
    refine tendsto_norm_of_tendsto_energy b g₂ ?_
    have hrw : ∀ r : ℝ, (ofLp b (g₂ r)).hilbertSchmidtEnergy b
        = ∑' j, ‖V.U r (T.adjoint (c j)) - T.adjoint (c j)‖ₑ ^ 2 := by
      intro r
      rw [hg₂, ofLp_ofOperator,
        ContinuousLinearMap.hilbertSchmidtEnergy_adjoint _ b c]
      simp only [map_sub, ContinuousLinearMap.adjoint_comp, adjoint_U_neg]
      exact energy_sub_comp_eq _ _ _
    simp_rw [hrw]
    exact tendsto_energy_sub_comp c T.adjoint hTadjtop (fun r => V.U r)
      (fun r => norm_preserving V r) (fun x => V.strong_continuous x)
      (fun x => by rw [V.identity]; rfl)
  refine squeeze_zero (fun r => norm_nonneg _) (fun r => ?_) (by simpa using h1.add h2)
  rw [hsplit r]
  exact norm_add_le _ _

/-- **The Sylvester conjugation flow is a one-parameter unitary group** on the
Hilbert–Schmidt space. -/
noncomputable def sylvesterGroup : OneParameterUnitaryGroup (lp (fun _ : ι => E) 2) where
  U := sylvesterOp U V b
  unitary t := by
    refine (LinearMap.norm_map_iff_inner_map_map (sylvesterOp U V b t).toLinearMap).mp ?_
    intro x
    exact norm_sylvesterFun U V b t x
  group_law s t := ContinuousLinearMap.ext fun f => by
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, sylvesterOp_apply]
    exact sylvesterFun_add_time U V b s t f
  identity := ContinuousLinearMap.ext fun f => by
    simp [sylvesterOp_apply, sylvesterFun_zero]
  strong_continuous f := by
    refine continuous_iff_continuousAt.mpr fun s => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hshift : ∀ t : ℝ, ‖sylvesterOp U V b t f - sylvesterOp U V b s f‖
        = ‖sylvesterFun U V b (t - s) f - f‖ := by
      intro t
      have hts : sylvesterFun U V b t f = sylvesterFun U V b s (sylvesterFun U V b (t - s) f) := by
        rw [← sylvesterFun_add_time]
        congr 1
        ring
      have hlin : sylvesterFun U V b s (sylvesterFun U V b (t - s) f) - sylvesterFun U V b s f
          = sylvesterFun U V b s (sylvesterFun U V b (t - s) f - f) := by
        simpa using (map_sub (sylvesterOp U V b s) (sylvesterFun U V b (t - s) f) f).symm
      rw [sylvesterOp_apply, sylvesterOp_apply, hts, hlin]
      exact norm_sylvesterFun U V b s _
    simp_rw [hshift]
    have hsub : Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 (s - s)) :=
        Filter.Tendsto.sub tendsto_id tendsto_const_nhds
      simpa using h
    exact (tendsto_norm_sylvesterFun_sub_zero U V b f).comp hsub

/-- The bundled group acts as the Sylvester operator at each time. -/
@[simp] theorem sylvesterGroup_apply (t : ℝ) :
    (sylvesterGroup U V b).U t = sylvesterOp U V b t := (rfl)

/-- **The generator of the Sylvester flow is self-adjoint.**

This is the statement SR-D3 exists to produce.  `spectralPVM` and the gap
inverse are built from a self-adjoint `LinearPMap`, so this is what lets the
sharp `δ⁻¹` bound be applied to the Sylvester equation.  It is immediate from
Stone's theorem once the flow is known to be a one-parameter unitary group,
which is the content of everything above. -/
theorem isSelfAdjoint_generator_sylvesterGroup :
    IsSelfAdjoint (generator (sylvesterGroup U V b)) :=
  isSelfAdjoint_generator _

end Sylvester

end HilbertSchmidt
end TauCeti
