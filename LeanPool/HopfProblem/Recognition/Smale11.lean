/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale10
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomologyStarCoproduct
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology2
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology3
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Degree2
import all LeanPool.HopfProblem.Recognition.Smale6
import all LeanPool.HopfProblem.Recognition.Smale7
import all LeanPool.HopfProblem.Recognition.Smale8
import all LeanPool.HopfProblem.Recognition.Smale9
import all LeanPool.HopfProblem.Recognition.Smale10
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube1
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomologyStarCoproduct

/-!
# Hopf problem: recognition · smale 11

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

private theorem MorseCancel.exists_positive_scalar_cubic_diffeomorph {a : ℝ} (ha : 0 < a) :
    ∃ e : ℝ ≃ₘ[ℝ] ℝ, ∀ s, e s = s ^ 3 / 3 + a ^ 2 * s := by
  let g : ℝ → ℝ := fun s => s ^ 3 / 3 + a ^ 2 * s
  have hg : ContDiff ℝ ∞ g := by unfold g; fun_prop
  have hd (s : ℝ) : HasDerivAt g (s ^ 2 + a ^ 2) s := by
    convert!
      (((hasDerivAt_id s).pow 3).div_const 3).add ((hasDerivAt_id s).const_mul (a ^ 2)) using 1;
    simp
  have hpos (s : ℝ) : 0 < s ^ 2 + a ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg s) (sq_pos_of_pos ha)
  have hmono : StrictMono g := strictMono_of_hasDerivAt_pos hd hpos
  have hbound {s t : ℝ} (hst : s ≤ t) : a ^ 2 * (t - s) ≤ g t - g s :=
    mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
      (fun x => by rw [(hd x).deriv]; exact le_add_of_nonneg_left (sq_nonneg x)) hst
  have hzero : g 0 = 0 := by simp [g]
  have hsurj : Function.Surjective g := by
    intro y
    apply mem_range_of_exists_le_of_exists_ge hg.continuous
    · refine ⟨Min.min 0 (y / a ^ 2), ?_⟩
      have hh := hbound (min_le_left 0 (y / a ^ 2))
      have hm : a ^ 2 * Min.min 0 (y / a ^ 2) ≤ y := by
        calc
          a ^ 2 * Min.min 0 (y / a ^ 2) ≤ a ^ 2 * (y / a ^ 2) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg a)
          _ = y := by field_simp
      rw [hzero] at hh
      linarith
    · refine ⟨Max.max 0 (y / a ^ 2), ?_⟩
      have hh := hbound (le_max_left 0 (y / a ^ 2))
      have hm : y ≤ a ^ 2 * Max.max 0 (y / a ^ 2) := by
        calc
          y = a ^ 2 * (y / a ^ 2) := by field_simp
          _ ≤ a ^ 2 * Max.max 0 (y / a ^ 2) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg a)
      rw [hzero] at hh
      linarith
  let c : ℝ ≃o ℝ := hmono.orderIsoOfSurjective g hsurj
  have hi : ContDiff ℝ ∞ c.toHomeomorph.symm :=
    c.toHomeomorph.contDiff_symm_deriv (fun s => (hpos s).ne') hd hg
  let e : ℝ ≃ₘ[ℝ] ℝ :=
    { toEquiv := c.toEquiv
      contMDiff_toFun := hg.contMDiff
      contMDiff_invFun := hi.contMDiff }
  exact ⟨e, fun _ => rfl⟩

private theorem MorseCancel.exists_positive_cubic_height_diffeomorph {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) : ∃ D : Model m ≃ₘ[ℝ] Model m, ∀ p, D p = (cubic σ (a ^ 2) p, p.2) := by
  obtain ⟨e, he⟩ := exists_positive_scalar_cubic_diffeomorph ha
  let Q : (Fin m → ℝ) → ℝ := fun z => ∑ i, σ i * z i ^ 2
  have hQ : ContDiff ℝ ∞ Q := by unfold Q; fun_prop
  have hec : ContDiff ℝ ∞ e := contMDiff_iff_contDiff.mp e.contMDiff
  have hei : ContDiff ℝ ∞ e.symm := contMDiff_iff_contDiff.mp e.symm.contMDiff
  let D : Model m ≃ₘ[ℝ] Model m :=
    { toFun := fun p => (e p.1 + Q p.2, p.2)
      invFun := fun p => (e.symm (p.1 - Q p.2), p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      contMDiff_toFun :=
        ((hec.comp contDiff_fst |>.add (hQ.comp contDiff_snd)).prodMk contDiff_snd).contMDiff
      contMDiff_invFun :=
        ((hei.comp (contDiff_fst.sub (hQ.comp contDiff_snd))).prodMk contDiff_snd).contMDiff }
  refine ⟨D, ?_⟩
  intro p
  change (e p.1 + Q p.2, p.2) = _
  rw [he]
  rfl

private theorem MorseCancel.hessian_comp_linearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E ≃L[ℝ] F) (x : E) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) x =
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap).comp
        ((fderiv ℝ (fderiv ℝ f) (L x)).comp L.toContinuousLinearMap) := by
  let A := (ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap
  have hgrad : fderiv ℝ (f ∘ L) = fun y => A (fderiv ℝ f (L y)) := by
    funext y
    rw [fderiv_comp y (hf.differentiable (by simp) (L y)) L.differentiableAt, L.fderiv]
    rfl
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [hgrad]
  exact
    (A.hasFDerivAt.comp x
        ((hdf.differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt)).fderiv

private theorem MorseCancel.euclidean_isMorse_comp_linearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (hm : Smale.MorsePerturbation.IsMorse f) (L : E ≃L[ℝ] F) :
    Smale.MorsePerturbation.IsMorse (f ∘ L) := by
  intro x hx
  have hcrit : fderiv ℝ f (L x) = 0 := by
    rw [fderiv_comp x (hf.differentiable (by simp) (L x)) L.differentiableAt, L.fderiv] at hx
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := L.surjective v
    exact congrArg (fun k : E →L[ℝ] ℝ => k w) hx
  let A := (ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap
  have hA : Function.Bijective A := by
    constructor
    · intro k l hkl
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := L.surjective v
      exact congrArg (fun k : E →L[ℝ] ℝ => k w) hkl
    · intro k
      refine ⟨k.comp L.symm.toContinuousLinearMap, ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      change k (L.symm (L v)) = k v
      rw [L.symm_apply_apply]
  rw [hessian_comp_linearEquiv hf L]
  exact hA.comp ((hm (L x) hcrit).comp L.bijective)

private theorem MorseCancel.isMorseAt_of_native_model_germ {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞) (L : E ≃L[ℝ] F) {f : M → ℝ} {b : F → ℝ} {p : F}
    (hp : p ∈ Φ.source) (hb : ContDiff ℝ ∞ b) (hmb : Smale.MorsePerturbation.IsMorse b)
    (hmodel : f ∘ Φ =ᶠ[𝓝 p] b) : Smale.ManifoldMorse.IsMorseAt E f (Φ p) := by
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have hpΨ : Φ p ∈ Ψ.target := by exact ⟨Φ.map_source' hp, Set.mem_univ _⟩
  have he : Ψ.symm.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    Ψ.symm.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn Ψ.contMDiffOn_invFun
      Ψ.contMDiffOn_toFun
  apply
    Smale.ManifoldMorse.isMorseAt_of_chart_eventuallyEq he hpΨ
      (euclidean_isMorse_comp_linearEquiv hb hmb L)
  have hcenter : Ψ.symm (Φ p) = L.symm p := by
    change L.symm (Φ.symm (Φ p)) = L.symm p
    exact congrArg L.symm (Φ.left_inv' hp)
  change f ∘ Ψ =ᶠ[𝓝 (Ψ.symm (Φ p))] b ∘ L
  rw [hcenter]
  have ht : Filter.Tendsto L (𝓝 (L.symm p)) (𝓝 p) := by
    simpa only [L.apply_symm_apply] using L.continuous.continuousAt.tendsto (x := L.symm p)
  exact hmodel.comp_tendsto ht

private theorem
    MorseCancel.euclidean_isMorse_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hm : Smale.MorsePerturbation.IsMorse f) {c : ℝ}
    (hc : c ≠ 0) (b : ℝ) : Smale.MorsePerturbation.IsMorse (fun x => b + c * f x) := by
  have hgrad : fderiv ℝ (fun x => b + c * f x) = fun x => c • fderiv ℝ f x := by
    funext x
    rw [fderiv_const_add, fderiv_const_mul (hf.differentiable (by simp) x)]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  intro x hx
  rw [hgrad] at hx ⊢
  have hcrit : fderiv ℝ f x = 0 := (smul_eq_zero.mp hx).resolve_left hc
  change Function.Bijective (fderiv ℝ (c • fderiv ℝ f) x)
  rw [fderiv_const_smul (hdf.differentiable (by simp) x)]
  exact (isUnit_iff_ne_zero.mpr hc).smul_bijective.comp (hm x hcrit)

private theorem MorseCancel.exists_pos_compact_smul_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (h0 : (0 : E) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ (fun x : E => δ • x) '' K ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  let R := Max.max C 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hCR : C < R := by dsimp [R]; linarith [le_max_left C 0]
  let δ := r / (2 * R)
  have hδ : 0 < δ := div_pos hr (mul_pos (by norm_num) hR)
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply hrU
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  have hnorm : ‖x‖ < R := (hC x hx).trans_lt hCR
  have hm : δ * ‖x‖ < δ * R := mul_lt_mul_of_pos_left hnorm hδ
  have heq : δ * R = r / 2 := by dsimp [δ]; field_simp
  rw [heq] at hm
  linarith

private theorem MorseCancel.exists_centered_native_height_chart {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (0 : Model m) ∈ Φ.source ∧ Φ 0 = x ∧ Φ.target ⊆ U ∧ ∀ p ∈ Φ.source, f (Φ p) = f x + p.1 := by
  obtain ⟨Q, hxQ, hQ, hQx⟩ := Smale.RegularLevel.exists_native_height_chart hf hx
  have hdim' : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Module.finrank_pi, Fintype.card_fin, Smale.RegularLevel.Model,
      finrank_euclideanSpace_fin]
    omega
  let L : (Fin m → ℝ) ≃L[ℝ] Smale.RegularLevel.Model E := ContinuousLinearEquiv.ofFinrankEq hdim'
  let D :
    Diffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, ℝ × Smale.RegularLevel.Model E) (Model m)
      (ℝ × Smale.RegularLevel.Model E) ∞ :=
    { toFun := fun p => (f x + p.1, L p.2)
      invFun := fun p => (p.1 - f x, L.symm p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      contMDiff_toFun :=
        ((contDiff_const.add contDiff_fst).prodMk (L.contDiff.comp contDiff_snd)).contMDiff
      contMDiff_invFun :=
        ((contDiff_fst.sub contDiff_const).prodMk (L.symm.contDiff.comp contDiff_snd)).contMDiff }
  let P := D.toPartialDiffeomorph.trans Q.symm
  let Φ := Smale.PartialChart.restrictTarget P hU
  have hD0 : D 0 = Q x := by
    rw [hQx]
    change (f x + (0 : ℝ), L 0) = (f x, 0)
    simp
  have h0P : (0 : Model m) ∈ P.source := by
    change (0 : Model m) ∈ Set.univ ∧ D 0 ∈ Q.target
    exact ⟨Set.mem_univ _, hD0.symm ▸ Q.map_source' hxQ⟩
  have hP0 : P 0 = x := by
    change Q.symm (D 0) = x
    rw [hD0]
    exact Q.left_inv' hxQ
  have h0Φ : (0 : Model m) ∈ Φ.source := by
    change (0 : Model m) ∈ P.source ∧ P 0 ∈ U
    exact ⟨h0P, hP0.symm ▸ hxU⟩
  refine ⟨Φ, h0Φ, hP0, fun _ hy => hy.2, ?_⟩
  intro p hp
  have hpt : D p ∈ Q.target := hp.1.2
  have hh := hQ (Q.symm (D p)) (Q.map_target' hpt)
  have hright : Q (Q.symm (D p)) = D p := Q.right_inv' hpt
  rw [hright] at hh
  exact hh.symm

private theorem MorseCancel.insert_morse_chart_pair {E D M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (L : E ≃L[ℝ] D) {f : M → ℝ} {b₀ b₁ : D → ℝ}
    {K : Set D} {p q : D} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hb₀ : ContDiff ℝ ∞ b₀) (hb₁ : ContDiff ℝ ∞ b₁)
    (hmb₁ : Smale.MorsePerturbation.IsMorse b₁) (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) (hp : p ∈ Φ.source)
    (hq : q ∈ Φ.source) (hpq : p ≠ q) (hreg : ∀ x, fderiv ℝ b₀ x ≠ 0)
    (hcrit : ∀ x, fderiv ℝ b₁ x = 0 ↔ x = p ∨ x = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard =
              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
            (∀ y,
                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = Φ p ∨ y = Φ q) ∧
              (∀ y, y ∉ Φ '' K → g =ᶠ[𝓝 y] f) ∧
                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                  ∀ z ∈ Φ.source, g (Φ z) = b₁ z := by
  let g := Degree.LocalFunctionReplacement.replace Φ f b₁
  have hg := Degree.LocalFunctionReplacement.contMDiff_replace Φ hf hb₁ hK hKΦ hmodel hfix
  have houtside (y : M) (hy : y ∉ Φ '' K) : g =ᶠ[𝓝 y] f :=
    Degree.LocalFunctionReplacement.replace_germ_off_support Φ hK hKΦ hmodel hfix hy
  have hnot (y : M) (hy : y ∈ Φ.target) : y ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro hc
    have he := Degree.LocalFunctionReplacement.replace_critical_iff Φ f hb₀ hy
    rw [Degree.LocalFunctionReplacement.replace_self Φ hmodel] at he
    exact hreg (Φ.symm y) (he.mp hc)
  have hcritg (y : M) :
    y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
      y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = Φ p ∨ y = Φ q := by
    by_cases hy : y ∈ Φ.target
    · have he := Degree.LocalFunctionReplacement.replace_critical_iff Φ f hb₁ hy
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y = 0 ↔ _
      rw [he, hcrit]
      constructor
      · rintro (h | h)
        · exact Or.inr (Or.inl ((Φ.right_inv' hy).symm.trans (congrArg Φ h)))
        · exact Or.inr (Or.inr ((Φ.right_inv' hy).symm.trans (congrArg Φ h)))
      · rintro (hc | rfl | rfl)
        · exact False.elim (hnot y hy hc)
        · exact Or.inl (Φ.left_inv' hp)
        · exact Or.inr (Φ.left_inv' hq)
    · have hyK : y ∉ Φ '' K := by
        rintro ⟨z, hz, rfl⟩
        exact hy (Φ.map_source' (hKΦ hz))
      have hyp : y ≠ Φ p := fun h => hy (h.symm ▸ Φ.map_source' hp)
      have hyq : y ≠ Φ q := fun h => hy (h.symm ▸ Φ.map_source' hq)
      have he :
        y ∈ Smale.ManifoldMorse.criticalPoints E g ↔ y ∈ Smale.ManifoldMorse.criticalPoints E f :=
        by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y = 0 ↔ _
        rw [(houtside y hyK).mfderiv_eq]
        rfl
      simpa only [hyp, hyq, or_false] using he
  have hmg : Smale.ManifoldMorse.IsMorse E g := by
    intro y
    by_cases hy : y ∈ Φ.target
    · have hx := Φ.map_target' hy
      have hmodelg : g ∘ Φ =ᶠ[𝓝 (Φ.symm y)] b₁ := by
        filter_upwards [Φ.open_source.mem_nhds hx] with z hz
        exact Degree.LocalFunctionReplacement.replace_chart Φ f b₁ hz
      have hh := isMorseAt_of_native_model_germ Φ L hx hb₁ hmb₁ hmodelg
      have hright : Φ (Φ.symm y) = y := Φ.right_inv' hy
      exact hright ▸ hh
    · apply Degree.MorseCancellationPreservation.isMorseAt_of_same_germ (hm y)
      apply houtside y
      rintro ⟨z, hz, rfl⟩
      exact hy (Φ.map_source' (hKΦ hz))
  have hneq : Φ p ≠ Φ q := fun h => hpq (Φ.toOpenPartialHomeomorph.injOn hp hq h)
  have hpnot := hnot (Φ p) (Φ.map_source' hp)
  have hqnot := hnot (Φ q) (Φ.map_source' hq)
  have heq :
    Smale.ManifoldMorse.criticalPoints E g =
      Insert.insert (Φ p) (Insert.insert (Φ q) (Smale.ManifoldMorse.criticalPoints E f)) := by
    ext y
    rw [hcritg]
    simp only [Set.mem_insert_iff]
    tauto
  refine
    ⟨g, hg, hmg, ?_, hcritg, houtside, ?_, fun z hz =>
      Degree.LocalFunctionReplacement.replace_chart Φ f b₁ hz⟩
  · rw [heq,
      Set.ncard_insert_of_notMem
        (by simp only [Set.mem_insert_iff, hneq, hpnot, or_self, not_false_eq_true])
        ((Smale.ManifoldMorse.finite_criticalPoints hf hm).insert (Φ q)),
      Set.ncard_insert_of_notMem hqnot (Smale.ManifoldMorse.finite_criticalPoints hf hm)]
  · intro y hy
    apply houtside y
    rintro ⟨z, hz, rfl⟩
    exact hnot (Φ z) (Φ.map_source' (hKΦ hz)) hy

private theorem MorseCancel.exists_native_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E)
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a δ : ℝ,
      0 < a ∧
        0 < δ ∧
          ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
            (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
              (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
                Φ.target ⊆ U ∧
                  (∀ z ∈ Φ.source, f (Φ z) = f x + δ * cubic σ (a ^ 2) z) ∧
                    ∃ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                        Smale.ManifoldMorse.IsMorse E g ∧
                          (Smale.ManifoldMorse.criticalPoints E g).ncard =
                              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨
                                    y = Φ (a, 0) ∨ y = Φ (-a, 0)) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  (g ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => f x + δ * cubic σ (-(a ^ 2)) z) ∧
                                    (g ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z =>
                                      f x + δ * cubic σ (-(a ^ 2)) z) := by
  obtain ⟨H, h0H, -, hHU, hH⟩ := exists_centered_native_height_chart hf hx hdim hU hxU
  obtain ⟨φ, hφ, hc, -, W, hW, h0W, hφW⟩ :=
    Degree.NativeCubicCancellation.exists_cutoff (m := m) isOpen_univ (Set.mem_univ _)
  obtain ⟨a, ha, hpW, hqW, b, hb, hcritb, hgerms, hfix⟩ :=
    exists_exact_cubic_birth σ hσ hφ hc hW h0W hφW
  have hmb : Smale.MorsePerturbation.IsMorse b := by
    intro z hz
    have hzW : z ∈ W := (hcritb z).mp hz |>.elim (fun h => h ▸ hpW) (fun h => h ▸ hqW)
    have heq := hgerms z hzW
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]
    apply cubic_isMorse σ hσ (neg_ne_zero.mpr (pow_ne_zero 2 ha.ne'))
    rw [← heq.fderiv_eq]
    exact hz
  obtain ⟨D, hD⟩ := exists_positive_cubic_height_diffeomorph σ ha
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_compact_smul_subset (hc.image D.continuous) H.open_source h0H
  let A : Model m ≃L[ℝ] Model m :=
    (LinearEquiv.smulOfNeZero ℝ (Model m) δ hδ.ne').toContinuousLinearEquiv
  let C := D.trans A.toDiffeomorph
  let Φ := C.toPartialDiffeomorph.trans H
  have hC (z : Model m) : C z = δ • D z := rfl
  have hKΦ : tsupport φ ⊆ Φ.source := by
    intro z hz
    change z ∈ Set.univ ∧ C z ∈ H.source
    exact ⟨Set.mem_univ _, hsmall ⟨D z, Set.mem_image_of_mem D hz, rfl⟩⟩
  have hWK : W ⊆ tsupport φ := by
    intro z hz
    apply subset_tsupport φ
    change φ z ≠ 0
    rw [hφW hz]
    norm_num
  have hpΦ := hKΦ (hWK hpW)
  have hqΦ := hKΦ (hWK hqW)
  have hΦU : Φ.target ⊆ U := fun _ hy => hHU hy.1
  let b₀ : Model m → ℝ := fun z => f x + δ * cubic σ (a ^ 2) z
  let b₁ : Model m → ℝ := fun z => f x + δ * b z
  have hb₀ : ContDiff ℝ ∞ b₀ := contDiff_const.add (contDiff_const.mul (contDiff_cubic σ _))
  have hb₁ : ContDiff ℝ ∞ b₁ := contDiff_const.add (contDiff_const.mul hb)
  have hmb₁ : Smale.MorsePerturbation.IsMorse b₁ := euclidean_isMorse_affine hb hmb hδ.ne' (f x)
  have hmodel (z : Model m) (hz : z ∈ Φ.source) : f (Φ z) = b₀ z := by
    change f (H (C z)) = _
    rw [hH (C z) hz.2, hC, hD]
    rfl
  have hfix₁ (z : Model m) (hz : z ∉ tsupport φ) : b₁ z = b₀ z := by
    dsimp [b₁, b₀]
    rw [(hfix z hz).self_of_nhds]
  have hderiv (v : Model m → ℝ) (hv : ContDiff ℝ ∞ v) (z : Model m) :
    fderiv ℝ (fun y => f x + δ * v y) z = δ • fderiv ℝ v z := by
    rw [fderiv_const_add, fderiv_const_mul (hv.differentiable (by simp) z)]
  have hreg₀ (z : Model m) : fderiv ℝ b₀ z ≠ 0 := by
    rw [hderiv _ (contDiff_cubic σ _) z]
    exact smul_ne_zero hδ.ne' (positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) z)
  have hcrit₁ (z : Model m) : fderiv ℝ b₁ z = 0 ↔ z = (a, 0) ∨ z = (-a, 0) := by
    rw [hderiv b hb z, smul_eq_zero]
    simp only [hδ.ne', false_or, hcritb]
  have hpq : (a, (0 : Fin m → ℝ)) ≠ (-a, 0) := by
    intro h
    have hh := congrArg Prod.fst h
    change a = -a at hh
    linarith
  let L : E ≃L[ℝ] Model m :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [Model, Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
          Fintype.card_fin]
        exact hdim.symm)
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior, hkeep, hnew⟩ :=
    insert_morse_chart_pair Φ L hf hm hb₀ hb₁ hmb₁ hc hKΦ hmodel hfix₁ hpΦ hqΦ hpq hreg₀ hcrit₁
  have hend (z : Model m) (hzΦ : z ∈ Φ.source) (hzW : z ∈ W) :
    g ∘ Φ =ᶠ[𝓝 z] fun w => f x + δ * cubic σ (-(a ^ 2)) w := by
    filter_upwards [Φ.open_source.mem_nhds hzΦ, hgerms z hzW] with w hw heq
    change g (Φ w) = _
    rw [hnew w hw]
    change f x + δ * b w = _
    rw [heq]
  refine
    ⟨a, δ, ha, hδ, Φ, hpΦ, hqΦ, hΦU, hmodel, g, hg, hmg, hcount, hcritg, ?_, hkeep,
      hend _ hpΦ hpW, hend _ hqΦ hqW⟩
  intro y hy
  apply hexterior y
  rintro ⟨z, hz, rfl⟩
  exact hy (hΦU (Φ.map_source' (hKΦ hz)))

private theorem MorseCancel.injOn_of_two_new_values {X : Type*} {f g : X → ℝ} {C : Set X} {p q : X}
    (hinj : Set.InjOn f C) (hkeep : ∀ y ∈ C, g y = f y) (hp : g p ∉ f '' C) (hq : g q ∉ f '' C)
    (hpq : g p ≠ g q) : Set.InjOn g {y | y ∈ C ∨ y = p ∨ y = q} := by
  intro y hy z hz heq
  rcases hy with hy | rfl | rfl
  · rcases hz with hz | rfl | rfl
    · exact hinj hy hz ((hkeep y hy).symm.trans (heq.trans (hkeep z hz)))
    · exact False.elim (hp ⟨y, hy, (hkeep y hy).symm.trans heq⟩)
    · exact False.elim (hq ⟨y, hy, (hkeep y hy).symm.trans heq⟩)
  · rcases hz with hz | rfl | rfl
    · exact False.elim (hp ⟨z, hz, (hkeep z hz).symm.trans heq.symm⟩)
    · rfl
    · exact False.elim (hpq heq)
  · rcases hz with hz | rfl | rfl
    · exact False.elim (hq ⟨z, hz, (hkeep z hz).symm.trans heq.symm⟩)
    · exact False.elim (hpq heq.symm)
    · rfl

private theorem MorseCancel.exists_excellent_native_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {l u : ℝ}
    (hband : ∀ y, f y ∈ Set.Ioo l u → y ∉ Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a δ : ℝ,
      0 < a ∧
        0 < δ ∧
          ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
            (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
              (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
                Φ.target ⊆ U ∧
                  ∃ g : M → ℝ,
                    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                      Smale.ManifoldMorse.IsMorse E g ∧
                        Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
                          (Smale.ManifoldMorse.criticalPoints E g).ncard =
                              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨
                                    y = Φ (a, 0) ∨ y = Φ (-a, 0)) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  g (Φ (a, 0)) < g (Φ (-a, 0)) ∧
                                    g (Φ (a, 0)) ∈ Set.Ioo l u ∧
                                      g (Φ (-a, 0)) ∈ Set.Ioo l u ∧
                                        (g ∘ Φ =ᶠ[𝓝 (a, 0)] fun z =>
                                            f x + δ * cubic σ (-(a ^ 2)) z) ∧
                                          (g ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z =>
                                            f x + δ * cubic σ (-(a ^ 2)) z) := by
  obtain
    ⟨a, δ, ha, hδ, Φ, hp, hq, hΦ, hmodel, g, hg, hmg, hcount, hcrit, hexterior, hkeep, hgp,
      hgq⟩ :=
    exists_native_morse_birth hf hm (hband x hx) hdim σ hσ
      (hU.inter (isOpen_Ioo.preimage hf.continuous)) ⟨hxU, hx⟩
  have hpa : f (Φ (a, 0)) = f x + δ * (4 * a ^ 3 / 3) := by
    rw [hmodel (a, 0) hp]
    simp only [cubic, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero,
      Finset.sum_const_zero, add_zero]
    ring
  have hqa : f (Φ (-a, 0)) = f x - δ * (4 * a ^ 3 / 3) := by
    rw [hmodel (-a, 0) hq]
    simp only [cubic, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero,
      Finset.sum_const_zero, add_zero]
    ring
  have hpval : g (Φ (a, 0)) = f x - δ * (2 * a ^ 3 / 3) := by
    have hh := hgp.self_of_nhds
    change g (Φ (a, 0)) = f x + δ * cubic σ (-(a ^ 2)) (a, 0) at hh
    rw [(cubic_critical_values σ a).1] at hh
    exact hh.trans (by ring)
  have hqval : g (Φ (-a, 0)) = f x + δ * (2 * a ^ 3 / 3) := by
    have hh := hgq.self_of_nhds
    change g (Φ (-a, 0)) = f x + δ * cubic σ (-(a ^ 2)) (-a, 0) at hh
    rw [(cubic_critical_values σ a).2] at hh
    exact hh
  have hpos : 0 < δ * (2 * a ^ 3 / 3) := by positivity
  have hpq : g (Φ (a, 0)) < g (Φ (-a, 0)) := by rw [hpval, hqval]; linarith
  have hpband : g (Φ (a, 0)) ∈ Set.Ioo l u := by
    have hb := (hΦ (Φ.map_source' hq)).2
    change f (Φ (-a, 0)) ∈ Set.Ioo l u at hb
    rw [hqa] at hb
    rw [hpval]
    constructor <;> nlinarith [hb.1, hx.2]
  have hqband : g (Φ (-a, 0)) ∈ Set.Ioo l u := by
    have hb := (hΦ (Φ.map_source' hp)).2
    change f (Φ (a, 0)) ∈ Set.Ioo l u at hb
    rw [hpa] at hb
    rw [hqval]
    constructor <;> nlinarith [hx.1, hb.2]
  have hnot (v : ℝ) (hv : v ∈ Set.Ioo l u) : v ∉ f '' Smale.ManifoldMorse.criticalPoints E f := by
    rintro ⟨y, hy, rfl⟩
    exact hband y hv hy
  have hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
    have hh :=
      injOn_of_two_new_values hinj (fun y hy => (hkeep y hy).self_of_nhds) (hnot _ hpband)
        (hnot _ hqband) hpq.ne
    intro y hy z hz heq
    exact hh ((hcrit y).mp hy) ((hcrit z).mp hz) heq
  refine
    ⟨a, δ, ha, hδ, Φ, hp, hq, fun _ hy => (hΦ hy).1, g, hg, hmg, hinjg, hcount, hcrit, ?_, hkeep,
      hpq, hpband, hqband, hgp, hgq⟩
  intro y hy
  exact hexterior y (fun hh => hy hh.1)

private theorem
    MorseCancel.exists_signed_chart_of_split_quadratic {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} {m : ℕ}
    (P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Model m) M (Model m) ∞) (hp : p ∈ P.source)
    (hcenter : P p = 0) (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (e : ℝ) (σ : Fin m → ℝ)
    (he : e = -1 ∨ e = 1) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hformula : ∀ y ∈ P.source, f y = f p + e * (P y).1 ^ 2 + ∑ i, σ i * (P y).2 i ^ 2) :
    ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p,
      c.weights (ρ Option.none) = e ∧ ∀ i, c.weights (ρ (Option.some i)) = σ i := by
  let w : Fin (Module.finrank ℝ E) → ℝ := fun j => (ρ.symm j).elim e σ
  have hwn : w (ρ Option.none) = e := by simp [w]
  have hws (i : Fin m) : w (ρ (Option.some i)) = σ i := by simp [w]
  have hw (j : Fin (Module.finrank ℝ E)) : w j = -1 ∨ w j = 1 := by
    change (ρ.symm j).elim e σ = -1 ∨ (ρ.symm j).elim e σ = 1
    cases h : ρ.symm j with
    | none => exact he
    | some i => exact hσ i
  have hsum (z : Model m) :
    (∑ j, w j * splitEquiv ρ z j ^ 2) = e * z.1 ^ 2 + ∑ i, σ i * z.2 i ^ 2 := by
    rw [split_signed_sum, hwn]
    simp only [hws]
  let C := P.trans (splitEquiv ρ).toDiffeomorph.toPartialDiffeomorph
  have hpC : p ∈ C.source := ⟨hp, Set.mem_univ _⟩
  have hC0 : C p = 0 := by
    change splitEquiv ρ (P p) = 0
    rw [hcenter, map_zero]
  have hCformula (y : M) (hy : y ∈ C.source) : f y = f p + ∑ i, w i * (C y i) ^ 2 := by
    change f y = f p + ∑ i, w i * splitEquiv ρ (P y) i ^ 2
    rw [hsum, hformula y hy.1]
    ring
  let c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p :=
    { weights := w
      signs := hw
      chart := C
      mem_source := hpC
      center := hC0
      equation := hCformula
      inverse_equation := by
        intro z hz
        have h := hCformula (C.symm z) (C.map_target' hz)
        have hr : C (C.symm z) = z := C.right_inv' hz
        rw [hr] at h
        exact h }
  exact ⟨c, hwn, hws⟩

private theorem
    MorseCancel.exists_signed_chart_of_scaled_cubic_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a δ b : ℝ} (ha : 0 < a) (hδ : 0 < δ) (e : ℝ) (he : e = -1 ∨ e = 1)
    (hp : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgerm : f ∘ Φ =ᶠ[𝓝 (e * a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f (Φ (e * a, 0)),
      c.weights (ρ Option.none) = e ∧ ∀ i, c.weights (ρ (Option.some i)) = σ i := by
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hgerm
  let T := Smale.PartialChart.restrictSource Φ hW
  have hpT : (e * a, (0 : Fin m → ℝ)) ∈ T.source := ⟨hp, hpW⟩
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  obtain ⟨P, hpP, hP0, -, hP⟩ := exists_endpoint_product_chart σ ha e he2
  let B : Model m ≃L[ℝ] Model m :=
    (LinearEquiv.smulOfNeZero ℝ (Model m) (Real.sqrt δ)
        (Real.sqrt_pos.mpr hδ).ne').toContinuousLinearEquiv
  let C := (T.symm.trans P).trans B.toDiffeomorph.toPartialDiffeomorph
  have hTinv : T.symm (Φ (e * a, 0)) = (e * a, 0) := T.left_inv' hpT
  have hpC : Φ (e * a, 0) ∈ C.source := by
    change (Φ (e * a, 0) ∈ T.target ∧ T.symm (Φ (e * a, 0)) ∈ P.source) ∧ _
    exact ⟨⟨T.map_source' hpT, hTinv.symm ▸ hpP⟩, Set.mem_univ _⟩
  have hC0 : C (Φ (e * a, 0)) = 0 := by
    change B (P (T.symm (Φ (e * a, 0)))) = 0
    rw [hTinv, hP0, map_zero]
  have hvalue : f (Φ (e * a, 0)) = b + δ * cubic σ (-(a ^ 2)) (e * a, 0) := hgerm.self_of_nhds
  have hscale (z : Model m) :
    e * (B z).1 ^ 2 + ∑ i, σ i * (B z).2 i ^ 2 = δ * (e * z.1 ^ 2 + ∑ i, σ i * z.2 i ^ 2) := by
    change e * (Real.sqrt δ * z.1) ^ 2 + (∑ i, σ i * (Real.sqrt δ * z.2 i) ^ 2) = _
    simp only [mul_pow, Real.sq_sqrt hδ.le]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  apply exists_signed_chart_of_split_quadratic C hpC hC0 ρ e σ he hσ
  intro y hy
  have hyT : y ∈ T.target := hy.1.1
  have hzT := T.map_target' hyT
  have hzP : T.symm y ∈ P.source := hy.1.2
  have hfy : f y = b + δ * cubic σ (-(a ^ 2)) (T.symm y) := by
    have hh := hWsub hzT.2
    change f (T (T.symm y)) = b + δ * cubic σ (-(a ^ 2)) (T.symm y) at hh
    have hr : T (T.symm y) = y := T.right_inv' hyT
    rw [hr] at hh
    exact hh
  change
    f y = f (Φ (e * a, 0)) + e * (B (P (T.symm y))).1 ^ 2 + ∑ i, σ i * (B (P (T.symm y))).2 i ^ 2
  rw [hfy, hvalue, hP (T.symm y) hzP]
  have hs := hscale (P (T.symm y))
  linarith

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.negative_card_split {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ) :
    Fintype.card { j // w j = -1 } =
      (if w (ρ Option.none) = -1 then 1 else 0) +
        Fintype.card { i // w (ρ (Option.some i)) = -1 } := by
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← ρ.sum_comp, Fintype.sum_option]

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_index_of_scaled_cubic_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a δ b : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (e : ℝ) (he : e = -1 ∨ e = 1)
    (hp : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgerm : f ∘ Φ =ᶠ[𝓝 (e * a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    nativeMorseIndex E f (Φ (e * a, 0)) =
      (if e = -1 then 1 else 0) + Fintype.card { i // σ i = -1 } := by
  let ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨c, hce, hcσ⟩ := exists_signed_chart_of_scaled_cubic_germ Φ ρ σ hσ ha hδ e he hp hgerm
  rw [nativeMorseIndex_eq_chart c]
  simp only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace]
  rw [negative_card_split ρ c.weights, hce]
  simp only [hcσ]

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_indices_of_cubic_birth_germs {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a δ b : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgp : f ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z)
    (hgq : f ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    nativeMorseIndex E f (Φ (a, 0)) = Fintype.card { i // σ i = -1 } ∧
      nativeMorseIndex E f (Φ (-a, 0)) = Fintype.card { i // σ i = -1 } + 1 := by
  constructor
  · have h :=
      native_index_of_scaled_cubic_germ Φ hdim σ hσ ha hδ 1 (Or.inr rfl)
        (by simpa only [one_mul] using hp) (by simpa only [one_mul] using hgp)
    simpa only [one_mul, ite_eq_right (by norm_num : (1 : ℝ) ≠ -1), zero_add] using h
  · have h :=
      native_index_of_scaled_cubic_germ Φ hdim σ hσ ha hδ (-1) (Or.inl rfl)
        (by simpa only [neg_one_mul] using hq) (by simpa only [neg_one_mul] using hgq)
    simpa [Nat.add_comm] using h

private theorem MorseCancel.exists_transverse_signs_of_count {m k : ℕ} (hk : k ≤ m) :
    ∃ σ : Fin m → ℝ, (∀ i, σ i = -1 ∨ σ i = 1) ∧ {i | σ i = -1}.ncard = k := by
  classical
  let σ : Fin m → ℝ := fun i => if i.val < k then -1 else 1
  refine ⟨σ, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < k
    · exact Or.inl (ite_eq_left hi)
    · exact Or.inr (ite_eq_right hi)
  · have heq : {i : Fin m | σ i = -1} = {i : Fin m | i.val < k} := by
      ext i
      by_cases hi : i.val < k <;> norm_num [σ, hi]
    rw [heq, ← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
    simp only [Set.mem_ofPred_eq]
    rw [Fin.card_filter_val_lt, min_eq_right hk]

private theorem
    MorseCancel.exists_excellent_indexed_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {l u : ℝ}
    (hband : ∀ y, f y ∈ Set.Ioo l u → y ∉ Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) {k : ℕ} (hk : k < Module.finrank ℝ E) {U : Set M} (hU : IsOpen U)
    (hxU : x ∈ U) :
    ∃ (g : M → ℝ) (p q : M),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            p ∈ U ∧
              q ∈ U ∧
                nativeMorseIndex E g p = k ∧
                  nativeMorseIndex E g q = k + 1 ∧
                    g p < g q ∧
                      g p ∈ Set.Ioo l u ∧
                        g q ∈ Set.Ioo l u ∧
                          (Smale.ManifoldMorse.criticalPoints E g).ncard =
                              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  nativeMorseCount E g k = nativeMorseCount E f k + 1 ∧
                                    nativeMorseCount E g (k + 1) =
                                        nativeMorseCount E f (k + 1) + 1 ∧
                                      ∀ j,
                                        j ≠ k →
                                          j ≠ k + 1 →
                                            nativeMorseCount E g j = nativeMorseCount E f j := by
  classical
  let m := Module.finrank ℝ E - 1
  have hdim : 1 + m = Module.finrank ℝ E := by dsimp [m]; omega
  have hkm : k ≤ m := by dsimp [m]; omega
  obtain ⟨σ, hσ, hcard⟩ := exists_transverse_signs_of_count hkm
  have hσne (i : Fin m) : σ i ≠ 0 := by rcases hσ i with h | h <;> rw [h] <;> norm_num
  obtain
    ⟨a, δ, ha, hδ, Φ, hp, hq, hΦ, g, hg, hmg, hinjg, hcount, hcrit, hexterior, hkeep, hpq, hpband,
      hqband, hgp, hgq⟩ :=
    exists_excellent_native_morse_birth hf hm hinj hband hx hdim σ hσne hU hxU
  obtain ⟨hip, hiq⟩ := native_indices_of_cubic_birth_germs Φ hdim σ hσ ha hδ hp hq hgp hgq
  have hc : Fintype.card { i // σ i = -1 } = k := (Set.fintypeCard_eq_ncard _).trans hcard
  rw [hc] at hip hiq
  have hpnot : Φ (a, 0) ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro h
    have hv : g (Φ (a, 0)) = f (Φ (a, 0)) := (hkeep _ h).self_of_nhds
    exact hband _ (hv ▸ hpband) h
  have hqnot : Φ (-a, 0) ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro h
    have hv : g (Φ (-a, 0)) = f (Φ (-a, 0)) := (hkeep _ h).self_of_nhds
    exact hband _ (hv ▸ hqband) h
  have hreverse (y : M) :
    y ∈ Smale.ManifoldMorse.criticalPoints E f ↔
      y ∈ Smale.ManifoldMorse.criticalPoints E g ∧ y ≠ Φ (a, 0) ∧ y ≠ Φ (-a, 0) := by
    rw [hcrit]
    constructor
    · intro hy
      exact ⟨Or.inl hy, fun h => hpnot (h ▸ hy), fun h => hqnot (h ▸ hy)⟩
    · rintro ⟨hy | hp' | hq', hnp, hnq⟩
      · exact hy
      · exact False.elim (hnp hp')
      · exact False.elim (hnq hq')
  have hpcrit := (hcrit (Φ (a, 0))).mpr (Or.inr (Or.inl rfl))
  have hqcrit := (hcrit (Φ (-a, 0))).mpr (Or.inr (Or.inr rfl))
  have hneq : Φ (a, 0) ≠ Φ (-a, 0) := fun h => hpq.ne (congrArg g h)
  obtain ⟨hck, hck', hcothers⟩ :=
    nativeMorseCount_adjacent_pair (Smale.ManifoldMorse.finite_criticalPoints hg hmg) hpcrit
      hqcrit hneq hreverse (fun y hy => (hkeep y hy).symm) hip hiq
  exact
    ⟨g, Φ (a, 0), Φ (-a, 0), hg, hmg, hinjg, hΦ (Φ.map_source' hp), hΦ (Φ.map_source' hq), hip,
      hiq, hpq, hpband, hqband, hcount, hcrit, hexterior, hkeep, hck.symm, hck'.symm,
      fun j hj hj' => (hcothers j hj hj').symm⟩

private theorem MorseCancel.superlevel_bound_of_critical_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l : ℝ} (hboundary : ∀ y, f y = l → g y = l)
    (hcritical : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E g, l ≤ f y → l ≤ g y) :
    ∀ x, l ≤ f x → l ≤ g x := by
  intro x hx
  have hK : IsCompact {y : M | l ≤ f y} := (isClosed_le continuous_const hf).isCompact
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hg.continuous.continuousOn
  have hgp : l ≤ g p := by
    by_cases hlt : l < f p
    · have hlocal : IsLocalMin g p := by
        filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hlt] with y hy
        exact hmin hy.le
      exact hcritical p (Smale.ManifoldMorse.mem_criticalPoints_of_localMin hg hlocal) hp
    · have heq : f p = l := le_antisymm (le_of_not_gt hlt) hp
      exact (hboundary p heq).ge
  exact hgp.trans (hmin hx)

private theorem MorseCancel.birth_preserves_lower_levels {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l : ℝ} {U : Set M} {p q : M} (hU : U ⊆ {y : M | l < f y})
    (hexterior : ∀ y, y ∉ U → g =ᶠ[𝓝 y] f)
    (hkeep : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f)
    (hcrit :
      ∀ y ∈ Smale.ManifoldMorse.criticalPoints E g,
        y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q)
    (hp : l ≤ g p) (hq : l ≤ g q) {a : ℝ} (ha : a < l) :
    (∀ y, g y = a ↔ f y = a) ∧ (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) := by
  have hout (y : M) (hy : f y ≤ l) : y ∉ U := fun h => (hU h).not_ge hy
  have hbound : ∀ y, l ≤ f y → l ≤ g y := by
    apply superlevel_bound_of_critical_bound hf hg
    · intro y hy
      exact (hexterior y (hout y hy.le)).self_of_nhds.trans hy
    · intro y hy hfy
      rcases hcrit y hy with hold | rfl | rfl
      · rw [(hkeep y hold).self_of_nhds]
        exact hfy
      · exact hp
      · exact hq
  refine ⟨?_, fun y hy => hexterior y (hout y (hy.trans ha.le))⟩
  intro y
  constructor
  · intro hgy
    have hfy : f y ≤ l := by
      by_contra h
      have hh := hbound y (le_of_not_ge h)
      rw [hgy] at hh
      exact ha.not_ge hh
    exact ((hexterior y (hout y hfy)).self_of_nhds).symm.trans hgy
  · intro hfy
    exact (hexterior y (hout y (hfy ▸ ha.le))).self_of_nhds.trans hfy

private def MorseCancel.equalLevelDiffeomorph {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f g : M → ℝ} {a : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a) :
    let _ := Smale.RegularLevel.chartedSpace hf hfr
    let _ := Smale.RegularLevel.chartedSpace hg hgr
    Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
      { y : M // f y = a } { y : M // g y = a } ∞ := by
  let _ := Smale.RegularLevel.chartedSpace hf hfr
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let F : { y : M // f y = a } → { y : M // g y = a } := fun y => ⟨y, (heq y).mpr y.property⟩
  let G : { y : M // g y = a } → { y : M // f y = a } := fun y => ⟨y, (heq y).mp y.property⟩
  exact
    { toFun := F
      invFun := G
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_toFun :=
        (Smale.RegularLevel.contMDiff_iff_inclusion hg hgr 𝓘(ℝ, Smale.RegularLevel.Model E) F).mpr
          (Smale.RegularLevel.contMDiff_inclusion hf hfr)
      contMDiff_invFun :=
        (Smale.RegularLevel.contMDiff_iff_inclusion hf hfr 𝓘(ℝ, Smale.RegularLevel.Model E) G).mpr
          (Smale.RegularLevel.contMDiff_inclusion hg hgr) }

private theorem
    MorseCancel.regular_level_of_retained_critical_germs {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
     {f g : M → ℝ} {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {p q : M}
    (hcrit :
      ∀ y ∈ Smale.ManifoldMorse.criticalPoints E g,
        y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q)
    (hkeep : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) (hp : a < g p)
    (hq : a < g q) : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g := by
  intro y hy hcy
  rcases hcrit y hcy with hold | rfl | rfl
  · exact hfr y (((hkeep y hold).self_of_nhds).symm.trans hy) hold
  · exact hp.ne' hy
  · exact hq.ne' hy

private theorem MorseCancel.isotopicToIdentity_conj {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
    (e : Diffeomorph I J M N ∞) {d : Diffeomorph I I M M ∞}
    (hd : Smale.SupportedDiffeomorph.IsotopicToIdentity d) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity ((e.symm.trans d).trans e) := by
  obtain ⟨A, hA, hA0, hA1, hslices⟩ := hd
  refine
    ⟨(fun p => e (A (p.1, e.symm p.2))),
      e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd))), ?_,
      ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hA0, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (d (e.symm y))
    rw [hA1]
  · intro t
    obtain ⟨dₜ, hdₜ⟩ := hslices t
    refine ⟨(e.symm.trans dₜ).trans e, ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (dₜ (e.symm y))
    rw [hdₜ]

private theorem MorseCancel.exists_equal_level_circle_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a })) :
    let _ := Smale.RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) →
                ∃ P :
                  Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                    { y : M // g y = a } { y : M // g y = a } ∞,
                  Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := Smale.RegularLevel.chartedSpace hf hfr
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let _ := Smale.RegularLevel.isManifold hf hfr
  let _ := Smale.RegularLevel.isManifold hg hgr
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  let L := equalLevelDiffeomorph hf hg hfr hgr heq
  let γ' : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨L.symm ∘ γ, L.symm.continuous.comp γ.continuous⟩
  let δ' : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨L.symm ∘ δ, L.symm.continuous.comp δ.continuous⟩
  have hγ' : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ' := L.symm.contMDiff.comp hγ
  have hδ' : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ' := L.symm.contMDiff.comp hδ
  have hderiv (κ : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a }))
    (hk : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ κ)
    (hkd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) κ z)) (z) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) (L.symm ∘ κ) z) := by
    rw [mfderiv_comp z (L.symm.contMDiff.mdifferentiableAt (by simp))
        (hk.mdifferentiableAt (by simp))]
    exact (L.symm.mfderivToContinuousLinearEquiv (by simp) (κ z)).injective.comp (hkd z)
  obtain ⟨Q, hQ, hformula⟩ :=
    exists_native_middle_level_circle_isotopy S hf e hdim hfr hhigh hlow γ' δ' hγ'
      (L.symm.injective.comp hγi) (hderiv γ hγ hγd) hδ' (L.symm.injective.comp hδi)
      (hderiv δ hδ hδd)
  refine ⟨(L.symm.trans Q).trans L, isotopicToIdentity_conj L hQ, ?_⟩
  intro z
  change L (Q (γ' z)) = δ z
  rw [hformula]
  exact L.apply_symm_apply (δ z)

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_new_attaching_circle_placement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ q : Smale.ManifoldMorse.criticalPoints E f, a ≤ f q → 3 ≤ nativeMorseIndex E f q)
    (hlow : ∀ q : Smale.ManifoldMorse.criticalPoints E f, f q ≤ a → nativeMorseIndex E f q ≤ 3)
    (p : Smale.ManifoldMorse.criticalPoints E g)
    [Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 1 + 1)] (hap : a < g p)
    (hgap : ∀ q : Smale.ManifoldMorse.criticalPoints E g, g q < g p → g q < a)
    (δ : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a })) :
    let _ := Smale.RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
      Function.Injective δ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) →
          ∃ Γ : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a }),
            ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Γ ∧
              Function.Injective Γ ∧
                (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z)) ∧
                  (∀ x,
                      x ∈ Set.range Γ ↔
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val)) ∧
                    ∃ P :
                      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E)
                        𝓘(ℝ, Smale.RegularLevel.Model E) { y : M // g y = a } { y : M // g y = a }
                        ∞,
                      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
                        (∀ z, P (Γ z) = δ z) ∧
                          ∀ x,
                            Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val) ↔
                              P x ∈ Set.range δ := by
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let _ := Smale.RegularLevel.chartedSpace hg (T.data p).lower_regular
  let _ := Smale.RegularLevel.isManifold hg hgr
  let _ := Smale.RegularLevel.isManifold hg (T.data p).lower_regular
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
      Function.Injective δ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) → _
  intro hδ hδi hδd
  obtain ⟨σ, D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    T.exists_attaching_circle_lower_transport hg p hgr hap hgap
  have hrange (x : { y : M // g y = a }) :
    x ∈ Set.range Γ ↔ Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val) :=
    T.transported_attaching_range_iff hg p hgr σ σ.surjective Γ hflow x
  obtain ⟨P, hP, hformula⟩ :=
    exists_equal_level_circle_isotopy S hf hg e hdim hfr hgr heq hhigh hlow Γ δ hΓ hΓi hΓd hδ hδi
      hδd
  refine ⟨Γ, hΓ, hΓi, hΓd, hrange, P, hP, hformula, ?_⟩
  intro x
  rw [← hrange]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hformula z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, P.injective ((hformula z).trans hz)⟩

private theorem MorseCancel.unit_level_count_of_circle_placement {M X : Type*} [TopologicalSpace M]
    (F : Flow ℝ M) {f : M → ℝ} {a : ℝ} {p q : M} (P : { y : M // f y = a } ≃ { y : M // f y = a })
    (δ : X → { y : M // f y = a }) (z₀ : X)
    (hplacement : ∀ x, Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ↔ P x ∈ Set.range δ)
    (hsingle : ∀ z, Filter.Tendsto (fun t => F t (δ z).val) Filter.atTop (𝓝 q) ↔ z = z₀) :
    {x : { y : M // f y = a } |
          Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ∧
            Filter.Tendsto (fun t => F t (P x).val) Filter.atTop (𝓝 q)}.ncard =
      1 := by
  have heq :
    {x : { y : M // f y = a } |
        Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t => F t (P x).val) Filter.atTop (𝓝 q)} =
      {P.symm (δ z₀)} := by
    ext x
    constructor
    · rintro ⟨hx, hforward⟩
      obtain ⟨z, hz⟩ := (hplacement x).mp hx
      have hz0 : z = z₀ := (hsingle z).mp (hz.symm ▸ hforward)
      apply Set.mem_singleton_iff.mpr
      apply P.injective
      rw [P.apply_symm_apply, ← hz, hz0]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      refine ⟨(hplacement _).mpr ⟨z₀, (P.apply_symm_apply _).symm⟩, ?_⟩
      rw [P.apply_symm_apply]
      exact (hsingle z₀).mpr rfl
  rw [heq]
  exact Set.ncard_singleton _

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_handle_trade_transverse_level_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : Smale.ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    [Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    let _ := Smale.RegularLevel.chartedSpace hg hgr
    ∃ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // g y = a } { y : M // g y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
        {x : { y : M // g y = a } |
                Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 r.val) ∧
                  Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 ∧
          ∃ (α : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a })) (z₀ :
            Smale.Hemisphere.Sphere 1) (β :
            Metric.sphere (0 : (T.data q).chart.PositiveCoordinates) 1 → { y : M // g y = a }) (v
            : Metric.sphere (0 : (T.data q).chart.PositiveCoordinates) 1),
            ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α ∧
              MDifferentiableAt (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) β v ∧
                β v = α z₀ ∧
                  Smale.NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) α β
                      z₀ v ∧
                    (∀ z, Filter.Tendsto (fun t => T.flow t (α z).val) Filter.atBot (𝓝 r.val)) ∧
                      (∀ᶠ w in 𝓝 v,
                          Filter.Tendsto (fun t => T.flow t (P (β w)).val) Filter.atTop
                            (𝓝 q.val)) ∧
                        ∀ x : { y : M // g y = a },
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 r.val) →
                            Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop (𝓝 m.val) ∨
                              Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop
                                (𝓝 q.val) := by
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let _ := Smale.RegularLevel.isManifold hg hgr
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  obtain ⟨δ, hδ, hδi, hδd, z₀, v, β₀, hβ₀, hcross₀, htrans₀, hβbasin, hsingle, hendpoints⟩ :=
    T.exists_transverse_middle_belt_loop hg hdim m q hm hq u hbranches hqa hgr hnewlow
  obtain ⟨α, hα, -, -, hrange, P, hP, hplace, hplacement⟩ :=
    exists_new_attaching_circle_placement S T hf hg e hdim hfr hgr heq hhigh hlow r har hgap δ hδ
      hδi hδd
  obtain ⟨β, hβ, hcross, htrans, hPβ⟩ :=
    exists_transverse_sheet_of_circle_placement P (hα.mdifferentiableAt (by simp)) hβ₀ hplace
      hcross₀ htrans₀
  refine
    ⟨P, hP, unit_level_count_of_circle_placement T.flow P.toEquiv δ z₀ hplacement hsingle, α, z₀,
      β, v, hα, hβ, hcross, htrans, ?_, ?_, ?_⟩
  · intro z
    exact (hrange (α z)).mp ⟨z, rfl⟩
  · filter_upwards [hβbasin] with w hw
    rw [hPβ w]
    exact hw
  · intro x hx
    obtain ⟨z, hz⟩ := (hplacement x).mp hx
    rw [← hz]
    exact hendpoints z

private theorem AdaptedWindows.realize_unit_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ}
    (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∀ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (z : { y : M // f y = a }),
            ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
              (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
                (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
                  (∀ x,
                      x ∉ Smale.ManifoldMorse.criticalPoints E f →
                        mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                    (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
                      Filter.Tendsto (fun t => G t z.val) Filter.atBot (𝓝 p.val) ∧
                        Filter.Tendsto (fun t => G t z.val) Filter.atTop (𝓝 q.val) ∧
                          (∀ x,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p.val) →
                                Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q.val) →
                                  ∃ t, G t z.val = x) ∧
                            (∀ (x : { y : M // f y = a }) y,
                                Filter.Tendsto (fun t => G t x.val) Filter.atBot (𝓝 y) ↔
                                  Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 y)) ∧
                              ∀ (x : { y : M // f y = a }) y,
                                Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 y) ↔
                                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop
                                    (𝓝 y) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.isManifold hf ha
  change
    ∀ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          _
  intro P hP hcount
  obtain ⟨z₀, -⟩ := Set.ncard_eq_one.mp hcount
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level ha
  obtain
    ⟨r, C, W, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband ha z₀ P hP
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val P
      (fun x y => (hgeometry x).2.1 y) (fun x y => (hgeometry x).2.2 y) hend hleft hright
  obtain ⟨z, hzb, hzf, hunique⟩ :=
    Degree.FlowSuspension.exists_unique_connection_of_unit_level_count S.flow G hf.continuous hpa
      hqa P (fun x => hback x p.val) (fun x => hforward x q.val) hcount
  exact
    ⟨V, G, z, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc, hgerms, hzb, hzf, hunique,
      hback, hforward⟩

private theorem
    AdaptedWindows.realize_unit_transverse_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {A B HA HB X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ} (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∀ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          ∀ (α : X → { y : M // f y = a }) (β : Y → { y : M // f y = a }) (x : X) (y : Y),
            MDifferentiableAt I 𝓘(ℝ, Smale.RegularLevel.Model E) α x →
              MDifferentiableAt I' 𝓘(ℝ, Smale.RegularLevel.Model E) β y →
                β y = α x →
                  Smale.NativeTransversality.At I I' 𝓘(ℝ, Smale.RegularLevel.Model E) α β x y →
                    (∀ᶠ u in 𝓝 x,
                        Filter.Tendsto (fun t => S.flow t (α u).val) Filter.atBot (𝓝 p.val)) →
                      (∀ᶠ u in 𝓝 y,
                          Filter.Tendsto (fun t => S.flow t (P (β u)).val) Filter.atTop
                            (𝓝 q.val)) →
                        ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
                          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                              (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                            (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
                              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, V z = 0) ∧
                                (∀ z,
                                    z ∉ Smale.ManifoldMorse.criticalPoints E f →
                                      mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
                                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ w in 𝓝 z, V w = S.field w) ∧
                                    Filter.Tendsto (fun t => G t (α x).val) Filter.atBot
                                        (𝓝 p.val) ∧
                                      Filter.Tendsto (fun t => G t (α x).val) Filter.atTop
                                          (𝓝 q.val) ∧
                                        (∀ z,
                                            Filter.Tendsto (fun t => G t z) Filter.atBot
                                                (𝓝 p.val) →
                                              Filter.Tendsto (fun t => G t z) Filter.atTop
                                                  (𝓝 q.val) →
                                                ∃ t, G t (α x).val = z) ∧
                                          (∀ (z : { w : M // f w = a }) w,
                                              Filter.Tendsto (fun t => G t z.val) Filter.atBot
                                                  (𝓝 w) ↔
                                                Filter.Tendsto (fun t => S.flow t z.val)
                                                  Filter.atBot (𝓝 w)) ∧
                                            (∀ (z : { w : M // f w = a }) w,
                                                Filter.Tendsto (fun t => G t z.val) Filter.atTop
                                                    (𝓝 w) ↔
                                                  Filter.Tendsto (fun t => S.flow t (P z).val)
                                                    Filter.atTop (𝓝 w)) ∧
                                              let C : X × ℝ → M := fun u => G u.2 (α u.1).val
                                              let D : Y × ℝ → M := fun u => G u.2 (β u.1).val
                                              MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) C
                                                  (x, 0) ∧
                                                MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) D
                                                    (y, 0) ∧
                                                  C (x, 0) = (α x).val ∧
                                                    D (y, 0) = (α x).val ∧
                                                      (∀ᶠ u in 𝓝 (x, (0 : ℝ)),
                                                          Filter.Tendsto (fun t => G t (C u))
                                                            Filter.atBot (𝓝 p.val)) ∧
                                                        (∀ᶠ u in 𝓝 (y, (0 : ℝ)),
                                                            Filter.Tendsto (fun t => G t (D u))
                                                              Filter.atTop (𝓝 q.val)) ∧
                                                          Smale.NativeTransversality.At
                                                            (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ))
                                                            𝓘(ℝ, E) C D (x, 0) (y, 0) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.isManifold hf ha
  change
    ∀ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          _
  intro P hP hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨V, G, z, hV, hG, hzero, hdesc, hgerms, -, -, hunique, hback, hforward⟩ :=
    S.realize_unit_level_isotopy hf p q hpa hqa ha P hP hcount
  have hαG : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => G t (α u).val) Filter.atBot (𝓝 p.val) := by
    filter_upwards [hαbasin] with u hu
    exact (hback (α u) p.val).mpr hu
  have hβG : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => G t (β u).val) Filter.atTop (𝓝 q.val) := by
    filter_upwards [hβbasin] with u hu
    exact (hforward (β u) q.val).mpr hu
  have hxforward : Filter.Tendsto (fun t => G t (α x).val) Filter.atTop (𝓝 q.val) := by
    have hh := hβG.self_of_nhds
    rwa [hcross] at hh
  obtain ⟨s, hs⟩ := hunique (α x).val hαG.self_of_nhds hxforward
  have huniq (w : M) (hwb : Filter.Tendsto (fun t => G t w) Filter.atBot (𝓝 p.val))
    (hwf : Filter.Tendsto (fun t => G t w) Filter.atTop (𝓝 q.val)) : ∃ t, G t (α x).val = w := by
    obtain ⟨t, ht⟩ := hunique w hwb hwf
    refine ⟨t - s, ?_⟩
    rw [← hs, ← G.map_add, sub_add_cancel, ht]
  refine
    ⟨V, G, hV, hG, hzero, hdesc, hgerms, hαG.self_of_nhds, hxforward, huniq, hback, hforward, ?_⟩
  exact
    Degree.FlowSuspension.native_transverse_basin_tubes_of_level_maps hf ha hV G hG
      (fun w hw => hdesc w (ha w hw)) α β x y hα hβ hcross htrans hαG hβG

private theorem
    MorseCancel.no_other_connections_of_two_level_endpoints {M : Type*} [TopologicalSpace M]
    [T2Space M] (F : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {C : Set M} (hinj : Set.InjOn f C)
    (p q r : C) {a : ℝ} (hpa : a < f p) (hgap : ∀ j : C, f j < f p → f j < a)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hends :
      ∀ x : { y : M // f y = a },
        Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p.val) →
          Filter.Tendsto (fun t => F t x.val) Filter.atTop (𝓝 q.val) ∨
            Filter.Tendsto (fun t => F t x.val) Filter.atTop (𝓝 r.val)) :
    ∀ j : C,
      j ≠ p →
        j ≠ q →
          j ≠ r →
            ∀ x,
              ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val)) := by
  intro j hjp hjq hjr x hx
  have hforwardHeight := hf.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f p :=
    (hmono x).le_of_tendsto hforwardHeight 0 |>.trans ((hmono x).ge_of_tendsto hbackwardHeight 0)
  have hlt : f j < f p :=
    lt_of_le_of_ne hle (fun h => hjp (Subtype.ext (hinj j.property p.property h)))
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits F hf hx.1 hx.2 hpa
      (hgap j hlt)
  let z : { y : M // f y = a } := ⟨F t x, ht⟩
  have hzb : Filter.Tendsto (fun s => F s z.val) Filter.atBot (𝓝 p.val) :=
    (flow_time_atBot_limit_iff F t x p.val).mpr hx.1
  have hzf : Filter.Tendsto (fun s => F s z.val) Filter.atTop (𝓝 j.val) :=
    (flow_time_atTop_limit_iff F t x j.val).mpr hx.2
  rcases hends z hzb with hq | hr
  · exact hjq (Subtype.ext (tendsto_nhds_unique hzf hq))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzf hr))

private theorem MorseCancel.cancel_transverse_pair_after_flow_preserving_descent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} {m : ℕ} {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB]
    {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X]
    [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hdim : Module.finrank ℝ E = m + 1) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : Smale.ManifoldMorse.criticalPoints E f) (hrp : f r < f p) (hpq : f p < f q)
    (hindex : nativeMorseIndex E f q = nativeMorseIndex E f p + 1)
    (hnoconnection :
      ∀ j : Smale.ManifoldMorse.criticalPoints E f,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val)))
    {z : M} (hzp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p.val))
    (hzq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q.val))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p.val) → ∃ t, F t z = x)
    {α : X → M} {β : Y → M} {x : X} {y : Y} (hα : MDifferentiableAt I 𝓘(ℝ, E) α x)
    (hβ : MDifferentiableAt I' 𝓘(ℝ, E) β y) (hα0 : α x = z) (hβ0 : β y = z)
    (hαbasin : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (α u)) Filter.atBot (𝓝 q.val))
    (hβbasin : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (β u)) Filter.atTop (𝓝 p.val))
    (htrans : Smale.NativeTransversality.At I I' 𝓘(ℝ, E) α β x y) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              (∀ w,
                  w ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                    w ∈ Smale.ManifoldMorse.criticalPoints E f ∧ w ≠ p.val ∧ w ≠ q.val) ∧
                ∀ w ∈ Smale.ManifoldMorse.criticalPoints E g,
                  nativeMorseIndex E g w = nativeMorseIndex E f w := by
  obtain ⟨h, hh, hmh, hcrit, hinjh, -, -, hpqh, hconsecutive, hdesch, hmodelsh, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf hm hinj hV F hF hzero hdesc hmodels p r q hrp hpq
      hnoconnection
  have hpcrit : p.val ∈ Smale.ManifoldMorse.criticalPoints E h := hcrit.symm ▸ p.property
  have hqcrit : q.val ∈ Smale.ManifoldMorse.criticalPoints E h := hcrit.symm ▸ q.property
  obtain ⟨cp, hcp⟩ := hmodelsh p.val hpcrit
  obtain ⟨cq, hcq⟩ := hmodelsh q.val hqcrit
  have hidx :
    Module.finrank ℝ cq.NegativeCoordinates = Module.finrank ℝ cp.NegativeCoordinates + 1 := by
    rw [← nativeMorseIndex_eq_chart cq, ← nativeMorseIndex_eq_chart cp, hindices q.val q.property,
      hindices p.val p.property]
    exact hindex
  have hcard :
    Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1 := by
    simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using hidx
  obtain ⟨W⟩ := Smale.ManifoldMorse.nonempty_surgeryWindows hh hmh hinjh
  let ph : Smale.ManifoldMorse.criticalPoints E h := ⟨p.val, hpcrit⟩
  let qh : Smale.ManifoldMorse.criticalPoints E h := ⟨q.val, hqcrit⟩
  have hconsecutiveh : ∀ s : Smale.ManifoldMorse.criticalPoints E h, ¬(h ph < h s ∧ h s < h qh) :=
    by
    intro s hs
    exact hconsecutive ⟨s.val, hcrit ▸ s.property⟩ hs
  have hpair := surgery_pair_band_isolation W ph qh hconsecutiveh
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior⟩ :=
    cancel_unique_connection_of_transverse_basin_sheets cp cq hh hmh hdim hcard V hV
      (fun w hw => hzero w (hcrit ▸ hw)) hdesch F hF hinjh hpcrit hqcrit hpqh
      (W.lower_lt_value ph) (W.value_lt_upper qh) hpair hzp hzq hunique hcp hcq hα hβ hα0 hβ0
      hαbasin hβbasin htrans
  have hkeep := surviving_critical_germs_of_pair_band hpair hcritg hexterior
  have hinjg :=
    distinct_critical_values_of_surviving_germs hinjh (fun w hw => ((hcritg w).mp hw).1) hkeep
  rw [hcrit] at hcount
  refine ⟨g, hg, hmg, hinjg, hcount, ?_, ?_⟩
  · intro w
    rw [hcritg w, hcrit]
  · intro w hw
    exact
      (nativeMorseIndex_congr_germ (hkeep w hw)).trans (hindices w (hcrit ▸ ((hcritg w).mp hw).1))

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.cancel_one_two_pair_at_preserved_middle_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f g : M → ℝ} (S : AdaptedWindows E f) (T : AdaptedWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : Smale.ManifoldMorse.IsMorse E g) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : Smale.ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard + 2 =
                (Smale.ManifoldMorse.criticalPoints E g).ncard ∧
              (∀ w,
                  w ∈ Smale.ManifoldMorse.criticalPoints E h ↔
                    w ∈ Smale.ManifoldMorse.criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
                ∀ w ∈ Smale.ManifoldMorse.criticalPoints E h,
                  nativeMorseIndex E h w = nativeMorseIndex E g w := by
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let _ := Smale.RegularLevel.isManifold hg hgr
  have hnegq : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨P, hP, hcount, α, z₀, β, v, hα, hβ, hcross, htrans, hαbasin, hβbasin, hends⟩ :=
    exists_handle_trade_transverse_level_data S T hf hg e hdim hfr hgr heq hhigh hlow m q r hm hq
      hr u hbranches hqa har hgap hnewlow
  have hqcut : g q < a := (T.toSurgeryWindows.value_lt_upper q).trans_le hqa
  obtain
    ⟨V, G, hV, hG, hzero, hdesc, hgerms, hbackr, hforwardq, hunique, hback, hforward, htubes⟩ :=
    T.realize_unit_transverse_level_isotopy hg r q har hqcut hgr P hP hcount α β z₀ v
      (hα.mdifferentiableAt (by simp)) hβ hcross htrans (Filter.Eventually.of_forall hαbasin)
      hβbasin
  have hendsG (x : { y : M // g y = a })
    (hx : Filter.Tendsto (fun t => G t x.val) Filter.atBot (𝓝 r.val)) :
    Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 q.val) ∨
      Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 m.val) := by
    have hh := hends x ((hback x r.val).mp hx)
    exact (hh.imp ((hforward x m.val).mpr) ((hforward x q.val).mpr)).symm
  have hnoconnection :=
    no_other_connections_of_two_level_endpoints G hg.continuous T.distinct r q m har hgap
      (Smale.FlowConstruction.antitone_flow_height hg G hG hzero hdesc) hendsG
  have hmodels :
    ∀ x ∈ Smale.ManifoldMorse.criticalPoints E g,
      ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    refine ⟨(T.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, T.critical_model_germ ⟨x, hx⟩] with y hy hyt
    exact hy.trans hyt
  have hmq : g m < g q :=
    (T.forward_limit_below_regular_level hg (T.data q).lower_regular
          ((T.data q).surgery.attachingSphere u) (hbranches u)).trans
      (T.toSurgeryWindows.lower_lt_value q)
  obtain ⟨hC, hD, hC0, hD0, hCb, hDb, htransM⟩ := htubes
  exact
    cancel_transverse_pair_after_flow_preserving_descent hg hmg T.distinct (m := 5) (by omega) hV
      G hG hzero hdesc hmodels q m r hmq (hqcut.trans har) (by omega) hnoconnection hforwardq
      hbackr hunique hC hD hC0 hD0 hCb hDb htransM

private theorem MorseCancel.exists_distinct_unitSphere_points_of_finrank_one {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 1) : ∃ u v : Metric.sphere (0 : V) 1, u ≠ v := by
  obtain ⟨L⟩ :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hdim)
  let e := Degree.UnitSphereEquiv.homeomorph L
  let u : Metric.sphere (0 : ℝ) 1 := ⟨1, by simp⟩
  let v : Metric.sphere (0 : ℝ) 1 := ⟨-1, by simp⟩
  refine ⟨e.symm u, e.symm v, ?_⟩
  intro heq
  have hh : u = v := e.symm.injective heq
  have hval : (1 : ℝ) = -1 := congrArg Subtype.val hh
  norm_num at hval

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.place_one_handle_in_unique_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hone : MorseCancel.nativeMorseIndex E f q = 1)
    (hunique :
      ∀ r : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f r = 0 → r = p) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧
        f p < S.toSurgeryWindows.lower q ∧
          ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
            Filter.Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
              Filter.atTop (𝓝 p.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data q).lower_regular
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := MorseCancel.exists_distinct_unitSphere_points_of_finrank_one hi
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := fun h => huv ((S.data q).attaching_isClosedEmbedding.injective h)
  obtain ⟨d, hd, ⟨r, hr, hru⟩, ⟨s, hs, hsv⟩⟩ :=
    MorseCancel.exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, Smale.RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpu : Filter.Tendsto (fun t => S.flow t (d (α u)).val) Filter.atTop (𝓝 p.val) :=
    hunique r hr ▸ hru
  have hpv : Filter.Tendsto (fun t => S.flow t (d (α v)).val) Filter.atTop (𝓝 p.val) :=
    hunique s hs ▸ hsv
  refine
    ⟨d, hd, S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu, ?_⟩
  intro w
  rcases MorseCancel.unitSphere_eq_two_points_of_finrank_one hi u v huv w with rfl | rfl
  · exact hpu
  · exact hpv

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.realize_unique_minimum_one_handle_branches {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hone : MorseCancel.nativeMorseIndex E f q = 1)
    (hunique :
      ∀ r : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f r = 0 → r = p) :
    ∃ T : AdaptedWindows E f,
      (∀ r : Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 r.val, T.field x = S.field x) ∧
        (∀ r, (T.data r).chart = (S.data r).chart) ∧
          (∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
              Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val)
                Filter.atTop (𝓝 p.val)) ∧
            ∀ r : Smale.ManifoldMorse.criticalPoints E f,
              r ≠ q →
                r ≠ p →
                  ∀ x,
                    ¬(Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 q.val) ∧
                        Filter.Tendsto (fun t => T.flow t x) Filter.atTop (𝓝 r.val)) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, hpq, hall⟩ := S.place_one_handle_in_unique_minimum_basin hf p q hone hunique
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := MorseCancel.exists_distinct_unitSphere_points_of_finrank_one hi
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain
    ⟨ρ, C, W, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  have hVz : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0 := fun x hx =>
    (hzero x).mpr (S.zero x hx)
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val d
      (fun x z => (hgeometry x).2.1 z) (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
      (𝓝 p.val) :=
    (hforward _ p.val).mpr (hall w)
  have hno (r : Smale.ManifoldMorse.criticalPoints E f) (hrq : r ≠ q) (hrp : r ≠ p) (x : M) :
    ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ∧
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 r.val)) := by
    intro hx
    have hmono := Smale.FlowConstruction.antitone_flow_height hf G hG hVz hdesc x
    have hle : f r ≤ f q :=
      (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.2) 0).trans
        (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.1) 0)
    have hrq' : f r < f q :=
      lt_of_le_of_ne hle (fun h => hrq (Subtype.ext (S.distinct r.property q.property h)))
    have hrlow : f r < S.toSurgeryWindows.lower q :=
      (S.toSurgeryWindows.value_lt_upper r).trans (S.separated r q hrq')
    obtain ⟨t, ht⟩ :=
      Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous hx.1 hx.2
        (S.toSurgeryWindows.lower_lt_value q) hrlow
    let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
    have hzq : Filter.Tendsto (fun s => G s z) Filter.atBot (𝓝 q.val) :=
      (MorseCancel.flow_time_atBot_limit_iff G t x q.val).mpr hx.1
    have hzr : Filter.Tendsto (fun s => G s z) Filter.atTop (𝓝 r.val) :=
      (MorseCancel.flow_time_atTop_limit_iff G t x r.val).mpr hx.2
    obtain ⟨w, hw⟩ := (hbq z).mp hzq
    have hpz := hends w
    rw [hw] at hpz
    exact hrp (Subtype.ext (tendsto_nhds_unique hzr hpz))
  have hmodel (r : Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 r.val, V x = (S.data r).chart.descentField x := by
    filter_upwards [hgerms r r.property, S.critical_model_germ r] with x hx hxs
    exact hx.trans hxs
  obtain ⟨T, hfield, hflow, hchart⟩ :=
    MorseCancel.exists_adapted_windows_with_prescribed_flow hf hm S.distinct hV G hG hVz hdesc
      (fun r => (S.data r).chart) hmodel
  refine ⟨T, ?_, hchart, ?_, ?_⟩
  · intro r
    rw [hfield]
    exact hgerms r r.property
  · intro w
    let z := (T.data q).surgery.attachingSphere w
    have hzq : Filter.Tendsto (fun t => T.flow t z.val) Filter.atBot (𝓝 q.val) :=
      (T.attaching_basin_iff hf q z).mpr ⟨w, rfl⟩
    obtain ⟨r₀, hr₀, r, hr, -, hrlim, hheight⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf T.smooth T.flow T.integral T.zero
        T.descent T.distinct z.val
    have hrq : (⟨r, hr⟩ : Smale.ManifoldMorse.criticalPoints E f) ≠ q := by
      intro heq
      have hlt := (hheight ((T.data q).lower_regular z.val z.property)).1
      have hrval : r = q.val := congrArg Subtype.val heq
      rw [hrval, z.property] at hlt
      nlinarith [sq_nonneg (T.data q).radius]
    have hrp : (⟨r, hr⟩ : Smale.ManifoldMorse.criticalPoints E f) = p := by
      by_contra hne
      apply hno ⟨r, hr⟩ hrq hne z.val
      rw [hflow] at hzq hrlim
      exact ⟨hzq, hrlim⟩
    exact (congrArg Subtype.val hrp) ▸ hrlim
  · intro r hrq hrp x
    rw [hflow]
    exact hno r hrq hrp x

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f g : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g)) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : Smale.ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = m)
    (hqa : g q < a) (har : a < g r)
    (hgap : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard + 2 =
                (Smale.ManifoldMorse.criticalPoints E g).ncard ∧
              (∀ w,
                  w ∈ Smale.ManifoldMorse.criticalPoints E h ↔
                    w ∈ Smale.ManifoldMorse.criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
                ∀ w ∈ Smale.ManifoldMorse.criticalPoints E h,
                  nativeMorseIndex E h w = nativeMorseIndex E g w := by
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨U, -, -, hbranchesU, -⟩ :=
    T₀.realize_unique_minimum_one_handle_branches hg hmg m q hq hminimum
  obtain ⟨T, -, hflow, -, hbelow, -⟩ := U.exists_same_flow_windows_avoiding_level hg hmg hgr
  have hbranches := U.attaching_branches_of_same_flow T hg m q hflow hbranchesU
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  obtain ⟨u, v, huv⟩ := exists_distinct_unitSphere_points_of_finrank_one hneg
  exact
    cancel_one_two_pair_at_preserved_middle_cut S T hf hg hmg e hdim hfr hgr heq hhigh hlow m q r
      hm hq hr u hbranches (hbelow q hqa).le har hgap hnewlow

private theorem MorseCancel.birth_preserves_lower_index_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {a : ℝ}
    {k : ℕ}
    (hcrit :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        z ∈ Smale.ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f) (hp : a < g p)
    (hq : a < g q)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ k) :
    ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ k := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · rw [nativeMorseIndex_congr_germ (hkeep z.val hold)]
    apply hlow ⟨z.val, hold⟩
    rwa [← (hkeep z.val hold).self_of_nhds]
  · exact False.elim (hp.not_ge (hzp ▸ hz))
  · exact False.elim (hq.not_ge (hzq ▸ hz))

private theorem MorseCancel.birth_first_new_value_gap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {a b : ℝ}
    (hcrit :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        z ∈ Smale.ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hreg : ∀ z, f z = a → z ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hband : ∀ z, f z ∈ Set.Ioo a b → z ∉ Smale.ManifoldMorse.criticalPoints E f) (hp : g p < b)
    (hpq : g p < g q) : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g p → g z < a := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · have hzb : g z < b := hz.trans hp
    have heq := (hkeep z.val hold).self_of_nhds
    by_contra hnot
    have haz : a ≤ f z := by rw [← heq]; exact le_of_not_gt hnot
    have hne : a ≠ f z := fun h => hreg z.val h.symm hold
    exact hband z.val ⟨lt_of_le_of_ne haz hne, by rwa [← heq]⟩ hold
  · exact False.elim ((hzp ▸ hz : g p < g p).false)
  · exact False.elim (hpq.not_gt (hzq ▸ hz))

private theorem MorseCancel.birth_preserves_unique_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (m : Smale.ManifoldMorse.criticalPoints E f)
    (hcrit :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        z ∈ Smale.ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hp : nativeMorseIndex E g p ≠ 0) (hq : nativeMorseIndex E g q ≠ 0)
    (hunique : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = m.val := by
  intro z hz hi
  rcases hcrit z hz with hold | rfl | rfl
  · have hiold : nativeMorseIndex E f z = 0 :=
      (nativeMorseIndex_congr_germ (hkeep z hold)).symm.trans hi
    exact congrArg Subtype.val (hunique ⟨z, hold⟩ hiold)
  · exact False.elim (hp hi)
  · exact False.elim (hq hi)

private theorem MorseCancel.indexed_criticalPoints_removed_of_index_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M}
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} \
        { p, q } := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
    exact ⟨⟨hzf, (hindex z hz).symm.trans hi⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hi⟩, hzp, hzq⟩
    have hz := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hz, (hindex z hz).trans hi⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.nativeMorseCount_removed_of_index_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) =
      nativeMorseCount E f k := by
  let K := {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ { p, q }) = K \ { p, q } := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hrem :
    (K ∩ { p, q }).ncard =
      (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) := by
    by_cases hip : nativeMorseIndex E f p = k
    · have hpK : p ∈ K := ⟨hp, hip⟩
      rw [Set.inter_insert_of_mem hpK, ite_eq_left hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), ite_eq_left hiq,
          Set.ncard_pair hpq]
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), ite_eq_right hiq]
        simp
    · have hpK : p ∉ K := fun h => hip h.2
      rw [Set.inter_insert_of_notMem hpK, ite_eq_right hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), ite_eq_left hiq]
        simp
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), ite_eq_right hiq]
        simp
  have hc := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_left : K ∩ { p, q } ⊆ K) hK
  rw [hdiff, hrem] at hc
  unfold nativeMorseCount
  rw [indexed_criticalPoints_removed_of_index_eq hcrit hindex k]
  exact (Nat.add_assoc _ _ _).trans hc

private theorem MorseCancel.nativeMorseCount_adjacent_removed_of_index_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M} (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    {k : ℕ} (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
        ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_removed_of_index_eq hfinite hp hq hpq hcrit hindex
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, ite_eq_right (Ne.symm hj), ite_eq_right (Ne.symm hj'),
      Nat.add_zero] using hc j

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_one_to_three_handle_trade {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) (m q : Smale.ManifoldMorse.criticalPoints E f)
    (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a l u : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) (hal : a < l)
    (hband : ∀ y, f y ∈ Set.Ioo a u → y ∉ Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  let U : Set M := f ⁻¹' Set.Ioo l u
  have hU : IsOpen U := isOpen_Ioo.preimage hf.continuous
  have hbirthband : ∀ y, f y ∈ Set.Ioo l u → y ∉ Smale.ManifoldMorse.criticalPoints E f :=
    fun y hy => hband y ⟨hal.trans hy.1, hy.2⟩
  obtain
    ⟨g, b₂, b₃, hg, hmg, hinjg, -, -, hi₂, hi₃, h₂₃, hv₂, hv₃, hcountbirth, hcrit, hexterior,
      hkeep, hcount₂, hcount₃, hcountOther⟩ :=
    exists_excellent_indexed_morse_birth hf hm S.distinct hbirthband hx (k := 2) (by omega) hU hx
  have hcrit' (z : M) (hz : z ∈ Smale.ManifoldMorse.criticalPoints E g) :
    z ∈ Smale.ManifoldMorse.criticalPoints E f ∨ z = b₂ ∨ z = b₃ := (hcrit z).mp hz
  have hab₂ : a < g b₂ := hal.trans hv₂.1
  have hab₃ : a < g b₃ := hal.trans hv₃.1
  obtain ⟨heq, -⟩ :=
    birth_preserves_lower_levels hf.continuous hg
      (show U ⊆ {y : M | l < f y} from fun _ hy => hy.1) hexterior hkeep hcrit' hv₂.1.le hv₃.1.le
      hal
  have hgr := regular_level_of_retained_critical_germs hreg hcrit' hkeep hab₂ hab₃
  have hgap := birth_first_new_value_gap hcrit' hkeep hreg hband hv₂.2 h₂₃
  have hnewlow := birth_preserves_lower_index_bound hcrit' hkeep hab₂ hab₃ hlow
  let mg : Smale.ManifoldMorse.criticalPoints E g :=
    ⟨m.val, (hcrit m.val).mpr (Or.inl m.property)⟩
  let qg : Smale.ManifoldMorse.criticalPoints E g :=
    ⟨q.val, (hcrit q.val).mpr (Or.inl q.property)⟩
  let rg : Smale.ManifoldMorse.criticalPoints E g := ⟨b₂, (hcrit b₂).mpr (Or.inr (Or.inl rfl))⟩
  have hmg0 : nativeMorseIndex E g mg = 0 :=
    (nativeMorseIndex_congr_germ (hkeep m.val m.property)).trans hm0
  have hqg1 : nativeMorseIndex E g qg = 1 :=
    (nativeMorseIndex_congr_germ (hkeep q.val q.property)).trans hq1
  have hminG :
    ∀ z : Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = mg := by
    intro z hz
    apply Subtype.ext
    exact
      birth_preserves_unique_index_zero m hcrit' hkeep (by rw [hi₂]; omega) (by rw [hi₃]; omega)
        hminimum z.val z.property hz
  have hqga : g qg < a := by
    change g q.val < a
    rw [(hkeep q.val q.property).self_of_nhds]
    exact hqa
  obtain ⟨h, hh, hmh, hinjh, hcountcancel, hcritcancel, hindices⟩ :=
    cancel_one_two_pair_at_unchanged_cut_of_unique_minimum S hf hg hmg hinjg e hdim hreg hgr heq
      hhigh (fun z hz => (hlow z hz).trans (by omega)) mg qg rg hmg0 hqg1 hi₂ hminG hqga hab₂ hgap
      hnewlow
  have hq₂ : qg.val ≠ rg.val := fun he => (hqga.trans hab₂).ne (congrArg g he)
  obtain ⟨hremove₁, hremove₂, hremoveOther⟩ :=
    nativeMorseCount_adjacent_removed_of_index_eq
      (Smale.ManifoldMorse.finite_criticalPoints hg hmg) qg.property rg.property hq₂ hcritcancel
      hindices hqg1 hi₂
  have htotal :
    (Smale.ManifoldMorse.criticalPoints E h).ncard =
      (Smale.ManifoldMorse.criticalPoints E f).ncard :=
    Nat.add_right_cancel (hcountcancel.trans hcountbirth)
  have hcount₁ : nativeMorseCount E g 1 = nativeMorseCount E f 1 :=
    hcountOther 1 (by omega) (by omega)
  have hcountₕ₂ : nativeMorseCount E h 2 = nativeMorseCount E f 2 :=
    Nat.add_right_cancel (hremove₂.trans hcount₂)
  refine
    ⟨h, hh, hmh, hinjh, htotal, hremove₁.trans hcount₁,
      (hremoveOther 3 (by omega) (by omega)).trans hcount₃, ?_⟩
  intro j hj1 hj3
  by_cases hj2 : j = 2
  · subst j
    exact hcountₕ₂
  · exact (hremoveOther j hj1 hj2).trans (hcountOther j hj2 hj3)

private theorem
    MorseCancel.exists_one_to_three_handle_trade_at_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) (m q : Smale.ManifoldMorse.criticalPoints E f)
    (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  have hneg : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq1
  have hsplit := (S.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨v, t, ht⟩ := S.exists_belt_point_reaching_level hf q 4 hqa hlow (by omega)
  let z := S.flow t ((S.data q).surgery.beltSphere v).val
  have hz : f z = a := ht
  obtain ⟨l₀, u, hl₀, hau, hband⟩ := S.regular_interval_around_level hreg
  have hc : Continuous (fun s : ℝ => f (S.flow s z)) :=
    hf.continuous.comp (S.flow.continuous continuous_id continuous_const)
  have h0 : (fun s : ℝ => f (S.flow s z)) 0 ∈ Set.Iio u := by
    simpa only [Flow.map_zero_apply, hz, Set.mem_Iio] using hau
  obtain ⟨ε, hε, hεball⟩ :=
    Metric.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0))
  let x := S.flow (-ε / 2) z
  have hxu : f x < u :=
    hεball
      (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith)
  have hax : a < f x := by
    have hh :=
      Smale.FlowConstruction.strictAnti_flow_height hf (S.smooth.of_le (by simp)) S.flow
        S.integral S.zero S.descent (hreg z hz) (show -ε / 2 < 0 by linarith)
    simpa only [Flow.map_zero_apply, hz] using hh
  exact
    exists_one_to_three_handle_trade S hf hm e hdim m q hm0 hq1 hminimum hreg hhigh hlow hqa
      (show a < (a + f x) / 2 by linarith) (fun y hy => hband y ⟨hl₀.le.trans hy.1.le, hy.2.le⟩)
      (show f x ∈ Set.Ioo ((a + f x) / 2) u from ⟨by linarith, hxu⟩)

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.exists_ordered_index_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    {k : ℕ} (q : Smale.ManifoldMorse.criticalPoints E f)
    (hq : MorseCancel.nativeMorseIndex E f q ≤ k) :
    ∃ a : ℝ,
      (∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) ∧
        f q < a ∧
          (∀ z : Smale.ManifoldMorse.criticalPoints E f,
              a ≤ f z → k + 1 ≤ MorseCancel.nativeMorseIndex E f z) ∧
            ∀ z : Smale.ManifoldMorse.criticalPoints E f,
              f z ≤ a → MorseCancel.nativeMorseIndex E f z ≤ k := by
  let _ := S.finite.fintype
  let K :=
    Finset.univ.filter
      (fun z : Smale.ManifoldMorse.criticalPoints E f => MorseCancel.nativeMorseIndex E f z ≤ k)
  have hqK : q ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  obtain ⟨r, hr, hmax⟩ :=
    K.exists_max_image (fun z : Smale.ManifoldMorse.criticalPoints E f => f z) ⟨q, hqK⟩
  have hrk : MorseCancel.nativeMorseIndex E f r ≤ k := (Finset.mem_filter.mp hr).2
  let a := S.toSurgeryWindows.upper r
  have hra : f r < a := S.toSurgeryWindows.value_lt_upper r
  refine ⟨a, (S.data r).upper_regular, (hmax q hqK).trans_lt hra, ?_, ?_⟩
  · intro z haz
    by_contra hnot
    have hzK : z ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    exact (not_lt_of_ge (haz.trans (hmax z hzK))) hra
  · intro z hza
    rcases lt_trichotomy (f z) (f r) with hzr | hzr | hrz
    · exact (horder z r hzr).trans hrk
    · have he : z = r := Subtype.ext (S.distinct z.property r.property hzr)
      simpa only [he] using hrk
    · have he : z = r :=
        Subtype.ext
          (S.toSurgeryWindows.isolated r z.val z.property
            ⟨(S.toSurgeryWindows.lower_lt_value r).le.trans hrz.le, hza⟩)
      simpa only [he] using hrk

private theorem MorseCancel.exists_one_to_three_handle_trade_of_ordered_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (m q : Smale.ManifoldMorse.criticalPoints E f) (hm0 : nativeMorseIndex E f m = 0)
    (hq1 : nativeMorseIndex E f q = 1)
    (hminimum :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  obtain ⟨a, hreg, hqa, hhigh, hlow⟩ :=
    S.exists_ordered_index_cut horder q (show nativeMorseIndex E f q ≤ 2 by omega)
  exact
    exists_one_to_three_handle_trade_at_cut S hf hm e hdim m q hm0 hq1 hminimum hreg hhigh hlow
      hqa

private theorem MorseCancel.exists_outer_index_minimal_ordered_morse_system (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
                  (∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        Smale.ManifoldMorse.IsMorse E g →
                          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                            (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                              (Smale.ManifoldMorse.criticalPoints E g).ncard) ∧
                    ∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        Smale.ManifoldMorse.IsMorse E g →
                          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                            (Smale.ManifoldMorse.criticalPoints E g).ncard =
                                (Smale.ManifoldMorse.criticalPoints E f).ncard →
                              nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  classical
  obtain ⟨f₀, hf₀, hm₀, S₀, hminimal₀⟩ := exists_minimal_excellent_morse_system E M
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧
            (Smale.ManifoldMorse.criticalPoints E f).ncard =
                (Smale.ManifoldMorse.criticalPoints E f₀).ncard ∧
              nativeMorseCount E f 1 + nativeMorseCount E f 5 = n
  have hex : ∃ n, P n := ⟨_, f₀, hf₀, hm₀, S₀.distinct, rfl, rfl⟩
  obtain ⟨g, hg, hmg, hinjg, hcardg, hcostg⟩ := Nat.find_spec hex
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨f, hf, hm, hcrit, -, S, horder, hcounts⟩ :=
    exists_index_ordered_morse_system_preserving_critical_points T hg hmg
  have hcardf :
    (Smale.ManifoldMorse.criticalPoints E f).ncard =
      (Smale.ManifoldMorse.criticalPoints E f₀).ncard := by rw [hcrit, hcardg]
  have hminimal :
    ∀ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h →
        Smale.ManifoldMorse.IsMorse E h →
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) →
            (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
              (Smale.ManifoldMorse.criticalPoints E h).ncard := by
    intro h hh hmh hinjh
    rw [hcardf]
    exact hminimal₀ h hh hmh hinjh
  obtain ⟨hmin, hmax⟩ := minimal_excellent_morse_extreme_counts_one S hf hm hminimal
  refine ⟨f, hf, hm, S, horder, hmin, hmax, hminimal, ?_⟩
  intro h hh hmh hinjh hcardh
  rw [hcounts 1, hcounts 5, hcostg]
  exact Nat.find_min' hex ⟨h, hh, hmh, hinjh, hcardh.trans hcardf, rfl⟩

private theorem
    MorseCancel.outer_index_minimal_index_one_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 := by
  by_contra hnot
  have hfinite :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  obtain ⟨q, hqcrit, hq1⟩ := (Set.ncard_pos hfinite).mp (Nat.pos_of_ne_zero hnot)
  change
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard =
      1 at hzero
  obtain ⟨m, hmset⟩ := Set.ncard_eq_one.mp hzero
  have hmem :
    m ∈ {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} := by
    rw [hmset]
    exact Set.mem_singleton m
  let mc : Smale.ManifoldMorse.criticalPoints E f := ⟨m, hmem.1⟩
  have hminimum (z : Smale.ManifoldMorse.criticalPoints E f) (hz : nativeMorseIndex E f z = 0) :
    z = mc := by
    apply Subtype.ext
    have hzmem :
      z.val ∈ {x : M | x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = 0} :=
      ⟨z.property, hz⟩
    rwa [hmset, Set.mem_singleton_iff] at hzmem
  obtain ⟨g, hg, hmg, hinjg, hcount, hcount1, -, hother⟩ :=
    exists_one_to_three_handle_trade_of_ordered_indices S hf hm e hdim horder mc ⟨q, hqcrit⟩
      hmem.2 hq1 hminimum
  have hcost := hsecondary g hg hmg hinjg hcount
  have hcount5 := hother 5 (by omega) (by omega)
  omega

private theorem MorseCancel.outer_index_minimality_neg {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
        {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        Smale.ManifoldMorse.IsMorse E g →
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
            (Smale.ManifoldMorse.criticalPoints E g).ncard =
                (Smale.ManifoldMorse.criticalPoints E (fun x => -f x)).ncard →
              nativeMorseCount E (fun x => -f x) 1 + nativeMorseCount E (fun x => -f x) 5 ≤
                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  intro g hg hmg hinjg hcard
  have hh :=
    hsecondary (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
      (by simpa only [Smale.ManifoldMorse.criticalPoints_neg] using hcard)
  have hf1 := nativeMorseCount_neg hf hm (k := 1) (by omega)
  have hf5 := nativeMorseCount_neg hf hm (k := 5) (by omega)
  have hg1 := nativeMorseCount_neg hg hmg (k := 1) (by omega)
  have hg5 := nativeMorseCount_neg hg hmg (k := 5) (by omega)
  simp only [hdim, Nat.reduceSub] at hf1 hf5 hg1 hg5
  omega

private theorem
    MorseCancel.outer_index_minimal_outer_counts_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0 := by
  refine ⟨outer_index_minimal_index_one_count_zero S hf hm e hdim horder hzero hsecondary, ?_⟩
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have horderN :
    ∀ p q : Smale.ManifoldMorse.criticalPoints E (fun x => -f x),
      -f p < -f q → nativeMorseIndex E (fun x => -f x) p ≤ nativeMorseIndex E (fun x => -f x) q :=
    by
    intro p q hpq
    let pf : Smale.ManifoldMorse.criticalPoints E f :=
      ⟨p.val, by simpa only [Smale.ManifoldMorse.criticalPoints_neg] using p.property⟩
    let qf : Smale.ManifoldMorse.criticalPoints E f :=
      ⟨q.val, by simpa only [Smale.ManifoldMorse.criticalPoints_neg] using q.property⟩
    have hrev := horder qf pf (neg_lt_neg_iff.mp hpq)
    have hp := nativeMorseIndex_neg_add (S.data pf).chart
    have hq := nativeMorseIndex_neg_add (S.data qf).chart
    change nativeMorseIndex E f q.val ≤ nativeMorseIndex E f p.val at hrev
    change nativeMorseIndex E (fun x => -f x) p.val + nativeMorseIndex E f p.val = _ at hp
    change nativeMorseIndex E (fun x => -f x) q.val + nativeMorseIndex E f q.val = _ at hq
    omega
  have hzeroN : nativeMorseCount E (fun x => -f x) 0 = 1 := by
    have hc := nativeMorseCount_neg hf hm (k := 6) (by omega)
    simpa only [hdim, Nat.sub_self, hsix] using hc
  have honeN :=
    outer_index_minimal_index_one_count_zero T hf.neg (isMorse_neg hm) e hdim horderN hzeroN
      (outer_index_minimality_neg hf hm hdim hsecondary)
  have hc := nativeMorseCount_neg hf hm (k := 5) (by omega)
  simpa only [hdim, Nat.reduceSub, honeN] using hc.symm

private theorem MorseCancel.exists_minimal_ordered_morse_system_without_outer_indices (E : Type)
    (M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] (e : M ≃ₕ Smale.SixSphere) (hdim : Module.finrank ℝ E = 6) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f 6 = 1 ∧
                  nativeMorseCount E f 1 = 0 ∧
                    nativeMorseCount E f 5 = 0 ∧
                      ∀ g : M → ℝ,
                        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                          Smale.ManifoldMorse.IsMorse E g →
                            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                                (Smale.ManifoldMorse.criticalPoints E g).ncard := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hminimal, hsecondary⟩ :=
    exists_outer_index_minimal_ordered_morse_system E M
  rw [hdim] at hsix
  obtain ⟨hone, hfive⟩ :=
    outer_index_minimal_outer_counts_zero S hf hm e hdim horder hzero hsix hsecondary
  exact ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩

private def Smale.DiskOnePointCollapse.boundary {N : Type*} [NormedAddCommGroup N] :
    Set (Smale.MorseHandle.UnitDisk N) :=
  {z | ‖(z : N)‖ = 1}

private theorem Smale.DiskOnePointCollapse.boundary_closed {N : Type*} [NormedAddCommGroup N] :
    IsClosed (boundary (N := N)) :=
  isClosed_eq continuous_subtype_val.norm continuous_const

private theorem Smale.DiskOnePointCollapse.not_mem_boundary_iff {N : Type*} [NormedAddCommGroup N]
    (z : Smale.MorseHandle.UnitDisk N) : z ∉ boundary ↔ ‖(z : N)‖ < 1 := by
  change ‖(z : N)‖ ≠ 1 ↔ ‖(z : N)‖ < 1
  constructor
  · exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.property)
  · exact ne_of_lt

private def Smale.DiskOnePointCollapse.interiorHomeomorph {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : ↥(boundary (N := N))ᶜ ≃ₜ N :=
  (Homeomorph.setCongr (by ext z; exact not_mem_boundary_iff z)).trans
    (Smale.DiskAnnulus.openDiskHomeomorph.trans Homeomorph.unitBall.symm)

private def
    Smale.DiskOnePointCollapse.collapse {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    C(Smale.MorseHandle.UnitDisk N, OnePoint N) :=
  ⟨fun z => interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary z),
    interiorHomeomorph.onePointCongr.continuous.comp
      (SixSphereCube.continuous_collapse boundary boundary_closed)⟩

private theorem Smale.DiskOnePointCollapse.collapse_boundary {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) (hz : ‖(z : N)‖ = 1) :
    collapse z = (OnePoint.infty) := by
  change interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary z) = (OnePoint.infty)
  rw [SixSphereCube.collapse_of_mem boundary hz]
  rfl

private theorem Smale.DiskOnePointCollapse.collapse_interior {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) (hz : ‖(z : N)‖ < 1) :
    collapse z = ((OpenPartialHomeomorph.univUnitBall.symm (z : N) : N) : OnePoint N) := by
  change interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary z) = _
  rw [SixSphereCube.collapse_of_not_mem boundary ((not_mem_boundary_iff z).mpr hz)]
  rfl

private theorem Smale.DiskOnePointCollapse.collapse_eq_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z w : Smale.MorseHandle.UnitDisk N) :
    collapse z = collapse w ↔ z = w ∨ ‖(z : N)‖ = 1 ∧ ‖(w : N)‖ = 1 := by
  change
    interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary z) =
        interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary w) ↔
      _
  rw [interiorHomeomorph.onePointCongr.injective.eq_iff, SixSphereCube.collapse_eq_iff]
  rfl

private def Smale.DiskOnePointCollapse.compress {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (x : N) : Smale.MorseHandle.UnitDisk N :=
  ⟨Homeomorph.unitBall x, Metric.ball_subset_closedBall (Homeomorph.unitBall x).property⟩

private theorem Smale.DiskOnePointCollapse.norm_compress_lt {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (x : N) : ‖(compress x : N)‖ < 1 :=
  mem_ball_zero_iff.mp (Homeomorph.unitBall x).property

private theorem Smale.DiskOnePointCollapse.compress_zero {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : (compress (0 : N) : N) = 0 :=
  Homeomorph.coe_unitBall_apply_zero

private theorem Smale.DiskOnePointCollapse.collapse_compress {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (x : N) : collapse (compress x) = (x : OnePoint N) := by
  rw [collapse_interior _ (norm_compress_lt x)]
  exact
    congrArg (fun y : N => (y : OnePoint N))
      (OpenPartialHomeomorph.univUnitBall.left_inv (Set.mem_univ x))

private theorem Smale.DiskOnePointCollapse.collapse_eq_coe_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) (x : N) :
    collapse z = (x : OnePoint N) ↔ z = compress x := by
  rw [← collapse_compress x, collapse_eq_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact ((ne_of_lt (norm_compress_lt x)) h.2).elim
  · exact Or.inl

private theorem Smale.DiskOnePointCollapse.collapse_eq_zero_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) :
    collapse z = ((0 : N) : OnePoint N) ↔ (z : N) = 0 := by
  rw [collapse_eq_coe_iff]
  constructor
  · intro hz
    exact (congrArg Subtype.val hz).trans compress_zero
  · intro hz
    exact Subtype.ext (hz.trans compress_zero.symm)

private theorem Smale.DiskOnePointCollapse.collapse_eq_infty_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) :
    collapse z = (OnePoint.infty) ↔ ‖(z : N)‖ = 1 := by
  by_cases hz : ‖(z : N)‖ = 1
  · rw [collapse_boundary z hz]
    exact iff_of_true rfl hz
  · rw [collapse_interior z ((not_mem_boundary_iff z).mp hz)]
    exact iff_of_false (OnePoint.coe_ne_infty _) hz

private theorem Smale.ClosedHandleCore.collapseMaps_agree {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) (a : A)
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P)
    (haz : oldInclusion A h a = handleInclusion A h z) :
    ((OnePoint.infty) : OnePoint N) = Smale.DiskOnePointCollapse.collapse z.1 := by
  have heq : (a : X) = h z := congrArg Subtype.val haz
  have hz := (hface z).mp (heq ▸ a.property)
  exact (Smale.DiskOnePointCollapse.collapse_boundary z.1 hz).symm

private def
    Smale.ClosedHandleCore.collapseMap {N P X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) :
    C(↥(A ∪ Set.range h), OnePoint N) :=
  Smale.ClosedCover.mapOfClosedPieces (oldInclusion A h) (handleInclusion A h) (old_closed A h hA)
    (handle_closed A h hh) (pieces_cover A h) (ContinuousMap.const A (OnePoint.infty))
    (Smale.DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface)

private theorem Smale.ClosedHandleCore.collapseMap_old {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) (a : A) :
    collapseMap A h hA hh hface (oldInclusion A h a) = (OnePoint.infty) :=
  Smale.ClosedCover.mapOfClosedPieces_left (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A (OnePoint.infty))
    (Smale.DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface) a

private theorem Smale.ClosedHandleCore.collapseMap_handle {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1)
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    collapseMap A h hA hh hface (handleInclusion A h z) =
      Smale.DiskOnePointCollapse.collapse z.1 :=
  Smale.ClosedCover.mapOfClosedPieces_right (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A (OnePoint.infty))
    (Smale.DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface) z

private theorem
    Smale.EmbeddedCellAttachment.collapse_piece_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Set.range (Subtype.val : D.old → X) ∪ Set.range D.cell = Set.univ := by
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using D.cover

private theorem Smale.EmbeddedCellAttachment.collapseMaps_agree {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (a : D.old)
    (z : Smale.MorseHandle.UnitDisk N) (haz : (a : X) = D.cell z) :
    ((OnePoint.infty) : OnePoint N) = Smale.DiskOnePointCollapse.collapse z :=
  (Smale.DiskOnePointCollapse.collapse_boundary z ((D.boundary z).mp (haz ▸ a.property))).symm

private def Smale.EmbeddedCellAttachment.collapseMap {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C(X, OnePoint N) :=
  Smale.ClosedCover.mapOfClosedPieces Subtype.val D.cell D.old_closed.isClosedEmbedding_subtypeVal
    D.cell_closed D.collapse_piece_cover (ContinuousMap.const D.old (OnePoint.infty))
    Smale.DiskOnePointCollapse.collapse D.collapseMaps_agree

private theorem Smale.EmbeddedCellAttachment.collapseMap_old {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (a : D.old) :
    D.collapseMap a = (OnePoint.infty) :=
  Smale.ClosedCover.mapOfClosedPieces_left Subtype.val D.cell
    D.old_closed.isClosedEmbedding_subtypeVal D.cell_closed D.collapse_piece_cover
    (ContinuousMap.const D.old (OnePoint.infty)) Smale.DiskOnePointCollapse.collapse
    D.collapseMaps_agree a

private theorem Smale.EmbeddedCellAttachment.collapseMap_cell {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (z : Smale.MorseHandle.UnitDisk N) :
    D.collapseMap (D.cell z) = Smale.DiskOnePointCollapse.collapse z :=
  Smale.ClosedCover.mapOfClosedPieces_right Subtype.val D.cell
    D.old_closed.isClosedEmbedding_subtypeVal D.cell_closed D.collapse_piece_cover
    (ContinuousMap.const D.old (OnePoint.infty)) Smale.DiskOnePointCollapse.collapse
    D.collapseMaps_agree z

private theorem
    Smale.EmbeddedCellAttachment.collapseMap_infty_iff {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (x : X) :
    D.collapseMap x = (OnePoint.infty) ↔ x ∈ D.old := by
  have hx : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · exact iff_of_true (D.collapseMap_old ⟨x, hx⟩) hx
  · rw [D.collapseMap_cell, Smale.DiskOnePointCollapse.collapse_eq_infty_iff, D.boundary]

private def Smale.OnePointCover.oldPatch {N : Type*} [NormedAddCommGroup N] : Set (OnePoint N) :=
  {((0 : N) : OnePoint N)}ᶜ

private def Smale.OnePointCover.finitePatch {N : Type*} : Set (OnePoint N) :=
  { OnePoint.infty }ᶜ

private theorem Smale.OnePointCover.cover {N : Type*} [NormedAddCommGroup N] :
    oldPatch (N := N) ∪ finitePatch = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = ((0 : N) : OnePoint N)
  · right
    subst x
    exact OnePoint.coe_ne_infty 0
  · exact Or.inl hx

private theorem Smale.OnePointCover.oldPatch_open {N : Type*} [NormedAddCommGroup N] :
    IsOpen (oldPatch (N := N)) :=
  isClosed_singleton.isOpen_compl

private theorem Smale.OnePointCover.finitePatch_open {N : Type*} [NormedAddCommGroup N] :
    IsOpen (finitePatch (N := N)) :=
  isClosed_singleton.isOpen_compl

private theorem Smale.OnePointCover.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] Smale.OnePointCover.instLocal1 in
private def Smale.OnePointCover.spherePunctureHomeomorph_mo1973_5327 (n : ℕ)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ↥({ a }ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) a).symm).trans
    ((stereographic' n a).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target a)).trans (Homeomorph.Set.univ _)))

attribute [local instance] Smale.OnePointCover.instLocal1 in
private def
    Smale.OnePointCover.punctureHomeomorph {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (a : OnePoint N) :
    ↥({ a }ᶜ : Set (OnePoint N)) ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ N)) := by
  let e : OnePoint N ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ N + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let es : ↥({ a }ᶜ : Set (OnePoint N)) ≃ₜ ↥({e a}ᶜ : Set _) :=
    e.subtype
      (fun x => by
        change x ≠ a ↔ e x ≠ e a
        exact e.injective.ne_iff.symm)
  exact es.trans (spherePunctureHomeomorph_mo1973_5327 _ (e a))

attribute [local instance] Smale.OnePointCover.instLocal1 in
private theorem Smale.OnePointCover.oldPatch_contractible {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] : ContractibleSpace (oldPatch (N := N)) :=
  (punctureHomeomorph ((0 : N) : OnePoint N)).contractibleSpace

attribute [local instance] Smale.OnePointCover.instLocal1 in
private theorem Smale.OnePointCover.finitePatch_contractible {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] : ContractibleSpace (finitePatch (N := N)) :=
  (punctureHomeomorph (OnePoint.infty : OnePoint N)).contractibleSpace

attribute [local instance] Smale.OnePointCover.instLocal1 in
private theorem Smale.OnePointCover.overlap_subset_range {N : Type*} [NormedAddCommGroup N] :
    oldPatch (N := N) ∩ finitePatch ⊆ Set.range (OnePoint.some : N → _) := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact (hx.2 rfl).elim
  | coe x => exact ⟨x, rfl⟩

attribute [local instance] Smale.OnePointCover.instLocal1 in
private theorem Smale.OnePointCover.overlap_preimage {N : Type*} [NormedAddCommGroup N] :
    (OnePoint.some : N → OnePoint N) ⁻¹' (oldPatch ∩ finitePatch) = {u : N | u ≠ 0} := by
  ext x
  change ((x : OnePoint N) ≠ ((0 : N) : OnePoint N) ∧ (x : OnePoint N) ≠ OnePoint.infty) ↔ x ≠ 0
  constructor
  · rintro ⟨h, -⟩ hx
    exact h (congrArg (OnePoint.some : N → OnePoint N) hx)
  · intro hx
    exact ⟨fun h => hx (OnePoint.coe_injective h), OnePoint.coe_ne_infty x⟩

attribute [local instance] Smale.OnePointCover.instLocal1 in
private def Smale.OnePointCover.overlapHomeomorph {N : Type*} [NormedAddCommGroup N] :
    Smale.PuncturedRadial.Space N ≃ₜ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (Homeomorph.setCongr overlap_preimage.symm).trans
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphOfSubsetRange overlap_subset_range)

attribute [local instance] Smale.OnePointCover.instLocal1 in
private theorem Smale.OnePointCover.overlapHomeomorph_apply {N : Type*} [NormedAddCommGroup N]
    (u : Smale.PuncturedRadial.Space N) : (overlapHomeomorph u).val = (u.val : OnePoint N) :=
  rfl

attribute [local instance] Smale.OnePointCover.instLocal1 in
private def
    Smale.OnePointCover.overlapSphereEquiv {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) : Metric.sphere (0 : N) 1 ≃ₕ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (Smale.PuncturedRadial.sphereHomotopyEquiv r hr).trans overlapHomeomorph.toHomotopyEquiv

private def Smale.CoverNaturality.mapOn {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x.val, hf x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem Smale.CoverNaturality.chainMap_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    FirstHurewicz.singularChainMap f ≫ FirstHurewicz.singularChainMap g =
      FirstHurewicz.singularChainMap (g.comp f) :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g)).symm

public
theorem Smale.CoverNaturality.map_intersection {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') : Set.MapsTo f (U ∩ V) (U' ∩ V') := fun _ hx => ⟨hU hx.1, hV hx.2⟩

private theorem Smale.CoverNaturality.inducedChain_mem_small {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') (n : ℕ) (c : FirstHurewicz.Chains X n)
    (hc : c ∈ SingularMayerVietoris.smallChainSubmodule U V n) :
    FirstHurewicz.inducedChain f n c ∈ SingularMayerVietoris.smallChainSubmodule U' V' n := by
  have hle :
    SingularMayerVietoris.smallChainSubmodule U V n ≤
      (SingularMayerVietoris.smallChainSubmodule U' V' n).comap
        (FirstHurewicz.inducedChain f n) := by
    rw [SingularMayerVietoris.smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change
      FirstHurewicz.inducedChain f n (FirstHurewicz.simplexChain X n σ) ∈
        SingularMayerVietoris.smallChainSubmodule U' V' n
    rw [FirstHurewicz.inducedChain_simplex]
    apply SingularMayerVietoris.simplexChain_mem_small
    rcases hσ with hσ | hσ
    · left
      rintro _ ⟨t, rfl⟩
      exact hU (hσ ⟨t, rfl⟩)
    · right
      rintro _ ⟨t, rfl⟩
      exact hV (hσ ⟨t, rfl⟩)
  exact hle hc

private def Smale.CoverNaturality.smallMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularMayerVietoris.smallComplex U V ⟶ SingularMayerVietoris.smallComplex U' V' :=
  SingularMayerVietoris.liftToSmall U' V'
    (SingularMayerVietoris.smallInclusion U V ≫ FirstHurewicz.singularChainMap f)
    (fun n c => inducedChain_mem_small U V U' V' f hU hV n c.val c.property)

private theorem Smale.CoverNaturality.smallMap_inclusion {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    smallMap U V U' V' f hU hV ≫ SingularMayerVietoris.smallInclusion U' V' =
      SingularMayerVietoris.smallInclusion U V ≫ FirstHurewicz.singularChainMap f :=
  SingularMayerVietoris.liftToSmall_inclusion U' V' _ _

private theorem
    Smale.CoverNaturality.smallMap_left {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularMayerVietoris.toSmallLeft U V ≫ smallMap U V U' V' f hU hV =
      FirstHurewicz.singularChainMap (mapOn f U U' hU) ≫
        SingularMayerVietoris.toSmallLeft U' V' := by
  apply (CategoryTheory.cancel_mono (SingularMayerVietoris.smallInclusion U' V')).mp
  rw [CategoryTheory.Category.assoc, smallMap_inclusion, ← CategoryTheory.Category.assoc,
    SingularMayerVietoris.toSmallLeft_inclusion, CategoryTheory.Category.assoc,
    SingularMayerVietoris.toSmallLeft_inclusion, chainMap_comp, chainMap_comp]
  rfl

private theorem Smale.CoverNaturality.smallMap_right {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularMayerVietoris.toSmallRight U V ≫ smallMap U V U' V' f hU hV =
      FirstHurewicz.singularChainMap (mapOn f V V' hV) ≫
        SingularMayerVietoris.toSmallRight U' V' := by
  apply (CategoryTheory.cancel_mono (SingularMayerVietoris.smallInclusion U' V')).mp
  rw [CategoryTheory.Category.assoc, smallMap_inclusion, ← CategoryTheory.Category.assoc,
    SingularMayerVietoris.toSmallRight_inclusion, CategoryTheory.Category.assoc,
    SingularMayerVietoris.toSmallRight_inclusion, chainMap_comp, chainMap_comp]
  rfl

private theorem Smale.CoverNaturality.intersection_left {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    FirstHurewicz.singularChainMap
          (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) ≫
        SingularMayerVietoris.intersectionToLeft U' V' =
      SingularMayerVietoris.intersectionToLeft U V ≫
        FirstHurewicz.singularChainMap (mapOn f U U' hU) := by
  unfold SingularMayerVietoris.intersectionToLeft
  rw [chainMap_comp, chainMap_comp]
  rfl

private theorem Smale.CoverNaturality.intersection_right {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    FirstHurewicz.singularChainMap
          (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) ≫
        SingularMayerVietoris.intersectionToRight U' V' =
      SingularMayerVietoris.intersectionToRight U V ≫
        FirstHurewicz.singularChainMap (mapOn f V V' hV) := by
  unfold SingularMayerVietoris.intersectionToRight
  rw [chainMap_comp, chainMap_comp]
  rfl

private def
    Smale.CoverNaturality.chainSequenceMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularMayerVietoris.chainSequence U V ⟶ SingularMayerVietoris.chainSequence U' V'
    where
  τ₁ :=
    FirstHurewicz.singularChainMap
      (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV))
  τ₂ :=
    CategoryTheory.Limits.biprod.map (FirstHurewicz.singularChainMap (mapOn f U U' hU))
      (FirstHurewicz.singularChainMap (mapOn f V V' hV))
  τ₃ := smallMap U V U' V' f hU hV
  comm₁₂ := by
    dsimp only [SingularMayerVietoris.chainSequence, SingularMayerVietoris.leftMap,
      SingularMayerVietoris.middleComplex]
    apply CategoryTheory.Limits.biprod.hom_ext
    · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_fst,
        CategoryTheory.Limits.biprod.map_fst, CategoryTheory.Limits.biprod.lift_fst_assoc]
      exact intersection_left U V U' V' f hU hV
    · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_snd,
        CategoryTheory.Limits.biprod.map_snd, CategoryTheory.Limits.biprod.lift_snd_assoc,
        CategoryTheory.Preadditive.comp_neg, CategoryTheory.Preadditive.neg_comp]
      exact congrArg Neg.neg (intersection_right U V U' V' f hU hV)
  comm₂₃ := by
    dsimp only [SingularMayerVietoris.chainSequence, SingularMayerVietoris.rightMap,
      SingularMayerVietoris.middleComplex]
    apply CategoryTheory.Limits.biprod.hom_ext'
    · simp only [CategoryTheory.Limits.biprod.inl_map_assoc,
        CategoryTheory.Limits.biprod.inl_desc, CategoryTheory.Limits.biprod.inl_desc_assoc]
      exact (smallMap_left U V U' V' f hU hV).symm
    · simp only [CategoryTheory.Limits.biprod.inr_map_assoc,
        CategoryTheory.Limits.biprod.inr_desc, CategoryTheory.Limits.biprod.inr_desc_assoc]
      exact (smallMap_right U V U' V' f hU hV).symm

private theorem Smale.CoverNaturality.smallConnecting_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap
            (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) n).comp
        (SingularMayerVietoris.smallConnectingMap U V n) =
      (SingularMayerVietoris.smallConnectingMap U' V' n).comp
        (SingularMayerVietoris.homologyLinearMap (smallMap U V U' V' f hU hV) (n + 1)) :=
  SingularMayerVietoris.connectingMap_naturality
    (SingularMayerVietoris.chainSequence_shortExact U V) (chainSequenceMap U V U' V' f hU hV)
    (SingularMayerVietoris.chainSequence_shortExact U' V') n

private theorem Smale.CoverNaturality.comparison_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') (n : ℕ) :
    (SingularMayerVietoris.smallHomologyComparison U' V' n).comp
        (SingularMayerVietoris.homologyLinearMap (smallMap U V U' V' f hU hV) n) =
      (SingularMayerVietoris.singularHomologyMap f n).comp
        (SingularMayerVietoris.smallHomologyComparison U V n) := by
  unfold SingularMayerVietoris.smallHomologyComparison
  rw [← SingularMayerVietoris.homologyLinearMap_comp, smallMap_inclusion,
    SingularMayerVietoris.homologyLinearMap_comp]

private theorem Smale.CoverNaturality.connecting_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap
            (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hfU hfV)) n).comp
        (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n) =
      (SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' n).comp
        (SingularMayerVietoris.singularHomologyMap f (n + 1)) := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, hb⟩ := (SingularMayerVietoris.smallHomologyEquiv U V hU hV hc (n + 1)).surjective a
  have hb' : SingularMayerVietoris.smallHomologyComparison U V (n + 1) b = a := hb
  rw [← hb']
  change
    SingularMayerVietoris.singularHomologyMap _ n
        (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n
          (SingularMayerVietoris.smallHomologyComparison U V (n + 1) b)) =
      SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' n
        (SingularMayerVietoris.singularHomologyMap f (n + 1)
          (SingularMayerVietoris.smallHomologyComparison U V (n + 1) b))
  rw [SingularMayerVietoris.connectingHomomorphism_comparison]
  have hcomp := LinearMap.congr_fun (comparison_naturality U V U' V' f hfU hfV (n + 1)) b
  change
    SingularMayerVietoris.smallHomologyComparison U' V' (n + 1)
        (SingularMayerVietoris.homologyLinearMap (smallMap U V U' V' f hfU hfV) (n + 1) b) =
      SingularMayerVietoris.singularHomologyMap f (n + 1)
        (SingularMayerVietoris.smallHomologyComparison U V (n + 1) b) at hcomp
  rw [← hcomp, SingularMayerVietoris.connectingHomomorphism_comparison]
  exact LinearMap.congr_fun (smallConnecting_naturality U V U' V' f hfU hfV n) b

private theorem Smale.CoverNaturality.connecting_naturality_apply {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.singularHomologyMap
        (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hfU hfV)) n
        (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n a) =
      SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' n
        (SingularMayerVietoris.singularHomologyMap f (n + 1) a) :=
  LinearMap.congr_fun (connecting_naturality U V U' V' f hfU hfV hU hV hc hU' hV' hc' n) a

private def Smale.OnePointCover.overlapRadius : ℝ :=
  (Real.sqrt (1 - (3 / 4 : ℝ) ^ 2))⁻¹ * (3 / 4)

private theorem Smale.OnePointCover.overlapRadius_pos : 0 < overlapRadius := by
  have h : 0 < 1 - (3 / 4 : ℝ) ^ 2 := by norm_num
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr h)) (by norm_num)

private theorem
    Smale.EmbeddedCellAttachment.collapseMap_eq_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (x : X) :
    D.collapseMap x = ((0 : N) : OnePoint N) ↔ D.cell ⟨0, by simp⟩ = x := by
  have hx : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · rw [D.collapseMap_old ⟨x, hx⟩]
    constructor
    · intro h
      exact (OnePoint.infty_ne_coe (0 : N) h).elim
    · intro h
      rw [← h, D.boundary] at hx
      simp at hx
  · rw [D.collapseMap_cell, Smale.DiskOnePointCollapse.collapse_eq_zero_iff]
    constructor
    · intro hz
      exact congrArg D.cell (Subtype.ext hz.symm)
    · intro hz
      exact (congrArg Subtype.val (D.cell_closed.injective hz)).symm

private theorem Smale.EmbeddedCellAttachment.collapseMaps_oldNeighborhood {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) :
    Set.MapsTo D.collapseMap D.oldNeighborhood (Smale.OnePointCover.oldPatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ ((0 : N) : OnePoint N)
  intro h
  have heq := (D.collapseMap_eq_zero_iff x).mp h
  rw [← heq, D.cell_mem_oldNeighborhood_iff] at hx
  norm_num at hx

private theorem
    Smale.EmbeddedCellAttachment.collapseMaps_diskPatch {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Set.MapsTo D.collapseMap D.diskPatch (Smale.OnePointCover.finitePatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ OnePoint.infty
  exact fun h => hx ((D.collapseMap_infty_iff x).mp h)

private def Smale.EmbeddedCellAttachment.collapseOverlapMap {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C(↥(D.oldNeighborhood ∩ D.diskPatch),
      ↥(Smale.OnePointCover.oldPatch (N := N) ∩ Smale.OnePointCover.finitePatch)) :=
  Smale.CoverNaturality.mapOn D.collapseMap _ _
    (Smale.CoverNaturality.map_intersection _ _ _ _ D.collapseMap D.collapseMaps_oldNeighborhood
      D.collapseMaps_diskPatch)

private theorem
    Smale.EmbeddedCellAttachment.collapseOverlap_sphere {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (u : Metric.sphere (0 : N) 1) :
    D.collapseOverlapMap (D.overlapSphereEquiv u) =
      Smale.OnePointCover.overlapSphereEquiv Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos u := by
  apply Subtype.ext
  change
    D.collapseMap (D.cell (Smale.DiskAnnulus.middleDisk u)) =
      ((Smale.OnePointCover.overlapRadius • (u : N) : N) : OnePoint N)
  rw [D.collapseMap_cell,
    Smale.DiskOnePointCollapse.collapse_interior _ (Smale.DiskAnnulus.middleDisk_mem u).2]
  apply congrArg (OnePoint.some : N → OnePoint N)
  change
    (Real.sqrt (1 - ‖(3 / 4 : ℝ) • (u : N)‖ ^ 2))⁻¹ • ((3 / 4 : ℝ) • (u : N)) =
      Smale.OnePointCover.overlapRadius • (u : N)
  rw [Smale.DiskAnnulus.norm_middle, smul_smul]
  rfl

private theorem Smale.EmbeddedCellAttachment.collapseOverlap_comp_sphere {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) :
    D.collapseOverlapMap.comp D.overlapSphereEquiv.toFun =
      (Smale.OnePointCover.overlapSphereEquiv (N := N) Smale.OnePointCover.overlapRadius
          Smale.OnePointCover.overlapRadius_pos).toFun :=
  ContinuousMap.ext D.collapseOverlap_sphere

private def
    Smale.OnePointCover.overlapHomologyEquiv {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (↥(oldPatch (N := N) ∩ finitePatch)) k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k

private def Smale.OnePointCover.sphereConnecting {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k :=
  (overlapHomologyEquiv r hr k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism oldPatch finitePatch oldPatch_open
      finitePatch_open cover k)

private theorem Smale.OnePointCover.sphereConnecting_injective {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Function.Injective (sphereConnecting (N := N) r hr k) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  have hi :
    Function.Injective
      (SingularMayerVietoris.connectingHomomorphism (oldPatch (N := N)) finitePatch oldPatch_open
        finitePatch_open cover k) :=
    CuspCentralHomology.contractibleCoverConnecting_injective (oldPatch (N := N)) finitePatch
      oldPatch_open finitePatch_open cover k
  exact (overlapHomologyEquiv (N := N) r hr k).symm.injective.comp hi

private def
    Smale.OnePointCover.sphereHomologyEquiv {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) (k + 1) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  exact
    (CuspCentralHomology.contractibleCoverHomologyHigherEquiv oldPatch finitePatch oldPatch_open
          finitePatch_open cover k).trans
      (overlapHomologyEquiv r hr (k + 1)).symm

private theorem Smale.EmbeddedCellAttachment.collapse_overlapHomology_compare {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.singularHomologyMap D.collapseOverlapMap k
        (D.overlapHomologyEquiv k a) =
      Smale.OnePointCover.overlapHomologyEquiv Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k a := by
  change
    SingularMayerVietoris.singularHomologyMap D.collapseOverlapMap k
        (SingularMayerVietoris.singularHomologyMap D.overlapSphereEquiv.toFun k a) =
      SingularMayerVietoris.singularHomologyMap _ k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    D.collapseOverlap_comp_sphere]

private theorem Smale.EmbeddedCellAttachment.collapse_connecting_compare {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    Smale.OnePointCover.sphereConnecting Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap D.collapseMap (k + 1) a) =
      D.cellConnectingMap k a := by
  apply
    (Smale.OnePointCover.overlapHomologyEquiv (N := N) Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k).injective
  change
    Smale.OnePointCover.overlapHomologyEquiv _ _ k
        ((Smale.OnePointCover.overlapHomologyEquiv _ _ k).symm _) =
      Smale.OnePointCover.overlapHomologyEquiv _ _ k ((D.overlapHomologyEquiv k).symm _)
  rw [LinearEquiv.apply_symm_apply, ← D.collapse_overlapHomology_compare,
    LinearEquiv.apply_symm_apply]
  exact
    (Smale.CoverNaturality.connecting_naturality_apply D.oldNeighborhood D.diskPatch
        Smale.OnePointCover.oldPatch Smale.OnePointCover.finitePatch D.collapseMap
        D.collapseMaps_oldNeighborhood D.collapseMaps_diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover Smale.OnePointCover.oldPatch_open
        Smale.OnePointCover.finitePatch_open Smale.OnePointCover.cover k a).symm

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.attachmentCollapseMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C(↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap),
      OnePoint d.chart.NegativeCoordinates) :=
  Smale.ClosedHandleCore.collapseMap _ d.handleMap (isClosed_le hf continuous_const)
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.upperCollapseMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C({ y : M // f y ≤ f p + d.radius ^ 2 }, OnePoint d.chart.NegativeCoordinates) :=
  (d.attachmentCollapseMap hf).comp d.attachmentHomeomorph.symm.toHomotopyEquiv.toFun

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_realization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap)) :
    d.upperCollapseMap hf (d.attachmentHomeomorph x) = d.attachmentCollapseMap hf x := by
  change d.attachmentCollapseMap hf (d.attachmentHomeomorph.symm (d.attachmentHomeomorph x)) = _
  exact congrArg (d.attachmentCollapseMap hf) (d.attachmentHomeomorph.symm_apply_apply x)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_old {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : { y : M // f y ≤ f p - d.radius ^ 2 }) :
    d.upperCollapseMap hf (d.realizedLowerInclusion x) = (OnePoint.infty) := by
  change
    d.upperCollapseMap hf
        (d.attachmentHomeomorph (Smale.ClosedHandleCore.oldInclusion _ d.handleMap x)) =
      (OnePoint.infty)
  rw [d.upperCollapse_realization]
  exact Smale.ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ x

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_handle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (z : d.HandleDomain) :
    d.upperCollapseMap hf (d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩) =
      Smale.DiskOnePointCollapse.collapse z.1 := by
  exact
    (d.upperCollapse_realization hf
          (Smale.ClosedHandleCore.handleInclusion _ d.handleMap z)).trans
      (Smale.ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _ z)

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.levelCollapseMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C(d.UpperLevel, OnePoint d.chart.NegativeCoordinates) :=
  (d.upperCollapseMap hf).comp ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_realized {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (y : d.UpperLevel) (x : ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap))
    (hy : (y : M) = (d.attachmentHomeomorph x).val) :
    d.levelCollapseMap hf y = d.attachmentCollapseMap hf x := by
  change d.upperCollapseMap hf ⟨y.val, y.property.le⟩ = _
  have heq :
    (⟨y.val, y.property.le⟩ : { z : M // f z ≤ f p + d.radius ^ 2 }) = d.attachmentHomeomorph x :=
    Subtype.ext hy
  rw [heq, d.upperCollapse_realization]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_newExterior {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (r) :
    d.levelCollapseMap hf (d.surgery.newExterior r) = (OnePoint.infty) := by
  rw [d.levelCollapse_realized hf _ _ (d.newExterior_eq r)]
  exact Smale.ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ ⟨r.val, r.property.1.le⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_newPiece {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.surgery.newPiece z) =
      Smale.DiskOnePointCollapse.collapse
        (Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1) := by
  rw [d.levelCollapse_realized hf _ _ (d.newPiece_eq z)]
  exact
    Smale.ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _
      (d.chart.handleBallCoordinates (z.1, Smale.PuncturedHandle.sphereToBall z.2))

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_zero_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : d.UpperLevel) :
    d.levelCollapseMap hf x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ Set.range d.surgery.beltSphere := by
  have hx : x ∈ Set.range d.surgery.newExterior ∪ Set.range d.surgery.newPiece := by
    rw [d.surgery.new_cover]
    trivial
  rcases hx with ⟨r, rfl⟩ | ⟨z, rfl⟩
  · rw [d.levelCollapse_newExterior]
    exact iff_of_false (OnePoint.infty_ne_coe _) (d.surgery.newExterior_avoids r)
  · rw [d.levelCollapse_newPiece, Smale.DiskOnePointCollapse.collapse_eq_zero_iff,
      d.surgery.newPiece_mem_belt_iff]
    rfl

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_coreCell {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    (d.upperCollapseMap hf).comp (d.coreUnionHomotopyEquiv hf).toFun =
      (d.coreCellPresentation hf).collapseMap := by
  apply ContinuousMap.ext
  rintro ⟨x, hx | ⟨u, rfl⟩⟩
  · exact
      (d.upperCollapse_old hf ⟨x, hx⟩).trans
        ((d.coreCellPresentation hf).collapseMap_old ⟨⟨x, Or.inl hx⟩, hx⟩).symm
  · change
      d.upperCollapseMap hf
          (d.attachmentHomeomorph ⟨d.handleMap (u, ⟨0, by simp⟩), Or.inr ⟨_, rfl⟩⟩) =
        (d.coreCellPresentation hf).collapseMap ((d.coreCellPresentation hf).cell u)
    rw [d.upperCollapse_handle, (d.coreCellPresentation hf).collapseMap_cell]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapseHomology_coreCell {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap)) k) :
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) k
        (d.cellTotalHomologyEquiv hf k a) =
      SingularMayerVietoris.singularHomologyMap (d.coreCellPresentation hf).collapseMap k a := by
  change
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) k
        (SingularMayerVietoris.singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    d.upperCollapse_coreCell]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_connecting_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 1)) :
    Smale.OnePointCover.sphereConnecting Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1) a) =
      d.morseConnectingMap hf k a := by
  obtain ⟨b, rfl⟩ := (d.cellTotalHomologyEquiv hf (k + 1)).surjective a
  rw [d.upperCollapseHomology_coreCell, (d.coreCellPresentation hf).collapse_connecting_compare,
    d.morseConnecting_compare]

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_homology_equiv_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 2)) :
    Smale.OnePointCover.sphereHomologyEquiv Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 2) a) =
      d.morseConnectingMap hf (k + 1) a :=
  d.upperCollapse_connecting_compare hf (k + 1) a

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_homology_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1)) =
      LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) := by
  rw [d.morse_exact_at_upper hf k]
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1) a = 0 ↔
      d.morseConnectingMap hf k a = 0
  rw [← d.upperCollapse_connecting_compare]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact
      (Smale.OnePointCover.sphereConnecting_injective Smale.OnePointCover.overlapRadius
          Smale.OnePointCover.overlapRadius_pos k)
        (h.trans (map_zero _).symm)

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.morseConnecting_surjective_of_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k)] :
    Function.Surjective (d.morseConnectingMap hf k) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.coreBoundaryHomologyMap k) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_attachingSphere hf k hk] at ha
  exact ha

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_surjective_of_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } (k + 1))] :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 2)) := by
  intro a
  let C :=
    Smale.OnePointCover.sphereHomologyEquiv (N := d.chart.NegativeCoordinates)
      Smale.OnePointCover.overlapRadius Smale.OnePointCover.overlapRadius_pos k
  obtain ⟨b, hb⟩ := d.morseConnecting_surjective_of_lower hf (k + 1) (by omega) (C a)
  refine ⟨b, C.injective ?_⟩
  exact (d.upperCollapse_homology_equiv_compare hf k b).trans hb

private theorem Smale.LocalDegree.exists_native_boundaryData {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → F} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x) (hzero : f x = 0)
    (hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap = fderiv ℝ (f ∘ Smale.NativeParametrization.centered (D := E) x) 0 ∧
        Nonempty
          (BoundaryData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
            ((Smale.NativeParametrization.centered (D := E) x).source ∩
              Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  let c := Smale.NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := Smale.NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := Smale.NativeParametrization.centered_zero x
  have hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (c 0) := hcx.symm ▸ hf
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc0)
  have hcomp : ContDiffAt ℝ ∞ (f ∘ c) 0 := (hcf.comp 0 hc).contDiffAt
  let A : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c 0)
  let C : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c 0
  have hAi : A.IsInvertible := by
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c 0)).IsInvertible
    rw [hcx]
    exact hA
  have hCi : C.IsInvertible :=
    ⟨(LinearEquiv.ofBijective C.toLinearMap
          (Smale.PartialChart.bijective_mfderiv c hc0)).toContinuousLinearEquiv,
      rfl⟩
  have hder : HasFDerivAt (f ∘ c) (A.comp C) 0 :=
    ((hcf.mdifferentiableAt (by simp)).hasMFDerivAt.comp 0
        (hc.mdifferentiableAt (by simp)).hasMFDerivAt).hasFDerivAt
  obtain ⟨L, hL⟩ := hAi.comp hCi
  have hdL : HasFDerivAt (f ∘ c) L.toContinuousLinearMap 0 := hL.symm ▸ hder
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc.continuousAt (hcx.symm ▸ hW))
  refine ⟨L, hdL.fderiv.symm, ?_⟩
  apply nonempty_boundaryData_of_contDiffAt L hdL _ hs hcomp
  change f (c 0) = 0
  rw [hcx]
  exact hzero

private structure Smale.LocalDegree.NeighborhoodData {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F)
    (s : Set E) where
  radius : ℝ
  radius_pos : 0 < radius
  center_zero : f 0 = 0
  ball_subset : Metric.closedBall 0 radius ⊆ s
  continuous : ContinuousOn f (Metric.closedBall 0 radius)
  remainder_bound : ∀ x ∈ Metric.closedBall 0 radius, ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖

private theorem Smale.LocalDegree.nonempty_neighborhoodData {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) : Nonempty (NeighborhoodData f L s) := by
  obtain ⟨ε, hε, hεb⟩ := exists_pos_remainder_bound L hf hzero
  obtain ⟨b⟩ :=
    nonempty_boundaryData L hf hzero (Filter.inter_mem hs (Metric.ball_mem_nhds 0 hε))
      (hc.mono Set.inter_subset_left)
  have hbs : Metric.closedBall (0 : E) b.radius ⊆ s := b.ball_subset.trans Set.inter_subset_left
  exact
    ⟨⟨b.radius, b.radius_pos, hzero, hbs, hc.mono hbs, fun x hx => hεb x (b.ball_subset hx).2⟩⟩

private theorem Smale.LocalDegree.nonempty_neighborhoodData_of_contDiffAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (L : E ≃L[ℝ] F) {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContDiffAt ℝ ∞ f 0) : Nonempty (NeighborhoodData f L s) := by
  obtain ⟨t, ht, htc⟩ := contDiffAt_zero.mp (hc.of_le (by simp))
  obtain ⟨d⟩ :=
    nonempty_neighborhoodData L hf hzero (Filter.inter_mem hs ht)
      (htc.mono Set.inter_subset_right)
  exact ⟨{ d with ball_subset := d.ball_subset.trans Set.inter_subset_left }⟩

private theorem
    Smale.LocalDegree.NeighborhoodData.image_ne_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) {x : E}
    (hx : x ∈ Metric.closedBall 0 d.radius) (hx0 : x ≠ 0) : f x ≠ 0 :=
  Smale.LocalDegree.image_ne_zero L hx0 (d.remainder_bound x hx)

private def Smale.LocalDegree.NeighborhoodData.innerBoundary {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) :
    Smale.LocalDegree.BoundaryData f L s := by
  have hr : 0 < d.radius / 2 := half_pos d.radius_pos
  have hballs : Metric.closedBall (0 : E) (d.radius / 2) ⊆ Metric.closedBall 0 d.radius :=
    Metric.closedBall_subset_closedBall (half_le_self d.radius_pos.le)
  have hparam (u : Metric.sphere (0 : E) 1) :
    (d.radius / 2) • (u : E) ∈ Metric.closedBall (0 : E) d.radius := by
    rw [mem_closedBall_zero_iff, Smale.LocalDegree.norm_radius_smul (d.radius / 2) hr u]
    exact half_le_self d.radius_pos.le
  refine ⟨d.radius / 2, hr, hballs.trans d.ball_subset, ?_, ?_⟩
  · exact d.continuous.comp_continuous (continuous_const.smul continuous_subtype_val) hparam
  · exact fun u => d.remainder_bound _ (hparam u)

private theorem Smale.LocalDegree.NeighborhoodData.innerBoundary_radius {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) :
    d.innerBoundary.radius = d.radius / 2 :=
  rfl

private theorem Smale.LocalDegree.NeighborhoodData.innerBoundary_mem_ball {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s)
    (u : Metric.sphere (0 : E) 1) :
    d.innerBoundary.radius • (u : E) ∈ Metric.ball (0 : E) d.radius := by
  rw [mem_ball_zero_iff, Smale.LocalDegree.norm_radius_smul _ d.innerBoundary.radius_pos,
    innerBoundary_radius]
  exact half_lt_self d.radius_pos

private theorem
    Smale.LocalDegree.exists_native_neighborhoodData {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → F} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x) (hzero : f x = 0)
    (hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap = fderiv ℝ (f ∘ Smale.NativeParametrization.centered (D := E) x) 0 ∧
        Nonempty
          (NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
            ((Smale.NativeParametrization.centered (D := E) x).source ∩
              Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  obtain ⟨L, hL, _⟩ := exists_native_boundaryData x hf hzero hA W hW
  let c := Smale.NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := Smale.NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := Smale.NativeParametrization.centered_zero x
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc0)
  have hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (c 0) := hcx.symm ▸ hf
  have hcomp : ContDiffAt ℝ ∞ (f ∘ c) 0 := (hcf.comp 0 hc).contDiffAt
  have hd : HasFDerivAt (f ∘ c) L.toContinuousLinearMap 0 := by
    rw [hL]
    exact (hcomp.differentiableAt (by simp)).hasFDerivAt
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc.continuousAt (hcx.symm ▸ hW))
  refine ⟨L, hL, nonempty_neighborhoodData_of_contDiffAt L hd ?_ hs hcomp⟩
  change f (c 0) = 0
  rw [hcx]
  exact hzero

private def
    Smale.ChartPuncturedBall.openSet {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    (c : OpenPartialHomeomorph E M) (R : ℝ) : Set M :=
  c '' Metric.ball (0 : E) R

private def Smale.ChartPuncturedBall.puncturedSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) : Set M :=
  {c 0}ᶜ ∩ openSet c R

private theorem Smale.ChartPuncturedBall.zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : (0 : E) ∈ c.source :=
  hs (by simpa using hR.le)

private theorem Smale.ChartPuncturedBall.ball_subset_source {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : Metric.ball (0 : E) R ⊆ c.source :=
  Metric.ball_subset_closedBall.trans hs

private theorem Smale.ChartPuncturedBall.isOpen_openSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : IsOpen (openSet c R) :=
  c.isOpen_image_of_subset_source Metric.isOpen_ball (ball_subset_source c R hs)

private theorem Smale.ChartPuncturedBall.center_mem_openSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R) :
    c 0 ∈ openSet c R :=
  Set.mem_image_of_mem c (by simpa using hR)

private def Smale.ChartPuncturedBall.ballHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : Metric.ball (0 : E) R ≃ₜ openSet c R :=
  c.homeomorphOfImageSubsetSource (ball_subset_source c R hs) rfl

private theorem Smale.ChartPuncturedBall.image_puncturedBall {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) :
    c '' {x : E | x ≠ 0 ∧ ‖x‖ < R} = puncturedSet c R := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx0, hxR⟩, rfl⟩
    have hx : x ∈ Metric.ball (0 : E) R := mem_ball_zero_iff.mpr hxR
    refine ⟨?_, ⟨x, hx, rfl⟩⟩
    change c x ≠ c 0
    exact fun h => hx0 (c.injOn (ball_subset_source c R hs hx) (zero_mem_source c R hR hs) h)
  · rintro ⟨hy0, x, hxR, rfl⟩
    refine ⟨x, ⟨?_, mem_ball_zero_iff.mp hxR⟩, rfl⟩
    intro hx0
    subst x
    exact hy0 rfl

private def Smale.ChartPuncturedBall.puncturedHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) :
    Smale.PuncturedBall.Space E R ≃ₜ puncturedSet c R :=
  c.homeomorphOfImageSubsetSource
    (fun _ hx => ball_subset_source c R hs (mem_ball_zero_iff.mpr hx.2))
    (image_puncturedBall c R hR hs)

private def Smale.LocalDegree.NativeNeighborhood.openSet {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Set M :=
  Smale.ChartPuncturedBall.openSet
    (Smale.NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph d.radius

private theorem Smale.LocalDegree.NativeNeighborhood.closedBall_subset_source {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Metric.closedBall (0 : E) d.radius ⊆ (Smale.NativeParametrization.centered x).source :=
  d.ball_subset.trans Set.inter_subset_left

private theorem
    Smale.LocalDegree.NativeNeighborhood.isOpen_openSet {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    IsOpen (openSet x d) :=
  Smale.ChartPuncturedBall.isOpen_openSet
    (Smale.NativeParametrization.centered x).toOpenPartialHomeomorph d.radius
    (closedBall_subset_source x d)

private theorem Smale.LocalDegree.NativeNeighborhood.center_mem_openSet {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    x ∈ openSet x d := by
  have h :=
    Smale.ChartPuncturedBall.center_mem_openSet
      (Smale.NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph d.radius
      d.radius_pos
  change Smale.NativeParametrization.centered x (0 : E) ∈ openSet x d at h
  rwa [Smale.NativeParametrization.centered_zero] at h

private theorem
    Smale.LocalDegree.NativeNeighborhood.openSet_subset {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    openSet x d ⊆ W := by
  rintro y ⟨u, hu, rfl⟩
  exact (d.ball_subset (Metric.ball_subset_closedBall hu)).2

private def
    Smale.LocalDegree.NativeNeighborhood.puncturedHomeomorph {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Smale.PuncturedBall.Space E d.radius ≃ₜ ↥({ x }ᶜ ∩ openSet x d) :=
  (Smale.ChartPuncturedBall.puncturedHomeomorph
        (Smale.NativeParametrization.centered x).toOpenPartialHomeomorph d.radius d.radius_pos
        (closedBall_subset_source x d)).trans
    (Homeomorph.setCongr
      (by
        change {Smale.NativeParametrization.centered x (0 : E)}ᶜ ∩ openSet x d = _
        rw [Smale.NativeParametrization.centered_zero]))

private def
    Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Metric.sphere (0 : E) 1 ≃ₕ ↥({ x }ᶜ ∩ openSet x d) :=
  (Smale.PuncturedBall.sphereHomotopyEquiv d.radius d.innerBoundary.radius
        d.innerBoundary.radius_pos
        (by
          rw [d.innerBoundary_radius]
          exact half_lt_self d.radius_pos)).trans
    (puncturedHomeomorph x d).toHomotopyEquiv

private structure Smale.LocalDegree.SeparatedNeighborhoods (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F M : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (P : Set M) (f : M → F) (W : Set M) where
  linear : P → E ≃L[ℝ] F
  derivative_eq :
    ∀ x : P,
      (linear x).toContinuousLinearMap =
        fderiv ℝ (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) 0
  data :
    ∀ x : P,
      NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) (linear x)
        ((Smale.NativeParametrization.centered (D := E) (x : M)).source ∩
          Smale.NativeParametrization.centered (D := E) (x : M) ⁻¹' W)
  disjoint : Pairwise (Disjoint on (fun x : P => NativeNeighborhood.openSet (x : M) (data x)))

private theorem Smale.LocalDegree.nonempty_separatedNeighborhoods (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F M : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [T2Space M] {P : Set M}
    {f : M → F} {W : Set M} (hP : P.Finite) (hf : ∀ x ∈ P, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (hz : ∀ x ∈ P, f x = 0) (hA : ∀ x ∈ P, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible)
    (hW : ∀ x ∈ P, W ∈ 𝓝 x) : Nonempty (SeparatedNeighborhoods E P f W) := by
  classical
  obtain ⟨U, hU, hdisj⟩ := hP.t2_separation
  have hex (x : P) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap =
          fderiv ℝ (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) 0 ∧
        Nonempty
          (NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) L
            ((Smale.NativeParametrization.centered (D := E) (x : M)).source ∩
              Smale.NativeParametrization.centered (D := E) (x : M) ⁻¹' (W ∩ U x))) :=
    exists_native_neighborhoodData (x : M) (hf x x.property) (hz x x.property) (hA x x.property)
      (W ∩ U x) (Filter.inter_mem (hW x x.property) ((hU x).2.mem_nhds (hU x).1))
  choose L hL hD using hex
  let D (x : P) :
    NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) (L x)
      ((Smale.NativeParametrization.centered (D := E) (x : M)).source ∩
        Smale.NativeParametrization.centered (D := E) (x : M) ⁻¹' (W ∩ U x)) :=
    Classical.choice (hD x)
  let D' (x : P) :
    NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) (L x)
      ((Smale.NativeParametrization.centered (D := E) (x : M)).source ∩
        Smale.NativeParametrization.centered (D := E) (x : M) ⁻¹' W) :=
    { D x with ball_subset := fun u hu => ⟨((D x).ball_subset hu).1, ((D x).ball_subset hu).2.1⟩ }
  refine ⟨⟨L, hL, D', ?_⟩⟩
  intro x y hxy
  change
    Disjoint (NativeNeighborhood.openSet (x : M) (D x)) (NativeNeighborhood.openSet (y : M) (D y))
  apply (hdisj x.property y.property (fun h => hxy (Subtype.ext h))).mono
  · exact (NativeNeighborhood.openSet_subset (x : M) (D x)).trans Set.inter_subset_right
  · exact (NativeNeighborhood.openSet_subset (y : M) (D y)).trans Set.inter_subset_right

private def
    Smale.LocalDegree.SeparatedNeighborhoods.neighborhood {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) : Set M :=
  Smale.LocalDegree.NativeNeighborhood.openSet (x : M) (D.data x)

private theorem Smale.LocalDegree.SeparatedNeighborhoods.isOpen_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    IsOpen (D.neighborhood x) :=
  Smale.LocalDegree.NativeNeighborhood.isOpen_openSet (x : M) (D.data x)

private theorem Smale.LocalDegree.SeparatedNeighborhoods.center_mem_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (x : M) ∈ D.neighborhood x :=
  Smale.LocalDegree.NativeNeighborhood.center_mem_openSet (x : M) (D.data x)

private theorem Smale.LocalDegree.SeparatedNeighborhoods.neighborhood_subset {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    D.neighborhood x ⊆ W :=
  Smale.LocalDegree.NativeNeighborhood.openSet_subset (x : M) (D.data x)

private theorem Smale.LocalDegree.SeparatedNeighborhoods.pairwise_disjoint {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) :
    Pairwise (Disjoint on D.neighborhood) :=
  D.disjoint

private theorem Smale.LocalDegree.SeparatedNeighborhoods.points_inter_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    P ∩ D.neighborhood x = {(x : M)} := by
  ext y
  constructor
  · rintro ⟨hyP, hy⟩
    change y = (x : M)
    by_contra hne
    let z : P := ⟨y, hyP⟩
    have hxz : x ≠ z := fun h => hne (congrArg Subtype.val h).symm
    exact Set.disjoint_left.mp (D.pairwise_disjoint hxz) hy (D.center_mem_neighborhood z)
  · rintro rfl
    exact ⟨x.property, D.center_mem_neighborhood x⟩

private theorem
    Smale.LocalDegree.SeparatedNeighborhoods.overlap_eq {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    Pᶜ ∩ D.neighborhood x = {(x : M)}ᶜ ∩ D.neighborhood x := by
  ext y
  constructor
  · rintro ⟨hyP, hy⟩
    refine ⟨?_, hy⟩
    rintro rfl
    exact hyP x.property
  · rintro ⟨hyx, hy⟩
    refine ⟨?_, hy⟩
    intro hyP
    have h : y ∈ P ∩ D.neighborhood x := ⟨hyP, hy⟩
    rw [D.points_inter_neighborhood x] at h
    exact hyx h

private theorem
    Smale.LocalDegree.SeparatedNeighborhoods.open_cover {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) :
    Pᶜ ∪ (⋃ x : P, D.neighborhood x) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y ∈ P
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨y, hy⟩, D.center_mem_neighborhood ⟨y, hy⟩⟩)
  · exact Or.inl hy

private def Smale.LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    Metric.sphere (0 : E) 1 ≃ₕ ↥(Pᶜ ∩ D.neighborhood x) :=
  (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).trans
    (Homeomorph.setCongr (D.overlap_eq x).symm).toHomotopyEquiv

private theorem Smale.LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv_apply {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P)
    (u : Metric.sphere (0 : E) 1) :
    (D.overlapSphereEquiv x u).val =
      Smale.NativeParametrization.centered (x : M) ((D.data x).innerBoundary.radius • (u : E)) :=
  rfl

private def Smale.LocalDegree.NeighborhoodData.puncturedMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) :
    C(Smale.PuncturedBall.Space E d.radius, Smale.PuncturedRadial.Space F) :=
  ⟨fun x => ⟨f x.val, d.image_ne_zero (mem_closedBall_zero_iff.mpr x.property.2.le) x.property.1⟩,
    (d.continuous.comp_continuous continuous_subtype_val
          (fun x => mem_closedBall_zero_iff.mpr x.property.2.le)).subtype_mk
      _⟩

private def Smale.LocalDegree.NativeNeighborhood.overlapMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    C(↥({ x }ᶜ ∩ openSet x d), Smale.PuncturedRadial.Space F) :=
  d.puncturedMap.comp (puncturedHomeomorph x d).symm.toHomotopyEquiv.toFun

private theorem
    Smale.LocalDegree.NativeNeighborhood.overlapMap_coe {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (y : ↥({ x }ᶜ ∩ openSet x d)) : (overlapMap x d y).val = f y.val := by
  have h := congrArg Subtype.val ((puncturedHomeomorph x d).apply_symm_apply y)
  change
    Smale.NativeParametrization.centered x ((puncturedHomeomorph x d).symm y).val = y.val at h
  exact congrArg f h

private def
    Smale.LocalDegree.SeparatedNeighborhoods.overlapMap {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    C(↥(Pᶜ ∩ D.neighborhood x), Smale.PuncturedRadial.Space F) :=
  (Smale.LocalDegree.NativeNeighborhood.overlapMap (x : M) (D.data x)).comp
    (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

private theorem Smale.LocalDegree.SeparatedNeighborhoods.overlapMap_coe {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P)
    (y : ↥(Pᶜ ∩ D.neighborhood x)) : (D.overlapMap x y).val = f y.val :=
  Smale.LocalDegree.NativeNeighborhood.overlapMap_coe (x : M) (D.data x) _

private theorem Smale.LocalDegree.SeparatedNeighborhoods.overlapMap_sphereEquiv {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (D.overlapMap x).comp (D.overlapSphereEquiv x).toFun = (D.data x).innerBoundary.map := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, overlapMap_coe, overlapSphereEquiv_apply,
    Smale.LocalDegree.BoundaryData.map_coe]
  rfl

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.beltFaceCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ≃ₜ
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates :=
  (Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates).trans
    (Smale.MorseHandle.beltFaceDiskHomeomorph.trans
      (Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates).symm)

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.beltClosedDiskPoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.chart.beltSource d.radius d.radius_pos :=
  ⟨(z.2, z.1.val),
    d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
      ⟨Set.mem_univ _, mem_closedBall_zero_iff.mpr (z.1.property.trans (by norm_num))⟩⟩

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.beltClosedDiskMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates,
      d.UpperLevel)
    where
  toFun
    z := (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (d.beltClosedDiskPoint z)).val
  continuous_toFun := by
    have hc : Continuous d.beltClosedDiskPoint :=
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _
    exact
      continuous_subtype_val.comp
        ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp hc)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.newPiece_beltFaceCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (u : Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.surgery.newPiece (d.beltFaceCoordinates u, v) = d.beltClosedDiskMap (u, v) := by
  let ud := Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates u
  let vd : Smale.MorseHandle.UnitDisk d.chart.PositiveCoordinates :=
    ⟨v.val, mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp v.property).le⟩
  have hv : ‖vd.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  let z := (Smale.MorseHandle.beltFaceDiskMap ud, vd)
  let x :
    ↥({x : M | f x ≤ f p - d.radius ^ 2} ∪
        Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) :=
    ⟨d.chart.attachingHandleMap d.radius d.radius_pos d.block z, Or.inr ⟨z, rfl⟩⟩
  have hnew :
    (d.surgery.newPiece (d.beltFaceCoordinates u, v) : M) = (d.attachmentHomeomorph x).val :=
    d.newPiece_eq _
  have hfront :
    x.val ∈
      frontier
        ({y | f y ≤ f p - d.radius ^ 2} ∪
          Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) := by
    apply (d.attachment_frontier x).mp
    rw [← hnew]
    exact (d.surgery.newPiece (d.beltFaceCoordinates u, v)).property
  have htgt := d.block (Smale.MorseHandle.modelMap_mem_product d.radius_pos z)
  have hsource : x.val ∈ d.chart.splitChart.source := d.chart.splitChart.map_target' htgt
  have hcoords : d.chart.splitChart x.val = Smale.MorseHandle.modelMap d.radius z :=
    d.chart.splitChart.right_inv' htgt
  have hend :
    Smale.MorseHandle.descentFlow (-Smale.MorseHandle.beltFaceTime ‖ud.val‖)
        (d.chart.splitChart x.val) =
      Smale.MorseHandle.beltLevelModel d.radius ud.val vd.val := by
    rw [hcoords]
    exact Smale.MorseHandle.descentFlow_neg_beltFaceTime d.radius ud vd hv
  have hpath :
    ∀ s ∈ Set.uIcc 0 (-Smale.MorseHandle.beltFaceTime ‖ud.val‖),
      Smale.MorseHandle.descentFlow s (d.chart.splitChart x.val) ∈
        Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
          Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
    intro s hs
    rw [hcoords]
    exact Smale.MorseHandle.descentFlow_positiveFace_mem_block d.radius_pos ud vd hv hs
  have hlevel :
    f
        (d.chart.splitChart.symm
          (Smale.MorseHandle.descentFlow (-Smale.MorseHandle.beltFaceTime ‖ud.val‖)
            (d.chart.splitChart x.val))) =
      f p + d.radius ^ 2 := by
    rw [d.chart.splitChart_inverse_equation (d.block (hpath _ Set.right_mem_uIcc)), hend]
    have hh := Smale.MorseHandle.beltLevelModel_height d.radius_pos ud.val hv
    change
      -‖(Smale.MorseHandle.beltLevelModel d.radius ud.val vd.val).1‖ ^ 2 +
          ‖(Smale.MorseHandle.beltLevelModel d.radius ud.val vd.val).2‖ ^ 2 =
        d.radius ^ 2 at hh
    linarith
  have horbit :=
    d.attachment_model_orbits x hfront hsource (-Smale.MorseHandle.beltFaceTime ‖ud.val‖)
      (neg_nonpos.mpr (Smale.MorseHandle.beltFaceTime_nonneg _)) hpath hlevel
  apply Subtype.ext
  rw [hnew, horbit, hend]
  rfl

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.range_newPiece_eq_range_beltClosedDiskMap
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    Set.range d.surgery.newPiece = Set.range d.beltClosedDiskMap := by
  ext y
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    refine ⟨(d.beltFaceCoordinates.symm u, v), ?_⟩
    rw [← d.newPiece_beltFaceCoordinates, d.beltFaceCoordinates.apply_symm_apply]
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact ⟨(d.beltFaceCoordinates u, v), d.newPiece_beltFaceCoordinates u v⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.beltClosedDiskMap_mem_newInterior_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltClosedDiskMap z ∈ d.surgery.NewInterior ↔ ‖z.1.val‖ < 1 := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.surgery.newPiece_mem_newInterior_iff]
  exact Smale.MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val

private theorem Smale.MorseHandle.contDiff_beltFaceMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] : ContDiff ℝ ∞ (beltFaceMap (N := N)) := by
  have hs : ContDiff ℝ ∞ (fun u : N => Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)).div_const _
  exact hs.smul contDiff_id

private theorem Smale.MorseHandle.hasFDerivAt_beltFaceMap_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    HasFDerivAt (beltFaceMap (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N) 0 := by
  have hs : ContDiff ℝ ∞ (fun u : N => Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)).div_const _
  have hd := (hs.differentiable (by simp) (0 : N)).hasFDerivAt.smul (hasFDerivAt_id (0 : N))
  change HasFDerivAt (fun u : N => (Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) • u) _ 0
  simpa [Pi.smul_def'] using hd

private theorem
    Smale.MorseHandle.hasFDerivAt_univUnitBall_symm_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm : N → N) (ContinuousLinearMap.id ℝ N)
      0 := by
  have hs : ContDiffAt ℝ ∞ (fun u : N => (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹) 0 := by
    apply ContDiffAt.inv
    · exact ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt.sqrt (by simp))
    · simp
  have hd := (hs.differentiableAt (by simp)).hasFDerivAt.smul (hasFDerivAt_id (0 : N))
  change HasFDerivAt (fun u : N => (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹ • u) (ContinuousLinearMap.id ℝ N) 0
  simpa [Pi.smul_def'] using hd

private def Smale.MorseHandle.beltCollapseCoordinate {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (u : N) : N :=
  OpenPartialHomeomorph.univUnitBall.symm (beltFaceMap u)

private theorem Smale.MorseHandle.beltCollapseCoordinate_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] : beltCollapseCoordinate (0 : N) = 0 := by
  rw [beltCollapseCoordinate, beltFaceMap_zero,
    OpenPartialHomeomorph.univUnitBall_symm_apply_zero]

private theorem
    Smale.MorseHandle.contDiffOn_beltCollapseCoordinate {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    ContDiffOn ℝ ∞ (beltCollapseCoordinate (N := N)) (Metric.ball 0 1) := by
  apply OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.comp contDiff_beltFaceMap.contDiffOn
  intro u hu
  exact mem_ball_zero_iff.mpr ((norm_beltFaceMap_lt_one_iff u).mpr (mem_ball_zero_iff.mp hu))

private theorem Smale.MorseHandle.hasFDerivAt_beltCollapseCoordinate_zero {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] :
    HasFDerivAt (beltCollapseCoordinate (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N)
      0 := by
  have hout :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm : N → N) (ContinuousLinearMap.id ℝ N)
      (beltFaceMap 0) := by
    rw [beltFaceMap_zero]
    exact hasFDerivAt_univUnitBall_symm_zero
  change HasFDerivAt ((OpenPartialHomeomorph.univUnitBall.symm : N → N) ∘ beltFaceMap) _ 0
  simpa only [ContinuousLinearMap.id_comp] using hout.comp 0 hasFDerivAt_beltFaceMap_zero

private theorem Smale.MorseHandle.hasFDerivAt_scaled_beltCollapseCoordinate_zero {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] (ρ : ℝ) :
    HasFDerivAt (fun u : N => beltCollapseCoordinate (ρ⁻¹ • u))
      (((Real.sqrt 2)⁻¹ * ρ⁻¹) • ContinuousLinearMap.id ℝ N) 0 := by
  have hout :
    HasFDerivAt (beltCollapseCoordinate (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N)
      (ρ⁻¹ • (0 : N)) := by
    simpa only [smul_zero] using hasFDerivAt_beltCollapseCoordinate_zero (N := N)
  simpa only [Function.comp_def, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, smul_smul, mul_comm] using
    hout.comp 0 ((hasFDerivAt_id (0 : N)).const_smul ρ⁻¹)

private theorem Smale.MorseHandle.scaled_beltCollapseCoordinate_factor_pos (ρ : ℝ) (hρ : 0 < ρ) :
    0 < (Real.sqrt 2)⁻¹ * ρ⁻¹ := by positivity

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.beltNormal_beltClosedDiskMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltNormal (d.beltClosedDiskMap z) = d.radius • z.1.val :=
  d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (d.beltClosedDiskPoint z)

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.collapseNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (x : d.UpperLevel) :
    d.chart.NegativeCoordinates :=
  Smale.MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • d.beltNormal x)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseNormal_belt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.collapseNormal (d.surgery.beltSphere v) = 0 := by
  rw [collapseNormal, d.beltNormal_belt, smul_zero, Smale.MorseHandle.beltCollapseCoordinate_zero]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_beltClosedDiskMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.beltClosedDiskMap z) =
      Smale.DiskOnePointCollapse.collapse
        (Smale.MorseHandle.beltFaceDiskMap
          (Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1)) := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.levelCollapse_newPiece]
  rfl

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_eq_coe_collapseNormal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    {x : d.UpperLevel} (hx : x ∈ d.surgery.NewInterior) :
    d.levelCollapseMap hf x = (d.collapseNormal x : OnePoint d.chart.NegativeCoordinates) := by
  have hr := d.surgery.newInterior_subset_range hx
  rw [d.range_newPiece_eq_range_beltClosedDiskMap] at hr
  obtain ⟨z, rfl⟩ := hr
  have hz := (d.beltClosedDiskMap_mem_newInterior_iff z).mp hx
  rw [d.levelCollapse_beltClosedDiskMap,
    Smale.DiskOnePointCollapse.collapse_interior _
      ((Smale.MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val).mpr hz)]
  unfold collapseNormal
  rw [d.beltNormal_beltClosedDiskMap, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
  rfl

private theorem Smale.SphereNormalCoordinates.normalDerivative_smul_isInvertible {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N)
    (hA : A.IsInvertible) (c : ℝ) (hc : c ≠ 0) : (c • A).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • A.inverse)
  · ext y
    simp [ContinuousLinearMap.comp_apply, smul_smul, hA.self_apply_inverse, hc]
  · ext y
    simp [ContinuousLinearMap.comp_apply, smul_smul, hA.inverse_apply_self, hc]

private theorem Smale.SphereNormalCoordinates.normalJacobian_smul_mul_pow {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : c ≠ 0) :
    normalJacobian j x (c • A) * c ^ Module.finrank ℝ N = normalJacobian j x A := by
  have hB := normalDerivative_smul_isInvertible A hA c hc
  have hcomp : A.comp A.inverse = ContinuousLinearMap.id ℝ N := by
    ext y
    exact hA.self_apply_inverse y
  have hdet : ((c • A).comp A.inverse).det = c ^ Module.finrank ℝ N := by
    rw [ContinuousLinearMap.smul_comp, hcomp]
    change (c • (LinearMap.id : N →ₗ[ℝ] N)).det = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hid : (A.comp A.inverse).det = 1 := by
    rw [hcomp]
    exact LinearMap.det_id
  have h :=
    (normalJacobian_mul_chartDet j x (c • A) hB A.inverse).trans
      (normalJacobian_mul_chartDet j x A hA A.inverse).symm
  simpa only [hdet, hid, mul_one] using h

private theorem Smale.SphereNormalCoordinates.sign_normalJacobian_smul_pos {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : 0 < c) :
    SignType.sign (normalJacobian j x (c • A)) = SignType.sign (normalJacobian j x A) := by
  have h := congrArg SignType.sign (normalJacobian_smul_mul_pow j x A hA c hc.ne')
  have hp : SignType.sign (c ^ Module.finrank ℝ N) = 1 := sign_eq_one_iff.mpr (pow_pos hc _)
  simpa only [sign_mul, hp, mul_one] using h

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.mfderiv_collapseNormal_comp {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) (x : Smale.Hemisphere.Sphere m)
    (hg : MDifferentiableAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)
    (hx : g x ∈ Set.range d.surgery.beltSphere) :
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x =
      ((Real.sqrt 2)⁻¹ * d.radius⁻¹) •
        mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x := by
  obtain ⟨v, hv⟩ := hx
  have hzero : (d.beltNormal ∘ g) x = 0 := by
    change d.beltNormal (g x) = 0
    rw [← hv, d.beltNormal_belt]
  have hout :
    HasFDerivAt
      (fun u : d.chart.NegativeCoordinates =>
        Smale.MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • u))
      (((Real.sqrt 2)⁻¹ * d.radius⁻¹) • ContinuousLinearMap.id ℝ _) ((d.beltNormal ∘ g) x) := by
    rw [hzero]
    exact Smale.MorseHandle.hasFDerivAt_scaled_beltCollapseCoordinate_zero d.radius
  have h := (hout.hasMFDerivAt.comp x hg.hasMFDerivAt).mfderiv
  change mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x = _ at h
  apply h.trans
  apply ContinuousLinearMap.ext
  intro u
  rfl

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) (x : Smale.Hemisphere.Sphere m)
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x).IsInvertible)
    (hx : g x ∈ Set.range d.surgery.beltSphere) :
    letI : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    SignType.sign
        (Smale.SphereNormalCoordinates.normalJacobian j x
          (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
      d.beltIntersectionSign m j g x := by
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hA) hx]
  exact
    Smale.SphereNormalCoordinates.sign_normalJacobian_smul_pos j x _ hA _
      (Smale.MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos)

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign_of_transverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Smale.Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        SignType.sign
            (Smale.SphereNormalCoordinates.normalJacobian j x
              (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
          d.beltIntersectionSign m j g x := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact d.collapseNormal_comp_sign m j g x hAi ⟨v, hv⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.contMDiffAt_collapseNormal_comp {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (x : Smale.Hemisphere.Sphere m),
      g x ∈ Set.range d.surgery.beltSphere →
        ContMDiffAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ (d.collapseNormal ∘ g) x := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg x hx
  obtain ⟨v, hv⟩ := hx
  have hn : ContMDiffAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ (d.beltNormal ∘ g) x := by
    have hnormal :=
      (d.contMDiffOn_beltNormal hf).contMDiffAt
        (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
    rw [hv] at hnormal
    exact hnormal.comp x hg.contMDiffAt
  have hzero : (d.beltNormal ∘ g) x = 0 := by
    change d.beltNormal (g x) = 0
    rw [← hv, d.beltNormal_belt]
  have hq :
    ContDiffAt ℝ ∞ (Smale.MorseHandle.beltCollapseCoordinate (N := d.chart.NegativeCoordinates))
      (d.radius⁻¹ • (d.beltNormal ∘ g) x) := by
    rw [hzero, smul_zero]
    exact
      Smale.MorseHandle.contDiffOn_beltCollapseCoordinate.contDiffAt
        (Metric.isOpen_ball.mem_nhds (by simp))
  have hs :
    ContDiffAt ℝ ∞
      (fun u : d.chart.NegativeCoordinates =>
        Smale.MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • u))
      ((d.beltNormal ∘ g) x) :=
    hq.comp _ (contDiff_id.const_smul d.radius⁻¹).contDiffAt
  exact hs.contMDiffAt.comp x hn

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.isInvertible_collapseNormal_comp_of_transverse
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Smale.Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x).IsInvertible :=
  by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hAi) ⟨v, hv⟩]
  exact
    Smale.SphereNormalCoordinates.normalDerivative_smul_isInvertible A hAi _
      (Smale.MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos).ne'

attribute [local instance 100] Classical.propDecidable in
private abbrev Smale.ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :=
  Smale.LocalDegree.SeparatedNeighborhoods (EuclideanSpace ℝ (Fin m))
    (d.beltIntersectionPoints m g) (d.collapseNormal ∘ g) (g ⁻¹' d.surgery.NewInterior)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.nonempty_collapseNeighborhoods {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] [CompactSpace M]
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      Nonempty (d.CollapseNeighborhoods m g) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  have hfin := d.finite_beltIntersectionPoints hf n m hdim g hg hinj ht
  apply Smale.LocalDegree.nonempty_separatedNeighborhoods (EuclideanSpace ℝ (Fin m)) hfin
  · exact fun x hx => d.contMDiffAt_collapseNormal_comp hf m g hg x hx
  · intro x hx
    obtain ⟨v, hv⟩ := hx
    change d.collapseNormal (g x) = 0
    rw [← hv, d.collapseNormal_belt]
  · exact fun x hx => d.isInvertible_collapseNormal_comp_of_transverse hf n m hdim g hg ht x hx
  · intro x hx
    apply hg.continuous.continuousAt
    apply d.surgery.isOpen_newInterior.mem_nhds
    obtain ⟨v, hv⟩ := hx
    rw [← hv]
    exact d.surgery.beltSphere_mem_newInterior v

private def Smale.DisjointOpenHomology.inclusion {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (i : ι) : C(W i, ↥(⋃ j, W j)) :=
  ⟨Set.inclusion (Set.subset_iUnion W i), continuous_subtype_val.subtype_mk _⟩

private def Smale.DisjointOpenHomology.unionHomeomorph {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W)) :
    (Σ i, W i) ≃ₜ ↥(⋃ i, W i) :=
  let e := Equiv.ofBijective (Set.sigmaToiUnion W) (Set.sigmaToiUnion_bijective W hd)
  e.toHomeomorphOfContinuousOpen
    (by
      apply continuous_sigma
      intro i
      exact (Smale.DisjointOpenHomology.inclusion W i).continuous)
    (by
      apply isOpenMap_sigma.mpr
      intro i
      exact (hW i).isOpenMap_inclusion (Set.subset_iUnion W i))

private def Smale.DisjointOpenHomology.homologyEquiv {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W)) [Fintype ι] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (↥(⋃ i, W i)) k ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (W i) k) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (unionHomeomorph W hW hd).symm k).trans
    (ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv (fun i => W i) k)

private theorem Smale.DisjointOpenHomology.homologyEquiv_symm_apply {X : Type} [TopologicalSpace X]
    {ι : Type} (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W))
    [Fintype ι] (k : ℕ) (a : ∀ i, SingularMayerVietoris.SingularHomology (W i) k) :
    (homologyEquiv W hW hd k).symm a =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (Smale.DisjointOpenHomology.inclusion W i) k
          (a i) := by
  change
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (unionHomeomorph W hW hd).symm k).symm
        ((ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv (fun i => W i) k).symm a) =
      _
  rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_symm_apply, Homeomorph.symm_symm,
    ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private def Smale.CoverOverlapHomology.componentInclusion {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) (i : ι) : C(↥(U ∩ V i), ↥(U ∩ ⋃ j, V j)) :=
  ⟨fun x => ⟨x.val, ⟨x.property.1, Set.mem_iUnion.mpr ⟨i, x.property.2⟩⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

private def
    Smale.CoverOverlapHomology.distributeHomeomorph {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) : ↥(U ∩ ⋃ i, V i) ≃ₜ ↥(⋃ i, U ∩ V i) :=
  Homeomorph.setCongr (by ext x; simp)

private theorem Smale.CoverOverlapHomology.disjoint_intersections {X : Type} {ι : Type} (U : Set X)
    (V : ι → Set X) (hd : Pairwise (Disjoint on V)) : Pairwise (Disjoint on (fun i => U ∩ V i)) :=
  by
  intro i j hij
  exact (hd hij).mono Set.inter_subset_right Set.inter_subset_right

private def Smale.CoverOverlapHomology.homologyEquiv {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (distributeHomeomorph U V) k).trans
    (Smale.DisjointOpenHomology.homologyEquiv (fun i => U ∩ V i) (fun i => hU.inter (hV i))
      (disjoint_intersections U V hd) k)

private theorem Smale.CoverOverlapHomology.homologyEquiv_symm_apply {X : Type} [TopologicalSpace X]
    {ι : Type} (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ)
    (a : ∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    (homologyEquiv U V hU hV hd k).symm a =
      ∑ i, SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k (a i) := by
  change
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (distributeHomeomorph U V) k).symm
        ((Smale.DisjointOpenHomology.homologyEquiv (fun i => U ∩ V i) (fun i => hU.inter (hV i))
              (disjoint_intersections U V hd) k).symm
          a) =
      _
  rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_symm_apply,
    Smale.DisjointOpenHomology.homologyEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private theorem Smale.CoverOverlapHomology.homology_decomposition {X : Type} [TopologicalSpace X]
    {ι : Type} (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    a =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k
          (homologyEquiv U V hU hV hd k a i) := by
  have h := homologyEquiv_symm_apply U V hU hV hd k (homologyEquiv U V hU hV hd k a)
  rwa [LinearEquiv.symm_apply_apply] at h

private theorem
    Smale.CoverOverlapHomology.homology_map_out {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] {Y : Type} [TopologicalSpace Y]
    (f : C(↥(U ∩ ⋃ i, V i), Y)) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    SingularMayerVietoris.singularHomologyMap f k a =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (f.comp (componentInclusion U V i)) k
          (homologyEquiv U V hU hV hd k a i) := by
  calc
    SingularMayerVietoris.singularHomologyMap f k a =
        SingularMayerVietoris.singularHomologyMap f k
          (∑ i,
            SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k
              (homologyEquiv U V hU hV hd k a i)) :=
      congrArg (SingularMayerVietoris.singularHomologyMap f k)
        (homology_decomposition U V hU hV hd k a)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply]

private def
    Smale.CoverLocalContributions.componentConnecting {X : Type} [TopologicalSpace X] {ι : Type}
    [Fintype ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ) (k : ℕ) :
    SingularMayerVietoris.SingularHomology X (k + 1) →ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :=
  (Smale.CoverOverlapHomology.homologyEquiv U V hU hV hd k).toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism U (⋃ i, V i) hU (isOpen_iUnion hV) hc k)

private theorem Smale.CoverLocalContributions.map_union {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (V : ι → Set X) (V' : Set Y) (f : C(X, Y))
    (hfV : ∀ i, Set.MapsTo f (V i) V') : Set.MapsTo f (⋃ i, V i) V' := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact hfV i hi

private def
    Smale.CoverLocalContributions.localMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : ∀ i, Set.MapsTo f (V i) V') (i : ι) : C(↥(U ∩ V i), ↥(U' ∩ V')) :=
  Smale.CoverNaturality.mapOn f _ _ (fun _ hx => ⟨hfU hx.1, hfV i hx.2⟩)

private theorem Smale.CoverLocalContributions.connecting_sum {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} [Fintype ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ)
    (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) V')
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' k
        (SingularMayerVietoris.singularHomologyMap f (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (localMap U V U' V' f hfU hfV i) k
          (componentConnecting U V hU hV hd hc k a i) := by
  rw [←
    Smale.CoverNaturality.connecting_naturality_apply U (⋃ i, V i) U' V' f hfU
      (map_union V V' f hfV) hU (isOpen_iUnion hV) hc hU' hV' hc' k a]
  rw [Smale.CoverOverlapHomology.homology_map_out U V hU hV hd]
  apply Finset.sum_congr rfl
  intro i _
  rfl

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.attachingCollapse {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) :
    C(Smale.Hemisphere.Sphere m, OnePoint d.chart.NegativeCoordinates) :=
  (d.levelCollapseMap hf).comp g

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.attachingCollapse_zero_iff {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (x : Smale.Hemisphere.Sphere m) :
    d.attachingCollapse hf m g x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ d.beltIntersectionPoints m g :=
  d.levelCollapse_zero_iff hf (g x)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_old {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) :
    Set.MapsTo (d.attachingCollapse hf m g) (d.beltIntersectionPoints m g)ᶜ
      Smale.OnePointCover.oldPatch := by
  intro x hx hzero
  exact hx ((d.attachingCollapse_zero_iff hf m g x).mp hzero)

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_neighborhood {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    Set.MapsTo (d.attachingCollapse hf m g) (D.neighborhood i) Smale.OnePointCover.finitePatch := by
  intro x hx
  have hnew : g x ∈ d.surgery.NewInterior := D.neighborhood_subset i hx
  change d.levelCollapseMap hf (g x) ≠ OnePoint.infty
  rw [d.levelCollapse_eq_coe_collapseNormal hf hnew]
  exact OnePoint.coe_ne_infty _

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.collapseOverlapMap {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    C(↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i),
      ↥(Smale.OnePointCover.oldPatch (N := d.chart.NegativeCoordinates) ∩
          Smale.OnePointCover.finitePatch)) :=
  Smale.CoverNaturality.mapOn (d.attachingCollapse hf m g) _ _
    (fun _ hx =>
      ⟨d.attachingCollapse_maps_old hf m g hx.1,
        d.attachingCollapse_maps_neighborhood hf m g D i hx.2⟩)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseOverlapMap_eq {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    d.collapseOverlapMap hf m g D i =
      Smale.OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.overlapMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    d.levelCollapseMap hf (g x.val) =
      (Smale.OnePointCover.overlapHomeomorph (D.overlapMap i x)).val
  rw [Smale.OnePointCover.overlapHomeomorph_apply,
    Smale.LocalDegree.SeparatedNeighborhoods.overlapMap_coe]
  exact d.levelCollapse_eq_coe_collapseNormal hf (D.neighborhood_subset i x.property.2)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseOverlapMap_sphereEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    (d.collapseOverlapMap hf m g D i).comp (D.overlapSphereEquiv i).toFun =
      Smale.OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp
        (D.data i).innerBoundary.map := by
  rw [d.collapseOverlapMap_eq hf m g D i, ContinuousMap.comp_assoc, D.overlapMap_sphereEquiv]

private def
    Smale.ManifoldMorse.MorseSurgeryData.upperLevelInclusion {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(d.UpperLevel, { y : M // f y ≤ f p + d.radius ^ 2 }) :=
  ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

private def Smale.ManifoldMorse.MorseSurgeryData.bandSublevelHomeomorph {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (d' : Smale.ManifoldMorse.MorseSurgeryData E f q) (T : M ≃ₜ M)
    (hT : T '' {y : M | f y ≤ f p + d.radius ^ 2} = {y : M | f y ≤ f q - d'.radius ^ 2}) :
    { y : M // f y ≤ f p + d.radius ^ 2 } ≃ₜ { y : M // f y ≤ f q - d'.radius ^ 2 } :=
  (T.image {y : M | f y ≤ f p + d.radius ^ 2}).trans (Homeomorph.setCongr hT)

private structure Smale.ManifoldMorse.SurgeryWindows.BandData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) where
  ambient : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞
  level : (S.data (S.point i)).UpperLevel ≃ₜ (S.data (S.point j)).LowerLevel
  sublevel_image :
    ambient '' {x : M | f x ≤ S.upper (S.point i)} = {x : M | f x ≤ S.lower (S.point j)}
  level_coe : ∀ x : (S.data (S.point i)).UpperLevel, (level x : M) = ambient x

private theorem Smale.ManifoldMorse.SurgeryWindows.nonempty_consecutiveBandData {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) : Nonempty (S.BandData i j) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
  obtain ⟨D, b, hD, hb⟩ := S.exists_consecutiveBandBridge hf i j hij
  exact ⟨⟨D, b.toHomeomorph, hD, hb⟩⟩

private def
    Smale.ManifoldMorse.SurgeryWindows.consecutiveBandData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) : S.BandData i j :=
  Classical.choice (S.nonempty_consecutiveBandData hf i j hij)

private def Smale.ManifoldMorse.SurgeryWindows.BandData.sublevelHomeomorph {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {S : Smale.ManifoldMorse.SurgeryWindows E f} {i j : Fin S.count} (D : S.BandData i j) :
    { x : M // f x ≤ S.upper (S.point i) } ≃ₜ { x : M // f x ≤ S.lower (S.point j) } :=
  (S.data (S.point i)).bandSublevelHomeomorph (S.data (S.point j)) D.ambient.toHomeomorph
    D.sublevel_image

private def
    Smale.ManifoldMorse.SurgeryWindows.BandData.homologyEquiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {S : Smale.ManifoldMorse.SurgeryWindows E f} {i j : Fin S.count} (D : S.BandData i j)
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point i) } k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point j) } k :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv D.sublevelHomeomorph k

private theorem
    Smale.SublevelDisk.contractibleSpace {M : Type} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    {n : ℕ} (d : Smale.SublevelDisk n f a) : ContractibleSpace { x : M // f x ≤ a } := by
  let : ContractibleSpace (Smale.Hemisphere.Ball n) :=
    (convex_closedBall (0 : Smale.Hemisphere.Ambient n) 1).contractibleSpace ⟨0, by simp⟩
  exact d.homeomorph.symm.contractibleSpace

private theorem Smale.SublevelDisk.homology_subsingleton {M : Type} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} {n : ℕ} (d : Smale.SublevelDisk n f a) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology { x : M // f x ≤ a } k) := by
  let := d.contractibleSpace
  exact PeriodTorusHigherHomology.contractible_homology_subsingleton _ k hk

private theorem
    Smale.ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin S.count) (hj : 0 < j.val)
    (hindex :
      ∀ i : Fin S.count,
        0 < i.val →
          i.val < j.val → 2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point j) } 1) := by
  have hupper :
    ∀ n : ℕ,
      ∀ hn : n < S.count,
        n < j.val →
          Subsingleton
            (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n, hn⟩) }
              1) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 1 one_ne_zero
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨n, hn'⟩) + (S.data (S.point ⟨n, hn'⟩)).radius ^ 2 } 1) :=
        ih hn' (by omega)
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨n, hn'⟩ ⟨n + 1, hn⟩ rfl
      let H :=
        (S.data (S.point ⟨n, hn'⟩)).bandSublevelHomeomorph (S.data (S.point ⟨n + 1, hn⟩))
          T.toHomeomorph hT
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) - (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2 }
            1) :=
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv H.symm 1).injective.subsingleton
      exact
        (S.data (S.point ⟨n + 1, hn⟩)).upperHomologyOne_subsingleton hf.continuous
          (hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj)
  have hp : j.val - 1 < S.count := by omega
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M //
          f x ≤ f (S.point ⟨j.val - 1, hp⟩) + (S.data (S.point ⟨j.val - 1, hp⟩)).radius ^ 2 }
        1) :=
    hupper (j.val - 1) hp (by omega)
  obtain ⟨T, _, hT, _⟩ :=
    S.exists_consecutiveBandBridge hf ⟨j.val - 1, hp⟩ j (by change j.val - 1 + 1 = j.val; omega)
  let H :=
    (S.data (S.point ⟨j.val - 1, hp⟩)).bandSublevelHomeomorph (S.data (S.point j)) T.toHomeomorph
      hT
  exact (PeriodTorusHigherHomology.homeomorphHomologyEquiv H.symm 1).injective.subsingleton

private theorem
    Smale.ManifoldMorse.MorseSurgeryData.attachingHomology_subsingleton_of_index {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) := by
  let n := Module.finrank ℝ d.chart.NegativeCoordinates - 2
  have hn : Module.finrank ℝ d.chart.NegativeCoordinates = (n + 1) + 1 := by
    dsimp [n]
    omega
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = (n + 1) + 1) := ⟨hn⟩
  let :
    Subsingleton (SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :=
    SphereHomology.unitSphere_homology_subsingleton n k hk (by omega)
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
            (n + 1)).symm.toHomeomorph
        k).injective.subsingleton

private theorem Smale.ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_index
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) := by
  let := d.attachingHomology_subsingleton_of_index k hk hindex hne
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf k hk

private def
    Smale.LinearSphereAction.puncturedMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (hi : Function.Injective A) :
    C(Metric.sphere (0 : E) 1, Smale.PuncturedRadial.Space F) :=
  ⟨fun x => ⟨A x.val, fun h => ne_zero_of_mem_unit_sphere x (hi (h.trans (map_zero A).symm))⟩,
    (A.continuous.comp continuous_subtype_val).subtype_mk _⟩

private def
    Smale.LinearSphereAction.sphereMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (hi : Function.Injective A) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1) :=
  Smale.PuncturedRadial.toSphere.comp (puncturedMap A hi)

private theorem Smale.LinearSphereAction.sphereMap_id {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    sphereMap (ContinuousLinearMap.id ℝ E) Function.injective_id =
      ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  ext x
  change ‖(x : E)‖⁻¹ • (x : E) = (x : E)
  rw [mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

private theorem Smale.LinearSphereAction.component_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {signWeight : ℝ}
    (A : Degree.LinearFramePaths.operatorComponent (D := E) signWeight) :
    Function.Injective A.val := by
  have hd : A.val.toLinearMap.det ≠ 0 := by
    intro hz
    have hp : 0 < signWeight * A.val.toLinearMap.det := A.property
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  apply LinearMap.ker_eq_bot.mp
  by_contra hk
  exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)

private def Smale.LinearSphereAction.componentHomotopy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {signWeight : ℝ}
    {A B : Degree.LinearFramePaths.operatorComponent (D := E) signWeight} (γ : Path A B) :
    (sphereMap A.val (component_injective A)).Homotopy (sphereMap B.val (component_injective B))
    where
  toFun q := sphereMap (γ q.1).val (component_injective (γ q.1)) q.2
  continuous_toFun := by
    have hA : Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => (γ q.1).val) :=
      continuous_subtype_val.comp (γ.continuous.comp continuous_fst)
    have hx : Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => q.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact Smale.PuncturedRadial.toSphere.continuous.comp ((hA.clm_apply hx).subtype_mk _)
  map_zero_left
    x := by
    change sphereMap (γ 0).val (component_injective (γ 0)) x = _
    rw [γ.source]
  map_one_left
    x := by
    change sphereMap (γ 1).val (component_injective (γ 1)) x = _
    rw [γ.target]

private theorem Smale.LinearSphereAction.homotopic_of_det_mul_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Finite ι] [Nontrivial ι]
    (b : Module.Basis ι ℝ E) (A B : E ≃L[ℝ] E)
    (h : 0 < A.toLinearEquiv.toLinearMap.det * B.toLinearEquiv.toLinearMap.det) :
    (sphereMap A.toContinuousLinearMap A.injective).Homotopic
      (sphereMap B.toContinuousLinearMap B.injective) := by
  have hd : A.toLinearEquiv.toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at h
    exact lt_irrefl _ h
  let A' : Degree.LinearFramePaths.operatorComponent (D := E) A.toLinearEquiv.toLinearMap.det :=
    ⟨A.toContinuousLinearMap, mul_self_pos.mpr hd⟩
  let B' : Degree.LinearFramePaths.operatorComponent (D := E) A.toLinearEquiv.toLinearMap.det :=
    ⟨B.toContinuousLinearMap, h⟩
  exact ⟨componentHomotopy (Degree.LinearFramePaths.joined_operatorComponent b A' B').somePath⟩

private theorem Smale.LinearSphereAction.sphereMap_comp {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E →L[ℝ] F) (B : F →L[ℝ] G) (hA : Function.Injective A)
    (hB : Function.Injective B) :
    (sphereMap B hB).comp (sphereMap A hA) = sphereMap (B.comp A) (hB.comp hA) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (B (‖A x.val‖⁻¹ • A x.val)) = NormedSpace.normalize (B (A x.val))
  rw [map_smul]
  exact
    NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr (norm_pos_iff.mpr (puncturedMap A hA x).property)) _

private theorem Smale.LinearSphereAction.sphereMap_trans {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E ≃L[ℝ] F) (B : F ≃L[ℝ] G) :
    sphereMap (A.trans B).toContinuousLinearMap (A.trans B).injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap A.toContinuousLinearMap A.injective) :=
  (sphereMap_comp A.toContinuousLinearMap B.toContinuousLinearMap A.injective B.injective).symm

private theorem
    Smale.LinearSphereAction.normalized_linearSphereMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E ≃L[ℝ] F) (r : ℝ)
    (hr : 0 < r) :
    Smale.PuncturedRadial.toSphere.comp (Smale.LocalDegree.linearSphereMap A r hr) =
      sphereMap A.toContinuousLinearMap A.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (A (r • x.val)) = NormedSpace.normalize (A x.val)
  rw [map_smul, NormedSpace.normalize_smul_of_pos hr]

private theorem Smale.LinearSphereAction.sphereMap_relative {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A B : E ≃L[ℝ] F) :
    sphereMap A.toContinuousLinearMap A.injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap (A.trans B.symm).toContinuousLinearMap (A.trans B.symm).injective) := by
  rw [← sphereMap_trans]
  have heq : (A.trans B.symm).trans B = A := by
    ext x
    exact B.apply_symm_apply (A x)
  rw [heq]

private def Smale.LinearSphereAction.sphereHomotopyEquiv {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₕ Metric.sphere (0 : F) 1 :=
  (Smale.LocalDegree.linearSphereEquiv B 1 zero_lt_one).trans
    (Smale.PuncturedRadial.sphereHomotopyEquiv 1 zero_lt_one).symm

private theorem
    Smale.LinearSphereAction.sphereHomotopyEquiv_toFun {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) :
    (sphereHomotopyEquiv B).toFun = sphereMap B.toContinuousLinearMap B.injective :=
  normalized_linearSphereMap B 1 zero_lt_one

private def
    Smale.LinearSphereAction.homologyEquiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : F) 1) k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (sphereHomotopyEquiv B) k

private theorem Smale.LinearSphereAction.homologyEquiv_apply {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k) :
    homologyEquiv B k a =
      SingularMayerVietoris.singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective) k
        a := by
  change SingularMayerVietoris.singularHomologyMap (sphereHomotopyEquiv B).toFun k a = _
  rw [sphereHomotopyEquiv_toFun]

private theorem Smale.SpherePoint.hyperplaneReflection_det {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (u : V) (hu : u ≠ 0) :
    ((ℝ ∙ u)ᗮ.reflection).toLinearMap.det = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hu,
    pow_one]

private theorem Smale.SpherePoint.positive_transport_of_normal {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (v w : Metric.sphere (0 : V) 1) (u : V)
    (hu : u ≠ 0) (huw : Inner.inner ℝ u w.val = 0) (hvw : v ≠ w) :
    ∃ R : V ≃ₗᵢ[ℝ] V, R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  have hvw' : (v : V) - (w : V) ≠ 0 := by
    intro h
    exact hvw (Subtype.ext (sub_eq_zero.mp h))
  let R₁ := (ℝ ∙ ((v : V) - (w : V)))ᗮ.reflection
  let R₂ := (ℝ ∙ u)ᗮ.reflection
  have h₁ : R₁ v.val = w.val :=
    Submodule.reflection_sub
      ((mem_sphere_zero_iff_norm.mp v.property).trans
        (mem_sphere_zero_iff_norm.mp w.property).symm)
  have h₂ : R₂ w.val = w.val :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr huw)
  refine ⟨R₁.trans R₂, ?_, ?_⟩
  · change R₂ (R₁ v.val) = w.val
    rw [h₁, h₂]
  · change (R₂.toLinearMap.comp R₁.toLinearMap).det = 1
    rw [LinearMap.det_comp, hyperplaneReflection_det u hu,
      hyperplaneReflection_det ((v : V) - (w : V)) hvw']
    norm_num

private theorem Smale.SpherePoint.exists_positive_transport (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) :
    ∃ R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)),
      R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  by_cases hvw : v = w
  · refine ⟨LinearIsometryEquiv.refl ℝ _, ?_, ?_⟩
    · exact congrArg Subtype.val hvw
    · exact LinearMap.det_id
  · let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) := ⟨by simp⟩
    let b :=
      OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1) (ne_zero_of_mem_unit_sphere w)
    let u : EuclideanSpace ℝ (Fin (n + 2)) :=
      (b (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 2)))
    have hun : ‖u‖ = 1 := b.norm_eq_one 0
    have hu : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hun
      exact zero_ne_one hun
    have huw : Inner.inner ℝ u w.val = 0 := by
      have h := (b (0 : Fin (n + 1))).property
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp h
    exact positive_transport_of_normal v w u hu huw hvw

private def Smale.SpherePoint.positiveTransport (n : ℕ) (v w : SphereHomology.UnitSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  Classical.choose (exists_positive_transport n v w)

private theorem Smale.SpherePoint.positiveTransport_apply (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) : positiveTransport n v w v.val = w.val :=
  (Classical.choose_spec (exists_positive_transport n v w)).1

private theorem Smale.SpherePoint.positiveTransport_det (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) : (positiveTransport n v w).toLinearMap.det = 1 :=
  (Classical.choose_spec (exists_positive_transport n v w)).2

private def Smale.CoverNaturality.intersectionSwap {X : Type} [TopologicalSpace X] (U V : Set X) :
    C(↥(U ∩ V), ↥(V ∩ U)) :=
  ⟨fun x => ⟨x.val, x.property.symm⟩, continuous_subtype_val.subtype_mk _⟩

private def Smale.CoverNaturality.smallSwap {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularMayerVietoris.smallComplex U V ⟶ SingularMayerVietoris.smallComplex V U :=
  SingularMayerVietoris.liftToSmall V U (SingularMayerVietoris.smallInclusion U V)
    (fun n c => by
      change c.val ∈ SingularMayerVietoris.smallChainSubmodule V U n
      simpa only [SingularMayerVietoris.smallChainSubmodule, sup_comm] using c.property)

private theorem
    Smale.CoverNaturality.smallSwap_inclusion {X : Type} [TopologicalSpace X] (U V : Set X) :
    smallSwap U V ≫ SingularMayerVietoris.smallInclusion V U =
      SingularMayerVietoris.smallInclusion U V :=
  SingularMayerVietoris.liftToSmall_inclusion V U _ _

private theorem Smale.CoverNaturality.smallSwap_left {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularMayerVietoris.toSmallLeft U V ≫ smallSwap U V =
      SingularMayerVietoris.toSmallRight V U := by
  apply (CategoryTheory.cancel_mono (SingularMayerVietoris.smallInclusion V U)).mp
  rw [CategoryTheory.Category.assoc, smallSwap_inclusion,
    SingularMayerVietoris.toSmallLeft_inclusion, SingularMayerVietoris.toSmallRight_inclusion]

private theorem
    Smale.CoverNaturality.smallSwap_right {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularMayerVietoris.toSmallRight U V ≫ smallSwap U V =
      SingularMayerVietoris.toSmallLeft V U := by
  apply (CategoryTheory.cancel_mono (SingularMayerVietoris.smallInclusion V U)).mp
  rw [CategoryTheory.Category.assoc, smallSwap_inclusion,
    SingularMayerVietoris.toSmallRight_inclusion, SingularMayerVietoris.toSmallLeft_inclusion]

private theorem Smale.CoverNaturality.intersectionSwap_left {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    FirstHurewicz.singularChainMap (intersectionSwap U V) ≫
        SingularMayerVietoris.intersectionToLeft V U =
      SingularMayerVietoris.intersectionToRight U V := by
  unfold SingularMayerVietoris.intersectionToLeft SingularMayerVietoris.intersectionToRight
  rw [chainMap_comp]
  rfl

private theorem Smale.CoverNaturality.intersectionSwap_right {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    FirstHurewicz.singularChainMap (intersectionSwap U V) ≫
        SingularMayerVietoris.intersectionToRight V U =
      SingularMayerVietoris.intersectionToLeft U V := by
  unfold SingularMayerVietoris.intersectionToLeft SingularMayerVietoris.intersectionToRight
  rw [chainMap_comp]
  rfl

private def Smale.CoverNaturality.chainSequenceSwap {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularMayerVietoris.chainSequence U V ⟶ SingularMayerVietoris.chainSequence V U
    where
  τ₁ := -FirstHurewicz.singularChainMap (intersectionSwap U V)
  τ₂ :=
    CategoryTheory.Limits.biprod.lift CategoryTheory.Limits.biprod.snd
      CategoryTheory.Limits.biprod.fst
  τ₃ := smallSwap U V
  comm₁₂ := by
    dsimp only [SingularMayerVietoris.chainSequence, SingularMayerVietoris.leftMap,
      SingularMayerVietoris.middleComplex]
    apply CategoryTheory.Limits.biprod.hom_ext
    · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_fst,
        CategoryTheory.Limits.biprod.lift_snd, CategoryTheory.Preadditive.neg_comp]
      exact congrArg Neg.neg (intersectionSwap_left U V)
    · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_snd,
        CategoryTheory.Limits.biprod.lift_fst, CategoryTheory.Preadditive.neg_comp,
        CategoryTheory.Preadditive.comp_neg, neg_neg]
      exact intersectionSwap_right U V
  comm₂₃ := by
    dsimp only [SingularMayerVietoris.chainSequence, SingularMayerVietoris.rightMap,
      SingularMayerVietoris.middleComplex]
    apply CategoryTheory.Limits.biprod.hom_ext'
    · simp only [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.comp_add,
        CategoryTheory.Limits.biprod.inl_snd_assoc, CategoryTheory.Limits.biprod.inl_fst_assoc,
        CategoryTheory.Limits.zero_comp, zero_add, CategoryTheory.Limits.biprod.inl_desc_assoc]
      exact (smallSwap_left U V).symm
    · simp only [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.comp_add,
        CategoryTheory.Limits.biprod.inr_snd_assoc, CategoryTheory.Limits.biprod.inr_fst_assoc,
        CategoryTheory.Limits.zero_comp, add_zero, CategoryTheory.Limits.biprod.inr_desc_assoc]
      exact (smallSwap_right U V).symm

private theorem
    Smale.CoverNaturality.smallConnecting_swap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularMayerVietoris.SmallHomology U V (n + 1)) :
    SingularMayerVietoris.smallConnectingMap V U n
        (SingularMayerVietoris.homologyLinearMap (smallSwap U V) (n + 1) a) =
      -SingularMayerVietoris.singularHomologyMap (intersectionSwap U V) n
          (SingularMayerVietoris.smallConnectingMap U V n a) := by
  have h :=
    LinearMap.congr_fun
      (SingularMayerVietoris.connectingMap_naturality
        (SingularMayerVietoris.chainSequence_shortExact U V) (chainSequenceSwap U V)
        (SingularMayerVietoris.chainSequence_shortExact V U) n)
      a
  change
    SingularMayerVietoris.homologyLinearMap
        (-FirstHurewicz.singularChainMap (intersectionSwap U V)) n
        (SingularMayerVietoris.smallConnectingMap U V n a) =
      _ at h
  rw [SingularMayerVietoris.homologyLinearMap_neg] at h
  exact h.symm

private theorem Smale.CoverNaturality.comparison_swap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularMayerVietoris.SmallHomology U V n) :
    SingularMayerVietoris.smallHomologyComparison V U n
        (SingularMayerVietoris.homologyLinearMap (smallSwap U V) n a) =
      SingularMayerVietoris.smallHomologyComparison U V n a := by
  change
    SingularMayerVietoris.homologyLinearMap (SingularMayerVietoris.smallInclusion V U) n
        (SingularMayerVietoris.homologyLinearMap (smallSwap U V) n a) =
      _
  rw [← LinearMap.comp_apply, ← SingularMayerVietoris.homologyLinearMap_comp, smallSwap_inclusion]
  rfl

private theorem Smale.CoverNaturality.connecting_swap {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ) (hc' : V ∪ U = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.connectingHomomorphism V U hV hU hc' n a =
      -SingularMayerVietoris.singularHomologyMap (intersectionSwap U V) n
          (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n a) := by
  obtain ⟨b, hb⟩ := (SingularMayerVietoris.smallHomologyEquiv U V hU hV hc (n + 1)).surjective a
  have hb' : SingularMayerVietoris.smallHomologyComparison U V (n + 1) b = a := hb
  rw [← hb', SingularMayerVietoris.connectingHomomorphism_comparison]
  rw [← comparison_swap U V (n + 1) b, SingularMayerVietoris.connectingHomomorphism_comparison]
  exact smallConnecting_swap U V n b

private def Smale.CoverNaturality.reversingIntersectionMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U V')
    (hV : Set.MapsTo f V U') : C(↥(U ∩ V), ↥(U' ∩ V')) :=
  mapOn f _ _ (fun _ hx => ⟨hV hx.2, hU hx.1⟩)

private theorem
    Smale.CoverNaturality.connecting_reversing_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U V')
    (hfV : Set.MapsTo f V U') (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' n
        (SingularMayerVietoris.singularHomologyMap f (n + 1) a) =
      -SingularMayerVietoris.singularHomologyMap (reversingIntersectionMap U V U' V' f hfU hfV) n
          (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n a) := by
  have hswap : V' ∪ U' = Set.univ := (Set.union_comm V' U').trans hc'
  rw [connecting_swap V' U' hV' hU' hswap hc']
  rw [← connecting_naturality_apply U V V' U' f hfU hfV hU hV hc hV' hU' hswap]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private def Smale.SuspensionReflection.reflect {X : Type} [TopologicalSpace X] :
    C(CuspCentralHomology.Suspension X, CuspCentralHomology.Suspension X)
    where
  toFun :=
    Quotient.lift (fun q => CuspCentralHomology.Suspension.mk (unitInterval.symm q.1) q.2)
      (by
        rintro a b ⟨ht, h0 | h1 | hx⟩
        · apply (CuspCentralHomology.Suspension.mk_eq_mk_iff _ _ _ _).mpr
          refine ⟨congrArg unitInterval.symm ht, Or.inr (Or.inl ?_)⟩
          simp [h0]
        · apply (CuspCentralHomology.Suspension.mk_eq_mk_iff _ _ _ _).mpr
          refine ⟨congrArg unitInterval.symm ht, Or.inl ?_⟩
          simp [h1]
        · exact
            (CuspCentralHomology.Suspension.mk_eq_mk_iff _ _ _ _).mpr
              ⟨congrArg unitInterval.symm ht, Or.inr (Or.inr hx)⟩)
  continuous_toFun :=
    CuspCentralHomology.Suspension.isQuotientMap_mk.continuous_iff.mpr
      (CuspCentralHomology.Suspension.continuous_mk.comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))

private theorem
    Smale.SuspensionReflection.reflect_mk {X : Type} [TopologicalSpace X] (t : (unitInterval))
    (x : X) :
    reflect (CuspCentralHomology.Suspension.mk t x) =
      CuspCentralHomology.Suspension.mk (unitInterval.symm t) x :=
  rfl

private theorem Smale.SuspensionReflection.reflect_height {X : Type} [TopologicalSpace X]
    (x : CuspCentralHomology.Suspension X) :
    CuspCentralHomology.Suspension.height (reflect x) =
      unitInterval.symm (CuspCentralHomology.Suspension.height x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := CuspCentralHomology.Suspension.mk_surjective x
  rfl

private theorem Smale.SuspensionReflection.reflect_north {X : Type} [TopologicalSpace X] :
    Set.MapsTo (reflect (X := X)) CuspCentralHomology.Suspension.northOpen
      CuspCentralHomology.Suspension.southOpen := by
  intro x hx
  change (CuspCentralHomology.Suspension.height x : ℝ) < 3 / 4 at hx
  change 1 / 4 < (CuspCentralHomology.Suspension.height (reflect x) : ℝ)
  rw [reflect_height, unitInterval.coe_symm_eq]
  linarith

private theorem Smale.SuspensionReflection.reflect_south {X : Type} [TopologicalSpace X] :
    Set.MapsTo (reflect (X := X)) CuspCentralHomology.Suspension.southOpen
      CuspCentralHomology.Suspension.northOpen := by
  intro x hx
  change 1 / 4 < (CuspCentralHomology.Suspension.height x : ℝ) at hx
  change (CuspCentralHomology.Suspension.height (reflect x) : ℝ) < 3 / 4
  rw [reflect_height, unitInterval.coe_symm_eq]
  linarith

private def Smale.SuspensionReflection.middleMap {X : Type} [TopologicalSpace X] :
    C(CuspCentralHomology.Suspension.middleBand X, CuspCentralHomology.Suspension.middleBand X) :=
  Smale.CoverNaturality.reversingIntersectionMap _ _ _ _ reflect reflect_north reflect_south

private theorem Smale.SuspensionReflection.middle_projection {X : Type} [TopologicalSpace X]
    (x : CuspCentralHomology.Suspension.middleBand X) :
    CuspCentralHomology.Suspension.middleBandHomotopyEquiv (middleMap x) =
      CuspCentralHomology.Suspension.middleBandHomotopyEquiv x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := CuspCentralHomology.Suspension.middleBandHomeomorph.symm.surjective x
  let q : Set.Ioo (1 / 4 : ℝ) (3 / 4) × X :=
    (⟨1 - (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩, u)
  have hpoint :
    middleMap (CuspCentralHomology.Suspension.middleBandHomeomorph.symm (t, u)) =
      CuspCentralHomology.Suspension.middleBandHomeomorph.symm q := by
    apply Subtype.ext
    change reflect (CuspCentralHomology.Suspension.mk _ u) = CuspCentralHomology.Suspension.mk _ u
    rw [reflect_mk]
    congr 1
  rw [hpoint, CuspCentralHomology.Suspension.middleBandHomotopyEquiv_apply,
    CuspCentralHomology.Suspension.middleBandHomotopyEquiv_apply, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

private theorem Smale.SuspensionReflection.middle_projection_comp {X : Type} [TopologicalSpace X] :
    (CuspCentralHomology.Suspension.middleBandHomotopyEquiv (X := X)).toFun.comp middleMap =
      (CuspCentralHomology.Suspension.middleBandHomotopyEquiv (X := X)).toFun :=
  ContinuousMap.ext middle_projection

private noncomputable def NoExotic.hyperplaneReflectionOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) : E →L[ℝ] E :=
  ((ℝ ∙ v)ᗮ.reflection).toContinuousLinearEquiv.toContinuousLinearMap

private theorem NoExotic.hyperplaneReflectionOperator_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) :
    hyperplaneReflectionOperator v w = w - (2 * (‖v‖ ^ 2)⁻¹ * Inner.inner ℝ v w) • v := by
  change (ℝ ∙ v)ᗮ.reflection w = _
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub, two_smul]
  rw [← add_smul]
  apply congrArg (fun r : ℝ ↦ w - r • v)
  simp only [div_eq_mul_inv]
  ring

private def Smale.SphereReflection.linearReflection (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  (ℝ ∙ EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))ᗮ.reflection

private theorem Smale.SphereReflection.linearReflection_apply (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 2))) :
    linearReflection n y = y - (2 * y 0) • EuclideanSpace.single 0 (1 : ℝ) := by
  change NoExotic.hyperplaneReflectionOperator (EuclideanSpace.single 0 (1 : ℝ)) y = _
  rw [NoExotic.hyperplaneReflectionOperator_apply]
  simp only [PiLp.norm_single, NormOneClass.norm_one, one_pow, inv_one, mul_one,
    EuclideanSpace.inner_single_left, map_one, one_mul]

private theorem Smale.SphereReflection.linearReflection_zero (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 2))) : linearReflection n y 0 = -y 0 := by
  rw [linearReflection_apply]
  change y 0 - (2 * y 0) * (EuclideanSpace.single 0 (1 : ℝ)) 0 = _
  simp
  ring

private theorem
    Smale.SphereReflection.linearReflection_succ (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 1)) : linearReflection n y i.succ = y i.succ := by
  rw [linearReflection_apply]
  change y i.succ - (2 * y 0) * (EuclideanSpace.single 0 (1 : ℝ)) i.succ = _
  simp

private theorem Smale.SphereReflection.linearReflection_det (n : ℕ) :
    (linearReflection n).toLinearMap.det = -1 := by
  have hv : (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)) ≠ 0 := by simp
  change
    LinearMap.det
        ((ℝ ∙ EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))ᗮ.reflection).toLinearMap =
      _
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hv,
    pow_one]

private def Smale.SphereReflection.sphereMap (n : ℕ) :
    C(SphereHomology.UnitSphere (n + 1), SphereHomology.UnitSphere (n + 1))
    where
  toFun
    x :=
    ⟨linearReflection n x.val, by
      rw [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map,
        SphereHomology.unitSphere_norm]⟩
  continuous_toFun := ((linearReflection n).continuous.comp continuous_subtype_val).subtype_mk _

private theorem Smale.SphereReflection.height_symm (t : (unitInterval)) :
    SphereHomology.Latitude.height (unitInterval.symm t) = -SphereHomology.Latitude.height t := by
  simp only [SphereHomology.Latitude.height, unitInterval.coe_symm_eq]
  ring

private theorem Smale.SphereReflection.radius_symm (t : (unitInterval)) :
    SphereHomology.Latitude.radius (unitInterval.symm t) = SphereHomology.Latitude.radius t := by
  simp only [SphereHomology.Latitude.radius, height_symm, neg_sq]

private theorem Smale.SphereReflection.sphereMap_latitude (n : ℕ) (t : (unitInterval))
    (x : SphereHomology.UnitSphere n) :
    sphereMap n (SphereHomology.Latitude.point n t x) =
      SphereHomology.Latitude.point n (unitInterval.symm t) x := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change
      linearReflection n (SphereHomology.Latitude.vector n t x) 0 =
        SphereHomology.Latitude.vector n (unitInterval.symm t) x 0
    rw [linearReflection_zero, SphereHomology.Latitude.vector_zero,
      SphereHomology.Latitude.vector_zero, height_symm]
  · change
      linearReflection n (SphereHomology.Latitude.vector n t x) j.succ =
        SphereHomology.Latitude.vector n (unitInterval.symm t) x j.succ
    rw [linearReflection_succ, SphereHomology.Latitude.vector_succ,
      SphereHomology.Latitude.vector_succ, radius_symm]

private theorem Smale.SphereReflection.sphereMap_suspension (n : ℕ)
    (x : CuspCentralHomology.Suspension (SphereHomology.UnitSphere n)) :
    sphereMap n (SphereHomology.suspensionSphereHomeomorph n x) =
      SphereHomology.suspensionSphereHomeomorph n (Smale.SuspensionReflection.reflect x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := CuspCentralHomology.Suspension.mk_surjective x
  rw [SphereHomology.suspensionSphereHomeomorph_mk, sphereMap_latitude,
    Smale.SuspensionReflection.reflect_mk, SphereHomology.suspensionSphereHomeomorph_mk]

private theorem Smale.SphereReflection.sphereMap_comp_suspension (n : ℕ) :
    (sphereMap n).comp (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun =
      (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun.comp
        Smale.SuspensionReflection.reflect :=
  ContinuousMap.ext (sphereMap_suspension n)

private theorem Smale.SuspensionReflection.middle_homology {X : Type} [TopologicalSpace X] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (CuspCentralHomology.Suspension.middleBand X) k) :
    SingularMayerVietoris.singularHomologyMap middleMap k a = a := by
  apply
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        CuspCentralHomology.Suspension.middleBandHomotopyEquiv k).injective
  change
    SingularMayerVietoris.singularHomologyMap
        CuspCentralHomology.Suspension.middleBandHomotopyEquiv.toFun k
        (SingularMayerVietoris.singularHomologyMap middleMap k a) =
      SingularMayerVietoris.singularHomologyMap
        CuspCentralHomology.Suspension.middleBandHomotopyEquiv.toFun k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    middle_projection_comp]

private theorem
    Smale.SuspensionReflection.reflect_homology {X : Type} [TopologicalSpace X] [Nonempty X]
    (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (CuspCentralHomology.Suspension X) (n + 1)) :
    SingularMayerVietoris.singularHomologyMap reflect (n + 1) a = -a := by
  apply
    CuspCentralHomology.contractibleCoverConnecting_injective
      CuspCentralHomology.Suspension.northOpen CuspCentralHomology.Suspension.southOpen
      CuspCentralHomology.Suspension.northOpen_isOpen
      CuspCentralHomology.Suspension.southOpen_isOpen CuspCentralHomology.Suspension.open_cover n
  rw [Smale.CoverNaturality.connecting_reversing_naturality
      CuspCentralHomology.Suspension.northOpen CuspCentralHomology.Suspension.southOpen
      CuspCentralHomology.Suspension.northOpen CuspCentralHomology.Suspension.southOpen reflect
      reflect_north reflect_south CuspCentralHomology.Suspension.northOpen_isOpen
      CuspCentralHomology.Suspension.southOpen_isOpen CuspCentralHomology.Suspension.open_cover
      CuspCentralHomology.Suspension.northOpen_isOpen
      CuspCentralHomology.Suspension.southOpen_isOpen CuspCentralHomology.Suspension.open_cover n
      a]
  change
    -SingularMayerVietoris.singularHomologyMap middleMap n
          (SingularMayerVietoris.connectingHomomorphism _ _ _ _ _ n a) =
      _
  rw [middle_homology, map_neg]

private theorem Smale.SphereReflection.sphereMap_homology (n k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap n) (k + 1) a = -a := by
  obtain ⟨b, rfl⟩ :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv (k + 1)).surjective
      a
  change
    SingularMayerVietoris.singularHomologyMap (sphereMap n) (k + 1)
        (SingularMayerVietoris.singularHomologyMap
          (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun (k + 1) b) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    sphereMap_comp_suspension, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, Smale.SuspensionReflection.reflect_homology, map_neg]
  rfl

private theorem Smale.LinearSphereAction.sphereMap_reflection (n : ℕ) :
    sphereMap
        (Smale.SphereReflection.linearReflection n).toContinuousLinearEquiv.toContinuousLinearMap
        (Smale.SphereReflection.linearReflection n).injective =
      Smale.SphereReflection.sphereMap n := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    ‖Smale.SphereReflection.linearReflection n x.val‖⁻¹ •
        Smale.SphereReflection.linearReflection n x.val =
      Smale.SphereReflection.linearReflection n x.val
  rw [LinearIsometryEquiv.norm_map, SphereHomology.unitSphere_norm, inv_one, one_smul]

private theorem Smale.LinearSphereAction.homology_of_det_pos (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (h : 0 < A.toLinearEquiv.toLinearMap.det) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective) k
        a =
      a := by
  have hh :=
    homotopic_of_det_mul_pos (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).toBasis A
      (ContinuousLinearEquiv.refl ℝ _)
      (by
        change 0 < A.toLinearEquiv.toLinearMap.det * (LinearMap.id : _ →ₗ[ℝ] _).det
        rwa [LinearMap.det_id, mul_one])
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hh k]
  change
    SingularMayerVietoris.singularHomologyMap
        (sphereMap (ContinuousLinearMap.id ℝ _) Function.injective_id) k a =
      a
  rw [sphereMap_id, PeriodTorusHigherHomology.singularHomologyMap_id]
  rfl

private theorem Smale.LinearSphereAction.homology_of_det_neg (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (h : A.toLinearEquiv.toLinearMap.det < 0) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      -a := by
  have hh :=
    homotopic_of_det_mul_pos (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).toBasis A
      (Smale.SphereReflection.linearReflection n).toContinuousLinearEquiv
      (by
        change
          0 <
            A.toLinearEquiv.toLinearMap.det *
              (Smale.SphereReflection.linearReflection n).toLinearMap.det
        rw [Smale.SphereReflection.linearReflection_det, mul_neg_one]
        exact neg_pos.mpr h)
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hh (k + 1), sphereMap_reflection,
    Smale.SphereReflection.sphereMap_homology]

private theorem Smale.LinearSphereAction.homology_eq_sign_smul (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2))) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      (SignType.sign A.toLinearEquiv.toLinearMap.det : ℤ) • a := by
  have hd : A.toLinearEquiv.toLinearMap.det ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  obtain hn | hp := lt_or_gt_of_ne hd
  · rw [homology_of_det_neg n A hn, sign_eq_neg_one_iff.mpr hn]
    simp
  · rw [homology_of_det_pos n A hp, sign_eq_one_iff.mpr hp]
    simp

private def
    Smale.SpherePoint.sphereHomeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : V ≃ₗᵢ[ℝ] V) : Metric.sphere (0 : V) 1 ≃ₜ Metric.sphere (0 : V) 1 :=
  R.toContinuousLinearEquiv.toHomeomorph.subtype
    (fun x => by
      simp only [mem_sphere_zero_iff_norm]
      change ‖x‖ = 1 ↔ ‖R x‖ = 1
      rw [R.norm_map])

private theorem Smale.SpherePoint.sphereHomeomorph_eq_normalized {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (R : V ≃ₗᵢ[ℝ] V) :
    (sphereHomeomorph R).toHomotopyEquiv.toFun =
      Smale.LinearSphereAction.sphereMap R.toContinuousLinearEquiv.toContinuousLinearMap
        R.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change R x.val = ‖R x.val‖⁻¹ • R x.val
  rw [R.norm_map, mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

private theorem Smale.SpherePoint.contMDiff_sphereHomeomorph {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (R : V ≃ₗᵢ[ℝ] V) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereHomeomorph R) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, V) ∞ (fun x : Metric.sphere (0 : V) 1 => R x.val) :=
    R.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff.comp
      (contMDiff_coe_sphere (m := ∞))
  exact h.codRestrict_sphere (n := n) (fun x => (sphereHomeomorph R x).property)

private def
    Smale.SpherePoint.sphereDiffeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (R : V ≃ₗᵢ[ℝ] V) :
    Diffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : V) 1) (Metric.sphere (0 : V) 1) ∞
    where
  toEquiv := (sphereHomeomorph R).toEquiv
  contMDiff_toFun := contMDiff_sphereHomeomorph R
  contMDiff_invFun := contMDiff_sphereHomeomorph R.symm

private theorem Smale.SpherePoint.sphereHomeomorph_homology_of_det_pos (n : ℕ)
    (R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (hR : 0 < R.toLinearMap.det) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap (sphereHomeomorph R).toHomotopyEquiv.toFun k a =
      a := by
  rw [sphereHomeomorph_eq_normalized]
  exact Smale.LinearSphereAction.homology_of_det_pos n R.toContinuousLinearEquiv hR k a

private theorem Smale.SpherePoint.positiveTransport_moves (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) :
    sphereHomeomorph (positiveTransport n v w) v = w :=
  Subtype.ext (positiveTransport_apply n v w)

private theorem Smale.SpherePoint.positiveTransport_homology (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap
        (sphereHomeomorph (positiveTransport n v w)).toHomotopyEquiv.toFun k a =
      a := by
  apply sphereHomeomorph_homology_of_det_pos n _ _ k a
  rw [positiveTransport_det]
  norm_num

private theorem Smale.LocalDegree.NativeNeighborhood.singlePoint_cover {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    { x }ᶜ ∪ openSet x d = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases h : y = x
  · subst y
    exact Or.inr (center_mem_openSet x d)
  · exact Or.inl h

private theorem Smale.LocalDegree.NativeNeighborhood.openSet_contractible {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    ContractibleSpace (openSet x d) := by
  let : ContractibleSpace (Metric.ball (0 : E) d.radius) :=
    (convex_ball (0 : E) d.radius).contractibleSpace ⟨0, by simpa using d.radius_pos⟩
  exact
    (Smale.ChartPuncturedBall.ballHomeomorph
        (Smale.NativeParametrization.centered x).toOpenPartialHomeomorph d.radius
        (closedBall_subset_source x d)).symm.contractibleSpace

private def
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] (k : ℕ) :
    SingularMayerVietoris.SingularHomology M (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv x d)
        k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism { x }ᶜ (openSet x d)
      isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k)

private def
    Smale.LocalDegree.NativeNeighborhood.sphereHomologyEquiv {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] [ContractibleSpace ({ x }ᶜ : Set M)] (k : ℕ) :
    SingularMayerVietoris.SingularHomology M (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) (k + 1) := by
  let : ContractibleSpace (openSet x d) := openSet_contractible x d
  exact
    (CuspCentralHomology.contractibleCoverHomologyHigherEquiv { x }ᶜ (openSet x d)
          isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k).trans
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv x d) (k + 1)).symm

private theorem Smale.NativeParametrization.centered_symm_self {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) :
    (centered (D := E) x).symm x = 0 := by
  have h := (centered (D := E) x).left_inv' (zero_mem_centered_source x)
  rwa [centered_zero] at h

private def Smale.NativeChartTransition.chart {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  ((Smale.NativeParametrization.centered (D := E) x).trans e.toPartialDiffeomorph).trans
    (Smale.NativeParametrization.centered (D := E) y).symm

private theorem Smale.NativeChartTransition.chart_apply {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (u : E) :
    chart x y e u =
      (Smale.NativeParametrization.centered (D := E) y).symm
        (e (Smale.NativeParametrization.centered (D := E) x u)) :=
  rfl

private theorem Smale.NativeChartTransition.zero_mem_source {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) : (0 : E) ∈ (chart x y e).source := by
  change
    (0 ∈ (Smale.NativeParametrization.centered (D := E) x).source ∧
        Smale.NativeParametrization.centered (D := E) x 0 ∈ (Set.univ : Set M)) ∧
      e (Smale.NativeParametrization.centered (D := E) x 0) ∈
        (Smale.NativeParametrization.centered (D := E) y).target
  refine ⟨⟨Smale.NativeParametrization.zero_mem_centered_source x, Set.mem_univ _⟩, ?_⟩
  rw [Smale.NativeParametrization.centered_zero, he]
  exact Smale.NativeParametrization.mem_centered_target y

private theorem Smale.NativeChartTransition.chart_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) : chart x y e (0 : E) = 0 := by
  rw [chart_apply, Smale.NativeParametrization.centered_zero, he,
    Smale.NativeParametrization.centered_symm_self]

private theorem Smale.NativeChartTransition.contDiffAt_chart {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) :
    ContDiffAt ℝ ∞ (chart x y e) (0 : E) :=
  ((chart x y e).contMDiffOn_toFun.contMDiffAt
      ((chart x y e).open_source.mem_nhds (zero_mem_source x y e he))).contDiffAt

private theorem Smale.NativeChartTransition.bijective_derivative {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) :
    Function.Bijective (fderiv ℝ (chart x y e) (0 : E)) := by
  have h := Smale.PartialChart.bijective_mfderiv (chart x y e) (zero_mem_source x y e he)
  rwa [mfderiv_eq_fderiv] at h

private def Smale.NativeChartTransition.linear {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] : E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (fderiv ℝ (chart x y e) (0 : E)).toLinearMap
      (bijective_derivative x y e he)).toContinuousLinearEquiv

private theorem Smale.NativeChartTransition.linear_eq_derivative {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] :
    (linear x y e he).toContinuousLinearMap = fderiv ℝ (chart x y e) (0 : E) :=
  rfl

private theorem Smale.NativeChartTransition.hasFDerivAt_chart {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] :
    HasFDerivAt (chart x y e) (linear x y e he).toContinuousLinearMap 0 := by
  rw [linear_eq_derivative]
  exact ((contDiffAt_chart x y e he).differentiableAt (by simp)).hasFDerivAt

private theorem
    Smale.NativeChartTransition.nonempty_neighborhoodData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] (W : Set M)
    (hW : W ∈ 𝓝 x) :
    Nonempty
      (Smale.LocalDegree.NeighborhoodData
        (((Smale.NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          Smale.NativeParametrization.centered (D := E) x)
        (linear x y e he)
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  let c := Smale.NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := Smale.NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := Smale.NativeParametrization.centered_zero x
  have hc : ContinuousAt c (0 : E) :=
    c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hc0)
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc (hcx.symm ▸ hW))
  exact
    Smale.LocalDegree.nonempty_neighborhoodData_of_contDiffAt (linear x y e he)
      (hasFDerivAt_chart x y e he) (chart_zero x y e he) hs (contDiffAt_chart x y e he)

private theorem Smale.SpherePoint.ambient_chart_hasFDerivAt {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ c.source) :
    HasFDerivAt (fun u => (c u : V)) (fderiv ℝ (fun u => (c u : V)) z) z := by
  have hc : ContDiffOn ℝ ∞ (fun u => (c u : V)) c.source :=
    ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).comp_contMDiffOn c.contMDiffOn_toFun).contDiffOn
  exact ((hc.contDiffAt (c.open_source.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt

private theorem Smale.SpherePoint.chart_transition_eventually_eq {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (fun u : EuclideanSpace ℝ (Fin m) =>
        (Smale.NativeParametrization.centered y
            (Smale.NativeChartTransition.chart x y (sphereDiffeomorph (n := m) R) u) :
          V)) =ᶠ[𝓝 0]
      (fun u : EuclideanSpace ℝ (Fin m) => R (Smale.NativeParametrization.centered x u : V)) := by
  let e := sphereDiffeomorph (n := m) R
  let T := Smale.NativeChartTransition.chart x y e
  have hS := T.open_source.mem_nhds (Smale.NativeChartTransition.zero_mem_source x y e he)
  filter_upwards [hS] with u hu
  have ht :
    e (Smale.NativeParametrization.centered x u) ∈
      (Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin m)) y).target :=
    hu.2
  have h := (Smale.NativeParametrization.centered y).right_inv' ht
  exact congrArg Subtype.val h

private theorem
    Smale.SpherePoint.chart_transition_ambient_derivative {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (fderiv ℝ (fun u => (Smale.NativeParametrization.centered y u : V)) 0).comp
        (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toContinuousLinearMap =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fun u => (Smale.NativeParametrization.centered x u : V)) 0) := by
  let e := sphereDiffeomorph (n := m) R
  let T := Smale.NativeChartTransition.chart x y e
  have hx :=
    ambient_chart_hasFDerivAt (m := m) (Smale.NativeParametrization.centered x)
      (Smale.NativeParametrization.zero_mem_centered_source x)
  have hy :=
    ambient_chart_hasFDerivAt (m := m) (Smale.NativeParametrization.centered y)
      (Smale.NativeParametrization.zero_mem_centered_source y)
  have hyT :
    HasFDerivAt
      (fun u : EuclideanSpace ℝ (Fin m) => (Smale.NativeParametrization.centered y u : V))
      (fderiv ℝ (fun u => (Smale.NativeParametrization.centered y u : V)) 0) (T 0) :=
    (Smale.NativeChartTransition.chart_zero x y e he).symm ▸ hy
  have hchain := hyT.comp 0 (Smale.NativeChartTransition.hasFDerivAt_chart x y e he)
  have hR := R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp 0 hx
  exact hchain.unique (hR.congr_of_eventuallyEq (chart_transition_eventually_eq x y R he))

private theorem Smale.SpherePoint.chart_radial_frame_comp {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y)
            0).comp
        ((ContinuousLinearMap.id ℝ ℝ).prodMap
          (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
              he).toContinuousLinearMap) =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered x)
          0) := by
  apply ContinuousLinearMap.ext
  intro z
  have hD :=
    congrArg (fun A : EuclideanSpace ℝ (Fin m) →L[ℝ] V => A z.2)
      (chart_transition_ambient_derivative x y R he)
  have hcenter :
    R (Smale.NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) =
      (Smale.NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) := by
    rw [Smale.NativeParametrization.centered_zero, Smale.NativeParametrization.centered_zero]
    exact congrArg Subtype.val he
  change
    z.1 • (Smale.NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) +
        (fderiv ℝ (fun u => (Smale.NativeParametrization.centered y u : V)) 0)
          (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he z.2) =
      R
        (z.1 • (Smale.NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) +
          (fderiv ℝ (fun u => (Smale.NativeParametrization.centered x u : V)) 0) z.2)
  rw [map_add, map_smul, hcenter]
  exact
    congrArg
      (fun v : V =>
        z.1 • (Smale.NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) + v)
      hD

private theorem Smale.LinearSphereAction.homology_relative_sign {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) (A B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      (SignType.sign (A.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        SingularMayerVietoris.singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) a := by
  rw [sphereMap_relative A B, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, homology_eq_sign_smul]
  exact map_zsmul _ _ _

private theorem Smale.LocalDegree.BoundaryData.normalized_homology_compare {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (b : Smale.LocalDegree.BoundaryData f L s) (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap k =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) k := by
  change
    SingularMayerVietoris.singularHomologyMap (Smale.PuncturedRadial.toSphere.comp b.map) k = _
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, b.homology_compare, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    Smale.LinearSphereAction.normalized_linearSphereMap]

end Mathoverflow1973

end
