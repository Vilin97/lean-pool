/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.Palomar.Bridge.Jet

/-!
# The Challenge's Tate algebras are the library's Gauss-restricted rings

The Challenge defines `𝓐⟨X₁, …, Xₙ⟩` as `Completion 𝓐[X₁, …, Xₙ]` for the Gauss norm; the library
works with `P E n = MvPowerSeries.Restricted E (fun _ => 1)`, the Gauss-restricted power series
over a normed ring `E`. For an isometric ring isomorphism `e : E ≃+* E'` with `E'` complete, the
polynomial embedding `E[X] → P E' n` (coefficients mapped by `e`) is an isometry with dense
image, so the completion of `E[X]` is `P E' n`. Applied to `jetAEquiv`, this identifies the
Challenge's `𝓐⟨X₁, …, Xₙ⟩` with the library's `P (JetA K) n`, on which the library proves
sheafiness.

Also here: the Challenge's Tate algebra over a ring with a norm-scaling pseudouniformizer is a
Tate ring (needed to apply the library's transports to it).
-/


noncomputable section

open Filter Topology

namespace PalomarBridge.TateExt

open FiniteJet.GraphKoszul

-- Mathlib's `MvPowerSeries/Evaluation.lean` (imported by the library) carries a *private*
-- instance putting the product uniformity on `MvPolynomial σ R = AddMonoidAlgebra R (σ →₀ ℕ)`.
-- The Challenge's Tate algebra is the completion for the Gauss-norm (metric) uniformity, so
-- within this file we make the metric uniformity the preferred one.
attribute [local instance 1100] PseudoMetricSpace.toUniformSpace

universe u

variable {E E' : Type u} [NormedCommRing E] [IsUltrametricDist E]
  [NormedCommRing E'] [IsUltrametricDist E'] [NormOneClass E'] [CompleteSpace E']
  (e : E ≃+* E') (he : ∀ x, ‖e x‖ = ‖x‖) (n : ℕ)

/-! ### The embedding `E[X₁, …, Xₙ] → P E' n` -/

/-- `ι' : E[X₁, …, Xₙ] →+* E'⟨X₁, …, Xₙ⟩`, applying `e` to the coefficients. -/
def iotaExt : AddMonoidAlgebra E (Fin n →₀ ℕ) →+* P E' n :=
  polyToP.comp (MvPolynomial.map e.toRingHom)

theorem coeff_iotaExt (p : AddMonoidAlgebra E (Fin n →₀ ℕ)) (s : Fin n →₀ ℕ) :
    MvPowerSeries.coeff s (iotaExt e n p).1 = e (p.coeff s) := by
  show MvPowerSeries.coeff s (polyToP (MvPolynomial.map e.toRingHom p)).1 = _
  rw [coeff_polyToP, MvPolynomial.coeff_map]
  rfl

/-- The Gauss norm of `P E' n`, coefficient by coefficient. -/
theorem norm_P_eq (F : P E' n) : ‖F‖ = ⨆ s : Fin n →₀ ℕ, ‖MvPowerSeries.coeff s F.1‖ := by
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  simp [Finsupp.prod]

theorem norm_coeff_le_P (F : P E' n) (s : Fin n →₀ ℕ) : ‖MvPowerSeries.coeff s F.1‖ ≤ ‖F‖ := by
  rw [MvRestricted.norm_eq]
  simpa using MvPowerSeries.le_gaussNorm norm (fun _ : Fin n => (1 : ℝ)) F.1
    (MvRestricted.hasGaussNorm (fun _ : Fin n => (1 : ℝ)) F) s

theorem norm_coeff_le_norm (p : AddMonoidAlgebra E (Fin n →₀ ℕ)) (m : Fin n →₀ ℕ) :
    ‖p.coeff m‖ ≤ ‖p‖ := by
  rw [← coe_nnnorm, ← coe_nnnorm, Palomar.nnnorm_eq_gauss]
  exact_mod_cast Palomar.nnnorm_coeff_le_gauss p m

include he in
theorem norm_iotaExt (p : AddMonoidAlgebra E (Fin n →₀ ℕ)) : ‖iotaExt e n p‖ = ‖p‖ := by
  apply le_antisymm
  · rw [norm_P_eq]
    refine Real.iSup_le (fun s => ?_) (norm_nonneg _)
    rw [coeff_iotaExt, he]
    exact norm_coeff_le_norm n p s
  · by_cases hp : p = 0
    · subst hp; simp
    · have hne : p.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr fun h =>
        hp (AddMonoidAlgebra.coeff_injective (h.trans AddMonoidAlgebra.coeff_zero.symm))
      obtain ⟨m₀, -, hsup⟩ := Finset.exists_mem_eq_sup _ hne fun m => ‖p.coeff m‖₊
      have h0 : ‖p‖ = ‖p.coeff m₀‖ := by
        rw [← coe_nnnorm, Palomar.nnnorm_eq_gauss, Palomar.gauss, hsup, coe_nnnorm]
      rw [h0, ← he, ← coeff_iotaExt e n p m₀]
      exact norm_coeff_le_P n (iotaExt e n p) m₀

/-! ### Density -/

/-- The truncation of `F ∈ E'⟨X⟩` to the exponents `≤ N`, pulled back to `E[X]`. -/
def truncExt (N : Fin n →₀ ℕ) (F : P E' n) : AddMonoidAlgebra E (Fin n →₀ ℕ) :=
  MvPolynomial.map e.symm.toRingHom (MvPowerSeries.trunc' E' N F.1)

theorem coeff_iotaExt_truncExt (N : Fin n →₀ ℕ) (F : P E' n) (s : Fin n →₀ ℕ) :
    MvPowerSeries.coeff s (iotaExt e n (truncExt e n N F)).1 =
      if s ≤ N then MvPowerSeries.coeff s F.1 else 0 := by
  rw [coeff_iotaExt]
  show e (MvPolynomial.coeff s (MvPolynomial.map e.symm.toRingHom
    (MvPowerSeries.trunc' E' N F.1))) = _
  rw [MvPolynomial.coeff_map, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply, MvPowerSeries.coeff_trunc']

/-- Outside a large enough box, all coefficients of `F ∈ E'⟨X⟩` are small. -/
theorem exists_box (F : P E' n) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Fin n →₀ ℕ, ∀ s, ¬ s ≤ N → ‖MvPowerSeries.coeff s F.1‖ < ε := by
  classical
  have h1 : Tendsto (fun s => ‖MvPowerSeries.coeff s F.1‖) cofinite (𝓝 0) := by
    have h0 : MvPowerSeries.IsRestrictedGauss (fun _ : Fin n => (1 : ℝ)) F.1 := F.2
    unfold MvPowerSeries.IsRestrictedGauss at h0
    simpa [Finsupp.prod] using h0
  have hfin : {s : Fin n →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff s F.1‖}.Finite := by
    have := (Metric.tendsto_nhds.mp h1 ε hε)
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun s hs => ?_
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _),
      not_lt] at hs ⊢
    exact hs
  refine ⟨hfin.toFinset.sup id, fun s hs => ?_⟩
  by_contra hle
  push Not at hle
  exact hs (Finset.le_sup (f := id) (hfin.mem_toFinset.mpr hle))

theorem exists_norm_sub_le (F : P E' n) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Fin n →₀ ℕ, ‖F - iotaExt e n (truncExt e n N F)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := exists_box n F hε
  refine ⟨N, ?_⟩
  rw [norm_P_eq n]
  refine Real.iSup_le (fun s => ?_) hε.le
  rw [show (F - iotaExt e n (truncExt e n N F)).1 = F.1 - (iotaExt e n (truncExt e n N F)).1
    from rfl, map_sub, coeff_iotaExt_truncExt]
  split_ifs with h
  · simp [hε.le]
  · rw [sub_zero]; exact (hN s h).le

theorem denseRange_iotaExt : DenseRange (iotaExt e n) := by
  refine Metric.denseRange_iff.mpr fun F ε hε => ?_
  obtain ⟨N, hN⟩ := exists_norm_sub_le e n F (half_pos hε)
  exact ⟨truncExt e n N F, by rw [dist_eq_norm]; exact hN.trans_lt (half_lt_self hε)⟩

include he in
theorem isometry_iotaExt : Isometry (iotaExt e n) :=
  AddMonoidHomClass.isometry_of_norm (iotaExt e n) (norm_iotaExt e he n)

/-! ### The completion of `E[X₁, …, Xₙ]` is `E'⟨X₁, …, Xₙ⟩` -/

include he in
/-- `E'⟨X⟩`, with `ι'`, is an abstract completion of `E[X]`. -/
def pkgExt : AbstractCompletion (AddMonoidAlgebra E (Fin n →₀ ℕ)) where
  space := P E' n
  coe := iotaExt e n
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := (isometry_iotaExt e he n).isUniformInducing
  dense := denseRange_iotaExt e n

include he in
/-- The uniform isomorphism `Completion E[X] ≃ᵤ E'⟨X⟩`. -/
def gaussUniformEquiv : Palomar.TateAlgebra E (Fin n →₀ ℕ) ≃ᵤ P E' n :=
  UniformSpace.Completion.cPkg.compareEquiv (pkgExt e he n)

include he in
/-- **`Completion E[X₁, …, Xₙ] ≃+* E'⟨X₁, …, Xₙ⟩`.** -/
def gaussEquiv : Palomar.TateAlgebra E (Fin n →₀ ℕ) ≃+* P E' n :=
  { UniformSpace.Completion.extensionHom (iotaExt e n) (isometry_iotaExt e he n).continuous with
    invFun := (gaussUniformEquiv e he n).symm
    left_inv := fun x => (gaussUniformEquiv e he n).symm_apply_apply x
    right_inv := fun y => (gaussUniformEquiv e he n).apply_symm_apply y }

include he in
theorem continuous_gaussEquiv : Continuous (gaussEquiv e he n) :=
  UniformSpace.Completion.continuous_extension

include he in
theorem continuous_gaussEquiv_symm : Continuous (gaussEquiv e he n).symm :=
  (gaussUniformEquiv e he n).symm.continuous

/-! ### The Challenge's `R⟨G⟩` is a Tate ring when `R` has a norm-scaling pseudouniformizer -/

section Tate

variable {R : Type u} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]
  {G : Type} [AddCommMonoid G]

theorem nnnorm_mul_of_scale {t : R} (ht : ∀ x, ‖t * x‖ = ‖t‖ * ‖x‖) (x : R) :
    ‖t * x‖₊ = ‖t‖₊ * ‖x‖₊ :=
  NNReal.coe_injective (by push_cast; exact ht x)

theorem gauss_smul_of_scale {t : R} (ht : ∀ x, ‖t * x‖ = ‖t‖ * ‖x‖) (p : AddMonoidAlgebra R G) :
    Palomar.gauss (t • p) = ‖t‖₊ * Palomar.gauss p := by
  apply le_antisymm
  · refine Palomar.gauss_le_iff.mpr fun m => ?_
    rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, nnnorm_mul_of_scale ht]
    gcongr
    exact Palomar.nnnorm_coeff_le_gauss p m
  · by_cases hp : p = 0
    · subst hp; simp [Palomar.gauss]
    have hne : p.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr fun h =>
      hp (AddMonoidAlgebra.coeff_injective (h.trans AddMonoidAlgebra.coeff_zero.symm))
    obtain ⟨m₀, -, hsup⟩ := Finset.exists_mem_eq_sup _ hne fun m => ‖p.coeff m‖₊
    calc ‖t‖₊ * Palomar.gauss p = ‖t‖₊ * ‖p.coeff m₀‖₊ := by rw [Palomar.gauss, hsup]
      _ = ‖(t • p).coeff m₀‖₊ := by
        rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, nnnorm_mul_of_scale ht]
      _ ≤ Palomar.gauss (t • p) := Palomar.nnnorm_coeff_le_gauss _ _

theorem norm_const_mul_of_scale {t : R} (ht : ∀ x, ‖t * x‖ = ‖t‖ * ‖x‖)
    (x : Palomar.TateAlgebra R G) :
    ‖(algebraMap R (AddMonoidAlgebra R G) t : Palomar.TateAlgebra R G) * x‖ = ‖t‖ * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [← UniformSpace.Completion.coe_mul, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, ← Algebra.smul_def, ← coe_nnnorm, ← coe_nnnorm,
      ← coe_nnnorm, Palomar.nnnorm_eq_gauss, Palomar.nnnorm_eq_gauss, gauss_smul_of_scale ht,
      NNReal.coe_mul]

/-- The Tate algebra `R⟨G⟩` over a nonarchimedean normed ring with a norm-scaling unit `t` of
norm `< 1` is a Tate ring: the constant `t` is a scaling pseudouniformizer of `R⟨G⟩`. -/
theorem isTateRing_tateAlgebra (t : R) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (ht : ∀ x, ‖t * x‖ = ‖t‖ * ‖x‖) : Palomar.IsTateRing (Palomar.TateAlgebra R G) := by
  have hnorm : ‖(algebraMap R (AddMonoidAlgebra R G) t : Palomar.TateAlgebra R G)‖ = ‖t‖ := by
    simpa using norm_const_mul_of_scale (G := G) ht 1
  refine Palomar.isTateRing_of_scale (algebraMap R (AddMonoidAlgebra R G) t : Palomar.TateAlgebra R G)
    (htu.map (UniformSpace.Completion.coeRingHom.comp (algebraMap R (AddMonoidAlgebra R G))))
    (hnorm ▸ ht1) (hnorm ▸ ht0) fun x => by rw [norm_const_mul_of_scale ht, hnorm]

end Tate

end PalomarBridge.TateExt
