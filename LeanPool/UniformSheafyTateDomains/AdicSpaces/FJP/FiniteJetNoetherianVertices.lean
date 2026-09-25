/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetRings
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCechAcyclicity

/-!
# The comparison vertices 𝓑, 𝓒, 𝓓 are strongly noetherian, hence sheafy

Source: [FJP] Prop 2.1 (verbatim): "Each of ℬ, 𝒞, 𝒟 is a quotient of a finite Tate algebra
over k, so each is strongly noetherian." and Theorem 5.3's proof: "The three comparison
rings are strongly noetherian. Huber's direct sheaf theorem [4, Theorem 2.2] gives the
rational-cover sheaf condition for their structure presheaves."

Strategy (design decision DD5, `plan.md`): everything reduces to `IsStronglyNoetherian K`
(`ExampleLaurentSeries.lean`) through
* the flattening pattern of `ExampleUnitDisc.lean` (`exists_flatten'`, `restrictedGaussEquiv`),
* a surjection `K⟨W,V,Z₁,…,Zₙ⟩ ↠ L⟨Z₁,…,Zₙ⟩` (evaluation `W ↦ Wu, V ↦ Wu⁻¹`, surjective via
  the norm-preserving monomial section — noetherianity passes along surjections; no kernel
  identification needed),
* `DualNumber S` noetherian for noetherian `S` (`JetDualNumberNorm.lean`), with the
  coefficientwise flattening `(DualNumber S)⟨Z⟩ ≅ DualNumber (S⟨Z⟩)`.

The payoff instances feed `isSheafy_of_stronglyNoetherian_828b` exactly as in the unit-disc
example. Note 𝓑 and 𝓓 are non-reduced; the 828b hypothesis bundle does not require reduced
or domain, so it applies ([FJP] Lemma 4.2's "possibly nonreduced" is mirrored here).
-/

@[expose] public section

open Filter Topology

namespace FiniteJet

open RestrictedLaurent

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### Strong noetherianity of the four coefficient rings -/

section MapRestricted

variable {B C : Type*} [NormedCommRing B] [NormedCommRing C]
  [IsUltrametricDist B] [IsUltrametricDist C]

/-- Coefficientwise application of a norm-nonincreasing ring homomorphism to radius-one
restricted multivariate power series. -/
noncomputable def mapRestrictedGauss (m : ℕ) (φ : B →+* C) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    MvPowerSeries.Restricted B (fun _ : Fin m => (1 : ℝ)) →+*
      MvPowerSeries.Restricted C (fun _ : Fin m => (1 : ℝ)) where
  toFun x := ⟨MvPowerSeries.map φ x.1, by
    show MvPowerSeries.IsRestrictedGauss _ _
    have hx : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) x.1 := x.2
    rw [MvPowerSeries.IsRestrictedGauss] at hx ⊢
    refine squeeze_zero (fun t => mul_nonneg (norm_nonneg _) ?_) (fun t => ?_) hx
    · rw [finsupp_prod_one]
      exact zero_le_one
    · rw [MvPowerSeries.coeff_map]
      exact mul_le_mul_of_nonneg_right (hφ _)
        (by rw [finsupp_prod_one]; exact zero_le_one)⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.map φ))
  map_mul' x y := Subtype.ext (map_mul (MvPowerSeries.map φ) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.map φ))
  map_add' x y := Subtype.ext (map_add (MvPowerSeries.map φ) x.1 y.1)

/-- The coefficientwise map is norm-nonincreasing. -/
theorem norm_mapRestrictedGauss_le (m : ℕ) (φ : B →+* C) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (x : MvPowerSeries.Restricted B (fun _ : Fin m => (1 : ℝ))) :
    ‖mapRestrictedGauss m φ hφ x‖ ≤ ‖x‖ := by
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun t => ?_) (norm_nonneg x)
  show ‖MvPowerSeries.coeff t (MvPowerSeries.map φ x.1)‖ * _ ≤ _
  rw [MvPowerSeries.coeff_map]
  calc ‖φ (MvPowerSeries.coeff t x.1)‖ * (t.prod fun _ k => (1 : ℝ) ^ k)
      ≤ ‖MvPowerSeries.coeff t x.1‖ * (t.prod fun _ k => (1 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right (hφ _) (by rw [finsupp_prod_one]; exact zero_le_one)
    _ ≤ ‖x‖ := by
        rw [MvRestricted.norm_eq]
        exact MvPowerSeries.le_gaussNorm _ _ _ (MvRestricted.hasGaussNorm _ x) t

/-- If `φ` admits a norm-nonincreasing set-theoretic section, so does the coefficientwise
map on restricted extensions. -/
theorem mapRestrictedGauss_exists_norm_le (m : ℕ) (φ : B →+* C) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (hsec : ∀ v : C, ∃ u : B, φ u = v ∧ ‖u‖ ≤ ‖v‖)
    (y : MvPowerSeries.Restricted C (fun _ : Fin m => (1 : ℝ))) :
    ∃ x, mapRestrictedGauss m φ hφ x = y ∧ ‖x‖ ≤ ‖y‖ := by
  classical
  set x : MvPowerSeries (Fin m) B :=
    fun t => (hsec (MvPowerSeries.coeff t y.1)).choose with hxdef
  have hxc : ∀ t, MvPowerSeries.coeff t x = (hsec (MvPowerSeries.coeff t y.1)).choose :=
    fun t => rfl
  have hmem : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) x := by
    have hy : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) y.1 := y.2
    unfold MvPowerSeries.IsRestrictedGauss at hy ⊢
    refine squeeze_zero (fun t => mul_nonneg (norm_nonneg _) ?_) (fun t => ?_) hy
    · rw [finsupp_prod_one]
      exact zero_le_one
    · rw [hxc]
      exact mul_le_mul_of_nonneg_right (hsec _).choose_spec.2
        (by rw [finsupp_prod_one]; exact zero_le_one)
  refine ⟨⟨x, hmem⟩, Subtype.ext ?_, ?_⟩
  · show MvPowerSeries.map φ x = y.1
    ext t
    rw [MvPowerSeries.coeff_map, hxc, (hsec _).choose_spec.1]
  · rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun t => ?_) (norm_nonneg y)
    show ‖MvPowerSeries.coeff t x‖ * _ ≤ _
    calc ‖MvPowerSeries.coeff t x‖ * (t.prod fun _ k => (1 : ℝ) ^ k)
        ≤ ‖MvPowerSeries.coeff t y.1‖ * (t.prod fun _ k => (1 : ℝ) ^ k) := by
          rw [hxc]
          exact mul_le_mul_of_nonneg_right (hsec _).choose_spec.2
            (by rw [finsupp_prod_one]; exact zero_le_one)
      _ ≤ ‖y‖ := by
          rw [MvRestricted.norm_eq]
          exact MvPowerSeries.le_gaussNorm _ _ _ (MvRestricted.hasGaussNorm _ y) t

/-- If `φ` admits a norm-nonincreasing set-theoretic section, the coefficientwise map on
restricted extensions is surjective. -/
theorem mapRestrictedGauss_surjective (m : ℕ) (φ : B →+* C) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (hsec : ∀ v : C, ∃ u : B, φ u = v ∧ ‖u‖ ≤ ‖v‖) :
    Function.Surjective (mapRestrictedGauss m φ hφ) := fun y =>
  let ⟨x, hx, _⟩ := mapRestrictedGauss_exists_norm_le m φ hφ hsec y
  ⟨x, hx⟩

end MapRestricted

/-- Restricted extensions of the Laurent ring are noetherian: `L⟨Z₁,…,Zₘ⟩` is a quotient of
the noetherian `K⟨W,V,Z₁,…,Zₘ⟩` ([FJP] Prop 2.1; the presentation `L = k⟨W,V⟩/(WV−1)`).
The surjection is `evalHom` applied coefficientwise (with its norm-nonincreasing monomial
section), and `K⟨W,V,Z₁,…,Zₘ⟩` is flattened onto `K⟨(m+2) variables⟩` by two applications of
the unit-disc flattening isometry. -/
theorem isNoetherianRing_restricted_L (m : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesSubring m (L F)) := by
  classical
  -- flattening: `(K⟨W⟩)⟨V⟩ ≅ K⟨W,V⟩`
  obtain ⟨e1, he1⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) 1
  -- flattening: `K⟨W,V⟩⟨Z₁,…,Zₘ⟩ ≅ (K⟨W⟩)⟨Z₀,…,Zₘ⟩`
  obtain ⟨e2, -⟩ := UnitDiscExample.exists_flatten'
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ)))
    (MvPowerSeries.Restricted K (fun _ : Fin 2 => (1 : ℝ)))
    e1.symm
    (fun x => by
      have h := he1 (e1.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) m
  -- flattening: `(K⟨W⟩)⟨Z₀,…,Zₘ⟩ ≅ K⟨(m+2) variables⟩`
  obtain ⟨e3, -⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) (m + 1)
  haveI hK : IsNoetherianRing (restrictedMvPowerSeriesSubring (m + 2) K) :=
    IsStronglyNoetherian.isNoetherianRing_restricted (m + 2)
  refine isNoetherianRing_of_surjective (restrictedMvPowerSeriesSubring (m + 2) K) _
    (((UnitDiscExample.restrictedGaussEquiv (L F) m).toRingHom).comp
      ((mapRestrictedGauss m (evalHom (R := K)) (evalHom_norm_le (R := K))).comp
        (((UnitDiscExample.restrictedGaussEquiv K (m + 2)).symm.trans
          (e3.symm.trans e2.symm)).toRingHom))) ?_
  rw [RingHom.coe_comp, RingHom.coe_comp]
  exact (RingEquiv.surjective _).comp
    ((mapRestrictedGauss_surjective m (evalHom (R := K)) (evalHom_norm_le (R := K))
      (evalHom_exists_norm_le (R := K))).comp (RingEquiv.surjective _))

/-- `L = K⟨W,W⁻¹⟩` is strongly noetherian. -/
instance : IsStronglyNoetherian (L F) :=
  ⟨isNoetherianRing_restricted_L F⟩

instance : IsNoetherianRing (L F) := IsStronglyNoetherian.isNoetherianRing (L F)

/-- Univariate restricted extensions of a strongly noetherian base are noetherian:
`R⟨Q⟩⟨Z₁,…,Zₘ⟩ ≅ R⟨Q,Z₁,…,Zₘ⟩` (the unit-disc flattening pattern over a generic base). -/
theorem isNoetherianRing_restricted_univariate (R : Type*) [NormedCommRing R]
    [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsStronglyNoetherian R]
    (m : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesSubring m (PowerSeries.Restricted R (1 : ℝ))) := by
  obtain ⟨e₂, -⟩ := UnitDiscExample.exists_flatten' R (PowerSeries.Restricted R (1 : ℝ))
    (innerToSeries (R := R)).symm (innerToSeries_symm_norm (R := R)) m
  haveI h : IsNoetherianRing (restrictedMvPowerSeriesSubring (m + 1) R) :=
    IsStronglyNoetherian.isNoetherianRing_restricted (m + 1)
  exact isNoetherianRing_of_surjective (restrictedMvPowerSeriesSubring (m + 1) R) _
    (((UnitDiscExample.restrictedGaussEquiv R (m + 1)).symm.trans e₂.symm).trans
      (UnitDiscExample.restrictedGaussEquiv (PowerSeries.Restricted R (1 : ℝ)) m)).toRingHom
    (RingEquiv.surjective _)

/-- `𝒞 = L⟨Q⟩` is strongly noetherian (flattening `𝒞⟨Z₁,…,Zₘ⟩ ≅ L⟨Q,Z₁,…,Zₘ⟩`, exactly the
unit-disc pattern over the base `L`). -/
instance : IsStronglyNoetherian (JetC F) :=
  ⟨fun m => isNoetherianRing_restricted_univariate (L F) m⟩

instance : IsNoetherianRing (JetC F) := IsStronglyNoetherian.isNoetherianRing (JetC F)

section DualFlatten

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S]

/-- `ε` as a constant restricted series over the dual numbers. -/
noncomputable def epsRestricted (m : ℕ) :
    MvPowerSeries.Restricted (DualNumber S) (fun _ : Fin m => (1 : ℝ)) :=
  ⟨MvPowerSeries.C (σ := Fin m) (R := DualNumber S) DualNumber.eps, by
    show MvPowerSeries.IsRestrictedGauss _ _
    rw [MvPowerSeries.IsRestrictedGauss]
    refine tendsto_nhds_of_eventually_eq ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (0 : Fin m →₀ ℕ)).subset fun t ht => ?_
    rw [Set.mem_setOf_eq] at ht
    by_contra hmem
    rw [Set.mem_singleton_iff] at hmem
    refine ht ?_
    rw [MvPowerSeries.coeff_C, if_neg hmem, norm_zero, zero_mul]⟩

/-- The constant-jet component series of a restricted series over dual numbers. -/
noncomputable def fstRestricted (m : ℕ)
    (y : MvPowerSeries.Restricted (DualNumber S) (fun _ : Fin m => (1 : ℝ))) :
    MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ)) :=
  ⟨fun t => (MvPowerSeries.coeff t y.1).fst, by
    show MvPowerSeries.IsRestrictedGauss _ _
    have hy : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) y.1 := y.2
    unfold MvPowerSeries.IsRestrictedGauss at hy ⊢
    refine squeeze_zero (fun t => mul_nonneg (norm_nonneg _)
      (by rw [finsupp_prod_one]; exact zero_le_one)) (fun t => ?_) hy
    refine mul_le_mul_of_nonneg_right ?_ (by rw [finsupp_prod_one]; exact zero_le_one)
    show ‖(MvPowerSeries.coeff t y.1).fst‖ ≤ ‖MvPowerSeries.coeff t y.1‖
    rw [JetNorm.norm_def]
    exact le_max_left _ _⟩

/-- The `ε`-jet component series of a restricted series over dual numbers. -/
noncomputable def sndRestricted (m : ℕ)
    (y : MvPowerSeries.Restricted (DualNumber S) (fun _ : Fin m => (1 : ℝ))) :
    MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ)) :=
  ⟨fun t => (MvPowerSeries.coeff t y.1).snd, by
    show MvPowerSeries.IsRestrictedGauss _ _
    have hy : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) y.1 := y.2
    unfold MvPowerSeries.IsRestrictedGauss at hy ⊢
    refine squeeze_zero (fun t => mul_nonneg (norm_nonneg _)
      (by rw [finsupp_prod_one]; exact zero_le_one)) (fun t => ?_) hy
    refine mul_le_mul_of_nonneg_right ?_ (by rw [finsupp_prod_one]; exact zero_le_one)
    show ‖(MvPowerSeries.coeff t y.1).snd‖ ≤ ‖MvPowerSeries.coeff t y.1‖
    rw [JetNorm.norm_def]
    exact le_max_right _ _⟩

end DualFlatten

/-- Jet flattening: restricted extension commutes with dual numbers,
`(DualNumber S)⟨Z₁,…,Zₘ⟩ ≅ DualNumber (S⟨Z₁,…,Zₘ⟩)` coefficientwise. Realised as a
surjection from the polynomial ring in `ε` over `S⟨Z₁,…,Zₘ⟩` (Hilbert basis), mirroring
`JetNorm.isNoetherianRing`. -/
theorem isNoetherianRing_restricted_dualNumber
    (S : Type*) [NormedCommRing S] [IsUltrametricDist S]
    (hS : ∀ m : ℕ, IsNoetherianRing (restrictedMvPowerSeriesSubring m S)) (m : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesSubring m (DualNumber S)) := by
  classical
  haveI hA : IsNoetherianRing (MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ))) := by
    haveI := hS m
    exact isNoetherianRing_of_surjective (restrictedMvPowerSeriesSubring m S) _
      (UnitDiscExample.restrictedGaussEquiv S m).symm.toRingHom (RingEquiv.surjective _)
  refine isNoetherianRing_of_surjective
    (Polynomial (MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ)))) _
    ((UnitDiscExample.restrictedGaussEquiv (DualNumber S) m).toRingHom.comp
      (Polynomial.eval₂RingHom
        (mapRestrictedGauss m (TrivSqZeroExt.inlHom S S)
          (fun x => le_of_eq (JetNorm.norm_inl x)))
        (epsRestricted m))) ?_
  rw [RingHom.coe_comp]
  refine (RingEquiv.surjective _).comp ?_
  intro y
  refine ⟨Polynomial.C (fstRestricted m y) + Polynomial.C (sndRestricted m y) * Polynomial.X,
    ?_⟩
  rw [map_add, map_mul]
  simp only [Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X]
  refine Subtype.ext ?_
  show MvPowerSeries.map (TrivSqZeroExt.inlHom S S) (fstRestricted m y).1 +
      MvPowerSeries.map (TrivSqZeroExt.inlHom S S) (sndRestricted m y).1 *
        MvPowerSeries.C (σ := Fin m) (R := DualNumber S) DualNumber.eps = y.1
  refine MvPowerSeries.ext fun t => ?_
  rw [map_add, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
  show TrivSqZeroExt.inl ((MvPowerSeries.coeff t y.1).fst) +
      TrivSqZeroExt.inl ((MvPowerSeries.coeff t y.1).snd) * DualNumber.eps =
      MvPowerSeries.coeff t y.1
  rw [show (DualNumber.eps : DualNumber S) = TrivSqZeroExt.inr 1 from rfl,
    TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one, TrivSqZeroExt.inl_fst_add_inr_snd_eq]

/-- `𝓑 = K⟨W⟩[Q]/(Q²)` is strongly noetherian ([FJP] Prop 2.1). -/
instance : IsStronglyNoetherian (JetB F) :=
  ⟨fun m => isNoetherianRing_restricted_dualNumber (PowerSeries.Restricted K (1 : ℝ))
    (fun j => isNoetherianRing_restricted_univariate K j) m⟩

instance : IsNoetherianRing (JetB F) := IsStronglyNoetherian.isNoetherianRing (JetB F)

/-- `𝓓 = L[Q]/(Q²)` is strongly noetherian ([FJP] Prop 2.1). -/
instance : IsStronglyNoetherian (JetD F) :=
  ⟨fun m => isNoetherianRing_restricted_dualNumber (L F)
    (fun j => isNoetherianRing_restricted_L F j) m⟩

instance : IsNoetherianRing (JetD F) := IsStronglyNoetherian.isNoetherianRing (JetD F)

/-! ### Noetherian unit-ball pods (inputs to the graph–Koszul layer)

[FJP] Lemma 4.2 constructs a noetherian ring of definition for each affinoid vertex; in our
concrete models these are the unit balls: `DualNumber (k°⟨W⟩)`, `L₀⟨Q⟩`, `DualNumber L₀`. -/

section BallTransfer

variable {A B : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormOneClass A]
  [NormedCommRing B] [IsUltrametricDist B] [NormOneClass B]

/-- Noetherianity of unit balls transfers along norm-nonincreasing ring homomorphisms with
norm-nonincreasing set-theoretic sections. -/
theorem isNoetherianRing_unitBall_of_section (f : A →+* B) (hf : ∀ x, ‖f x‖ ≤ ‖x‖)
    (hsec : ∀ y : B, ∃ x : A, f x = y ∧ ‖x‖ ≤ ‖y‖)
    (h : IsNoetherianRing (unitBall A)) : IsNoetherianRing (unitBall B) := by
  haveI := h
  refine isNoetherianRing_of_surjective (unitBall A) _
    (RingHom.codRestrict (f.comp (unitBall A).subtype) (unitBall B)
      (fun x => (hf x.1).trans x.2)) ?_
  rintro ⟨y, hy⟩
  obtain ⟨x, hfx, hx⟩ := hsec y
  exact ⟨⟨x, hx.trans hy⟩, Subtype.ext hfx⟩

/-- Noetherianity of unit balls transfers along isometric ring equivalences. -/
theorem isNoetherianRing_unitBall_of_isometry (e : A ≃+* B) (he : ∀ x, ‖e x‖ = ‖x‖)
    (h : IsNoetherianRing (unitBall A)) : IsNoetherianRing (unitBall B) :=
  isNoetherianRing_unitBall_of_section e.toRingHom (fun x => (he x).le)
    (fun y => ⟨e.symm y, e.apply_symm_apply y, by
      have hs := he (e.symm y)
      rw [RingEquiv.apply_symm_apply] at hs
      exact hs.ge⟩) h

end BallTransfer

/-- **The Gauss unit ball of `K⟨T₁,…,Tₖ⟩` is noetherian**: the integral restricted series
are exactly the transpose images of the noetherian `(MvPolynomial (Fin k) F)⟦X⟧`
([FJP] Lemma 4.2: noetherian rings of definition). -/
theorem isNoetherianRing_unitBall_gaussK (k : ℕ) :
    IsNoetherianRing (unitBall (MvPowerSeries.Restricted K (fun _ : Fin k => (1 : ℝ)))) := by
  classical
  refine isNoetherianRing_of_surjective (PowerSeries (MvPolynomial (Fin k) F)) _
    (RingHom.codRestrict
      (((UnitDiscExample.restrictedGaussEquiv K k).symm.toRingHom).comp
        (LaurentSeriesExample.psiR F k))
      (unitBall _) (fun g => ?_)) ?_
  · -- the transpose image is integral: every coefficient has valuation ≤ 1
    show ‖(UnitDiscExample.restrictedGaussEquiv K k).symm (LaurentSeriesExample.psiR F k g)‖
      ≤ 1
    rw [MvRestricted.norm_eq]
    show MvPowerSeries.gaussNorm _ _ (LaurentSeriesExample.Psi F k g) ≤ 1
    rw [MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun t => ?_) zero_le_one
    rw [finsupp_prod_one, mul_one]
    rw [Valued.toNormedField.norm_le_one_iff]
    have hv := LaurentSeriesExample.psi_coeff_v_le F k g t 0
      (fun m hm => absurd hm (Nat.not_lt_zero m))
    rwa [show (-(0 : ℕ) : ℤ) = 0 by omega, WithZero.exp_zero] at hv
  · -- surjectivity: integral restricted series are transpose images
    rintro ⟨y, hy⟩
    have hyres : MvPowerSeries.IsRestricted y.1 :=
      (UnitDiscExample.isRestrictedGauss_one_iff K k y.1).mp y.2
    have hyint : ∀ t, Valued.v (MvPowerSeries.coeff t y.1) ≤ 1 := fun t => by
      rw [← Valued.toNormedField.norm_le_one_iff]
      have h := MvPowerSeries.le_gaussNorm _ _ _ (MvRestricted.hasGaussNorm _ y) t
      rw [finsupp_prod_one, mul_one] at h
      refine h.trans ?_
      rw [← MvRestricted.norm_eq]
      exact hy
    obtain ⟨g, hg⟩ := LaurentSeriesExample.exists_psi_eq F k y.1 hyres hyint
    exact ⟨g, Subtype.ext (Subtype.ext hg)⟩

/-- `L° = 𝒪_K⟨W,W⁻¹⟩` is noetherian: the `evalHom`-image of the integral `K⟨W,V⟩`
([FJP] Lemma 4.2 for the annulus vertex). -/
theorem isNoetherianRing_unitBall_L : IsNoetherianRing (unitBall (L F)) :=
  isNoetherianRing_unitBall_of_section (evalHom (R := K)) (evalHom_norm_le (R := K))
    (evalHom_exists_norm_le (R := K)) (isNoetherianRing_unitBall_gaussK F 2)

/-- `k°⟨W⟩` (the unit ball of the disc coefficient ring) is noetherian. -/
theorem isNoetherianRing_unitBall_KW :
    IsNoetherianRing (unitBall (PowerSeries.Restricted K (1 : ℝ))) :=
  isNoetherianRing_unitBall_of_isometry (innerToSeries (R := K))
    (innerToSeries_norm (R := K)) (isNoetherianRing_unitBall_gaussK F 1)

section DualBall

variable (S : Type*) [NormedCommRing S] [IsUltrametricDist S] [NormOneClass S]

/-- The unit ball of the dual numbers over `S` is noetherian whenever the unit ball of `S`
is: it is the `ε`-polynomial image of the ball (`(f+Qg)` decomposition on balls). -/
theorem isNoetherianRing_unitBall_dualNumber
    (h : IsNoetherianRing (unitBall S)) : IsNoetherianRing (unitBall (DualNumber S)) := by
  classical
  haveI := h
  have hEmem : (DualNumber.eps : DualNumber S) ∈ unitBall (DualNumber S) := by
    show ‖(DualNumber.eps : DualNumber S)‖ ≤ 1
    rw [JetNorm.norm_def]
    refine max_le ?_ ?_
    · show ‖(TrivSqZeroExt.inr (1 : S) : DualNumber S).fst‖ ≤ 1
      rw [TrivSqZeroExt.fst_inr, norm_zero]
      exact zero_le_one
    · show ‖(TrivSqZeroExt.inr (1 : S) : DualNumber S).snd‖ ≤ 1
      rw [TrivSqZeroExt.snd_inr, norm_one]
  refine isNoetherianRing_of_surjective (Polynomial ↥(unitBall S)) _
    (Polynomial.eval₂RingHom
      (RingHom.codRestrict ((TrivSqZeroExt.inlHom S S).comp (unitBall S).subtype)
        (unitBall (DualNumber S)) (fun x => by
          show ‖(TrivSqZeroExt.inl (x : S) : DualNumber S)‖ ≤ 1
          rw [JetNorm.norm_inl]
          exact x.2))
      ⟨DualNumber.eps, hEmem⟩) ?_
  rintro ⟨y, hy⟩
  have hymax : max ‖y.fst‖ ‖y.snd‖ ≤ 1 := (JetNorm.norm_def y).symm.trans_le hy
  refine ⟨Polynomial.C ⟨y.fst, (le_max_left _ _).trans hymax⟩ +
    Polynomial.C ⟨y.snd, (le_max_right _ _).trans hymax⟩ * Polynomial.X, ?_⟩
  rw [map_add, map_mul]
  simp only [Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X]
  refine Subtype.ext ?_
  show TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inl y.snd * DualNumber.eps = y
  rw [show (DualNumber.eps : DualNumber S) = TrivSqZeroExt.inr 1 from rfl,
    TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one, TrivSqZeroExt.inl_fst_add_inr_snd_eq]

end DualBall

theorem isNoetherianRing_unitBall_JetB : IsNoetherianRing (unitBall (JetB F)) :=
  isNoetherianRing_unitBall_dualNumber (PowerSeries.Restricted K (1 : ℝ))
    (isNoetherianRing_unitBall_KW F)

/-- `𝒞° = L°⟨Q⟩` is noetherian: reached from the integral `K⟨W,V,Q⟩` by the flattening
isometries and the coefficientwise `evalHom`. -/
theorem isNoetherianRing_unitBall_JetC : IsNoetherianRing (unitBall (JetC F)) := by
  obtain ⟨e1, he1⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) 1
  obtain ⟨e2, he2⟩ := UnitDiscExample.exists_flatten'
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ)))
    (MvPowerSeries.Restricted K (fun _ : Fin 2 => (1 : ℝ)))
    e1.symm
    (fun x => by
      have h := he1 (e1.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) 1
  obtain ⟨e3, he3⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) 2
  -- ball of `(K⟨W⟩)⟨Z₀,Z₁⟩` from the integral `K⟨3 vars⟩`
  have h23 := isNoetherianRing_unitBall_of_isometry e3.symm
    (fun x => by
      have h := he3 (e3.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) (isNoetherianRing_unitBall_gaussK F 3)
  -- ball of `K⟨W,V⟩⟨Q⟩`
  have h3 := isNoetherianRing_unitBall_of_isometry e2.symm
    (fun x => by
      have h := he2 (e2.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) h23
  -- ball of `L⟨Q⟩` in `Fin 1` form
  have h4 := isNoetherianRing_unitBall_of_section
    (mapRestrictedGauss 1 (evalHom (R := K)) (evalHom_norm_le (R := K)))
    (norm_mapRestrictedGauss_le 1 (evalHom (R := K)) (evalHom_norm_le (R := K)))
    (mapRestrictedGauss_exists_norm_le 1 (evalHom (R := K)) (evalHom_norm_le (R := K))
      (evalHom_exists_norm_le (R := K))) h3
  exact isNoetherianRing_unitBall_of_isometry (innerToSeries (R := L F))
    (innerToSeries_norm (R := L F)) h4

theorem isNoetherianRing_unitBall_JetD : IsNoetherianRing (unitBall (JetD F)) :=
  isNoetherianRing_unitBall_dualNumber (L F) (isNoetherianRing_unitBall_L F)

/-! ### Arity-`m` unit balls (inputs to the strict-localization layer, [FJP] §4) -/

/-- The unit ball of `L⟨T₁,…,Tₘ⟩` is noetherian (the transfer chain at arity `m`). -/
theorem isNoetherianRing_unitBall_restricted_L (m : ℕ) :
    IsNoetherianRing (unitBall
      (MvPowerSeries.Restricted (L F) (fun _ : Fin m => (1 : ℝ)))) := by
  obtain ⟨e1, he1⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) 1
  obtain ⟨e2, he2⟩ := UnitDiscExample.exists_flatten'
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ)))
    (MvPowerSeries.Restricted K (fun _ : Fin 2 => (1 : ℝ)))
    e1.symm
    (fun x => by
      have h := he1 (e1.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) m
  obtain ⟨e3, he3⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) (m + 1)
  have h23 := isNoetherianRing_unitBall_of_isometry e3.symm
    (fun x => by
      have h := he3 (e3.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) (isNoetherianRing_unitBall_gaussK F (m + 2))
  have h3 := isNoetherianRing_unitBall_of_isometry e2.symm
    (fun x => by
      have h := he2 (e2.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) h23
  exact isNoetherianRing_unitBall_of_section
    (mapRestrictedGauss m (evalHom (R := K)) (evalHom_norm_le (R := K)))
    (norm_mapRestrictedGauss_le m (evalHom (R := K)) (evalHom_norm_le (R := K)))
    (mapRestrictedGauss_exists_norm_le m (evalHom (R := K)) (evalHom_norm_le (R := K))
      (evalHom_exists_norm_le (R := K))) h3

/-- The unit ball of `R⟨Q⟩⟨T₁,…,Tₘ⟩` is noetherian whenever the ball of `R⟨T₀,…,Tₘ⟩` is
(one application of the flattening isometry). -/
theorem isNoetherianRing_unitBall_restricted_univariate (R : Type*) [NormedCommRing R]
    [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] (m : ℕ)
    (hballs : IsNoetherianRing (unitBall
      (MvPowerSeries.Restricted R (fun _ : Fin (m + 1) => (1 : ℝ))))) :
    IsNoetherianRing (unitBall (MvPowerSeries.Restricted (PowerSeries.Restricted R (1 : ℝ))
      (fun _ : Fin m => (1 : ℝ)))) := by
  obtain ⟨e, he⟩ := UnitDiscExample.exists_flatten' R (PowerSeries.Restricted R (1 : ℝ))
    (innerToSeries (R := R)).symm (innerToSeries_symm_norm (R := R)) m
  exact isNoetherianRing_unitBall_of_isometry e.symm
    (fun x => by
      have h := he (e.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) hballs

/-- Ball version of the dual-number flattening: the unit ball of `(DualNumber S)⟨T⃗⟩` is
noetherian whenever the ball of `S⟨T⃗⟩` is (the `ε`-polynomial surjection restricts to
balls). -/
theorem isNoetherianRing_unitBall_restricted_dualNumber
    (S : Type*) [NormedCommRing S] [IsUltrametricDist S] [NormOneClass S] (m : ℕ)
    (h : IsNoetherianRing (unitBall
      (MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ))))) :
    IsNoetherianRing (unitBall
      (MvPowerSeries.Restricted (DualNumber S) (fun _ : Fin m => (1 : ℝ)))) := by
  classical
  haveI := h
  have hcoeffle : ∀ (y : MvPowerSeries.Restricted (DualNumber S) (fun _ : Fin m => (1 : ℝ)))
      (s : Fin m →₀ ℕ), ‖MvPowerSeries.coeff s y.1‖ ≤ ‖y‖ := fun y s => by
    have hb := MvPowerSeries.le_gaussNorm _ _ _ (MvRestricted.hasGaussNorm _ y) s
    rw [finsupp_prod_one, mul_one] at hb
    rw [MvRestricted.norm_eq]
    exact hb
  have hEball : ‖(epsRestricted (S := S) m)‖ ≤ 1 := by
    rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun s => ?_) zero_le_one
    rw [finsupp_prod_one, mul_one]
    show ‖MvPowerSeries.coeff s (MvPowerSeries.C (σ := Fin m) (R := DualNumber S)
      DualNumber.eps)‖ ≤ 1
    rw [MvPowerSeries.coeff_C]
    split
    · rw [JetNorm.norm_def]
      refine max_le ?_ ?_
      · show ‖(TrivSqZeroExt.inr (1 : S) : DualNumber S).fst‖ ≤ 1
        rw [TrivSqZeroExt.fst_inr, norm_zero]
        exact zero_le_one
      · show ‖(TrivSqZeroExt.inr (1 : S) : DualNumber S).snd‖ ≤ 1
        rw [TrivSqZeroExt.snd_inr, norm_one]
    · rw [norm_zero]
      exact zero_le_one
  refine isNoetherianRing_of_surjective
    (Polynomial ↥(unitBall (MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ))))) _
    (Polynomial.eval₂RingHom
      (RingHom.codRestrict ((mapRestrictedGauss m (TrivSqZeroExt.inlHom S S)
          (fun x => le_of_eq (JetNorm.norm_inl x))).comp
        (unitBall (MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ)))).subtype)
        (unitBall _)
        (fun q => (norm_mapRestrictedGauss_le m (TrivSqZeroExt.inlHom S S)
          (fun x => le_of_eq (JetNorm.norm_inl x)) q.1).trans q.2))
      ⟨epsRestricted m, hEball⟩) ?_
  rintro ⟨y, hy⟩
  have hfstball : ‖fstRestricted m y‖ ≤ 1 := by
    rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun s => ?_) zero_le_one
    rw [finsupp_prod_one, mul_one]
    show ‖(MvPowerSeries.coeff s y.1).fst‖ ≤ 1
    refine le_trans (le_trans ?_ (hcoeffle y s)) hy
    rw [JetNorm.norm_def]
    exact le_max_left _ _
  have hsndball : ‖sndRestricted m y‖ ≤ 1 := by
    rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun s => ?_) zero_le_one
    rw [finsupp_prod_one, mul_one]
    show ‖(MvPowerSeries.coeff s y.1).snd‖ ≤ 1
    refine le_trans (le_trans ?_ (hcoeffle y s)) hy
    rw [JetNorm.norm_def]
    exact le_max_right _ _
  refine ⟨Polynomial.C ⟨fstRestricted m y, hfstball⟩ +
    Polynomial.C ⟨sndRestricted m y, hsndball⟩ * Polynomial.X, ?_⟩
  rw [map_add, map_mul]
  simp only [Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X]
  refine Subtype.ext (Subtype.ext ?_)
  show MvPowerSeries.map (TrivSqZeroExt.inlHom S S) (fstRestricted m y).1 +
      MvPowerSeries.map (TrivSqZeroExt.inlHom S S) (sndRestricted m y).1 *
        MvPowerSeries.C (σ := Fin m) (R := DualNumber S) DualNumber.eps = y.1
  refine MvPowerSeries.ext fun t => ?_
  rw [map_add, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
  show TrivSqZeroExt.inl ((MvPowerSeries.coeff t y.1).fst) +
      TrivSqZeroExt.inl ((MvPowerSeries.coeff t y.1).snd) * DualNumber.eps =
      MvPowerSeries.coeff t y.1
  rw [show (DualNumber.eps : DualNumber S) = TrivSqZeroExt.inr 1 from rfl,
    TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one, TrivSqZeroExt.inl_fst_add_inr_snd_eq]

/-! ### The payoff: the three comparison vertices are sheafy

[FJP] Theorem 5.3 (input): "The three comparison rings are strongly noetherian. Huber's
direct sheaf theorem [4, Theorem 2.2] gives the rational-cover sheaf condition for their
structure presheaves."  In the project's vocabulary this is
`isSheafy_of_stronglyNoetherian_828b`, whose hypothesis bundle (`PlusSubring`, `IsTateRing`,
`IsStronglyNoetherian`, `T2Space`, `IsRingOfIntegralElements A⁺`, right-uniformity
completeness) was assembled in `FiniteJetRings.lean` — with the maximal plus rings, which for
𝓑 and 𝓓 are unbounded ([FJP] (2.1d)); no domain/reducedness hypothesis is needed. -/

theorem isSheafy_JetB : ValuationSpectrum.IsSheafy (JetB F) :=
  ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

theorem isSheafy_JetC : ValuationSpectrum.IsSheafy (JetC F) :=
  ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

theorem isSheafy_JetD : ValuationSpectrum.IsSheafy (JetD F) :=
  ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

end FiniteJet
