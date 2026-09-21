/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamWeinberger
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.SchurComplement

/-! # Beam Eigenbasis -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Section 9, equations (9.9)--(9.11): the beam block realization

`Section9/SchurComplement.lean` states equations (9.9)--(9.11) abstractly, and
`Section9/IndividualAngles.lean` assembles the individual-angle envelope from an
in-plane and an out-of-plane tangent estimate.  Neither is attached to the
genuine perturbed free beam.  This file supplies the missing realization.

## What is proved here

* **The low spectral subspace is exactly two-dimensional.**  `beamLowFiveHundred`
  is a spectral range, and nothing about its dimension was previously available:
  the Rayleigh--Ritz count in `BeamTangent` caps only *finite-dimensional*
  subspaces of it.  `rank_beamLowFiveHundred_le` promotes that cap to the space
  itself, `finiteDimensional_beamLowFiveHundred` and `finrank_beamLowFiveHundred`
  record the consequences, and `beamLowFiveHundred_eq_specRange_ritzHigh` shows
  the same subspace is already the spectral range below the upper Ritz value --
  so `A + ε t` has no spectrum whatever in `(ritzHigh ε, 500]`.
* **An orthonormal eigenbasis.**  The restriction `beamLowOperator` of
  `A + ε t` to that subspace is a genuine symmetric endomorphism of a
  two-dimensional space, and `beamLowEigenbasis` diagonalises it.  Its vectors
  `beamLowEigenvector` are honest eigenvectors of the unbounded operator, with
  real eigenvalues `beamLowEigenvalue` strictly below `500`.
* **Equation (9.9), lower block.**  `beam_lower_block_equation` splits the exact
  eigenvalue equation along `beamTrial ⊕ beamTrialᗮ` and produces exactly the
  `b + w = lam • y` shape that `norm_lower_coordinate_le` consumes, with `b` the
  Rayleigh--Ritz residual column at the trial coordinate.
* **The out-of-plane bound.**  `beam_tan_eta_le` is the tangent estimate
  `tan eta ≤ ‖B‖ / (500.5 - lam)` with the exact recentered singular value
  `‖B‖ = |ε| √15 / 15`; this is the `htaneta` input of
  `individual_angle_le_exact_envelope_of_subspace`, and the coefficient matches
  its `tanEtaCoefficient` on the nose.

The in-plane rotation `psi_k` is *not* supplied here; see the census row
`DK-9.9-9.11` for the remaining step and the exact identity that delivers it.

No resolvent is constructed: the lower block enters only through the vector
`A₁ y`, exactly as in `SchurComplement.lean`.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model


open DavisKahan1970.Section9

noncomputable section

/-! ## The low spectral subspace is two-dimensional

`beamLowFiveHundred ε` is defined as a spectral range, so nothing about its
dimension is available for free.  The Rayleigh--Ritz dimension count caps every
*finite-dimensional* subspace of it by `finrank beamTrial = 2`; that cap is
promoted to the subspace itself by testing it against arbitrary finite linearly
independent families, and the reverse inequality comes from the Ritz half of the
same count. -/

/-- The low spectral subspace is the spectral range of `Set.Iic 500`. -/
theorem beamLowFiveHundred_eq_specRange (ε : ℝ) :
    beamLowFiveHundred ε =
      TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
        (Set.Iic 500) measurableSet_Iic := rfl

/-- **The Rayleigh--Ritz cap, promoted from finite subspaces to the whole
spectral range.**  Every finite linearly independent family inside the low
spectral subspace spans a finite-dimensional subspace of the spectral range, so
it has at most `finrank beamTrial = 2` members. -/
theorem rank_beamLowFiveHundred_le (ε : ℝ) (hε : 0 ≤ ε) :
    Module.rank ℂ (beamLowFiveHundred ε) ≤ 2 := by
  classical
  have h2 : (2 : Cardinal) = ((2 : ℕ) : Cardinal) := by norm_num
  rw [h2]
  refine rank_le (n := 2) ?_
  intro s hs
  have hsmap : LinearIndependent ℂ
      (fun i : s => ((i : (beamLowFiveHundred ε)) : BeamL2)) :=
    hs.map' (beamLowFiveHundred ε).subtype (Submodule.ker_subtype _)
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun i : s => ((i : (beamLowFiveHundred ε)) : BeamL2)))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hrank : Module.finrank ℂ (Submodule.span ℂ
      (Set.range (fun i : s => ((i : (beamLowFiveHundred ε)) : BeamL2)))) = s.card := by
    rw [finrank_span_eq_card hsmap]
    exact Fintype.card_coe s
  have hle : Submodule.span ℂ
      (Set.range (fun i : s => ((i : (beamLowFiveHundred ε)) : BeamL2)))
      ≤ TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
        (Set.Iic 500) measurableSet_Iic := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (i : (beamLowFiveHundred ε)).2
  have hmain := beamPerturbed_finrank_le ε hε hle
  rw [hrank, finrank_beamTrial] at hmain
  exact hmain

/-- The low spectral subspace of the perturbed beam is finite-dimensional. -/
theorem finiteDimensional_beamLowFiveHundred (ε : ℝ) (hε : 0 ≤ ε) :
    FiniteDimensional ℂ (beamLowFiveHundred ε) :=
  Module.rank_lt_aleph0_iff.1
    (lt_of_le_of_lt (rank_beamLowFiveHundred_le ε hε)
      (by exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 2))))

/-- Spectral ranges of the perturbed beam grow with the Borel set. -/
theorem beamPerturbed_specRange_mono (ε : ℝ) {B C : Set ℝ}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : B ⊆ C) :
    TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε) B hB
      ≤ TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε) C hC := by
  intro x hx
  have hfix : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε) B hB x = x :=
    (TauCeti.LinearPMap.mem_specRange_iff _ _ _ _).1 hx
  refine (TauCeti.LinearPMap.mem_specRange_iff _ _ _ _).2 ?_
  have hcongr : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (C ∩ B) (hC.inter hB)
      = TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε) B hB := by
    simp only [TauCeti.LinearPMap.specProjection_def]
    exact (TauCeti.LinearPMap.spectralPVM (beamPerturbed_isSelfAdjoint ε)).proj_congr
      (Set.inter_eq_right.2 hBC) (hC.inter hB) hB
  conv_lhs => rw [← hfix]
  rw [TauCeti.LinearPMap.specProjection_apply_specProjection, hcongr, hfix]

/-- **The low spectral subspace is exactly two-dimensional.** -/
theorem finrank_beamLowFiveHundred (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) :
    Module.finrank ℂ (beamLowFiveHundred ε) = 2 := by
  have := finiteDimensional_beamLowFiveHundred ε hε
  have hle : Module.finrank ℂ (beamLowFiveHundred ε) ≤ 2 :=
    Module.finrank_le_of_rank_le (by
      have := rank_beamLowFiveHundred_le ε hε
      exact_mod_cast this)
  have hmono : TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic ≤ beamLowFiveHundred ε :=
    beamPerturbed_specRange_mono ε measurableSet_Iic measurableSet_Iic
      (Set.Iic_subset_Iic.2 (ritzHigh_lt_five_hundred hε100).le)
  have hge := beamTrial_finrank_le ε hε hmono
  rw [finrank_beamTrial] at hge
  omega

/-- **The low spectral subspace is already the spectral range below the upper Ritz
value.**  The two ranges are nested and both two-dimensional, so they coincide;
hence the perturbed beam has no spectrum at all in `(ritzHigh ε, 500]`. -/
theorem beamLowFiveHundred_eq_specRange_ritzHigh (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) :
    beamLowFiveHundred ε
      = TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
          (Set.Iic (ritzHigh ε)) measurableSet_Iic := by
  have := finiteDimensional_beamLowFiveHundred ε hε
  have hmono : TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic ≤ beamLowFiveHundred ε :=
    beamPerturbed_specRange_mono ε measurableSet_Iic measurableSet_Iic
      (Set.Iic_subset_Iic.2 (ritzHigh_lt_five_hundred hε100).le)
  have hfd : FiniteDimensional ℂ (TauCeti.LinearPMap.specRange
      (beamPerturbed_isSelfAdjoint ε) (Set.Iic (ritzHigh ε)) measurableSet_Iic) :=
    Submodule.finiteDimensional_of_le hmono
  have hge := beamTrial_finrank_le ε hε
    (W := TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic) le_rfl
  rw [finrank_beamTrial] at hge
  have hle : Module.finrank ℂ (beamLowFiveHundred ε) = 2 :=
    finrank_beamLowFiveHundred ε hε hε100
  exact (Submodule.eq_of_le_of_finrank_le hmono (by omega)).symm

/-- Every vector of the low spectral subspace lies in the operator domain. -/
theorem beamLowFiveHundred_le_domain (ε : ℝ) (hε : 0 ≤ ε) {x : BeamL2}
    (hx : x ∈ beamLowFiveHundred ε) : x ∈ (beamPerturbed ε).domain :=
  beamPerturbed_specRange_le_domain ε hε hx

/-- The low spectral subspace sits inside the operator domain. -/
theorem beamLowFiveHundred_le_domain' (ε : ℝ) (hε : 0 ≤ ε) :
    beamLowFiveHundred ε ≤ (beamPerturbed ε).domain :=
  fun _ hx => beamLowFiveHundred_le_domain ε hε hx

/-- **The perturbed beam restricted to its low spectral subspace.**  The subspace
lies in the operator domain and is invariant, so the restriction is an honest
linear endomorphism of a two-dimensional space. -/
def beamLowOperator (ε : ℝ) (hε : 0 ≤ ε) :
    (beamLowFiveHundred ε) →ₗ[ℂ] (beamLowFiveHundred ε) :=
  LinearMap.codRestrict (beamLowFiveHundred ε)
    ((beamPerturbed ε).toFun ∘ₗ
      Submodule.inclusion (beamLowFiveHundred_le_domain' ε hε))
    (fun x => selfAdjoint_maps_spectralSubspace (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) measurableSet_Iic
      ⟨(x : BeamL2), beamLowFiveHundred_le_domain ε hε x.2⟩ x.2)

/-- The restriction acts by the ambient operator. -/
@[simp] theorem beamLowOperator_coe (ε : ℝ) (hε : 0 ≤ ε) (x : beamLowFiveHundred ε) :
    ((beamLowOperator ε hε x : beamLowFiveHundred ε) : BeamL2)
      = (beamPerturbed ε) ⟨(x : BeamL2), beamLowFiveHundred_le_domain ε hε x.2⟩ :=
  rfl

/-- The restriction is symmetric. -/
theorem beamLowOperator_isSymmetric (ε : ℝ) (hε : 0 ≤ ε) :
    (beamLowOperator ε hε).IsSymmetric := by
  intro x y
  exact (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint
      (beamPerturbed_isSelfAdjoint ε))
    ⟨(x : BeamL2), beamLowFiveHundred_le_domain ε hε x.2⟩
    ⟨(y : BeamL2), beamLowFiveHundred_le_domain ε hε y.2⟩

/-- **The orthonormal eigenbasis of the perturbed beam on its low spectral
subspace.**  Two orthonormal eigenvectors `f 0`, `f 1` of `A + ε t`. -/
def beamLowEigenbasis (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) :
    OrthonormalBasis (Fin 2) ℂ (beamLowFiveHundred ε) :=
  haveI := finiteDimensional_beamLowFiveHundred ε hε
  (beamLowOperator_isSymmetric ε hε).eigenvectorBasis
    (finrank_beamLowFiveHundred ε hε hε100)

/-- The `k`-th exact eigenvector of the perturbed beam below `500`. -/
def beamLowEigenvector (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) (k : Fin 2) : BeamL2 :=
  ((beamLowEigenbasis ε hε hε100 k : beamLowFiveHundred ε) : BeamL2)

/-- The `k`-th exact eigenvalue of the perturbed beam below `500`. -/
def beamLowEigenvalue (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) (k : Fin 2) : ℝ :=
  haveI := finiteDimensional_beamLowFiveHundred ε hε
  (beamLowOperator_isSymmetric ε hε).eigenvalues
    (finrank_beamLowFiveHundred ε hε hε100) k

/-- The `k`-th eigenvector lies in the low spectral subspace. -/
theorem beamLowEigenvector_mem (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) (k : Fin 2) :
    beamLowEigenvector ε hε hε100 k ∈ beamLowFiveHundred ε :=
  (beamLowEigenbasis ε hε hε100 k).2

/-- The `k`-th eigenvector lies in the operator domain. -/
theorem beamLowEigenvector_mem_domain (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) (k : Fin 2) :
    beamLowEigenvector ε hε hε100 k ∈ (beamPerturbed ε).domain :=
  beamLowFiveHundred_le_domain ε hε (beamLowEigenvector_mem ε hε hε100 k)

/-- The eigenbasis is orthonormal in the ambient space. -/
theorem beamLowEigenvector_orthonormal (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) :
    Orthonormal ℂ (beamLowEigenvector ε hε hε100) := by
  have h := (beamLowEigenbasis ε hε hε100).orthonormal
  exact h.comp_linearIsometry (beamLowFiveHundred ε).subtypeₗᵢ

/-- The eigenvectors are unit vectors. -/
theorem norm_beamLowEigenvector (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100) (k : Fin 2) :
    ‖beamLowEigenvector ε hε hε100 k‖ = 1 :=
  (beamLowEigenvector_orthonormal ε hε hε100).1 k

/-- **The eigenvalue equation.** -/
theorem beamPerturbed_apply_beamLowEigenvector (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100)
    (k : Fin 2) :
    (beamPerturbed ε)
        ⟨beamLowEigenvector ε hε hε100 k, beamLowEigenvector_mem_domain ε hε hε100 k⟩
      = ((beamLowEigenvalue ε hε hε100 k : ℝ) : ℂ) • beamLowEigenvector ε hε hε100 k := by
  have := finiteDimensional_beamLowFiveHundred ε hε
  have h := (beamLowOperator_isSymmetric ε hε).apply_eigenvectorBasis
    (finrank_beamLowFiveHundred ε hε hε100) k
  exact congrArg (fun z : beamLowFiveHundred ε => (z : BeamL2)) h

/-- Each eigenvalue below `500` is in fact strictly below `500`; the perturbed
beam has no spectrum in `(ritzHigh ε, 500]`. -/
theorem beamLowEigenvalue_lt_five_hundred (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100)
    (k : Fin 2) : beamLowEigenvalue ε hε hε100 k < 500 := by
  set f := beamLowEigenvector ε hε hε100 k with hfdef
  have hfn : ‖f‖ = 1 := norm_beamLowEigenvector ε hε hε100 k
  have hfne : f ≠ 0 := by
    intro h
    rw [h, norm_zero] at hfn
    exact absurd hfn (by norm_num)
  have hmem : f ∈ TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic := by
    rw [← beamLowFiveHundred_eq_specRange_ritzHigh ε hε hε100]
    exact beamLowEigenvector_mem ε hε hε100 k
  have hfix : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic f = f :=
    (TauCeti.LinearPMap.mem_specRange_iff _ _ _ _).1 hmem
  have hIci : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Ici 500) measurableSet_Ici f = 0 := by
    conv_lhs => rw [← hfix]
    rw [TauCeti.LinearPMap.specProjection_apply_specProjection]
    refine TauCeti.LinearPMap.specProjection_apply_eq_zero_of_eq_empty _ _ ?_ _
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, Set.mem_empty_iff_false,
      iff_false, not_and, not_le]
    intro ht
    have := ritzHigh_lt_five_hundred hε100
    linarith
  have hlt := TauCeti.LinearPMap.re_inner_lt_of_specProjection_Ici_apply_eq_zero
    (beamPerturbed_isSelfAdjoint ε)
    (⟨f, beamLowEigenvector_mem_domain ε hε hε100 k⟩ : (beamPerturbed ε).domain) hIci hfne
  have heig : (beamPerturbed ε)
      ⟨f, beamLowEigenvector_mem_domain ε hε hε100 k⟩
      = ((beamLowEigenvalue ε hε hε100 k : ℝ) : ℂ) • f :=
    beamPerturbed_apply_beamLowEigenvector ε hε hε100 k
  rw [show ((beamPerturbed ε)
      (⟨f, beamLowEigenvector_mem_domain ε hε hε100 k⟩ : (beamPerturbed ε).domain))
      = (beamPerturbed ε) ⟨f, beamLowEigenvector_mem_domain ε hε hε100 k⟩ from rfl,
    heig, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K] at hlt
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hlt
  rw [hfn] at hlt
  push_cast at hlt
  simpa using hlt

/-! ## Equation (9.9): the block decomposition at an exact eigenvector -/

/-- The trial coordinate of a domain vector is again a domain vector. -/
theorem beamTrial_starProjection_mem_domain (ε : ℝ) (f : BeamL2) :
    beamTrial.starProjection f ∈ (beamPerturbed ε).domain :=
  beamTrial_le_domain (beamTrial.starProjection_apply_mem f)

/-- The complementary coordinate of a domain vector is again a domain vector. -/
theorem beamOrthogonal_part_mem_domain (ε : ℝ) {f : BeamL2}
    (hf : f ∈ (beamPerturbed ε).domain) :
    f - beamTrial.starProjection f ∈ (beamPerturbed ε).domain :=
  Submodule.sub_mem _ hf (beamTrial_starProjection_mem_domain ε f)

/-- **Equation (9.9), lower block, for the genuine free beam.**

Splitting an exact eigenvector `f` of `A + ε t` into its trial coordinate
`x = P f` and its complementary coordinate `y = f - P f`, and projecting the
eigenvalue equation onto `beamTrialᗮ`, gives `B x + A₁ y = lam y` with
`B x` the Rayleigh--Ritz residual column at `x` and `A₁ y` the compression of
`A + ε t` to the complement. -/
theorem beam_lower_block_equation (ε : ℝ) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f) :
    (beamPerturbation ε (beamTrial.starProjection f)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f)))
      + ((beamPerturbed ε)
            ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩
          - beamTrial.starProjection ((beamPerturbed ε)
              ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩))
      = ((lam : ℝ) : ℂ) • (f - beamTrial.starProjection f) := by
  have hxmem : beamTrial.starProjection f ∈ beamTrial :=
    beamTrial.starProjection_apply_mem f
  have hxdom : beamTrial.starProjection f ∈ (beamPerturbed ε).domain :=
    beamTrial_starProjection_mem_domain ε f
  have hTx : (beamPerturbed ε) ⟨beamTrial.starProjection f, hxdom⟩
      = beamPerturbation ε (beamTrial.starProjection f) :=
    beamPerturbed_apply_of_mem_beamTrial ε hxmem hxdom
  have hsum : (⟨beamTrial.starProjection f, hxdom⟩ : (beamPerturbed ε).domain)
      + ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩
      = ⟨f, hfdom⟩ := by
    apply Subtype.ext
    change beamTrial.starProjection f + (f - beamTrial.starProjection f) = f
    abel
  have hTsplit : beamPerturbation ε (beamTrial.starProjection f)
      + (beamPerturbed ε)
          ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩
      = ((lam : ℝ) : ℂ) • f := by
    rw [← hTx, ← LinearPMap.map_add, hsum, hf]
  have hproj : beamTrial.starProjection (((lam : ℝ) : ℂ) • f)
      = ((lam : ℝ) : ℂ) • beamTrial.starProjection f := map_smul _ _ _
  have hexpand : (beamPerturbation ε (beamTrial.starProjection f)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f)))
      + ((beamPerturbed ε)
            ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩
          - beamTrial.starProjection ((beamPerturbed ε)
              ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩))
      = (beamPerturbation ε (beamTrial.starProjection f)
            + (beamPerturbed ε)
              ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f)
            + (beamPerturbed ε)
              ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩) := by
    rw [map_add]
    abel
  rw [hexpand, hTsplit, hproj, smul_sub]

/-- The lower-block form bound, in the shape the Schur estimates consume. -/
theorem beam_lower_block_form_ge (ε : ℝ) (hε : 0 ≤ ε) (f : BeamL2)
    (hfdom : f ∈ (beamPerturbed ε).domain) :
    (1001 / 2 : ℝ) * ‖f - beamTrial.starProjection f‖ ^ 2
      ≤ RCLike.re (inner ℂ ((beamPerturbed ε)
          ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩
        - beamTrial.starProjection ((beamPerturbed ε)
            ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩))
          (f - beamTrial.starProjection f)) := by
  have hy : f - beamTrial.starProjection f ∈ beamTrialᗮ :=
    Submodule.sub_starProjection_mem_orthogonal f
  have hzero : (inner ℂ (beamTrial.starProjection ((beamPerturbed ε)
      ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩))
      (f - beamTrial.starProjection f) : ℂ) = 0 :=
    hy _ (beamTrial.starProjection_apply_mem _)
  rw [inner_sub_left, hzero, sub_zero]
  exact beamPerturbed_form_ge_of_mem_orthogonal ε hε
    ⟨f - beamTrial.starProjection f, beamOrthogonal_part_mem_domain ε hfdom⟩ hy

/-- The residual column at the trial coordinate is bounded by the exact
recentered singular value. -/
theorem beam_norm_residual_column_le (ε : ℝ) (f : BeamL2) :
    ‖beamPerturbation ε (beamTrial.starProjection f)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f))‖
      ≤ orthogonalResidualSingularValue ε * ‖beamTrial.starProjection f‖ :=
  norm_beamRitzResidual_le ε ⟨beamTrial.starProjection f,
    beamTrial.starProjection_apply_mem f⟩

/-- **Equation (9.10) for the beam.**  The complementary coordinate of an exact
eigenvector is controlled by its trial coordinate. -/
theorem beam_norm_orthogonal_part_le (ε : ℝ) (hε : 0 ≤ ε) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f)
    (hlam : lam < 1001 / 2) :
    ((1001 : ℝ) / 2 - lam) * ‖f - beamTrial.starProjection f‖
      ≤ orthogonalResidualSingularValue ε * ‖beamTrial.starProjection f‖ := by
  have hmain := norm_lower_coordinate_le (𝕜 := ℂ)
    (beam_lower_block_equation ε hfdom hf)
    (beam_lower_block_form_ge ε hε f hfdom) hlam
  exact hmain.trans (beam_norm_residual_column_le ε f)

/-- The trial coordinate of a unit eigenvector below `500` never vanishes. -/
theorem beam_starProjection_ne_zero (ε : ℝ) (hε : 0 ≤ ε) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f)
    (hlam : lam < 1001 / 2) (hfn : ‖f‖ = 1) :
    beamTrial.starProjection f ≠ 0 := by
  intro hzero
  have hb : beamPerturbation ε (beamTrial.starProjection f)
      - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f)) = 0 := by
    rw [hzero, map_zero, map_zero, sub_zero]
  have hy := lower_coordinate_eq_zero_of_residual_eq_zero (𝕜 := ℂ)
    (beam_lower_block_equation ε hfdom hf)
    (beam_lower_block_form_ge ε hε f hfdom) hlam hb
  rw [hzero, sub_zero] at hy
  rw [hy, norm_zero] at hfn
  exact absurd hfn (by norm_num)

/-- **The out-of-plane tangent bound.**  The angle between an exact eigenvector
`f` of `A + ε t` and the affine trial subspace satisfies
`tan eta ≤ ‖B‖ / (500.5 - lam)`, with `‖B‖` the exact recentered residual
singular value `|ε| √15 / 15`. -/
theorem beam_tan_eta_le (ε : ℝ) (hε : 0 ≤ ε) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f)
    (hlam : lam < 1001 / 2) (hfn : ‖f‖ = 1) :
    Real.tan (Real.arccos ‖beamTrial.starProjection f‖)
      ≤ orthogonalResidualSingularValue ε / ((1001 : ℝ) / 2 - lam) := by
  have hne := beam_starProjection_ne_zero ε hε hfdom hf hlam hfn
  have hpos : 0 < ‖beamTrial.starProjection f‖ := norm_pos_iff.2 hne
  have hpy := TauCeti.norm_sq_starProjection_add_norm_sq_sub beamTrial f
  rw [hfn] at hpy
  have hsqrt : Real.sqrt (1 - ‖beamTrial.starProjection f‖ ^ 2)
      = ‖f - beamTrial.starProjection f‖ := by
    rw [show (1 : ℝ) - ‖beamTrial.starProjection f‖ ^ 2
      = ‖f - beamTrial.starProjection f‖ ^ 2 from by nlinarith [hpy]]
    exact Real.sqrt_sq (norm_nonneg _)
  rw [Real.tan_arccos, hsqrt, div_le_div_iff₀ hpos (by linarith)]
  have h := beam_norm_orthogonal_part_le ε hε hfdom hf hlam
  nlinarith [h, norm_nonneg (f - beamTrial.starProjection f), hpos]

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
