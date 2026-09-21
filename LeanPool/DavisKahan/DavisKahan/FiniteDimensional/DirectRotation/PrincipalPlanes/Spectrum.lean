/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes.Basic
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan

/-!
# The spectrum of the direct displacement `I - R`

Building on `PrincipalPlanes.Basic`, this module supplies the finite
two-projection structure theory needed to compute the singular values of the
direct displacement `I - R`: the vanishing-direction descent lemmas (a vector
orthogonal to the principal-plane family lies in the common fixed part), the
Gram identity `(I-R)⋆(I-R) = 2 (I - |S|)`, and the closed forms

* `singularValues_directRotation_displacement`
  (`sigma_k (I-R) = 2 sin(theta_{k/2}/2)`, each chord twice) and
* `kyFanSum_directRotation_displacement_eq_principalChords`.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ## Vanishing directions

A vector orthogonal to every principal source vector is annihilated by the
sine map; a vector orthogonal to the whole principal-plane family lies in the
common fixed part, where the two projections agree.  These descent lemmas are
the finite two-projection structure theory needed to compute the spectrum of
`I - R`. -/

/-- The sine map vanishes on vectors orthogonal to every principal source
vector. -/
theorem sinThetaMap_apply_eq_zero_of_orthogonal_sources
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : ∀ i, ⟪principalSourceVector U V i, x⟫_𝕜 = 0) :
    sinThetaMap U V x = 0 := by
  classical
  set b := rightSingularBasis (sinThetaMap U V) with hb
  have hxdecomp := b.sum_repr x
  calc sinThetaMap U V x
      = sinThetaMap U V (∑ j, b.repr x j • b j) := by rw [hxdecomp]
    _ = ∑ j, b.repr x j • sinThetaMap U V (b j) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : (j : ℕ) < nontrivialAngleCount U V
        · have hcoeff : b.repr x j = 0 := by
            rw [b.repr_apply_apply]
            have hidx : b j = principalSourceVector U V ⟨(j : ℕ), hj⟩ := by
              rw [principalSourceVector]
              congr 1
            rw [hidx]
            exact hx ⟨(j : ℕ), hj⟩
          rw [hcoeff, zero_smul]
        · have hσ : (sinThetaMap U V).singularValues (j : ℕ) = 0 :=
            (sinThetaMap U V).singularValues_eq_zero_iff_le_finrank_range.mpr
              (Nat.le_of_not_lt hj)
          rw [apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero
            (sinThetaMap U V) hσ, smul_zero]

/-- A vector of `U` orthogonal to every principal source vector lies in `V`. -/
theorem mem_of_mem_orthogonal_sources
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hxU : x ∈ U)
    (hx : ∀ i, ⟪principalSourceVector U V i, x⟫_𝕜 = 0) :
    x ∈ V := by
  have hsin := sinThetaMap_apply_eq_zero_of_orthogonal_sources U V hx
  rw [sinThetaMap, LinearMap.comp_apply, projection_apply_of_mem hxU] at hsin
  have hmem : x ∈ Vᗮᗮ :=
    (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hsin
  rwa [Submodule.orthogonal_orthogonal] at hmem

/-- The positive cosine fixes every vector of `U` orthogonal to the principal
source vectors. -/
theorem abs_canonicalIntertwiner_apply_eq_self_of_orthogonal_sources
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hxU : x ∈ U)
    (hx : ∀ i, ⟪principalSourceVector U V i, x⟫_𝕜 = 0) :
    TauCeti.operatorAbs (canonicalIntertwiner U V) x = x := by
  have hxV := mem_of_mem_orthogonal_sources U V hxU hx
  exact abs_canonicalIntertwiner_apply_eq_self_of_projection_eq U V
    (by rw [projection_apply_of_mem hxU, projection_apply_of_mem hxV])

/-- Inner products against the sine map vanish on vectors orthogonal to the
principal-plane family. -/
theorem inner_sinThetaMap_apply_eq_zero_of_orthogonal_family
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    {z : E} (hzu : ∀ i, ⟪principalSourceVector U V i, z⟫_𝕜 = 0)
    (hzj : ∀ i, ⟪principalOrthogonalVector U V hacute i, z⟫_𝕜 = 0)
    (w : E) :
    ⟪sinThetaMap U V w, z⟫_𝕜 = 0 := by
  classical
  set b := rightSingularBasis (sinThetaMap U V) with hb
  have hwdecomp := b.sum_repr w
  have hsinu : ∀ i : Fin (nontrivialAngleCount U V),
      ⟪sinThetaMap U V (principalSourceVector U V i), z⟫_𝕜 = 0 := by
    intro i
    have hu := principalSourceVector_mem U V hacute i
    have hsin : sinThetaMap U V (principalSourceVector U V i) =
        principalSourceVector U V i -
          projection V (principalSourceVector U V i) := by
      rw [sinThetaMap, LinearMap.comp_apply, projection_apply_of_mem hu]
      exact Submodule.starProjection_orthogonal_val _
    simp only [hsin, projection_apply_principalSourceVector U V hacute i,
      directRotation_apply_principalSourceVector U V hacute i, inner_sub_left,
      inner_smul_left, inner_add_left, inner_smul_left, inner_smul_left,
      hzu i, hzj i]
    ring
  calc ⟪sinThetaMap U V w, z⟫_𝕜
      = ⟪sinThetaMap U V (∑ j, b.repr w j • b j), z⟫_𝕜 := by rw [hwdecomp]
    _ = ∑ j, (starRingEnd 𝕜) (b.repr w j) * ⟪sinThetaMap U V (b j), z⟫_𝕜 := by
        rw [map_sum, sum_inner]
        exact Finset.sum_congr rfl fun j _ => by
          rw [map_smul, inner_smul_left]
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : (j : ℕ) < nontrivialAngleCount U V
        · have hidx : b j = principalSourceVector U V ⟨(j : ℕ), hj⟩ := by
            rw [principalSourceVector]
            congr 1
          rw [hidx, hsinu ⟨(j : ℕ), hj⟩, mul_zero]
        · have hσ : (sinThetaMap U V).singularValues (j : ℕ) = 0 :=
            (sinThetaMap U V).singularValues_eq_zero_iff_le_finrank_range.mpr
              (Nat.le_of_not_lt hj)
          rw [apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero
            (sinThetaMap U V) hσ, inner_zero_left, mul_zero]

/-- **Descent to the fixed part.**  On the orthogonal complement of the
principal-plane family the two projections agree. -/
theorem projection_eq_projection_of_orthogonal_family
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    {x : E} (hxu : ∀ i, ⟪principalSourceVector U V i, x⟫_𝕜 = 0)
    (hxj : ∀ i, ⟪principalOrthogonalVector U V hacute i, x⟫_𝕜 = 0) :
    projection U x = projection V x := by
  set y := projection U x with hy
  set z := complementaryProjection U x with hz
  have hxyz : y + z = x := U.starProjection_add_starProjection_orthogonal x
  have hyU : y ∈ U := U.starProjection_apply_mem x
  have hzUperp : z ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  -- `y` is orthogonal to the source vectors.
  have hyu : ∀ i, ⟪principalSourceVector U V i, y⟫_𝕜 = 0 := by
    intro i
    have := projection_inner_left_eq_right U (principalSourceVector U V i) x
    rw [projection_apply_of_mem (principalSourceVector_mem U V hacute i)] at this
    rw [hy, ← this, hxu i]
  -- Hence `y ∈ V`.
  have hyV : y ∈ V := mem_of_mem_orthogonal_sources U V hyU hyu
  -- `z` is orthogonal to the whole family.
  have hzu : ∀ i, ⟪principalSourceVector U V i, z⟫_𝕜 = 0 := by
    intro i
    have hsplit : ⟪principalSourceVector U V i, x⟫_𝕜 =
        ⟪principalSourceVector U V i, y⟫_𝕜 +
          ⟪principalSourceVector U V i, z⟫_𝕜 := by
      rw [← inner_add_right, hxyz]
    rw [hxu i, hyu i] at hsplit
    -- `hsplit : 0 = 0 + w` in `𝕜`; no ordered-field reasoning is needed
    simpa using hsplit.symm
  have hzj : ∀ i, ⟪principalOrthogonalVector U V hacute i, z⟫_𝕜 = 0 := by
    intro i
    have hjy : ⟪principalOrthogonalVector U V hacute i, y⟫_𝕜 = 0 := by
      have := projection_inner_left_eq_right U
        (principalOrthogonalVector U V hacute i) x
      rw [projection_apply_of_mem_orthogonal
        (principalOrthogonalVector_mem U V hacute i), inner_zero_left] at this
      rw [hy, ← this]
    have hsplit : ⟪principalOrthogonalVector U V hacute i, x⟫_𝕜 =
        ⟪principalOrthogonalVector U V hacute i, y⟫_𝕜 +
          ⟪principalOrthogonalVector U V hacute i, z⟫_𝕜 := by
      rw [← inner_add_right, hxyz]
    rw [hxj i, hjy] at hsplit
    simpa using hsplit.symm
  -- The `V`-projection of `z` vanishes: it is a vector of `V` orthogonal to `U`.
  have hvzero : projection V z = 0 := by
    set v := projection V z with hv
    have hvV : v ∈ V := V.starProjection_apply_mem z
    have hvUperp : ∀ u ∈ U, ⟪u, v⟫_𝕜 = 0 := by
      intro u huU
      have h1 : ⟪u, v⟫_𝕜 = ⟪projection V u, z⟫_𝕜 := by
        rw [hv, projection_inner_left_eq_right]
      have h2 : projection V u = u - sinThetaMap U V u := by
        rw [sinThetaMap, LinearMap.comp_apply, projection_apply_of_mem huU]
        -- `complementaryProjection` hides the `starProjection` the orthogonal
        -- splitting lemma matches on, so finish by the splitting identity
        exact (eq_sub_of_add_eq
          (Submodule.starProjection_add_starProjection_orthogonal (K := V) u))
      rw [h1, h2, inner_sub_left,
        Submodule.inner_right_of_mem_orthogonal huU hzUperp,
        inner_sinThetaMap_apply_eq_zero_of_orthogonal_family U V hacute hzu hzj u,
        sub_zero]
    have hvmem : v ∈ Uᗮ := by
      rw [Submodule.mem_orthogonal]
      exact hvUperp
    have hproj0 : U.starProjection v = 0 :=
      projection_apply_of_mem_orthogonal hvmem
    exact hacute.2 v hvV hproj0
  -- Conclude.
  have hyproj : projection V y = y := projection_apply_of_mem hyV
  calc projection U x = y := hy.symm
    _ = projection V y + projection V z := by rw [hyproj, hvzero, add_zero]
    _ = projection V x := by rw [← map_add, hxyz]

/-! ## The spectrum of the direct displacement -/

/-- The Gram operator of the displacement `I - R` is twice the defect of the
positive cosine: `(I-R)⋆(I-R) = 2 (I - |S|)`. -/
theorem adjoint_comp_displacement_directRotation
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (LinearMap.id - (directRotation U V hacute).toLinearMap).adjoint ∘ₗ
        (LinearMap.id - (directRotation U V hacute).toLinearMap) =
      (2 : 𝕜) • (LinearMap.id -
        TauCeti.operatorAbs (canonicalIntertwiner U V)) := by
  have htwo := two_smul_abs_canonicalIntertwiner U V hacute
  have hadj : (directRotation U V hacute).toLinearMap.adjoint =
      (directRotation U V hacute).symm.toLinearMap :=
    (directRotation U V hacute).adjoint_toLinearMap_eq_symm
  have hcomp : (directRotation U V hacute).symm.toLinearMap ∘ₗ
      (directRotation U V hacute).toLinearMap = LinearMap.id := by
    ext x
    -- `simp` unfolds `directRotation` into its polar factor, after which
    -- `symm_apply_apply` no longer matches; state the goal instead
    show (directRotation U V hacute).symm ((directRotation U V hacute) x) = x
    exact (directRotation U V hacute).symm_apply_apply x
  rw [map_sub, LinearMap.adjoint_id, hadj]
  have hexpand : (LinearMap.id - (directRotation U V hacute).symm.toLinearMap) ∘ₗ
      (LinearMap.id - (directRotation U V hacute).toLinearMap) =
      (2 : 𝕜) • LinearMap.id -
        ((directRotation U V hacute).toLinearMap +
          (directRotation U V hacute).symm.toLinearMap) := by
    -- `simp only` applies each identity as often as it occurs; the fixed `rw`
    -- sequence assumed a multiplicity the goal does not have
    simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id, hcomp]
    ext x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    module
  rw [hexpand, ← htwo]
  ext x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_sub]

/-- The mutually orthogonal nontrivial principal planes fit in the ambient
space. -/
theorem twice_nontrivialAngleCount_le_finrank_of_acute
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    2 * nontrivialAngleCount U V ≤ finrank 𝕜 E := by
  let f : Fin (nontrivialAngleCount U V) × Fin 2 → E := fun p =>
    if p.2 = 0 then principalSourceVector U V p.1
    else principalOrthogonalVector U V hacute p.1
  have hf : LinearIndependent 𝕜 f :=
    (orthonormal_principalPlaneFamily U V hacute).linearIndependent
  have hspan := finrank_span_eq_card hf
  have hle := Submodule.finrank_le (Submodule.span 𝕜 (Set.range f))
  rw [hspan, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hle
  omega

/-- The angle count is bounded by the ambient dimension. -/
theorem nontrivialAngleCount_le_finrank
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    nontrivialAngleCount U V ≤ finrank 𝕜 E :=
  LinearMap.finrank_range_le (sinThetaMap U V)

/-- Elementary pairing identity for a sequence whose entries occur twice. -/
theorem sum_repeated_pair_prefix {m : ℕ}
    (d : Fin m → ℝ) (k : ℕ) :
    (∑ n : Fin k, if hn : (n : ℕ) < 2 * m then
        d ⟨(n : ℕ) / 2,
          (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
      else 0) =
      (∑ i : Fin (min (k / 2) m), 2 * d (Fin.castLE (min_le_right _ _) i)) +
        if hodd : k % 2 = 1 ∧ k / 2 < m then d ⟨k / 2, hodd.2⟩ else 0 := by
  classical
  -- Replace every `Fin`-indexed value by a total `ℕ`-indexed one.  The index
  -- type on the right changes size with `k`, which no rewrite can follow, and
  -- the embedded bound proofs block congruence.
  set D : ℕ → ℝ := fun j => if h : j < m then d ⟨j, h⟩ else 0 with hD
  have hDval : ∀ (j : ℕ) (h : j < m), D j = d ⟨j, h⟩ := fun _ h => dite_eq_left h
  have hleft : (∑ n : Fin k, if hn : (n : ℕ) < 2 * m then
        d ⟨(n : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
      else 0) = ∑ j ∈ Finset.range k, (if j < 2 * m then D (j / 2) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j : ℕ => if j < 2 * m then D (j / 2) else 0) k]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : (n : ℕ) < 2 * m
    · rw [dite_eq_left hn, ite_eq_left hn, hDval _ (by omega)]
    · rw [dite_eq_right hn, ite_eq_right hn]
  have hright : ∀ (p : ℕ) (hp : p ≤ m),
      (∑ i : Fin p, 2 * d (Fin.castLE hp i)) = ∑ j ∈ Finset.range p, 2 * D j := by
    intro p hp
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => 2 * D j) p]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hDval _ (lt_of_lt_of_le i.isLt hp)]
    rfl
  have hextra : ∀ n : ℕ,
      (if hodd : n % 2 = 1 ∧ n / 2 < m then d ⟨n / 2, hodd.2⟩ else 0) =
        (if n % 2 = 1 ∧ n / 2 < m then D (n / 2) else 0) := by
    intro n
    by_cases h : n % 2 = 1 ∧ n / 2 < m
    · rw [dite_eq_left h, ite_eq_left h, hDval _ h.2]
    · rw [dite_eq_right h, ite_eq_right h]
  rw [hleft, hright _ (min_le_right _ _), hextra]
  clear hleft
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hkm : k < 2 * m
      · rw [ite_eq_left hkm]
        rcases Nat.even_or_odd k with heven | hodd
        · obtain ⟨q, rfl⟩ := heven
          rw [ite_eq_right (by omega), ite_eq_left (by omega),
            show min ((q + q) / 2) m = min ((q + q + 1) / 2) m from by omega,
            show (q + q) / 2 = (q + q + 1) / 2 from by omega]
          ring
        · obtain ⟨q, rfl⟩ := hodd
          rw [ite_eq_left (show (2 * q + 1) % 2 = 1 ∧ (2 * q + 1) / 2 < m from
              by omega),
            ite_eq_right (by omega),
            show min ((2 * q + 1 + 1) / 2) m = min ((2 * q + 1) / 2) m + 1 from
              by omega,
            Finset.sum_range_succ,
            show min ((2 * q + 1) / 2) m = (2 * q + 1) / 2 from by omega]
          ring
      · rw [ite_eq_right hkm, ite_eq_right (by omega), ite_eq_right (by omega),
          show min ((k + 1) / 2) m = min (k / 2) m from by omega]
        ring

/-- **The singular values of the direct displacement** are the principal chord
lengths, each repeated twice, followed by zeros.  This is the quantitative
heart of Davis--Kahan Proposition 4.1: `sigma_k (I - R) = 2 sin(theta_{k/2}/2)`. -/
theorem singularValues_directRotation_displacement
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (n : ℕ) :
    (LinearMap.id - (directRotation U V hacute).toLinearMap).singularValues n =
      if hn : n < 2 * nontrivialAngleCount U V then
        principalPlaneChord U V
          ⟨n / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
      else 0 := by
  classical
  set m := nontrivialAngleCount U V with hm
  set A := LinearMap.id - (directRotation U V hacute).toLinearMap with hA
  set S := canonicalIntertwiner U V with hS
  have h2m : 2 * m ≤ finrank 𝕜 E :=
    twice_nontrivialAngleCount_le_finrank_of_acute U V hacute
  -- The candidate eigenvector family on `Fin (finrank 𝕜 E)`.
  set v : Fin (finrank 𝕜 E) → E := fun k =>
    if hk : (k : ℕ) < 2 * m then
      (if (k : ℕ) % 2 = 0
        then principalSourceVector U V
          ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
        else principalOrthogonalVector U V hacute
          ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩)
    else 0 with hv
  set s : Set (Fin (finrank 𝕜 E)) := {k | (k : ℕ) < 2 * m} with hs
  -- The family restricted to `s` is orthonormal.
  have hfam := orthonormal_principalPlaneFamily U V hacute
  have hres : Orthonormal 𝕜 (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : (a : ℕ) < 2 * m := ha
    have hb' : (b : ℕ) < 2 * m := hb
    have hva : v a = (fun p : Fin m × Fin 2 =>
        if p.2 = 0 then principalSourceVector U V p.1
        else principalOrthogonalVector U V hacute p.1)
        (⟨⟨(a : ℕ) / 2, by omega⟩, ⟨(a : ℕ) % 2, by omega⟩⟩) := by
      rw [hv]
      simp only [dite_eq_left ha']
      by_cases hpar : (a : ℕ) % 2 = 0
      · simp [hpar]
      · have : (a : ℕ) % 2 = 1 := by omega
        simp [hpar, show (⟨(a:ℕ) % 2, by omega⟩ : Fin 2) ≠ 0 from by
          intro h; apply hpar; simpa [Fin.ext_iff] using h]
    have hvb : v b = (fun p : Fin m × Fin 2 =>
        if p.2 = 0 then principalSourceVector U V p.1
        else principalOrthogonalVector U V hacute p.1)
        (⟨⟨(b : ℕ) / 2, by omega⟩, ⟨(b : ℕ) % 2, by omega⟩⟩) := by
      rw [hv]
      simp only [dite_eq_left hb']
      by_cases hpar : (b : ℕ) % 2 = 0
      · simp [hpar]
      · have : (b : ℕ) % 2 = 1 := by omega
        simp [hpar, show (⟨(b:ℕ) % 2, by omega⟩ : Fin 2) ≠ 0 from by
          intro h; apply hpar; simpa [Fin.ext_iff] using h]
    have hij := orthonormal_iff_ite.mp hfam
      ⟨⟨(a : ℕ) / 2, by omega⟩, ⟨(a : ℕ) % 2, by omega⟩⟩
      ⟨⟨(b : ℕ) / 2, by omega⟩, ⟨(b : ℕ) % 2, by omega⟩⟩
    simp only [Set.domRestrict_apply]
    rw [hva, hvb, hij]
    congr 1
    simp only [Prod.mk.injEq, Fin.mk.injEq, Subtype.mk.injEq, eq_iff_iff]
    constructor
    · rintro ⟨h1, h2⟩
      apply Fin.ext
      omega
    · intro h
      have : (a : ℕ) = (b : ℕ) := by exact_mod_cast congrArg Fin.val h
      omega
  obtain ⟨b, hb⟩ := hres.exists_orthonormalBasis_extension_of_card_eq
    (by simp) (v := v)
  -- The eigenvalue list.
  set μ : Fin (finrank 𝕜 E) → ℝ := fun k =>
    if hk : (k : ℕ) < 2 * m then
      principalPlaneChord U V
        ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩ ^ 2
    else 0 with hμ
  have hμanti : Antitone μ := by
    intro a c hac
    -- `omega` cannot see through `Fin` order or through `Fin.val` of a `mk`
    have hac' : (a : ℕ) ≤ (c : ℕ) := hac
    rw [hμ]
    simp only
    split_ifs with h1 h2 h2
    · have hba : (a : ℕ)/2 < m := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
      have hbc : (c : ℕ)/2 < m := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
      have hchord := principalPlaneChord_antitone U V
        (show (⟨(a : ℕ)/2, hba⟩ : Fin m) ≤ ⟨(c : ℕ)/2, hbc⟩ from
          Fin.le_def.mpr (Nat.div_le_div_right hac'))
      have h0a := principalPlaneChord_nonneg U V ⟨(a : ℕ)/2, hba⟩
      have h0c := principalPlaneChord_nonneg U V ⟨(c : ℕ)/2, hbc⟩
      nlinarith
    -- `a ≤ c < 2m` makes this branch vacuous; the next one is the genuine
    -- nonnegativity of a squared chord
    · omega
    · positivity
    · exact le_rfl
  -- The Gram operator is diagonal in the extended basis.
  have hgram := adjoint_comp_displacement_directRotation U V hacute
  have habs_u := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute
  have habs_j := abs_canonicalIntertwiner_apply_principalOrthogonalVector U V hacute
  have hdiag : ∀ k, (A.adjoint ∘ₗ A) (b k) = ((μ k : ℝ) : 𝕜) • b k := by
    intro k
    -- `hgram` is stated in the unfolded form, so `A` has to be expanded here
    rw [hA]
    by_cases hk : (k : ℕ) < 2 * m
    · have hbk : b k = v k := hb k hk
      rw [hgram, hbk, hv]
      simp only [dite_eq_left hk]
      by_cases hpar : (k : ℕ) % 2 = 0
      · rw [ite_eq_left hpar]
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
          habs_u ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩]
        rw [hμ]
        simp only [dite_eq_left hk]
        rw [principalPlaneChord_sq]
        match_scalars
        ring
      · rw [ite_eq_right hpar]
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
          habs_j ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩]
        rw [hμ]
        simp only [dite_eq_left hk]
        rw [principalPlaneChord_sq]
        match_scalars
        ring
    · -- `b k` is orthogonal to the whole family, so `|S|` fixes it.
      have hperp_u : ∀ i, ⟪principalSourceVector U V i, b k⟫_𝕜 = 0 := by
        intro i
        have hpos : 2 * (i : ℕ) < 2 * m := by omega
        have hval : ((⟨2 * (i : ℕ), by omega⟩ : Fin (finrank 𝕜 E)) : ℕ) < 2 * m := hpos
        have hbu : b ⟨2 * (i : ℕ), by omega⟩ = principalSourceVector U V i := by
          rw [hb _ hval, hv]
          simp only [dite_eq_left hval]
          rw [ite_eq_left (by omega)]
          congr 1
          ext
          simp
        have hne : (⟨2 * (i : ℕ), by omega⟩ : Fin (finrank 𝕜 E)) ≠ k := by
          intro h
          rw [← h] at hk
          exact hk hpos
        rw [← hbu]
        exact b.orthonormal.inner_eq_zero hne
      have hperp_j : ∀ i, ⟪principalOrthogonalVector U V hacute i, b k⟫_𝕜 = 0 := by
        intro i
        have hpos : 2 * (i : ℕ) + 1 < 2 * m := by omega
        have hval : ((⟨2 * (i : ℕ) + 1, by omega⟩ : Fin (finrank 𝕜 E)) : ℕ) < 2 * m := hpos
        have hbj : b ⟨2 * (i : ℕ) + 1, by omega⟩ =
            principalOrthogonalVector U V hacute i := by
          rw [hb _ hval, hv]
          simp only [dite_eq_left hval]
          rw [ite_eq_right (by omega)]
          congr 1
          ext
          simp
          omega
        have hne : (⟨2 * (i : ℕ) + 1, by omega⟩ : Fin (finrank 𝕜 E)) ≠ k := by
          intro h
          rw [← h] at hk
          exact hk hpos
        rw [← hbj]
        exact b.orthonormal.inner_eq_zero hne
      have hproj := projection_eq_projection_of_orthogonal_family U V hacute
        hperp_u hperp_j
      have habs := abs_canonicalIntertwiner_apply_eq_self_of_projection_eq U V hproj
      rw [hgram]
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, habs,
        sub_self, smul_zero, hμ]
      simp [dite_eq_right hk]
  -- Identify the sorted eigenvalues.
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis A.isSymmetric_adjoint_comp_self rfl b
    hμanti hdiag
  rcases lt_or_ge n (finrank 𝕜 E) with hnE | hnE
  · rw [A.singularValues_of_lt rfl hnE, heig]
    rw [hμ]
    simp only
    split_ifs with hn
    · exact Real.sqrt_sq (principalPlaneChord_nonneg U V _)
    · exact Real.sqrt_zero
  · rw [A.singularValues_of_finrank_le hnE]
    rw [dite_eq_right (by omega)]

/-- Closed Ky Fan formula for the direct displacement. -/
theorem kyFanSum_directRotation_displacement_eq_principalChords
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (k : ℕ) :
    kyFanSum k (LinearMap.id - (directRotation U V hacute).toLinearMap) =
      (∑ i : Fin (min (k / 2) (nontrivialAngleCount U V)),
        2 * principalPlaneChord U V
          (Fin.castLE (min_le_right _ _) i)) +
      if hodd : k % 2 = 1 ∧ k / 2 < nontrivialAngleCount U V then
        principalPlaneChord U V ⟨k / 2, hodd.2⟩ else 0 := by
  rw [kyFanSum_eq_sum_fin]
  simp_rw [singularValues_directRotation_displacement U V hacute]
  exact sum_repeated_pair_prefix (fun i => principalPlaneChord U V i) k
end DavisKahan.FiniteDimensional
end TauCeti
