/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63FiniteSource

/-! # Theorem63Trial Data -/

open TauCeti.DavisKahan.Sylvester

/-!
# Theorem 6.3 over abstract trial-block data

The finite-trial Theorem 6.3 chain in `Theorem63FiniteSource.lean` takes a bounded
symmetric ambient operator `T` and derives the compression and Ritz residual from it.  The
paper's unbounded scope claim needs the same chain when the ambient operator is a closed
unbounded self-adjoint operator: there the trial action, its compression, and its residual
are still bounded (the trial subspace sits inside the operator domain with bounded block
data), but no bounded ambient operator exists.

This module isolates exactly what the tangent chain consumes as **data**:

* `Theorem63TrialData`: the bounded trial action `Z →L H`, its compression, and its
  residual, tied by the block identity and residual orthogonality;
* the two **form hypotheses** — the compression bounded above by `α`, and the crossed
  pairing `⟪P_{Vᗮ} z, P_{Vᗮ} (action z)⟫` bounded below by `(α + δ) ‖P_{Vᗮ} z‖²` — the
  latter replacing the unbounded operator's quadratic form on `Vᗮ`, which is only defined
  on the operator domain; on vectors of the form `P_{Vᗮ} z` with `z` in the trial space it
  is available through spectral commutation, and those are the only vectors the singular
  value argument ever uses;
* the finite-trial Ky Fan core over this data
  (`Theorem63TrialData.all_kyFan_core_directedTangent`).

The orthonormality of the residual witnesses is reused from the bounded chain through a
**surrogate operator**: the witness family depends only on the geometry of the sine block
and on its singular values sitting strictly below one, so `Vᗮ.starProjection` itself
serves as a bounded symmetric operator satisfying the bounded chain's hypotheses.

`Theorem63TrialData.ofBounded` recovers the bounded chain's data, so the bounded theorems
are instances.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open Module (finrank)

universe u

section ScalarGeneric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The bounded data of a trial block for the Theorem 6.3 chain: the ambient action of
the trial subspace, its compression back into the trial subspace, and the residual,
tied by the block identity.  For a bounded symmetric ambient operator these are
`T ∘L Z.subtypeL`, `theorem63Compression T Z`, and `theorem63Residual T Z`; for an
unbounded self-adjoint operator whose domain contains the trial subspace they are the
bundled data of an `BoundedCompressionTrialBlock`.

Every field is a bounded map, so the bundle is scalar-generic: it makes sense over a
real Hilbert space exactly as it does over a complex one. -/
structure Theorem63TrialData (Z V : Submodule 𝕜 H)
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] where
  /-- The ambient action of the trial subspace. -/
  action : Z →L[𝕜] H
  /-- The compression of the action back into the trial subspace. -/
  compression : Z →L[𝕜] Z
  /-- The Ritz residual of the trial subspace. -/
  residual : Z →L[𝕜] H
  /-- The compression is symmetric. -/
  compression_isSymmetric : compression.IsSymmetric
  /-- The block identity: action = compression + residual. -/
  action_eq : ∀ z : Z, action z = ((compression z : Z) : H) + residual z
  /-- The residual is orthogonal to the trial subspace. -/
  residual_orthogonal : ∀ (z z' : Z), ⟪residual z, ((z' : Z) : H)⟫_𝕜 = 0

namespace Theorem63TrialData

variable {Z V : Submodule 𝕜 H} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The residual is orthogonal to the trial subspace, inner product on the left. -/
theorem inner_residual_left (data : Theorem63TrialData Z V) (z z' : Z) :
    ⟪((z' : Z) : H), data.residual z⟫_𝕜 = 0 := by
  rw [← inner_conj_symm, data.residual_orthogonal z z', map_zero]

/-- The residual lands in the orthogonal complement of the trial subspace. -/
theorem residual_mem_orthogonal (data : Theorem63TrialData Z V) (z : Z) :
    data.residual z ∈ Zᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  exact data.inner_residual_left z ⟨u, hu⟩

/-- The compression is the trial projection of the action. -/
theorem starProjection_action (data : Theorem63TrialData Z V) (z : Z) :
    Z.starProjection (data.action z) = ((data.compression z : Z) : H) := by
  rw [data.action_eq z, map_add,
    Submodule.starProjection_eq_self_iff.mpr (data.compression z).2,
    (Submodule.starProjection_apply_eq_zero_iff Z).mpr
      (data.residual_mem_orthogonal z), add_zero]

/-- The compression's quadratic form is the ambient pairing of the action. -/
theorem inner_compression_eq (data : Theorem63TrialData Z V) (z : Z) :
    ⟪data.compression z, z⟫_𝕜 = ⟪data.action z, ((z : Z) : H)⟫_𝕜 := by
  rw [Submodule.coe_inner, data.action_eq z, inner_add_left,
    data.residual_orthogonal z z, add_zero]

end Theorem63TrialData

end ScalarGeneric

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace Theorem63TrialData

variable {Z V : Submodule ℂ H} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- The sine-side Sylvester identity, in pure block algebra: projecting the action onto
`Vᗮ` is the sine block of the compression plus the projected residual. -/
theorem sineSylvester (data : Theorem63TrialData Z V) (v : Z) :
    Vᗮ.starProjection (data.action v) =
      theorem63DirectedSineBlock Z V (data.compression v) +
        Vᗮ.starProjection (data.residual v) := by
  rw [data.action_eq v, map_add]
  rfl

/-! ### The bounded instance -/

/-- The trial-block data of a bounded symmetric ambient operator. -/
noncomputable def ofBounded (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Theorem63TrialData Z V where
  action := T ∘L Z.subtypeL
  compression := theorem63Compression T Z
  residual := theorem63Residual T Z
  compression_isSymmetric := by
    intro x y
    calc
      ⟪(theorem63Compression T Z x : Z), y⟫_ℂ =
          ⟪T ((x : Z) : H), ((y : Z) : H)⟫_ℂ := by
        rw [Submodule.coe_inner]
        change ⟪(Z.orthogonalProjectionOnto (T ((x : Z) : H)) : H), ((y : Z) : H)⟫_ℂ = _
        have hc : (Z.orthogonalProjectionOnto (T ((x : Z) : H)) : H) =
            Z.starProjection (T ((x : Z) : H)) := rfl
        rw [hc, Z.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr y.2]
      _ = ⟪((x : Z) : H), T ((y : Z) : H)⟫_ℂ := hT _ _
      _ = ⟪x, theorem63Compression T Z y⟫_ℂ := by
        rw [Submodule.coe_inner]
        change _ = ⟪((x : Z) : H), (Z.orthogonalProjectionOnto (T ((y : Z) : H)) : H)⟫_ℂ
        have hc : (Z.orthogonalProjectionOnto (T ((y : Z) : H)) : H) =
            Z.starProjection (T ((y : Z) : H)) := rfl
        rw [hc, ← Z.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr x.2]
  action_eq := fun z => by
    change T ((z : Z) : H) = ((theorem63Compression T Z z : Z) : H) +
      theorem63Residual T Z z
    have h := theorem63Residual_eq_complementaryProjection T Z
    have hz := congrArg (fun L : Z →L[ℂ] H => L z) h
    simp only [ContinuousLinearMap.comp_apply] at hz
    have hsplit := (Submodule.starProjection_add_starProjection_orthogonal
      (K := Z) (T ((z : Z) : H))).symm
    rw [hz]
    have hc : ((theorem63Compression T Z z : Z) : H) =
        Z.starProjection (T ((z : Z) : H)) := rfl
    rw [hc]
    exact hsplit
  residual_orthogonal := fun z z' =>
    Submodule.inner_left_of_mem_orthogonal z'.2
      (theorem63Residual_apply_mem_orthogonal T Z z)

omit [CompleteSpace H] in
/-- The bounded instance's residual is the Ritz residual. -/
theorem ofBounded_residual (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (ofBounded T hT Z V).residual = theorem63Residual T Z := rfl

omit [CompleteSpace H] in
/-- The bounded instance's compression is the Ritz compression. -/
theorem ofBounded_compression (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (ofBounded T hT Z V).compression = theorem63Compression T Z := rfl

omit [CompleteSpace H] in
/-- The crossed form hypothesis holds for a bounded symmetric operator that reduces `V`
and is bounded below on `Vᗮ`. -/
theorem ofBounded_crossed_lower (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hV : T.Reduces V) {c : ℝ}
    (hUnwantedLower : ∀ y ∈ Vᗮ, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ) (z : Z) :
    c * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection ((ofBounded T hT Z V).action z)⟫_ℂ := by
  set y : H := Vᗮ.starProjection ((z : Z) : H) with hy_def
  have hyV : y ∈ Vᗮ := Vᗮ.starProjection_apply_mem _
  have haction : (ofBounded T hT Z V).action z = T ((z : Z) : H) := rfl
  have hsplit : T ((z : Z) : H) =
      T (V.starProjection ((z : Z) : H)) + T y := by
    rw [hy_def, ← map_add]
    congr 1
    exact (Submodule.starProjection_add_starProjection_orthogonal
      (K := V) ((z : Z) : H)).symm
  have hpair : ⟪y, Vᗮ.starProjection (T ((z : Z) : H))⟫_ℂ = ⟪y, T y⟫_ℂ := by
    rw [← Vᗮ.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hyV, hsplit, inner_add_right]
    have hTV : T (V.starProjection ((z : Z) : H)) ∈ V :=
      hV.1 _ (V.starProjection_apply_mem _)
    rw [Submodule.inner_left_of_mem_orthogonal hTV hyV, zero_add]
  rw [haction, hpair]
  have h := hUnwantedLower y hyV
  calc
    c * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := h
    _ = RCLike.re ⟪y, T y⟫_ℂ := by
      rw [← inner_conj_symm, RCLike.conj_re]

/-! ### Restriction to a subspace of the trial space -/

/-- The continuous inclusion of one submodule into a larger one. -/
noncomputable def inclCLM {F Z : Submodule ℂ H} (hFZ : F ≤ Z) : F →L[ℂ] Z :=
  (Submodule.inclusion hFZ).mkContinuous 1 (fun x => by
    change ‖((x : F) : H)‖ ≤ 1 * ‖x‖
    simp)

omit [CompleteSpace H] in
/-- The inclusion does not move the ambient vector. -/
theorem inclCLM_coe {F Z : Submodule ℂ H} (hFZ : F ≤ Z) (x : F) :
    ((inclCLM hFZ x : Z) : H) = ((x : F) : H) := rfl

/-- **Trial-block data from a bounded symmetric action on the trial subspace.**

The compression and the residual are not extra data: they are the trial projection of the
action and its complementary part.  Everything the bundle asks for is then a consequence
of the action being symmetric on the trial subspace.

This is the constructor the ambient operator never appears in, so it is the one an
unbounded ambient operator — or an unbounded Ritz compression truncated to a reducing
subspace — can use. -/
noncomputable def ofAction (Z V : Submodule ℂ H)
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (act : Z →L[ℂ] H)
    (hsym : ∀ z z' : Z, ⟪act z, ((z' : Z) : H)⟫_ℂ = ⟪((z : Z) : H), act z'⟫_ℂ) :
    Theorem63TrialData Z V where
  action := act
  compression := Z.orthogonalProjectionOnto ∘L act
  residual := act - Z.subtypeL ∘L (Z.orthogonalProjectionOnto ∘L act)
  compression_isSymmetric := by
    intro x y
    have hx : ⟪(Z.orthogonalProjectionOnto (act x) : Z), y⟫_ℂ =
        ⟪act x, ((y : Z) : H)⟫_ℂ := by
      rw [Submodule.coe_inner]
      have hc : ((Z.orthogonalProjectionOnto (act x) : Z) : H) =
          Z.starProjection (act x) := rfl
      rw [hc, Z.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr y.2]
    have hy : ⟪x, (Z.orthogonalProjectionOnto (act y) : Z)⟫_ℂ =
        ⟪((x : Z) : H), act y⟫_ℂ := by
      rw [Submodule.coe_inner]
      have hc : ((Z.orthogonalProjectionOnto (act y) : Z) : H) =
          Z.starProjection (act y) := rfl
      rw [hc, ← Z.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr x.2]
    calc
      ⟪((Z.orthogonalProjectionOnto ∘L act) x : Z), y⟫_ℂ =
          ⟪act x, ((y : Z) : H)⟫_ℂ := hx
      _ = ⟪((x : Z) : H), act y⟫_ℂ := hsym x y
      _ = ⟪x, ((Z.orthogonalProjectionOnto ∘L act) y : Z)⟫_ℂ := hy.symm
  action_eq := fun z => by
    simp only [ContinuousLinearMap.comp_apply, sub_apply]
    have hc : ((Z.orthogonalProjectionOnto (act z) : Z) : H) =
        Z.starProjection (act z) := rfl
    change act z =
      Z.starProjection (act z) + (act z - Z.starProjection (act z))
    abel
  residual_orthogonal := fun z z' => by
    simp only [ContinuousLinearMap.comp_apply, sub_apply]
    change ⟪act z - Z.starProjection (act z), ((z' : Z) : H)⟫_ℂ = 0
    exact Submodule.inner_left_of_mem_orthogonal z'.2
      (Submodule.sub_starProjection_mem_orthogonal (K := Z) (act z))

omit [CompleteSpace H] in
/-- The action of `ofAction` is the supplied action. -/
@[simp] theorem ofAction_action (Z V : Submodule ℂ H)
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (act : Z →L[ℂ] H)
    (hsym : ∀ z z' : Z, ⟪act z, ((z' : Z) : H)⟫_ℂ = ⟪((z : Z) : H), act z'⟫_ℂ) :
    (ofAction Z V act hsym).action = act := rfl

omit [CompleteSpace H] in
/-- The residual of `ofAction` is the complementary part of the action. -/
theorem ofAction_residual_apply (Z V : Submodule ℂ H)
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (act : Z →L[ℂ] H)
    (hsym : ∀ z z' : Z, ⟪act z, ((z' : Z) : H)⟫_ℂ = ⟪((z : Z) : H), act z'⟫_ℂ)
    (z : Z) :
    (ofAction Z V act hsym).residual z = act z - Z.starProjection (act z) := rfl

/-- The trial-block data restricted to a subspace of the trial space. -/
noncomputable def restrict (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] :
    Theorem63TrialData F V :=
  ofAction F V (data.action ∘L inclCLM hFZ) (by
    intro x y
    have h1 : ⟪data.action (inclCLM hFZ x), ((y : F) : H)⟫_ℂ =
        ⟪data.compression (inclCLM hFZ x), inclCLM hFZ y⟫_ℂ := by
      rw [data.action_eq (inclCLM hFZ x), inner_add_left]
      have hres := data.residual_orthogonal (inclCLM hFZ x) (inclCLM hFZ y)
      rw [inclCLM_coe] at hres
      rw [hres, add_zero, Submodule.coe_inner]
      rfl
    have h2 : ⟪((x : F) : H), data.action (inclCLM hFZ y)⟫_ℂ =
        ⟪inclCLM hFZ x, data.compression (inclCLM hFZ y)⟫_ℂ := by
      rw [data.action_eq (inclCLM hFZ y), inner_add_right]
      have hres := data.inner_residual_left (inclCLM hFZ y) (inclCLM hFZ x)
      rw [inclCLM_coe] at hres
      rw [hres, add_zero, Submodule.coe_inner]
      rfl
    change ⟪data.action (inclCLM hFZ x), ((y : F) : H)⟫_ℂ =
      ⟪((x : F) : H), data.action (inclCLM hFZ y)⟫_ℂ
    rw [h1, h2]
    exact data.compression_isSymmetric _ _)

omit [CompleteSpace H] in
/-- The restricted action, applied. -/
theorem restrict_action_apply (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] (f : F) :
    (data.restrict F hFZ).action f = data.action (inclCLM hFZ f) := rfl

omit [CompleteSpace H] in
/-- The compression form bound restricts to every subspace of the trial space. -/
theorem restrict_compression_upper (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] {alpha : ℝ}
    (hM : ∀ z : Z, RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2) :
    ∀ f : F, RCLike.re ⟪(data.restrict F hFZ).compression f, f⟫_ℂ ≤
      alpha * ‖f‖ ^ 2 := by
  intro f
  have h1 : ⟪(data.restrict F hFZ).compression f, f⟫_ℂ =
      ⟪(data.restrict F hFZ).action f, ((f : F) : H)⟫_ℂ :=
    (data.restrict F hFZ).inner_compression_eq f
  have h2 : ⟪data.compression (inclCLM hFZ f), inclCLM hFZ f⟫_ℂ =
      ⟪data.action (inclCLM hFZ f), ((inclCLM hFZ f : Z) : H)⟫_ℂ :=
    data.inner_compression_eq (inclCLM hFZ f)
  have hle := hM (inclCLM hFZ f)
  rw [h2] at hle
  rw [h1, restrict_action_apply]
  have hcoe : ((inclCLM hFZ f : Z) : H) = ((f : F) : H) := rfl
  rw [hcoe] at hle
  have hnorm : ‖inclCLM hFZ f‖ = ‖f‖ := rfl
  rw [hnorm] at hle
  exact hle

omit [CompleteSpace H] in
/-- The crossed lower form bound restricts to every subspace of the trial space. -/
theorem restrict_crossed_lower (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] {c : ℝ}
    (hVl : ∀ z : Z, c * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection (data.action z)⟫_ℂ) :
    ∀ f : F, c * ‖Vᗮ.starProjection ((f : F) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((f : F) : H),
        Vᗮ.starProjection ((data.restrict F hFZ).action f)⟫_ℂ := by
  intro f
  have h := hVl (inclCLM hFZ f)
  have hcoe : ((inclCLM hFZ f : Z) : H) = ((f : F) : H) := rfl
  rw [hcoe] at h
  rw [restrict_action_apply]
  exact h


/-! ### The Theorem 6.3 chain over trial-block data

The *crossed action* the equation-(6.6) estimate needs is not extra data: it is
`P_{Vᗮ} ∘ action`.  For a bounded operator reducing `V` that is `T (P_{Vᗮ} z)`, and for an
unbounded self-adjoint operator whose domain contains the trial space and whose `V` is a
spectral subspace it is `A (P_{Vᗮ} z)` — the spectral projection preserves the domain, so
the crossed quadratic form is defined exactly at the vectors the singular-value argument
evaluates it on, even though the operator is unbounded on `Vᗮ`.

`sineSylvester` above is already the Sylvester identity for that choice, so the whole
chain rests on the two printed form bounds and nothing else. -/

section Chain

variable {Z V : Submodule ℂ H} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- On a trial vector that already lies in `Vᗮ`, the crossed form is the compression's
quadratic form.  This is what turns the two printed form bounds into a contradiction at a
sine value of one. -/
theorem crossed_eq_compression_of_mem_orthogonal (data : Theorem63TrialData Z V)
    (z : Z) (hz : ((z : Z) : H) ∈ Vᗮ) :
    RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection (data.action z)⟫_ℂ =
      RCLike.re ⟪data.compression z, z⟫_ℂ := by
  have hfix : Vᗮ.starProjection ((z : Z) : H) = ((z : Z) : H) :=
    Submodule.starProjection_eq_self_iff.mpr hz
  have h1 : ⟪Vᗮ.starProjection ((z : Z) : H),
      Vᗮ.starProjection (data.action z)⟫_ℂ =
      ⟪((z : Z) : H), data.action z⟫_ℂ := by
    rw [hfix, ← Vᗮ.inner_starProjection_left_eq_right, hfix]
  rw [h1, data.inner_compression_eq z]
  conv_lhs => rw [← inner_conj_symm]
  rw [RCLike.conj_re]

omit [CompleteSpace H] in
/-- **Directed transversality over trial-block data.**  The printed form gap forces the
coordinate projection from the trial space onto `V` to be injective. -/
theorem transverse_of_formBounds (data : Theorem63TrialData Z V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection (data.action z)⟫_ℂ) :
    Function.Injective (V.orthogonalProjectionOnto ∘L Z.subtypeL) := by
  intro x y hxy
  have hproj : V.starProjection (((x - y : Z) : H)) = 0 := by
    have hp := congrArg Subtype.val hxy
    change V.starProjection (x : H) = V.starProjection (y : H) at hp
    simpa [map_sub] using sub_eq_zero.mpr hp
  have hperp : ((x - y : Z) : H) ∈ Vᗮ :=
    (Submodule.starProjection_apply_eq_zero_iff V).mp hproj
  have hfix : Vᗮ.starProjection (((x - y : Z) : H)) = ((x - y : Z) : H) :=
    Submodule.starProjection_eq_self_iff.mpr hperp
  have hlower := hcross (x - y)
  rw [crossed_eq_compression_of_mem_orthogonal data (x - y) hperp, hfix] at hlower
  have hupper := hMupper (x - y)
  have hnorm : ‖((x - y : Z) : H)‖ = ‖x - y‖ := rfl
  rw [hnorm] at hlower
  have hzero : x - y = 0 := by
    by_contra hne
    have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr hne
    nlinarith [sq_pos_of_pos hn]
  exact sub_eq_zero.mp hzero

omit [CompleteSpace H] in
/-- **No pole, over trial-block data.**  Under the printed form gap every directed sine
singular value is strictly below one, so every tangent the theorem names is finite. -/
theorem sine_lt_one_of_formBounds (data : Theorem63TrialData Z V)
    [FiniteDimensional ℂ Z]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection (data.action z)⟫_ℂ)
    (i : Fin (finrank ℂ Z)) :
    finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i < 1 := by
  let S := theorem63DirectedSineBlock Z V
  let v := finiteSourceRightSingularBasis S i
  have hle : finiteSourceSingularValue S i ≤ 1 :=
    theorem63_singularValues_sine_le_one Z V i
  by_contra hlt
  have hsigma : finiteSourceSingularValue S i = 1 :=
    le_antisymm hle (not_lt.mp hlt)
  have hvnorm : ‖v‖ = 1 := (finiteSourceRightSingularBasis S).orthonormal.norm_eq_one i
  have hSnorm : ‖S v‖ = 1 := by
    rw [norm_apply_finiteSourceRightSingularBasis, hsigma]
  have hperpnorm : ‖Vᗮ.starProjection (v : H)‖ = 1 := hSnorm
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (v : H) V
  have hvambient : ‖(v : H)‖ = 1 := hvnorm
  have hprojnorm : ‖V.starProjection (v : H)‖ = 0 := by
    rw [hvambient, hperpnorm] at hpyth
    nlinarith [norm_nonneg (V.starProjection (v : H))]
  have hprojzero : V.starProjection (v : H) = 0 := norm_eq_zero.mp hprojnorm
  have hinj := transverse_of_formBounds data hdelta hMupper hcross
  have hvzero : v = 0 := by
    apply hinj
    apply Subtype.ext
    change V.starProjection (v : H) = V.starProjection (0 : H)
    simpa using hprojzero
  exact (finiteSourceRightSingularBasis S).orthonormal.ne_zero i hvzero

/-- **The Ky Fan tangent inequalities over trial-block data**, for prefixes within the
trial dimension. -/
private theorem kyFan_core_of_le_finrank (data : Theorem63TrialData Z V)
    [FiniteDimensional ℂ Z]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection (data.action z)⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    {k : ℕ} (hk : k ≤ finrank ℂ Z) :
    delta * kyFanApproximationGauge k tanTheta0 ≤
      kyFanApproximationGauge k data.residual := by
  have hlt := sine_lt_one_of_formBounds data hdelta hMupper hcross
  let castIndex : Fin k → Fin (finrank ℂ Z) := fun i => Fin.castLE hk i
  have huFull := orthonormal_theorem63ResidualWitness Z V hlt
  have hu : Orthonormal ℂ
      (fun i : Fin k => theorem63ResidualWitness Z V (castIndex i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [castIndex] using
      (orthonormal_iff_ite.mp huFull (castIndex i) (castIndex j))
  have hv : Orthonormal ℂ
      (fun i : Fin k =>
        (finiteSourceRightSingularBasis
          (theorem63DirectedSineBlock Z V) (castIndex i) : Z)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [castIndex] using
      (orthonormal_iff_ite.mp
        (finiteSourceRightSingularBasis
          (theorem63DirectedSineBlock Z V)).orthonormal
        (castIndex i) (castIndex j))
  have hscalar : ∀ i : Fin k,
      delta * approximationSingularValue (castIndex i) tanTheta0 ≤
        RCLike.re ⟪theorem63ResidualWitness Z V (castIndex i),
          data.residual (finiteSourceRightSingularBasis
            (theorem63DirectedSineBlock Z V) (castIndex i))⟫_ℂ := by
    intro i
    refine theorem63ResidualWitness_scalar_of_data V Z
      data.compression data.residual (Vᗮ.starProjection ∘L data.action)
      hMupper hcross data.residual_orthogonal ?_ hlt tanTheta0 htan (castIndex i)
    intro z
    have h := data.sineSylvester z
    change Vᗮ.starProjection (data.action z) -
      theorem63DirectedSineBlock Z V (data.compression z) = _
    rw [h]
    abel
  have hsum := sum_le_kyFanApproximationGauge_of_orthonormal
    data.residual hu hv hscalar
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge at hsum ⊢
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  simpa [castIndex, approximationSingularValue] using hsum

/-- **Theorem 6.3's Ky Fan root over trial-block data.**

Only the two printed form bounds are assumed: the compression is bounded above by `α`,
and the crossed form is bounded below by `α + δ`.  Nothing here mentions a bounded ambient
operator, which is what lets the unbounded scope claim reuse the chain. -/
theorem all_kyFan_core_of_formBounds (data : Theorem63TrialData Z V)
    [FiniteDimensional ℂ Z]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection (data.action z)⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0) :
    ∀ k, delta * kyFanApproximationGauge k tanTheta0 ≤
      kyFanApproximationGauge k data.residual := by
  intro k
  by_cases hk : k ≤ finrank ℂ Z
  · exact kyFan_core_of_le_finrank data hdelta hMupper hcross tanTheta0 htan hk
  · have hdk : finrank ℂ Z ≤ k := Nat.le_of_not_ge hk
    rw [kyFanApproximationGauge_eq_finrank_of_finrank_le tanTheta0 hdk,
      kyFanApproximationGauge_eq_finrank_of_finrank_le data.residual hdk]
    exact kyFan_core_of_le_finrank data hdelta hMupper hcross tanTheta0 htan le_rfl

/-- **Theorem 6.3 at ideal-gauge scope over trial-block data.** -/
theorem ideal_of_formBounds (data : Theorem63TrialData Z V)
    [FiniteDimensional ℂ Z]
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection (data.action z)⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    (hResidual : N.Mem data.residual) :
    N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge data.residual :=
  ExactSinTheta.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hdelta hResidual
    (all_kyFan_core_of_formBounds data hdelta hMupper hcross tanTheta0 htan)

end Chain

end Theorem63TrialData

end TanTheta
end DavisKahan
end TauCeti
