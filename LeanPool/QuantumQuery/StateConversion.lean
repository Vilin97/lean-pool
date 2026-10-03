/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
module

public import LeanPool.QuantumQuery.Adversary
public import LeanPool.QuantumQuery.Algorithms
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Spectral detection and coherent state conversion

Ported from the corresponding upstream modules listed by the source sections below.
References beginning with `Source` name these retained sections.
-/

public section

section SourceQuantumChordGap

/-!
# The chord form of a unitary

**A spike for the spectral layer.**  Spectral windows for a unitary `U` are
usually stated with `Complex.arg` of its eigenvalues, which drags in branch cuts
and trigonometry.  The **chord distance** `‖1 - z‖` avoids that, and it has a
matrix avatar that avoids diagonalizing `U` at all:

  `chordSq U = (1 - U)ᴴ (1 - U)`.

This matrix is Hermitian (`chordSq_conjTranspose`) and positive semidefinite, so
Mathlib's spectral theory
for *Hermitian* matrices applies directly — no eigenbasis for a general unitary
is needed.  Its quadratic form is exactly the squared chord distance
(`qNormSq_sub_mulVec`), so "the eigenvalues of `chordSq U` are at most `Δ²`" is
precisely "the chord-distance window of threshold `Δ²`" (equivalently of radius
`|Δ|` — nothing here assumes `Δ` nonnegative).

Two facts make one Hermitian decomposition serve both halves of the phase
detector:

* `chordSq_commute` — `chordSq U` commutes with `U`, so `U` preserves each of
  its spectral subspaces.  This is what removes the need for simultaneous
  diagonalization: the windows are defined by a Hermitian matrix, and `U` acts
  within them.
* `one_sub_mul_geom_sum` — `(1 - U) ∑_{t<T} U^t = 1 - U^T`, the telescoping
  identity behind the uniform-clock estimate on the far window.

On a unitary the chord form collapses to `2 - U - Uᴴ`, which is where both
facts come from.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The chord form of `U`: `(1 - U)ᴴ (1 - U)`. -/
def chordSq (U : Matrix H H ℂ) : Matrix H H ℂ := (1 - U)ᴴ * (1 - U)

/-- The chord form is Hermitian — stated as the raw identity, so this section needs
no extra Mathlib import. -/
lemma chordSq_conjTranspose (U : Matrix H H ℂ) : (chordSq U)ᴴ = chordSq U := by
  unfold chordSq
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- **The quadratic form of `chordSq` is the squared chord distance.**  This is
what makes a spectral window of `chordSq U` a chord-distance window. -/
theorem qNormSq_sub_mulVec (U : Matrix H H ℂ) (ψ : H → ℂ) :
    qNormSq ((1 - U) *ᵥ ψ) = (qInner ψ (chordSq U *ᵥ ψ)).re := by
  have h : qInner ((1 - U) *ᵥ ψ) ((1 - U) *ᵥ ψ) = qInner ψ (chordSq U *ᵥ ψ) := by
    rw [qInner_mulVec_left, chordSq, ← Matrix.mulVec_mulVec]
  rw [← h, qInner_self, Complex.ofReal_re]

/-- On a unitary the chord form collapses. -/
theorem chordSq_eq_of_unitary {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) : chordSq U = 1 + 1 - U - Uᴴ := by
  have h1 : Uᴴ * U = 1 := conjTranspose_mul_self_of_unitary hU
  unfold chordSq
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub,
    Matrix.one_mul, Matrix.mul_one, h1]
  abel

/-- **The chord form commutes with the unitary**, so `U` preserves each spectral
subspace of `chordSq U`.  No simultaneous diagonalization is needed. -/
theorem chordSq_commute {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    chordSq U * U = U * chordSq U := by
  have h1 : Uᴴ * U = 1 := conjTranspose_mul_self_of_unitary hU
  have h2 : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [chordSq_eq_of_unitary hU]
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2]

/-- The chord form kills exactly what `1 - U` kills. -/
theorem chordSq_mulVec_eq_zero_iff (U : Matrix H H ℂ) (ψ : H → ℂ) :
    chordSq U *ᵥ ψ = 0 ↔ (1 - U) *ᵥ ψ = 0 := by
  constructor
  · intro h
    have hq := qNormSq_sub_mulVec U ψ
    rw [h, qInner_zero_right, Complex.zero_re] at hq
    exact qNormSq_eq_zero_iff.mp hq
  · intro h
    rw [chordSq, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- **The core identity of the effective gap.**  If `L` (the plan's `Λ`) kills
`w`, the product of the two reflections moves `w` by exactly `2 P w` (the plan's
`2 Π w`).  `Π` is reserved notation in Lean, hence the renaming. -/
theorem one_sub_qRefl_mul_qRefl_mulVec {P L : Matrix H H ℂ} {w : H → ℂ}
    (hw : L *ᵥ w = 0) :
    (1 - qRefl P * qRefl L) *ᵥ w = (2 : ℂ) • (P *ᵥ w) := by
  have h1 : qRefl L *ᵥ w = -w := by
    rw [qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, hw, Matrix.one_mulVec, smul_zero,
      zero_sub]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, h1, qRefl,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg]
  module

/-- **The telescoping identity** behind the uniform clock. -/
theorem one_sub_mul_geom_sum (U : Matrix H H ℂ) (T : ℕ) :
    (1 - U) * (∑ t ∈ Finset.range T, U ^ t) = 1 - U ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, mul_add, ih, sub_mul, Matrix.one_mul, ← pow_succ']
      abel

end QuantumQueryComplexity

end SourceQuantumChordGap

section SourceQuantumProjector

/-!
# Orthogonal projectors and reflections, as raw matrices

**A spike, to fix the representation before the witness construction.**

The upper bound reflects about the span of a finite family of vectors coming
from a `DualPair`.  Rather than build projectors by hand, construct the subspace
in `EuclideanSpace ℂ H`, take Mathlib's `Submodule.starProjection`, and carry it
back to a raw `Matrix H H ℂ`.

The transport is `Matrix.toEuclideanCLM`, which is a **star-algebra
equivalence** — not merely a linear one.  That single fact is what makes this
representation the right one: idempotence and self-adjointness of the projector
come from `map_mul` and `map_star`, with no matrix computation at all, and
`IsQProjector` (hence `qRefl`, already proved unitary and involutive) follows
immediately.

## What the spike establishes

* `subProj_mulVec` — the raw action: `subProj K *ᵥ ψ` is `K.starProjection`
  applied to `ψ`, read back through `WithLp`.
* `subProj_mulVec_of_mem` / `subProj_mulVec_of_mem_orthogonal` — the **fixed
  space** and the **killed space**, the two characterizations a reflection
  argument actually uses.
* `isQProjector_subProj`, and hence `subRefl` with `subRefl_mul_self`,
  `subRefl_mem_unitaryGroup`, `subRefl_mulVec_of_mem` (`+ψ`) and
  `subRefl_mulVec_of_mem_orthogonal` (`-ψ`).
* `spanProj` / `spanRefl` — the finite-span case, which is the one the witness
  construction needs.

The membership side conditions are stated in `EuclideanSpace` (`WithLp.toLp 2 ψ ∈ K`)
rather than raw, deliberately: that is where the span of a family of vectors is
easy to reason about, and `WithLp.toLp` is an equivalence, so nothing is lost.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-! ## The projector -/

/-- The orthogonal projector onto `K`, as a raw matrix. -/
noncomputable def subProj (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : Matrix H H ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := H)).symm K.starProjection

lemma toEuclideanCLM_subProj (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (subProj K) = K.starProjection :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := H)).apply_symm_apply _

/-- **The raw action of the projector.** -/
theorem subProj_mulVec (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] (ψ : H → ℂ) :
    (WithLp.toLp 2 (subProj K *ᵥ ψ) : EuclideanSpace ℂ H)
      = K.starProjection (WithLp.toLp 2 ψ) := by
  rw [← Matrix.toEuclideanCLM_toLp, toEuclideanCLM_subProj]

/-- **It is an orthogonal projector.**  Both halves come from
`Matrix.toEuclideanCLM` being a star-algebra equivalence. -/
theorem isQProjector_subProj (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : IsQProjector (subProj K) := by
  let e := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := H)).symm
  constructor
  · change star (e K.starProjection) = e K.starProjection
    exact (e.map_star' K.starProjection).symm.trans
      (congrArg e (isSelfAdjoint_starProjection K))
  · change e K.starProjection * e K.starProjection = e K.starProjection
    exact (e.map_mul' K.starProjection K.starProjection).symm.trans
      (congrArg e K.isIdempotentElem_starProjection)

/-- **The fixed space.** -/
theorem subProj_mulVec_of_mem (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ K) : subProj K *ᵥ ψ = ψ := by
  have h1 := subProj_mulVec K ψ
  rw [Submodule.starProjection_eq_self_iff.mpr h] at h1
  exact WithLp.toLp_injective 2 h1

/-- **The fixed space, as an iff.**  What a witness construction has to hit:
being fixed by the projector *is* membership. -/
theorem subProj_mulVec_eq_self_iff (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] (ψ : H → ℂ) :
    subProj K *ᵥ ψ = ψ ↔ (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ K := by
  constructor
  · intro h
    have h1 := subProj_mulVec K ψ
    rw [h] at h1
    exact Submodule.starProjection_eq_self_iff.mp h1.symm
  · exact subProj_mulVec_of_mem K

/-- **The killed space.** -/
theorem subProj_mulVec_of_mem_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ Kᗮ) : subProj K *ᵥ ψ = 0 := by
  have h1 := subProj_mulVec K ψ
  rw [(Submodule.starProjection_apply_eq_zero_iff K).mpr h] at h1
  have h2 : (WithLp.toLp 2 (subProj K *ᵥ ψ) : EuclideanSpace ℂ H)
      = WithLp.toLp 2 (0 : H → ℂ) := by
    rw [h1]
    rfl
  exact WithLp.toLp_injective 2 h2

/-! ## The reflection -/

/-- The reflection about `K`. -/
noncomputable def subRefl (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : Matrix H H ℂ := qRefl (subProj K)

theorem subRefl_mem_unitaryGroup (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] :
    subRefl K ∈ Matrix.unitaryGroup H ℂ :=
  qRefl_mem_unitaryGroup (isQProjector_subProj K)

theorem subRefl_mul_self (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : subRefl K * subRefl K = 1 :=
  qRefl_mul_self (isQProjector_subProj K)

lemma subRefl_mulVec (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] (ψ : H → ℂ) :
    subRefl K *ᵥ ψ = (2 : ℂ) • (subProj K *ᵥ ψ) - ψ := by
  rw [subRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **The reflection fixes `K`.** -/
theorem subRefl_mulVec_of_mem (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ K) : subRefl K *ᵥ ψ = ψ := by
  rw [subRefl_mulVec, subProj_mulVec_of_mem K h]
  module

/-- **The reflection negates `Kᗮ`.** -/
theorem subRefl_mulVec_of_mem_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ Kᗮ) : subRefl K *ᵥ ψ = -ψ := by
  rw [subRefl_mulVec, subProj_mulVec_of_mem_orthogonal K h]
  module

/-! ## The orthogonal complement

**The sign matters.**  The plan's `Λ` is the projector onto `span{ψₓ}ᗮ`, and its
reflection is *minus* the reflection about the span.  A global sign shifts every
eigenphase by `π`, so it cannot be dropped when the operator is fed to
controlled phase detection. -/

/-- **The projector onto the orthogonal complement.** -/
theorem subProj_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : subProj Kᗮ = 1 - subProj K := by
  rw [subProj, subProj, Submodule.starProjection_orthogonal', map_sub, map_one]

/-- **The reflection about the complement is minus the reflection about the
subspace.**  This is the sign that must not be dropped. -/
theorem subRefl_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : subRefl Kᗮ = - subRefl K := by
  rw [subRefl, subRefl, qRefl, qRefl, subProj_orthogonal]
  module

/-! ## Finite spans

The case the witness construction needs: reflect about the span of a finite
family of raw vectors. -/

/-- The subspace spanned by a finite family of raw vectors. -/
noncomputable def rawSpan {ι' : Type} (v : ι' → (H → ℂ)) :
    Submodule ℂ (EuclideanSpace ℂ H) :=
  Submodule.span ℂ (Set.range fun i => (WithLp.toLp 2 (v i) : EuclideanSpace ℂ H))

omit [DecidableEq H] in
/-- **Orthogonality to a span is orthogonality to its generators.**  This is the
form a witness construction can actually verify: one inner product per
generator, no spans. -/
theorem mem_rawSpan_orthogonal_iff {ι' : Type} (v : ι' → (H → ℂ)) (ψ : H → ℂ) :
    (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ (rawSpan v)ᗮ ↔ ∀ i, qInner (v i) ψ = 0 := by
  classical
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h i
    rw [qInner_eq_euclidean]
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [← qInner_eq_euclidean]
        exact h i
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- The projector onto the span of a finite family. -/
noncomputable def spanProj {ι' : Type} (v : ι' → (H → ℂ)) : Matrix H H ℂ :=
  subProj (rawSpan v)

/-- The reflection about the span of a finite family. -/
noncomputable def spanRefl {ι' : Type} (v : ι' → (H → ℂ)) : Matrix H H ℂ :=
  subRefl (rawSpan v)

theorem isQProjector_spanProj {ι' : Type} (v : ι' → (H → ℂ)) :
    IsQProjector (spanProj v) := isQProjector_subProj _

theorem spanRefl_mem_unitaryGroup {ι' : Type} (v : ι' → (H → ℂ)) :
    spanRefl v ∈ Matrix.unitaryGroup H ℂ := subRefl_mem_unitaryGroup _

theorem spanRefl_mul_self {ι' : Type} (v : ι' → (H → ℂ)) :
    spanRefl v * spanRefl v = 1 := subRefl_mul_self _

/-- The projector onto the complement of a span. -/
theorem spanProj_orthogonal {ι' : Type} (v : ι' → (H → ℂ)) :
    subProj (rawSpan v)ᗮ = 1 - spanProj v := subProj_orthogonal _

/-- **The reflection about the complement of a span**, with its sign. -/
theorem spanRefl_orthogonal {ι' : Type} (v : ι' → (H → ℂ)) :
    subRefl (rawSpan v)ᗮ = - spanRefl v := subRefl_orthogonal _

/-- Each spanning vector is fixed by the projector. -/
theorem spanProj_mulVec_self {ι' : Type} (v : ι' → (H → ℂ)) (i : ι') :
    spanProj v *ᵥ v i = v i :=
  subProj_mulVec_of_mem _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Each spanning vector is fixed by the reflection. -/
theorem spanRefl_mulVec_self {ι' : Type} (v : ι' → (H → ℂ)) (i : ι') :
    spanRefl v *ᵥ v i = v i :=
  subRefl_mulVec_of_mem _ (Submodule.subset_span ⟨i, rfl⟩)

end QuantumQueryComplexity

end SourceQuantumProjector

section SourceQuantumChordWindow

/-!
# The chord-distance spectral windows

The near and far windows of a unitary `U` at **threshold `Δ²`** — equivalently
chord radius `|Δ|`, since `Δ` is not assumed nonnegative anywhere — as the
spectral projectors of the **Hermitian** matrix `chordSq U = (1-U)ᴴ(1-U)`:

  `chordNearProj U Δ = cfc (fun l => if l ≤ Δ² then 1 else 0) (chordSq U)`,
  `chordFarProj  U Δ = 1 - chordNearProj U Δ`.

Two things make this work where diagonalizing a general unitary would not:

* **The discontinuous mask is legitimate.**  Mathlib's `cfc` needs the function
  continuous only *on the spectrum*, and a matrix has finite real spectrum
  (`Matrix.finite_real_spectrum`), which is discrete — so
  `Set.Finite.continuousOn` discharges every side condition.  Nothing here is an
  approximation of an indicator; it *is* the indicator.
* **`U` preserves the windows.**  `chordSq_commute` says `U` commutes with
  `chordSq U`, and `Commute.cfc_real` upgrades that to commuting with any `cfc`
  of it.  No simultaneous diagonalization, and no eigenbasis for `U`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The complement of a projector is a projector. -/
lemma IsQProjector.one_sub {P : Matrix H H ℂ} (hP : IsQProjector P) :
    IsQProjector (1 - P) := by
  constructor
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1]
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP.2]
    abel

lemma isSelfAdjoint_chordSq (U : Matrix H H ℂ) : IsSelfAdjoint (chordSq U) := by
  change star (chordSq U) = chordSq U
  rw [Matrix.star_eq_conjTranspose]
  exact chordSq_conjTranspose U

/-- The near-window mask.  Discontinuous on `ℝ`, but that is irrelevant: it is
only ever restricted to a finite spectrum. -/
noncomputable def chordMask (Δ : ℝ) : ℝ → ℝ := fun l => if l ≤ Δ ^ 2 then 1 else 0

lemma continuousOn_chordMask (A : Matrix H H ℂ) (Δ : ℝ) :
    ContinuousOn (chordMask Δ) (spectrum ℝ A) :=
  Matrix.finite_real_spectrum.continuousOn _

lemma chordMask_mul_self (Δ : ℝ) (l : ℝ) :
    chordMask Δ l * chordMask Δ l = chordMask Δ l := by
  unfold chordMask
  by_cases h : l ≤ Δ ^ 2 <;> simp [h]

/-- **The near window**: the spectral projector of `chordSq U` for eigenvalues
at most `Δ²`, i.e. chord distance at most `|Δ|`. -/
noncomputable def chordNearProj (U : Matrix H H ℂ) (Δ : ℝ) : Matrix H H ℂ :=
  cfc (chordMask Δ) (chordSq U)

/-- **The far window.** -/
noncomputable def chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) : Matrix H H ℂ :=
  1 - chordNearProj U Δ

theorem isQProjector_chordNearProj (U : Matrix H H ℂ) (Δ : ℝ) :
    IsQProjector (chordNearProj U Δ) := by
  constructor
  · have h : IsSelfAdjoint (chordNearProj U Δ) := cfc_predicate _ _
    have h2 : star (chordNearProj U Δ) = chordNearProj U Δ := h
    rwa [Matrix.star_eq_conjTranspose] at h2
  · rw [chordNearProj, ← cfc_mul (chordMask Δ) (chordMask Δ) (chordSq U)
      (continuousOn_chordMask _ Δ) (continuousOn_chordMask _ Δ)]
    congr 1
    funext l
    exact chordMask_mul_self Δ l

theorem isQProjector_chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) :
    IsQProjector (chordFarProj U Δ) :=
  (isQProjector_chordNearProj U Δ).one_sub

/-- **`U` preserves the near window.** -/
theorem chordNearProj_commute {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (Δ : ℝ) :
    chordNearProj U Δ * U = U * chordNearProj U Δ := by
  have hc : Commute (chordSq U) U := chordSq_commute hU
  exact hc.cfc_real (chordMask Δ)

/-- **`U` preserves the far window.** -/
theorem chordFarProj_commute {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (Δ : ℝ) :
    chordFarProj U Δ * U = U * chordFarProj U Δ := by
  rw [chordFarProj, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    chordNearProj_commute hU]

/-! ## Quadratic forms

The bound below is an inequality between quadratic forms, so these are the
manipulations it needs.  Nothing here is specific to the chord form. -/

omit [DecidableEq H] in
lemma qInner_add_mulVec (M M' : Matrix H H ℂ) (x : H → ℂ) :
    qInner x ((M + M') *ᵥ x) = qInner x (M *ᵥ x) + qInner x (M' *ᵥ x) := by
  classical
  rw [Matrix.add_mulVec, qInner_add_right]

omit [DecidableEq H] in
lemma qInner_smul_mulVec (r : ℝ) (M : Matrix H H ℂ) (x : H → ℂ) :
    qInner x ((r • M) *ᵥ x) = (r : ℂ) * qInner x (M *ᵥ x) := by
  classical
  have hsm : (r • (M *ᵥ x) : H → ℂ) = ((r : ℂ)) • (M *ᵥ x) := by
    funext i
    simp [Complex.real_smul]
  rw [Matrix.smul_mulVec, hsm, qInner_smul_right]

omit [DecidableEq H] in
/-- On a projector the quadratic form is the squared norm of the image. -/
lemma qInner_proj_self {P : Matrix H H ℂ} (hP : IsQProjector P) (x : H → ℂ) :
    qInner x (P *ᵥ x) = (qNormSq (P *ᵥ x) : ℂ) := by
  classical
  have h2 : qInner (P *ᵥ x) (P *ᵥ x) = qInner x (Pᴴ *ᵥ (P *ᵥ x)) :=
    qInner_mulVec_left P x (P *ᵥ x)
  rw [hP.1, Matrix.mulVec_mulVec, hP.2] at h2
  rw [← h2, qInner_self]

omit [DecidableEq H] in
/-- For an operator commuting with a projector, the quadratic form restricts to
the projector's range. -/
lemma qInner_mul_proj {A P : Matrix H H ℂ} (hP : IsQProjector P)
    (hc : A * P = P * A) (x : H → ℂ) :
    qInner x ((A * P) *ᵥ x) = qInner (P *ᵥ x) (A *ᵥ (P *ᵥ x)) := by
  classical
  have h : qInner (P *ᵥ x) (A *ᵥ (P *ᵥ x)) = qInner x (Pᴴ *ᵥ (A *ᵥ (P *ᵥ x))) :=
    qInner_mulVec_left P x (A *ᵥ (P *ᵥ x))
  rw [hP.1] at h
  rw [h]
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hc, Matrix.mul_assoc, hP.2]

/-- **A `cfc` of a nonnegative function has nonnegative quadratic form.**  Proved
by writing `g = √g · √g`, so the matrix is `MᴴM`; no order theory is needed. -/
lemma qInner_cfc_nonneg (a : Matrix H H ℂ) (g : ℝ → ℝ) (hg : ∀ l, 0 ≤ g l)
    (x : H → ℂ) : 0 ≤ (qInner x (cfc g a *ᵥ x)).re := by
  set h : ℝ → ℝ := fun l => Real.sqrt (g l) with hhdef
  have hfun : (fun l => h l * h l) = g := funext fun l => Real.mul_self_sqrt (hg l)
  have hcfc : cfc g a = cfc h a * cfc h a := by
    rw [← hfun, cfc_mul h h a (Matrix.finite_real_spectrum.continuousOn _)
      (Matrix.finite_real_spectrum.continuousOn _)]
  have hsa : (cfc h a)ᴴ = cfc h a := by
    have hp : IsSelfAdjoint (cfc h a) := cfc_predicate h a
    have hst : star (cfc h a) = cfc h a := hp
    rwa [Matrix.star_eq_conjTranspose] at hst
  have hkey : qInner x (cfc g a *ᵥ x) = (qNormSq (cfc h a *ᵥ x) : ℂ) := by
    have e1 : qInner (cfc h a *ᵥ x) (cfc h a *ᵥ x)
        = qInner x (cfc h a *ᵥ (cfc h a *ᵥ x)) := by
      rw [qInner_mulVec_left, hsa]
    rw [hcfc, ← Matrix.mulVec_mulVec, ← e1, qInner_self]
  rw [hkey, Complex.ofReal_re]
  exact qNormSq_nonneg _

/-! ## The near-window bound -/

/-- The gap function `(Δ² - l)·mask l`, nonnegative everywhere. -/
noncomputable def chordGapFun (Δ : ℝ) : ℝ → ℝ :=
  fun l => (Δ ^ 2 - l) * chordMask Δ l

lemma chordGapFun_nonneg (Δ : ℝ) (l : ℝ) : 0 ≤ chordGapFun Δ l := by
  unfold chordGapFun chordMask
  by_cases h : l ≤ Δ ^ 2
  · rw [ite_eq_left h, mul_one]
    linarith
  · rw [ite_eq_right h, mul_zero]

lemma chordSq_mul_chordNearProj (U : Matrix H H ℂ) (Δ : ℝ) :
    chordSq U * chordNearProj U Δ + cfc (chordGapFun Δ) (chordSq U)
      = (Δ ^ 2 : ℝ) • chordNearProj U Δ := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (chordSq U)) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  have h1 : cfc (fun l : ℝ => id l * chordMask Δ l) (chordSq U)
      = chordSq U * chordNearProj U Δ := by
    rw [cfc_mul _ _ _ (hcont _) (hcont _), cfc_id ℝ (chordSq U) (isSelfAdjoint_chordSq U)]
    rfl
  have h2 : cfc (fun l : ℝ => Δ ^ 2 * chordMask Δ l) (chordSq U)
      = (Δ ^ 2 : ℝ) • chordNearProj U Δ := cfc_const_mul _ _ _ (hcont _)
  have h3 : chordGapFun Δ
      = fun l : ℝ => Δ ^ 2 * chordMask Δ l - id l * chordMask Δ l := by
    funext l
    unfold chordGapFun
    simp only [id]
    ring
  rw [h3, cfc_sub _ _ _ (hcont _) (hcont _), h1, h2]
  abel

/-- **The near-window bound**: on the near window the chord distance is at most
`|Δ|` (stated squared, so no absolute value appears). -/
theorem chordNear_bound_sq (U : Matrix H H ℂ) (Δ : ℝ) (x : H → ℂ) :
    qNormSq ((1 - U) *ᵥ (chordNearProj U Δ *ᵥ x))
      ≤ Δ ^ 2 * qNormSq (chordNearProj U Δ *ᵥ x) := by
  have hN := isQProjector_chordNearProj U Δ
  have hcomm : chordSq U * chordNearProj U Δ = chordNearProj U Δ * chordSq U := by
    have hc : Commute (chordSq U) (chordSq U) := Commute.refl _
    exact ((hc.cfc_real (chordMask Δ)) : Commute (chordNearProj U Δ) (chordSq U)).symm
  -- the left side, as a quadratic form at `x`
  have hL : qNormSq ((1 - U) *ᵥ (chordNearProj U Δ *ᵥ x))
      = (qInner x ((chordSq U * chordNearProj U Δ) *ᵥ x)).re := by
    rw [qNormSq_sub_mulVec, qInner_mul_proj hN hcomm x]
  -- the right side, likewise
  have hR : qNormSq (chordNearProj U Δ *ᵥ x)
      = (qInner x (chordNearProj U Δ *ᵥ x)).re := by
    rw [qInner_proj_self hN, Complex.ofReal_re]
  -- the gap term is nonnegative
  have hgap : 0 ≤ (qInner x (cfc (chordGapFun Δ) (chordSq U) *ᵥ x)).re :=
    qInner_cfc_nonneg _ _ (chordGapFun_nonneg Δ) x
  -- and the three add up
  have hsum := congrArg (fun M : Matrix H H ℂ => (qInner x (M *ᵥ x)).re)
    (chordSq_mul_chordNearProj U Δ)
  simp only [qInner_add_mulVec, qInner_smul_mulVec, Complex.add_re] at hsum
  rw [Complex.re_ofReal_mul] at hsum
  rw [hL, hR]
  linarith

/-! ## Decomposition, and the fixed space

The two windows are complementary orthogonal projectors, so every state splits
into a near part and a far part with no cross term.  And the **fixed space of
`U` sits entirely in the near window**, for every `Δ`: a vector with `U x = x`
has chord distance `0`, and `0 ≤ Δ²` always.  That is the statement a phase
detector needs in order to conclude that it never mistakes a fixed vector for a
rotating one. -/

@[simp] theorem chordNearProj_add_chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) :
    chordNearProj U Δ + chordFarProj U Δ = 1 := by
  rw [chordFarProj]
  abel

theorem chordNearProj_mul_chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) :
    chordNearProj U Δ * chordFarProj U Δ = 0 := by
  rw [chordFarProj, Matrix.mul_sub, Matrix.mul_one,
    (isQProjector_chordNearProj U Δ).2, sub_self]

theorem chordFarProj_mul_chordNearProj (U : Matrix H H ℂ) (Δ : ℝ) :
    chordFarProj U Δ * chordNearProj U Δ = 0 := by
  rw [chordFarProj, Matrix.sub_mul, Matrix.one_mul,
    (isQProjector_chordNearProj U Δ).2, sub_self]

/-- **The Pythagorean decomposition** across the two windows. -/
theorem qNormSq_chord_decomp (U : Matrix H H ℂ) (Δ : ℝ) (x : H → ℂ) :
    qNormSq x = qNormSq (chordNearProj U Δ *ᵥ x) + qNormSq (chordFarProj U Δ *ᵥ x) := by
  have hsplit : chordNearProj U Δ *ᵥ x + chordFarProj U Δ *ᵥ x = x := by
    rw [← Matrix.add_mulVec, chordNearProj_add_chordFarProj, Matrix.one_mulVec]
  have horth : (qInner (chordNearProj U Δ *ᵥ x) (chordFarProj U Δ *ᵥ x)).re = 0 := by
    rw [qInner_mulVec_left, (isQProjector_chordNearProj U Δ).1, Matrix.mulVec_mulVec,
      chordNearProj_mul_chordFarProj, Matrix.zero_mulVec, qInner_zero_right,
      Complex.zero_re]
  have hadd := qNormSq_add (chordNearProj U Δ *ᵥ x) (chordFarProj U Δ *ᵥ x)
  rw [hsplit, horth] at hadd
  linarith

/-- If `g` vanishes at `0` then `cfc g a` kills the kernel of `a`.  Proved by
factoring `g l = l · h l` — legitimate for *any* `g` here, since `h` need only
be continuous on a finite spectrum. -/
lemma cfc_mulVec_eq_zero_of_mulVec_eq_zero {a : Matrix H H ℂ} (ha : IsSelfAdjoint a)
    (g : ℝ → ℝ) (hg0 : g 0 = 0) {x : H → ℂ} (hx : a *ᵥ x = 0) : cfc g a *ᵥ x = 0 := by
  classical
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ a) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  set h : ℝ → ℝ := fun l => if l = 0 then 0 else g l / l with hhdef
  have hfun : (fun l : ℝ => id l * h l) = g := by
    funext l
    by_cases hl : l = 0
    · rw [hl]
      simp [hhdef, hg0]
    · simp only [hhdef, id, ite_eq_right hl]
      field_simp
  have hcomm : cfc h a * a = a * cfc h a := (Commute.refl a).cfc_real h
  have hsplit : cfc g a = cfc h a * a := by
    have h1 : cfc (fun l : ℝ => id l * h l) a = a * cfc h a := by
      rw [cfc_mul _ _ _ (hcont _) (hcont _), cfc_id ℝ a ha]
    rw [← hfun, h1, ← hcomm]
  rw [hsplit, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- **The fixed space of `U` lies in the near window**, for every `Δ`. -/
theorem chordNearProj_mulVec_of_fixed (U : Matrix H H ℂ) (Δ : ℝ) {x : H → ℂ}
    (hx : U *ᵥ x = x) : chordNearProj U Δ *ᵥ x = x := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (chordSq U)) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  have h0 : chordSq U *ᵥ x = 0 := by
    rw [chordSq_mulVec_eq_zero_iff, Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_self]
  have hg : cfc (fun l : ℝ => chordMask Δ l - 1) (chordSq U)
      = chordNearProj U Δ - 1 := by
    rw [show (fun l : ℝ => chordMask Δ l - 1)
        = (fun l : ℝ => chordMask Δ l - (1 : ℝ → ℝ) l) from rfl,
      cfc_sub _ _ _ (hcont _) (hcont _), cfc_one ℝ (chordSq U) (isSelfAdjoint_chordSq U)]
    rfl
  have hmask0 : chordMask Δ 0 - 1 = 0 := by
    unfold chordMask
    rw [ite_eq_left (sq_nonneg Δ), sub_self]
  have hz := cfc_mulVec_eq_zero_of_mulVec_eq_zero (isSelfAdjoint_chordSq U)
    (fun l => chordMask Δ l - 1) hmask0 h0
  rw [hg, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
  exact hz

/-- **The far window misses the fixed space.** -/
theorem chordFarProj_mulVec_of_fixed (U : Matrix H H ℂ) (Δ : ℝ) {x : H → ℂ}
    (hx : U *ᵥ x = x) : chordFarProj U Δ *ᵥ x = 0 := by
  rw [chordFarProj, Matrix.sub_mulVec, Matrix.one_mulVec,
    chordNearProj_mulVec_of_fixed U Δ hx, sub_self]

/-! ## The far-window bound

The companion to `chordNear_bound_sq`, and the coercivity estimate the
uniform-clock argument consumes: off the near window the chord distance is at
least `|Δ|`.  Same proof shape, with the gap function's sign reversed. -/

lemma chordFarProj_eq_cfc (U : Matrix H H ℂ) (Δ : ℝ) :
    chordFarProj U Δ = cfc (fun l : ℝ => 1 - chordMask Δ l) (chordSq U) := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (chordSq U)) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  rw [show (fun l : ℝ => 1 - chordMask Δ l)
      = (fun l : ℝ => (1 : ℝ → ℝ) l - chordMask Δ l) from rfl,
    cfc_sub _ _ _ (hcont _) (hcont _), cfc_one ℝ (chordSq U) (isSelfAdjoint_chordSq U)]
  rfl

/-- The far gap function `(l - Δ²)·(1 - mask l)`, nonnegative everywhere. -/
noncomputable def chordFarGapFun (Δ : ℝ) : ℝ → ℝ :=
  fun l => (l - Δ ^ 2) * (1 - chordMask Δ l)

lemma chordFarGapFun_nonneg (Δ : ℝ) (l : ℝ) : 0 ≤ chordFarGapFun Δ l := by
  unfold chordFarGapFun chordMask
  by_cases h : l ≤ Δ ^ 2
  · rw [ite_eq_left h]
    simp
  · rw [ite_eq_right h]
    have hlt : Δ ^ 2 < l := not_le.mp h
    have : (0 : ℝ) ≤ l - Δ ^ 2 := by linarith
    simpa using this

lemma chordSq_mul_chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) :
    (Δ ^ 2 : ℝ) • chordFarProj U Δ + cfc (chordFarGapFun Δ) (chordSq U)
      = chordSq U * chordFarProj U Δ := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (chordSq U)) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  have h1 : cfc (fun l : ℝ => id l * (1 - chordMask Δ l)) (chordSq U)
      = chordSq U * chordFarProj U Δ := by
    rw [cfc_mul _ _ _ (hcont _) (hcont _), cfc_id ℝ (chordSq U) (isSelfAdjoint_chordSq U),
      chordFarProj_eq_cfc]
  have h2 : cfc (fun l : ℝ => Δ ^ 2 * (1 - chordMask Δ l)) (chordSq U)
      = (Δ ^ 2 : ℝ) • chordFarProj U Δ := by
    rw [cfc_const_mul _ _ _ (hcont _), chordFarProj_eq_cfc]
  have h3 : chordFarGapFun Δ
      = fun l : ℝ => id l * (1 - chordMask Δ l) - Δ ^ 2 * (1 - chordMask Δ l) := by
    funext l
    unfold chordFarGapFun
    simp only [id]
    ring
  rw [h3, cfc_sub _ _ _ (hcont _) (hcont _), h1, h2]
  abel

/-- **The far-window bound (coercivity)**: off the near window the chord
distance is at least `|Δ|`. -/
theorem chordFar_bound_sq (U : Matrix H H ℂ) (Δ : ℝ) (x : H → ℂ) :
    Δ ^ 2 * qNormSq (chordFarProj U Δ *ᵥ x)
      ≤ qNormSq ((1 - U) *ᵥ (chordFarProj U Δ *ᵥ x)) := by
  have hF := isQProjector_chordFarProj U Δ
  have hNc : chordSq U * chordNearProj U Δ = chordNearProj U Δ * chordSq U := by
    have hc : Commute (chordSq U) (chordSq U) := Commute.refl _
    exact ((hc.cfc_real (chordMask Δ)) : Commute (chordNearProj U Δ) (chordSq U)).symm
  have hcomm : chordSq U * chordFarProj U Δ = chordFarProj U Δ * chordSq U := by
    rw [chordFarProj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hNc]
  have hR : qNormSq ((1 - U) *ᵥ (chordFarProj U Δ *ᵥ x))
      = (qInner x ((chordSq U * chordFarProj U Δ) *ᵥ x)).re := by
    rw [qNormSq_sub_mulVec, qInner_mul_proj hF hcomm x]
  have hL : qNormSq (chordFarProj U Δ *ᵥ x)
      = (qInner x (chordFarProj U Δ *ᵥ x)).re := by
    rw [qInner_proj_self hF, Complex.ofReal_re]
  have hgap : 0 ≤ (qInner x (cfc (chordFarGapFun Δ) (chordSq U) *ᵥ x)).re :=
    qInner_cfc_nonneg _ _ (chordFarGapFun_nonneg Δ) x
  have hsum := congrArg (fun M : Matrix H H ℂ => (qInner x (M *ᵥ x)).re)
    (chordSq_mul_chordFarProj U Δ)
  simp only [qInner_add_mulVec, qInner_smul_mulVec, Complex.add_re] at hsum
  rw [Complex.re_ofReal_mul] at hsum
  rw [hL, hR]
  linarith

/-! ## The effective spectral gap

The statement is naturally *squared*: everything in sight is a squared norm, and
squaring avoids square roots entirely.  The core is the elementary identity
`(1 - R_P R_L) w = 2 P w` of `SourceQuantumChordGap`; the spectral content is only that
the near window contracts `1 - U` by `Δ` and that a projector does not expand. -/

/-- **The effective spectral gap.**  If `L` annihilates `w`, then the part of
`P w` lying in the chord-distance window of threshold `Δ²` (radius `|Δ|`) of
`R_P R_L` has squared norm at most `(Δ²/4)‖w‖²`.

No sign hypothesis on `Δ` is needed: the squared formulation makes `0 ≤ Δ`
vacuous, since only `Δ²` ever appears. -/
theorem effective_chord_gap_sq {P L : Matrix H H ℂ} (hP : IsQProjector P)
    (hL : IsQProjector L) {w : H → ℂ} (hw : L *ᵥ w = 0) (Δ : ℝ) :
    qNormSq (chordNearProj (qRefl P * qRefl L) Δ *ᵥ (P *ᵥ w))
      ≤ (Δ ^ 2 / 4) * qNormSq w := by
  set U := qRefl P * qRefl L with hUdef
  have hUu : U ∈ Matrix.unitaryGroup H ℂ :=
    mul_mem (qRefl_mem_unitaryGroup hP) (qRefl_mem_unitaryGroup hL)
  set N := chordNearProj U Δ with hNdef
  have hNcomm : N * (1 - U) = (1 - U) * N := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      chordNearProj_commute hUu]
  have hcore : (1 - U) *ᵥ w = (2 : ℂ) • (P *ᵥ w) := one_sub_qRefl_mul_qRefl_mulVec hw
  have key : (2 : ℂ) • (N *ᵥ (P *ᵥ w)) = (1 - U) *ᵥ (N *ᵥ w) := by
    calc (2 : ℂ) • (N *ᵥ (P *ᵥ w))
        = N *ᵥ ((2 : ℂ) • (P *ᵥ w)) := by rw [Matrix.mulVec_smul]
      _ = N *ᵥ ((1 - U) *ᵥ w) := by rw [hcore]
      _ = (N * (1 - U)) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = ((1 - U) * N) *ᵥ w := by rw [hNcomm]
      _ = (1 - U) *ᵥ (N *ᵥ w) := by rw [Matrix.mulVec_mulVec]
  have h4 : (4 : ℝ) * qNormSq (N *ᵥ (P *ᵥ w)) = qNormSq ((1 - U) *ᵥ (N *ᵥ w)) := by
    rw [← key, qNormSq_smul]
    norm_num
  have hbound := chordNear_bound_sq U Δ w
  have hproj := (isQProjector_chordNearProj U Δ).qNormSq_mulVec_le w
  nlinarith [sq_nonneg Δ, qNormSq_nonneg (N *ᵥ (P *ᵥ w)), qNormSq_nonneg w]

end QuantumQueryComplexity

end SourceQuantumChordWindow

section SourceQuantumClockGap

/-!
# Uniform-clock suppression on the far window

The spectral half of the uniform-clock detector, and **nothing operational**:
this section knows about a unitary and its chord windows, not about clocks,
routines, or queries.

The statement is that on the far window — chord distance at least `|Δ|` — the
uniform average of the first `T` powers is small:

  `‖T⁻¹ ∑_{c<T} Uᶜ x‖² ≤ 4/(T²Δ²) · ‖x‖²`.

The proof is three lines of mathematics.  Telescoping gives
`(1 - U)·∑_{t<T} Uᵗ = 1 - Uᵀ`, so the average, hit with `1 - U`, becomes
`T⁻¹(1 - Uᵀ)x`, which has norm at most `2/T·‖x‖` because `Uᵀ` is unitary.  On the
far window `‖(1 - U)y‖ ≥ |Δ|·‖y‖` (`chordFar_bound_sq`), and dividing by `Δ`
gives the bound.  The far projector commutes with `U`, so it commutes with the
geometric sum and can be moved wherever it is needed.

The workhorse is stated **multiplied out**, `T²Δ²·‖avg‖² ≤ 4‖x‖²`, which holds
for every `Δ` and every `T` with no positivity hypothesis; the divided form
follows for `0 < Δ` and `0 < T`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- **A unitary moves a vector by at most twice its norm**: `‖(1 - Uᵀ)x‖ ≤ 2‖x‖`,
squared. -/
lemma qNormSq_one_sub_pow_mulVec_le {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (T : ℕ) (x : H → ℂ) :
    qNormSq ((1 - U ^ T) *ᵥ x) ≤ 4 * qNormSq x := by
  have hUT : U ^ T ∈ Matrix.unitaryGroup H ℂ := pow_mem hU T
  have hsplit : x + (-1 : ℂ) • (U ^ T *ᵥ x) = (1 - U ^ T) *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    module
  have hneg : qNormSq ((-1 : ℂ) • (U ^ T *ᵥ x)) = qNormSq x := by
    rw [qNormSq_smul, qNormSq_mulVec hUT]
    simp
  have htri := sqrt_qNormSq_add_le x ((-1 : ℂ) • (U ^ T *ᵥ x))
  rw [hsplit, hneg] at htri
  have h0 : (0 : ℝ) ≤ qNormSq x := qNormSq_nonneg x
  have hsq := Real.sq_sqrt (qNormSq_nonneg ((1 - U ^ T) *ᵥ x))
  have hxsq := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (qNormSq ((1 - U ^ T) *ᵥ x)), Real.sqrt_nonneg (qNormSq x)]

/-- The far projector commutes with the geometric sum, since it commutes with
`U`. -/
lemma chordFarProj_commute_geom {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (Δ : ℝ) (T : ℕ) :
    Commute (chordFarProj U Δ) (∑ t ∈ Finset.range T, U ^ t) :=
  Commute.sum_right _ _ _ fun t _ =>
    (show Commute (chordFarProj U Δ) U from chordFarProj_commute hU Δ).pow_right t

/-- **Uniform-clock suppression**, multiplied out.  Holds for every `Δ` and every
`T`, with **no positivity hypothesis**: it is vacuous at `Δ = 0` or `T = 0`,
which is exactly why the divided form below is the one that asks for both to be
positive. -/
theorem qNormSq_avg_pow_chordFar {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (Δ : ℝ) (T : ℕ) (x : H → ℂ) :
    (T : ℝ) ^ 2 * Δ ^ 2
        * qNormSq ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ (chordFarProj U Δ *ᵥ x))
      ≤ 4 * qNormSq x := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · -- an empty clock: the left side carries the factor `T² = 0`
    subst hT
    have hq := qNormSq_nonneg x
    have h0 : ((0 : ℕ) : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, zero_mul, zero_mul]
    linarith
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hFU : Commute (chordFarProj U Δ) U := chordFarProj_commute hU Δ
  have hFG := chordFarProj_commute_geom hU Δ T
  -- the sum over `Fin T` is the geometric sum, with the projector moved across
  have hFGx : (∑ t ∈ Finset.range T, U ^ t) *ᵥ (chordFarProj U Δ *ᵥ x)
      = chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hFG.eq]
  have hrewrite : ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ (chordFarProj U Δ *ᵥ x))
      = (T : ℂ)⁻¹ • (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x)) := by
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun t => (U ^ t) *ᵥ (chordFarProj U Δ *ᵥ x)) T,
      ← Matrix.sum_mulVec, hFGx]
  -- `(1 - U)` also commutes with the projector, and telescopes against the sum
  have hF1U : (1 - U) * chordFarProj U Δ = chordFarProj U Δ * (1 - U) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hFU.eq]
  have hcomm2 : (1 - U) *ᵥ (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x))
      = chordFarProj U Δ *ᵥ ((1 - U ^ T) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hF1U, Matrix.mul_assoc, one_sub_mul_geom_sum]
  -- coercivity on the far window, then the projector shrinks, then `‖1 - Uᵀ‖ ≤ 2`
  have key : Δ ^ 2 * qNormSq (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x))
      ≤ 4 * qNormSq x := by
    have h1 := chordFar_bound_sq U Δ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x)
    rw [hcomm2] at h1
    have h2 : qNormSq (chordFarProj U Δ *ᵥ ((1 - U ^ T) *ᵥ x))
        ≤ qNormSq ((1 - U ^ T) *ᵥ x) :=
      (isQProjector_chordFarProj U Δ).qNormSq_mulVec_le _
    have h3 := qNormSq_one_sub_pow_mulVec_le hU T x
    linarith
  have hnormsq : Complex.normSq ((T : ℂ)⁻¹) = ((T : ℝ) * (T : ℝ))⁻¹ := by
    rw [Complex.normSq_inv, ← Complex.ofReal_natCast, Complex.normSq_ofReal]
  rw [hrewrite, qNormSq_smul, hnormsq]
  calc (T : ℝ) ^ 2 * Δ ^ 2
        * (((T : ℝ) * (T : ℝ))⁻¹
          * qNormSq (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x)))
      = Δ ^ 2 * qNormSq (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x)) := by
        field_simp
    _ ≤ 4 * qNormSq x := key

/-- **Uniform-clock suppression**, in the form the detector uses:
`‖T⁻¹ ∑_{c<T} Uᶜ x‖² ≤ 4/(T²Δ²)·‖x‖²` on the far window. -/
theorem qNormSq_avg_pow_chordFar_div {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {Δ : ℝ} (hΔ : 0 < Δ) {T : ℕ} (hT : 0 < T)
    (x : H → ℂ) :
    qNormSq ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ (chordFarProj U Δ *ᵥ x))
      ≤ 4 / ((T : ℝ) ^ 2 * Δ ^ 2) * qNormSq x := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hpos : (0 : ℝ) < (T : ℝ) ^ 2 * Δ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm]
  exact qNormSq_avg_pow_chordFar hU Δ T x

end QuantumQueryComplexity

end SourceQuantumClockGap

section SourceQuantumReflection

/-!
# The input-dependent reflection, in exactly two queries

The reflection the upper bound needs is about
the orthogonal complement of a span of input-dependent vectors; it is built as

  `O_a · (fixed reflection) · O_a`,

one query on each side of a fixed unitary, and **that is exactly two queries** —
`QRoutine.conjFixed` costs `2 · R.len`, and inversion is free because the
transposition oracle is self-adjoint.

**The sign is part of the statement.**  `spanRefl v` fixes the span, but the
construction reflects about the *complement*, and
`subRefl (rawSpan v)ᗮ = -spanRefl v`.  Dropping that minus would shift every
eigenphase by `π`, which controlled phase detection would then read off wrongly.
`inputRefl_run` therefore carries the negation explicitly.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **The input-dependent reflection**: reflect about the orthogonal complement
of a span, conjugated by one query on each side. -/
noncomputable def inputRefl (v : ι' → (QBasis ι σ W → ℂ)) : QRoutine ι σ W :=
  QRoutine.query.conjFixed (subRefl (rawSpan v)ᗮ) (subRefl_mem_unitaryGroup _)

/-- **Exactly two queries.** -/
@[simp] theorem inputRefl_len (v : ι' → (QBasis ι σ W → ℂ)) :
    (inputRefl v).len = 2 := by
  rw [inputRefl, QRoutine.conjFixed_len, QRoutine.query_len]

/-- **The operator it implements**, with the complement's sign explicit. -/
theorem inputRefl_run (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    (inputRefl v).run a = oracleMat a * (-spanRefl v * oracleMat a) := by
  rw [inputRefl, QRoutine.conjFixed_run, QRoutine.query_run,
    QRoutine.oracleMat_conjTranspose, spanRefl_orthogonal]

/-- The same, before the sign is resolved: it is the conjugate of the
complement reflection. -/
theorem inputRefl_run' (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    (inputRefl v).run a = oracleMat a * (subRefl (rawSpan v)ᗮ * oracleMat a) := by
  rw [inputRefl, QRoutine.conjFixed_run, QRoutine.query_run,
    QRoutine.oracleMat_conjTranspose]

/-! ## The bridge to the mathematical layer

The effective-gap theorem is cleanest stated for an arbitrary projector.  This
is the projector the operational two-query reflection actually reflects about,
so the final algorithm can instantiate the abstract theorem with it. -/

/-- **The input-dependent projector**: the fixed complement projector,
conjugated by one query on each side. -/
noncomputable def inputProj (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  oracleMat a * subProj (rawSpan v)ᗮ * oracleMat a

theorem isQProjector_inputProj (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    IsQProjector (inputProj v a) := by
  have h := (isQProjector_subProj (rawSpan v)ᗮ).conj (oracleMat_mem_unitaryGroup a)
  rwa [QRoutine.oracleMat_conjTranspose] at h

/-- **The operational reflection is the reflection about that projector.** -/
theorem inputRefl_run_eq_qRefl (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    (inputRefl v).run a = qRefl (inputProj v a) := by
  rw [inputRefl_run', qRefl, inputProj, subRefl, qRefl, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, oracleMat_mul_self]
  simp only [Matrix.mul_assoc]

/-! ## The composition-order trap

`QRoutine.comp` composes in **execution** order, while the matrix product
composes in the opposite one: `comp_run : (R.comp S).run a = S.run a * R.run a`.
So the operator `R_P · R_L` — the one the effective-gap theorem takes — is
implemented by running `L` **first**, i.e. by `RL.comp RP`.  Getting this
backwards would silently build `R_L · R_P`, whose spectrum is the same but whose
eigenvectors are not, so it is pinned here as a theorem rather than a comment. -/

/-- **The reflection product, in execution order.** -/
theorem comp_run_eq_qRefl_mul {RP RL : QRoutine ι σ W}
    {P L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ} (a : ι → σ)
    (hP : RP.run a = qRefl P) (hL : RL.run a = qRefl L) :
    (RL.comp RP).run a = qRefl P * qRefl L := by
  rw [QRoutine.comp_run, hP, hL]

@[simp] lemma comp_len_reflProd (RP RL : QRoutine ι σ W) :
    (RL.comp RP).len = RL.len + RP.len := rfl

/-! ## The reflection product

`effective_chord_gap_sq` consumes `qRefl P * qRefl L`.  This definition builds
exactly that operator as a routine, and in doing so **pins the two facts a query
count depends on**:

* the **order** — `L` is run first, so the operator is `R_P · R_L` and not its
  reverse (see the trap above);
* the **cost** — the `L`-side reflection is a *fixed*, input-independent unitary,
  supplied as a zero-query `ofUnitary`.  So the product costs exactly the two
  queries of the input-dependent side.  `inputRefl_len = 2` on its own says
  nothing about this: if both sides were input-dependent the product would cost
  four, and every downstream clock estimate would double.

`inputReflProduct_len` is therefore the theorem that licenses the `2` in the
detector's query accounting.  The specialization of the effective-gap theorem to
this routine is proved in `SourceQuantumOperationalGap`. -/

/-- **The reflection product** `R_P · R_L`, with `R_L` a fixed zero-query
reflection and `R_P` the input-dependent two-query reflection. -/
noncomputable def inputReflProduct (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) :
    QRoutine ι σ W :=
  (QRoutine.ofUnitary (qRefl L) (qRefl_mem_unitaryGroup hL)).comp (inputRefl v)

/-- **Exactly two queries** — because the `L`-side is fixed. -/
@[simp] theorem inputReflProduct_len (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) :
    (inputReflProduct v L hL).len = 2 := by
  rw [inputReflProduct, QRoutine.comp_len, QRoutine.ofUnitary_len, inputRefl_len]

/-- **The operator it implements**, in the order `effective_chord_gap_sq`
expects. -/
theorem inputReflProduct_run (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (a : ι → σ) :
    (inputReflProduct v L hL).run a = qRefl (inputProj v a) * qRefl L := by
  rw [inputReflProduct, QRoutine.comp_run, QRoutine.ofUnitary_run,
    inputRefl_run_eq_qRefl]

theorem inputRefl_run_mem_unitaryGroup (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    (inputRefl v).run a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
  QRoutine.run_mem_unitaryGroup _ a

end QuantumQueryComplexity

end SourceQuantumReflection

section SourceQuantumRoutineLift

/-!
# Lifting a routine along a workspace extension

A routine built on workspace `W` runs unchanged on `V × W`: lift every fixed
step with `liftReg`, and the queries pass through because the oracle ignores the
workspace (`blockFam_oracle`).  The query count is unchanged, and on the encoded
subspace the lifted routine does exactly what the original does.

This is what lets a subroutine written for a small workspace be used inside a
circuit that carries extra registers — a phase register, say.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ V W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

namespace QRoutine

/-- **Lift a routine along a workspace extension.** -/
@[expose]
def liftReg (V : Type) [Fintype V] [DecidableEq V] (R : QRoutine ι σ W) :
    QRoutine ι σ (V × W) where
  len := R.len
  step := fun t => QuantumQueryComplexity.liftReg V (R.step t)
  step_unitary := fun t => liftReg_mem_unitaryGroup (R.step_unitary t)

@[simp] lemma liftReg_len (R : QRoutine ι σ W) : (R.liftReg V).len = R.len := rfl

@[simp] lemma liftReg_step (R : QRoutine ι σ W) (t : ℕ) :
    (R.liftReg V).step t = QuantumQueryComplexity.liftReg V (R.step t) := rfl

theorem liftReg_runUpto (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    (R.liftReg V).runUpto a t = QuantumQueryComplexity.liftReg V (R.runUpto a t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runUpto_succ, runUpto_succ, liftReg_step, ih, blockFam_oracle (V := V),
        liftReg_mul, liftReg_mul]

theorem liftReg_run (R : QRoutine ι σ W) (a : ι → σ) :
    (R.liftReg V).run a = QuantumQueryComplexity.liftReg V (R.run a) :=
  liftReg_runUpto R a R.len

/-- **The lifted routine acts as the original on the encoded subspace.** -/
theorem liftReg_run_embed (R : QRoutine ι σ W) (a : ι → σ) (v : V)
    (ψ : QBasis ι σ W → ℂ) :
    (R.liftReg V).run a *ᵥ embedReg v ψ = embedReg v (R.run a *ᵥ ψ) := by
  rw [liftReg_run, liftReg_mulVec_embed]

end QRoutine

end QuantumQueryComplexity

end SourceQuantumRoutineLift

section SourceQuantumClock

/-!
# The clock compiler: coherent powers of a routine

A uniform clock needs `selectPowers`, the **coherent** map

  `|c⟩|ψ⟩ ↦ |c⟩ Uᶜ|ψ⟩`,

which is *not* `QRoutine.iterate` — that applies a global `Uⁿ` to every branch.
The compilation is the standard one: `T-1` rounds, the `j`-th applying `U`
exactly on the branches whose clock has reached `j`.  Each round is

  XOR the predicate `j ≤ c` into the control bit  (a basis permutation, free)
  → `QRoutine.control` of the lifted routine        (`R.len` queries)
  → XOR it back                                     (free),

so a round costs exactly `R.len` and `selectPowers R T` costs `(T-1)·R.len`.

On top of `SELECT` this section builds the rest of the **operational** side of a
uniform-clock detector:

* `clockPack` — a *packed history*, one workspace vector per clock branch.  The
  branches are orthogonal, so Pythagoras holds and `SELECT` acts entrywise.
* `uniformClock` — the constant packed history, normalized.
* `clockAvgProj` — projection of the clock register onto its uniform
  superposition.  On a packed history it returns the **exact vector average**
  `T⁻¹ ∑_{c<T} f c`; on `SELECT` applied to a uniform clock, `T⁻¹ ∑_{c<T} Uᶜψ`.
* `clockPhaseRefl` — the conjugation `SELECTᴴ · clockRefl · SELECT`, of exact
  length `2(T-1)·R.len`: the reflection is a fixed unitary, so conjugation is
  the only cost.

The workspace is `CtrlWork ι (Fin T × W)`: the control bit and parking slot of
`SourceQuantumControl`, then the clock register, then the routine's own workspace.  This
file depends only on `Control` and `RoutineLift`; **whether that average is
small — the spectral half of the detector — is proved elsewhere**, and the
connection to spectral suppression belongs in a later file, not here.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- The workspace of a clocked routine. -/
abbrev ClockWork (ι : Type) (T : ℕ) (W : Type) : Type := CtrlWork ι (Fin T × W)

/-- The state with clock `c`, control bit `b`, blank parking slot, and `ψ`
elsewhere. -/
noncomputable def embedClock (c : Fin T) (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    QBasis ι σ (ClockWork ι T W) → ℂ :=
  embedCtrl b (embedReg c ψ)

/-! ## Flipping the control bit on the clock -/

/-- Flip the control bit exactly on the branches whose clock has reached `j`. -/
def clockXorMap (j : ℕ) :
    QBasis ι σ (ClockWork ι T W) → QBasis ι σ (ClockWork ι T W)
  | (k, t, (b, s, (c, w))) => (k, t, (xor b (decide (j ≤ (c : ℕ))), s, (c, w)))

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma clockXorMap_involutive (j : ℕ) :
    Function.Involutive (clockXorMap (ι := ι) (σ := σ) (W := W) (T := T) j) := by
  rintro ⟨k, t, b, s, c, w⟩
  change ((k, t, (xor (xor b (decide (j ≤ (c : ℕ)))) (decide (j ≤ (c : ℕ))), s, (c, w))) :
      QBasis ι σ (ClockWork ι T W)) = (k, t, (b, s, (c, w)))
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The bit flip, as a permutation of the basis. -/
def clockXorPerm (j : ℕ) : Equiv.Perm (QBasis ι σ (ClockWork ι T W)) :=
  Function.Involutive.toPerm _ (clockXorMap_involutive j)

/-- The bit flip, as a zero-query unitary. -/
def clockXorMat (j : ℕ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qPerm (clockXorPerm j)

lemma clockXorMat_mem_unitaryGroup (j : ℕ) :
    clockXorMat (ι := ι) (σ := σ) (W := W) (T := T) j
      ∈ Matrix.unitaryGroup (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma clockXorMat_mulVec_apply (j : ℕ) (Φ : QBasis ι σ (ClockWork ι T W) → ℂ)
    (p : QBasis ι σ (ClockWork ι T W)) :
    (clockXorMat j *ᵥ Φ) p = Φ (clockXorMap j p) := by
  rw [clockXorMat, qPerm_mulVec_apply]
  rfl

/-- **The bit flip reads the clock and touches nothing else.** -/
theorem clockXorMat_mulVec_embedClock (j : ℕ) (c : Fin T) (b : Bool)
    (ψ : QBasis ι σ W → ℂ) :
    clockXorMat j *ᵥ embedClock c b ψ
      = embedClock c (xor b (decide (j ≤ (c : ℕ)))) ψ := by
  funext p
  rw [clockXorMat_mulVec_apply]
  obtain ⟨k, t, b', s, c', w⟩ := p
  rw [embedClock, embedClock, embedCtrl_apply, embedCtrl_apply]
  change (if xor b' (decide (j ≤ (c' : ℕ))) = b ∧ s = none then
      embedReg c ψ (k, t, (c', w)) else 0)
    = if b' = xor b (decide (j ≤ (c : ℕ))) ∧ s = none then
      embedReg c ψ (k, t, (c', w)) else 0
  by_cases hc : c' = c
  · subst hc
    by_cases hs : s = none
    · simp only [hs, and_true]
      by_cases hb : b' = xor b (decide (j ≤ (c' : ℕ)))
      · rw [ite_eq_left, ite_eq_left hb]
        rw [hb]
        cases b <;> cases (decide (j ≤ (c' : ℕ))) <;> rfl
      · rw [ite_eq_right, ite_eq_right hb]
        intro hcon
        exact hb (by rw [← hcon]; cases b' <;> cases (decide (j ≤ (c' : ℕ))) <;> rfl)
    · simp [hs]
  · have h0 : embedReg c ψ ((k, t, (c', w)) : QBasis ι σ (Fin T × W)) = 0 := by
      rw [embedReg_apply, ite_eq_right hc]
    simp [h0]

/-! ## One round -/

/-- One clocked round: apply `R` exactly on the branches whose clock has reached
`j`.  The two bit flips are free, so this costs exactly `R.len` queries. -/
noncomputable def clockRound (R : QRoutine ι σ W) (T : ℕ) (j : ℕ) :
    QRoutine ι σ (ClockWork ι T W) :=
  ((QRoutine.ofUnitary (clockXorMat j) (clockXorMat_mem_unitaryGroup j)).comp
      ((R.liftReg (Fin T)).control)).comp
    (QRoutine.ofUnitary (clockXorMat j) (clockXorMat_mem_unitaryGroup j))

@[simp] lemma clockRound_len (R : QRoutine ι σ W) (T : ℕ) (j : ℕ) :
    (clockRound R T j).len = R.len := by
  change 0 + ((R.liftReg (Fin T)).control).len + 0 = R.len
  rw [control_len, QRoutine.liftReg_len]
  omega

lemma clockRound_run_matrix (R : QRoutine ι σ W) (T : ℕ) (j : ℕ) (a : ι → σ) :
    (clockRound R T j).run a
      = clockXorMat j * (((R.liftReg (Fin T)).control).run a * clockXorMat j) := by
  rw [clockRound, QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run]

/-- **One round applies `R` exactly on the branches that have reached `j`.** -/
theorem clockRound_run (R : QRoutine ι σ W) (T : ℕ) (j : ℕ) (a : ι → σ)
    (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    (clockRound R T j).run a *ᵥ embedClock c false ψ
      = embedClock c false (if j ≤ (c : ℕ) then R.run a *ᵥ ψ else ψ) := by
  rw [clockRound_run_matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    clockXorMat_mulVec_embedClock, Bool.false_xor]
  by_cases hj : j ≤ (c : ℕ)
  · have hd : decide (j ≤ (c : ℕ)) = true := decide_eq_true hj
    rw [hd, ite_eq_left hj, embedClock, control_run_true, QRoutine.liftReg_run_embed,
      show embedCtrl true (embedReg c (R.run a *ᵥ ψ))
        = embedClock c true (R.run a *ᵥ ψ) from rfl,
      clockXorMat_mulVec_embedClock, hd, Bool.xor_self]
  · have hd : decide (j ≤ (c : ℕ)) = false := decide_eq_false hj
    rw [hd, ite_eq_right hj, embedClock, control_run_false,
      show embedCtrl false (embedReg c ψ) = embedClock c false ψ from rfl,
      clockXorMat_mulVec_embedClock, hd, Bool.xor_self]

/-! ## Coherent powers -/

/-- The first `n` clocked rounds. -/
noncomputable def selectUpto (R : QRoutine ι σ W) (T : ℕ) :
    ℕ → QRoutine ι σ (ClockWork ι T W)
  | 0 => QRoutine.identity
  | n + 1 => (selectUpto R T n).comp (clockRound R T (n + 1))

/-- **Coherent powers**: `|c⟩|ψ⟩ ↦ |c⟩ Uᶜ|ψ⟩`, compiled as `T-1` rounds. -/
noncomputable def selectPowers (R : QRoutine ι σ W) (T : ℕ) :
    QRoutine ι σ (ClockWork ι T W) :=
  selectUpto R T (T - 1)

@[simp] lemma selectUpto_len (R : QRoutine ι σ W) (T : ℕ) (n : ℕ) :
    (selectUpto R T n).len = n * R.len := by
  induction n with
  | zero =>
      change (0 : ℕ) = 0 * R.len
      omega
  | succ n ih =>
      change (selectUpto R T n).len + (clockRound R T (n + 1)).len = (n + 1) * R.len
      rw [ih, clockRound_len]
      ring

/-- **The exact query count**: `(T-1) · R.len`. -/
@[simp] theorem selectPowers_len (R : QRoutine ι σ W) (T : ℕ) :
    (selectPowers R T).len = (T - 1) * R.len :=
  selectUpto_len R T (T - 1)

theorem selectUpto_run (R : QRoutine ι σ W) (T : ℕ) (n : ℕ) (a : ι → σ)
    (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    (selectUpto R T n).run a *ᵥ embedClock c false ψ
      = embedClock c false ((R.run a) ^ (min n (c : ℕ)) *ᵥ ψ) := by
  induction n with
  | zero =>
      change (1 : Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ)
        *ᵥ embedClock c false ψ = _
      rw [Matrix.one_mulVec, Nat.zero_min, pow_zero, Matrix.one_mulVec]
  | succ n ih =>
      change ((selectUpto R T n).comp (clockRound R T (n + 1))).run a *ᵥ _ = _
      rw [QRoutine.comp_run, ← Matrix.mulVec_mulVec, ih, clockRound_run]
      congr 1
      by_cases hj : n + 1 ≤ (c : ℕ)
      · rw [ite_eq_left hj,
          show min (n + 1) (c : ℕ) = min n (c : ℕ) + 1 from by omega,
          pow_succ', Matrix.mulVec_mulVec]
      · rw [ite_eq_right hj, show min (n + 1) (c : ℕ) = min n (c : ℕ) from by omega]

/-- **Coherent powers, verified**: on a branch with clock `c` the routine has
been applied exactly `c` times. -/
theorem selectPowers_run (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ) (c : Fin T)
    (ψ : QBasis ι σ W → ℂ) :
    (selectPowers R T).run a *ᵥ embedClock c false ψ
      = embedClock c false ((R.run a) ^ (c : ℕ) *ᵥ ψ) := by
  rw [selectPowers, selectUpto_run]
  have hc : (c : ℕ) < T := c.isLt
  rw [show min (T - 1) (c : ℕ) = (c : ℕ) from by omega]

/-! ## Packed histories

A **packed history** places a clock-indexed family in the clock branches, all
with a blank control bit.  It is the shape every statement about the clock takes:
`selectPowers` acts on one entrywise, the branches are mutually orthogonal, and
the uniform clock is the constant packed history, normalized. -/

/-- The packed history: `f c` in the branch whose clock reads `c`. -/
noncomputable def clockPack (f : Fin T → (QBasis ι σ W → ℂ)) :
    QBasis ι σ (ClockWork ι T W) → ℂ :=
  ∑ c : Fin T, embedClock c false (f c)

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma embedClock_smul (c : Fin T) (b : Bool) (a : ℂ) (ψ : QBasis ι σ W → ℂ) :
    embedClock c b (a • ψ) = a • embedClock c b ψ := by
  classical
  simp only [embedClock, embedCtrl]
  rw [embedReg_smul, embedReg_smul, embedReg_smul]

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma embedClock_sum {α : Type*} (c : Fin T) (b : Bool) (s : Finset α)
    (f : α → (QBasis ι σ W → ℂ)) :
    embedClock c b (∑ i ∈ s, f i) = ∑ i ∈ s, embedClock c b (f i) := by
  classical
  simp only [embedClock, embedCtrl]
  rw [embedReg_sum, embedReg_sum, embedReg_sum]

/-- **`SELECT` acts on a packed history entrywise**: branch `c` gets `Uᶜ`. -/
theorem selectPowers_run_clockPack (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ)
    (f : Fin T → (QBasis ι σ W → ℂ)) :
    (selectPowers R T).run a *ᵥ clockPack f
      = clockPack (fun c => (R.run a) ^ (c : ℕ) *ᵥ f c) := by
  rw [clockPack, Matrix.mulVec_sum, clockPack]
  exact Finset.sum_congr rfl fun c _ => selectPowers_run R T a c (f c)

omit [DecidableEq W] [DecidableEq σ] in
/-- **Distinct clock branches are orthogonal**, and a branch is an isometry. -/
theorem qInner_embedClock (c c' : Fin T) (b b' : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (embedClock c b ψ) (embedClock c' b' φ)
      = if c = c' ∧ b = b' then qInner ψ φ else 0 := by
  classical
  simp only [embedClock, embedCtrl, qInner_embedReg]
  by_cases hb : b = b' <;> by_cases hc : c = c' <;> simp [hb, hc]

omit [DecidableEq W] [DecidableEq σ] in
/-- **Pythagoras for a packed history.** -/
theorem qNormSq_clockPack (f : Fin T → (QBasis ι σ W → ℂ)) :
    qNormSq (clockPack f) = ∑ c : Fin T, qNormSq (f c) := by
  classical
  have h : ((qNormSq (clockPack f) : ℝ) : ℂ)
      = ∑ c : Fin T, ((qNormSq (f c) : ℝ) : ℂ) := by
    rw [← qInner_self, clockPack, qInner_sum_left]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [qInner_sum_right, Finset.sum_eq_single c]
    · rw [qInner_embedClock, ite_eq_left ⟨rfl, rfl⟩, qInner_self]
    · intro c' _ hc'
      rw [qInner_embedClock, ite_eq_right fun hcon => hc' hcon.1.symm]
    · simp
  exact_mod_cast h

/-! ## The uniform clock -/

/-- The uniform clock: `ψ` in every branch, normalized. -/
noncomputable def uniformClock (T : ℕ) (ψ : QBasis ι σ W → ℂ) :
    QBasis ι σ (ClockWork ι T W) → ℂ :=
  ((Real.sqrt T : ℝ) : ℂ)⁻¹ • clockPack (fun _ : Fin T => ψ)

omit [DecidableEq W] [DecidableEq σ] in
/-- **The uniform clock is normalized** (for `0 < T`). -/
theorem qNormSq_uniformClock (hT : 0 < T) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (uniformClock T ψ) = qNormSq ψ := by
  classical
  have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have h1 : Complex.normSq (((Real.sqrt T : ℝ) : ℂ)⁻¹) = ((T : ℝ))⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg T)]
  rw [uniformClock, qNormSq_smul, h1, qNormSq_clockPack, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
/-- **The clock spread preserves basis support**: where the underlying
vector vanishes at the stripped coordinate, the clocked vector vanishes at
the full one.  This is what lets a readout of the underlying workspace act
through the clock. -/
lemma uniformClock_apply_eq_zero (T : ℕ) (ψ : QBasis ι σ W → ℂ)
    {b : QBasis ι σ (ClockWork ι T W)}
    (h : ψ (b.1, b.2.1, b.2.2.2.2.2) = 0) :
    uniformClock T ψ b = 0 := by
  obtain ⟨k, t, bb, s, c', w⟩ := b
  have h' : ψ (k, t, w) = 0 := h
  have hz : ∀ c : Fin T,
      embedClock c false ψ ((k, t, (bb, s, (c', w)))
        : QBasis ι σ (ClockWork ι T W)) = 0 := by
    intro c
    simp [embedClock, embedCtrl, embedReg_apply, h']
  rw [uniformClock, Pi.smul_apply, clockPack, Finset.sum_apply,
    Finset.sum_eq_zero fun c _ => hz c, smul_zero]

/-- **`SELECT` on the uniform clock** builds the history `Uᶜψ`. -/
theorem selectPowers_run_uniformClock (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ)
    (ψ : QBasis ι σ W → ℂ) :
    (selectPowers R T).run a *ᵥ uniformClock T ψ
      = ((Real.sqrt T : ℝ) : ℂ)⁻¹ • clockPack (fun c => (R.run a) ^ (c : ℕ) *ᵥ ψ) := by
  rw [uniformClock, Matrix.mulVec_smul, selectPowers_run_clockPack]

/-! ## The averaging projector

Projecting the clock register back onto the uniform superposition is what turns a
packed history into the **vector average** `T⁻¹ ∑_{c<T} Uᶜψ`.  That average is
the whole point of a uniform clock: it is `1` on a fixed vector and small on a
vector whose chord distance is large, which is the suppression the detector
needs. -/

/-- The uniform-average matrix on the clock register. -/
noncomputable def avgMat (T : ℕ) : Matrix (Fin T) (Fin T) ℂ :=
  Matrix.of fun _ _ => (T : ℂ)⁻¹

theorem isQProjector_avgMat (T : ℕ) : IsQProjector (avgMat T) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    exact ⟨by ext i j; exact i.elim0, by ext i j; exact i.elim0⟩
  have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  constructor
  · ext i j
    rw [Matrix.conjTranspose_apply]
    change star ((T : ℂ)⁻¹) = (T : ℂ)⁻¹
    rw [star_inv₀, star_natCast]
  · ext i j
    rw [Matrix.mul_apply]
    change (∑ _k : Fin T, (T : ℂ)⁻¹ * (T : ℂ)⁻¹) = (T : ℂ)⁻¹
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- **The averaging projector on the clock register.** -/
noncomputable def clockAvgProj (T : ℕ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  liftReg Bool (liftReg (Option ι) (regOp (avgMat T)))

theorem isQProjector_clockAvgProj (T : ℕ) :
    IsQProjector (clockAvgProj (ι := ι) (σ := σ) (W := W) T) :=
  isQProjector_liftReg (isQProjector_liftReg (isQProjector_regOp (isQProjector_avgMat T)))

theorem clockAvgProj_mulVec_embedClock (T : ℕ) (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    clockAvgProj T *ᵥ embedClock c false ψ
      = ∑ c' : Fin T, (T : ℂ)⁻¹ • embedClock c' false ψ := by
  rw [clockAvgProj, embedClock, embedCtrl, liftReg_mulVec_embed, liftReg_mulVec_embed,
    regOp_mulVec_embedReg, embedReg_sum, embedReg_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [embedReg_smul, embedReg_smul]
  rfl

/-- **The averaging projector produces the exact vector average.**  On the packed
history `f` it returns the constant history `T⁻¹ ∑_{c<T} f c` — in particular, on
`SELECT` applied to a uniform clock, `T⁻¹ ∑_{c<T} Uᶜψ`. -/
theorem clockAvgProj_mulVec_clockPack (T : ℕ) (f : Fin T → (QBasis ι σ W → ℂ)) :
    clockAvgProj T *ᵥ clockPack f
      = clockPack (fun _ => (T : ℂ)⁻¹ • ∑ c : Fin T, f c) := by
  rw [clockPack, Matrix.mulVec_sum,
    Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) =>
      clockAvgProj_mulVec_embedClock T c (f c),
    Finset.sum_comm, clockPack]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [embedClock_smul, embedClock_sum, Finset.smul_sum]

/-! ## The phase reflection

`clockRefl` reflects about the uniform-clock subspace; it is a fixed unitary,
touching no oracle.  Conjugating it by `SELECT` is the phase reflection of a
uniform-clock detector, and the conjugation is where the query count doubles —
and only doubles. -/

/-- The reflection about the uniform-clock subspace. -/
noncomputable def clockRefl (T : ℕ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qRefl (clockAvgProj T)

theorem clockRefl_mem_unitaryGroup (T : ℕ) :
    clockRefl (ι := ι) (σ := σ) (W := W) T
      ∈ Matrix.unitaryGroup (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qRefl_mem_unitaryGroup (isQProjector_clockAvgProj T)

/-- **`SELECTᴴ` undoes the powers branchwise.** -/
theorem selectPowers_conjTranspose_mulVec_embedClock (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    ((selectPowers R T).run a)ᴴ *ᵥ embedClock c false ψ
      = embedClock c false (((R.run a) ^ (c : ℕ))ᴴ *ᵥ ψ) := by
  have hpow : (R.run a) ^ (c : ℕ) ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
    pow_mem (R.run_mem_unitaryGroup a) _
  have hinv : (R.run a) ^ (c : ℕ) * (((R.run a) ^ (c : ℕ))ᴴ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hpow
    rwa [Matrix.star_eq_conjTranspose] at h
  have hS : (selectPowers R T).run a
      *ᵥ embedClock c false (((R.run a) ^ (c : ℕ))ᴴ *ᵥ ψ) = embedClock c false ψ := by
    rw [selectPowers_run, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [← hS, Matrix.mulVec_mulVec,
    conjTranspose_mul_self_of_unitary
      ((selectPowers R T).run_mem_unitaryGroup a), Matrix.one_mulVec]

/-- **`SELECTᴴ` on a packed history.** -/
theorem selectPowers_conjTranspose_mulVec_clockPack (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) (f : Fin T → (QBasis ι σ W → ℂ)) :
    ((selectPowers R T).run a)ᴴ *ᵥ clockPack f
      = clockPack (fun c => ((R.run a) ^ (c : ℕ))ᴴ *ᵥ f c) := by
  rw [clockPack, Matrix.mulVec_sum, clockPack]
  exact Finset.sum_congr rfl fun c _ =>
    selectPowers_conjTranspose_mulVec_embedClock R T a c (f c)

omit [Fintype W] [Fintype σ] in
omit [Fintype ι] in
/-- **The clock reflection is self-adjoint** — it is the reflection about a
projector.  No positivity hypothesis. -/
theorem clockRefl_conjTranspose (T : ℕ) [Finite W] [Finite σ] [Finite ι] :
    (clockRefl (ι := ι) (σ := σ) (W := W) T)ᴴ = clockRefl T := by
  classical
  let := Fintype.ofFinite ι
  classical
  let := Fintype.ofFinite W
  let := Fintype.ofFinite σ
  exact qRefl_conjTranspose (isQProjector_clockAvgProj T)

/-- **The phase reflection**: `SELECTᴴ · clockRefl · SELECT`. -/
noncomputable def clockPhaseRefl (R : QRoutine ι σ W) (T : ℕ) :
    QRoutine ι σ (ClockWork ι T W) :=
  (selectPowers R T).conjFixed (clockRefl T) (clockRefl_mem_unitaryGroup T)

/-- **The exact query count of the phase reflection**: `2(T-1)·R.len`.  The
reflection itself is free, so conjugation is the only cost. -/
@[simp] theorem clockPhaseRefl_len (R : QRoutine ι σ W) (T : ℕ) :
    (clockPhaseRefl R T).len = 2 * ((T - 1) * R.len) := by
  rw [clockPhaseRefl, QRoutine.conjFixed_len, selectPowers_len]

theorem clockPhaseRefl_run (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ) :
    (clockPhaseRefl R T).run a
      = ((selectPowers R T).run a)ᴴ * (clockRefl T * (selectPowers R T).run a) :=
  QRoutine.conjFixed_run _ _ _ _

/-- **The detector is self-adjoint.**  Conjugating a self-adjoint reflection
by a unitary keeps it self-adjoint.  With unitarity this is what makes the
two signed conversion errors *orthogonal*, so they combine by an exact
half-sum rather than a triangle inequality — which is where the constant
would otherwise be lost. -/
theorem clockPhaseRefl_run_conjTranspose (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) :
    ((clockPhaseRefl R T).run a)ᴴ = (clockPhaseRefl R T).run a := by
  rw [clockPhaseRefl_run, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, clockRefl_conjTranspose,
    Matrix.mul_assoc]

/-! ## The averaging identity, and exact completeness

Two facts fix the detector's behaviour at the two extremes.  On a **fixed**
vector it is exactly the identity — not approximately, which is what lets the
effective-gap argument conclude anything at all.  On a general vector it returns
the **vector average** `T⁻¹ ∑_{c<T} Uᶜψ`, whose size is the detector's entire
content; bounding *that* is the spectral half, proved elsewhere. -/

/-- **The normalized averaging identity.**  Projecting `SELECT` applied to a
uniform clock returns a uniform clock carrying the exact vector average. -/
theorem clockAvgProj_mulVec_selectPowers_uniformClock (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    clockAvgProj T *ᵥ ((selectPowers R T).run a *ᵥ uniformClock T ψ)
      = uniformClock T ((T : ℂ)⁻¹ • ∑ c : Fin T, (R.run a) ^ (c : ℕ) *ᵥ ψ) := by
  rw [selectPowers_run_uniformClock, Matrix.mulVec_smul,
    clockAvgProj_mulVec_clockPack, uniformClock]

/-- **The uniform clock is fixed by the averaging projector**: averaging a
constant history changes nothing. -/
theorem clockAvgProj_mulVec_uniformClock (hT : 0 < T) (ψ : QBasis ι σ W → ℂ) :
    clockAvgProj T *ᵥ uniformClock T ψ = uniformClock T ψ := by
  have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hconst : ((T : ℂ)⁻¹ • ∑ _c : Fin T, ψ) = ψ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hT0, one_smul]
  simp only [uniformClock, Matrix.mulVec_smul, clockAvgProj_mulVec_clockPack, hconst]

/-- **The reflection fixes the uniform clock** (`+1`). -/
theorem clockRefl_mulVec_uniformClock (hT : 0 < T) (ψ : QBasis ι σ W → ℂ) :
    clockRefl T *ᵥ uniformClock T ψ = uniformClock T ψ := by
  rw [clockRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    clockAvgProj_mulVec_uniformClock hT]
  module

/-- **The reflection negates the complement** (`-1`).  This is the sign: with
`qRefl P = 2P - 1` the *uniform* subspace is the `+1` eigenspace, so a detector
built from it reports agreement as `+1` and disagreement as `-1`. -/
theorem clockRefl_mulVec_of_avg_eq_zero {T : ℕ} {v : QBasis ι σ (ClockWork ι T W) → ℂ}
    (h : clockAvgProj T *ᵥ v = 0) : clockRefl T *ᵥ v = -v := by
  rw [clockRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h,
    smul_zero, zero_sub]

lemma pow_mulVec_eq_self {U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    {ψ : QBasis ι σ W → ℂ} (h : U *ᵥ ψ = ψ) (n : ℕ) : U ^ n *ᵥ ψ = ψ := by
  induction n with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, ih]

/-- **`SELECT` fixes a uniform clock over a fixed vector**: every branch applies
a power of `U`, and every power fixes `ψ`. -/
theorem selectPowers_run_mulVec_uniformClock_of_fixed (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) {ψ : QBasis ι σ W → ℂ} (h : R.run a *ᵥ ψ = ψ) :
    (selectPowers R T).run a *ᵥ uniformClock T ψ = uniformClock T ψ := by
  have hf : (fun c : Fin T => (R.run a) ^ (c : ℕ) *ᵥ ψ) = (fun _ : Fin T => ψ) :=
    funext fun c => pow_mulVec_eq_self h _
  rw [selectPowers_run_uniformClock, hf, uniformClock]

/-- **Exact completeness**: on a fixed vector the detector is the identity, with
no error term at all. -/
theorem clockPhaseRefl_run_mulVec_uniformClock_of_fixed (R : QRoutine ι σ W) {T : ℕ}
    (hT : 0 < T) (a : ι → σ) {ψ : QBasis ι σ W → ℂ} (h : R.run a *ᵥ ψ = ψ) :
    (clockPhaseRefl R T).run a *ᵥ uniformClock T ψ = uniformClock T ψ := by
  have hS : (selectPowers R T).run a *ᵥ uniformClock T ψ = uniformClock T ψ :=
    selectPowers_run_mulVec_uniformClock_of_fixed R T a h
  have hSt : ((selectPowers R T).run a)ᴴ *ᵥ uniformClock T ψ = uniformClock T ψ := by
    conv_lhs => rw [← hS]
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary
      ((selectPowers R T).run_mem_unitaryGroup a), Matrix.one_mulVec]
  rw [clockPhaseRefl_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hS,
    clockRefl_mulVec_uniformClock hT, hSt]

/-! ## The uniform clock, as an isometry

Moved down from `SourceQuantumDetection`: this geometry is generic, and the uniform
witness needs the clock isometry without importing the Boolean detection
layer. -/

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma embedReg_add {V : Type} [DecidableEq V] (v : V)
    (ψ φ : QBasis ι σ W → ℂ) :
    embedReg v (ψ + φ) = embedReg v ψ + embedReg v φ := by
  classical
  funext p
  by_cases h : p.2.2.1 = v <;> simp [embedReg_apply, h]

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma embedClock_add (c : Fin T) (b : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    embedClock c b (ψ + φ) = embedClock c b ψ + embedClock c b φ := by
  classical
  simp only [embedClock, embedCtrl]
  rw [embedReg_add, embedReg_add, embedReg_add]

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
/-- **The uniform clock is additive.** -/
lemma uniformClock_add (T : ℕ) (ψ φ : QBasis ι σ W → ℂ) :
    uniformClock T (ψ + φ) = uniformClock T ψ + uniformClock T φ := by
  classical
  simp only [uniformClock, clockPack]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun c _ => embedClock_add c false ψ φ

omit [DecidableEq W] [DecidableEq σ] in
/-- **The inner product of two packed histories** is branchwise. -/
theorem qInner_clockPack (f g : Fin T → (QBasis ι σ W → ℂ)) :
    qInner (clockPack f) (clockPack g) = ∑ c : Fin T, qInner (f c) (g c) := by
  classical
  rw [clockPack, clockPack, qInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [qInner_sum_right, Finset.sum_eq_single c]
  · rw [qInner_embedClock, ite_eq_left ⟨rfl, rfl⟩]
  · intro c' _ hc'
    rw [qInner_embedClock, ite_eq_right fun hcon => hc' hcon.1.symm]
  · simp

omit [DecidableEq W] [DecidableEq σ] in
/-- **The uniform clock is an isometry** (for `0 < T`). -/
theorem qInner_uniformClock (hT : 0 < T) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (uniformClock T ψ) (uniformClock T φ) = qInner ψ φ := by
  classical
  have hcast : ((T : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  rw [uniformClock, uniformClock, qInner_smul_left, qInner_smul_right,
    qInner_clockPack, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, star_inv₀, RCLike.star_def, Complex.conj_ofReal]
  rw [show (((Real.sqrt T : ℝ) : ℂ))⁻¹
        * ((((Real.sqrt T : ℝ) : ℂ))⁻¹ * ((T : ℂ) * qInner ψ φ))
      = (((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ))⁻¹
        * ((T : ℂ) * qInner ψ φ) from by rw [mul_inv]; ring]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg T),
    show (((T : ℝ) : ℂ)) = ((T : ℕ) : ℂ) from by push_cast; ring,
    inv_mul_cancel_left₀ hcast]

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
/-- **The uniform clock is `ℂ`-homogeneous.** -/
lemma uniformClock_smul (T : ℕ) (r : ℂ) (ψ : QBasis ι σ W → ℂ) :
    uniformClock T (r • ψ) = r • uniformClock T ψ := by
  classical
  simp only [uniformClock, clockPack]
  rw [Finset.sum_congr rfl fun c _ => embedClock_smul c false r ψ,
    ← Finset.smul_sum, smul_comm]

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
/-- **The uniform clock is subtractive.** -/
lemma uniformClock_sub (T : ℕ) (ψ φ : QBasis ι σ W → ℂ) :
    uniformClock T (ψ - φ) = uniformClock T ψ - uniformClock T φ := by
  classical
  have h2 := uniformClock_add T (ψ - φ) φ
  rw [sub_add_cancel] at h2
  rw [h2, add_sub_cancel_right]

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
/-- **The empty clock carries nothing**: at `T = 0` the clock pack is an empty
sum, so `uniformClock 0 ψ = 0`.  This is what lets `T = 0` splits downstream
avoid positivity hypotheses. -/
lemma uniformClock_zero (ψ : QBasis ι σ W → ℂ) :
    uniformClock 0 ψ = 0 := by
  rw [uniformClock, clockPack]
  simp

end QuantumQueryComplexity

end SourceQuantumClock

section SourceQuantumOperationalGap

/-!
# The effective gap, for the operational reflection product

The **effective-gap specialization bridge**, where the *operational* layer
(routines, queries, oracles) and the *spectral* layer (functional calculus,
chord windows) meet for the reflection product.  It is not the only such
crossing — `SourceQuantumClockDetector` is the *suppression* bridge, joining the same
two layers for the uniform clock — so the two are kept apart, and
`SourceQuantumInputDetector` combines both estimates.

`SourceQuantumChordWindow` states the effective gap for an arbitrary pair of projectors,
which is how it should be stated — it is a fact about reflections, not about
queries.  `SourceQuantumReflection` builds the operational product `R_P · R_L` as a
two-query routine. This section instantiates the spectral theorem with that routine.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **The effective gap, for the operational product.**  The abstract theorem of
`SourceQuantumChordWindow`, instantiated by the two-query routine of
`SourceQuantumReflection`. -/
theorem effective_chord_gap_sq_inputReflProduct (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (a : ι → σ)
    {w : QBasis ι σ W → ℂ} (hw : L *ᵥ w = 0) (Δ : ℝ) :
    qNormSq (chordNearProj ((inputReflProduct v L hL).run a) Δ *ᵥ (inputProj v a *ᵥ w))
      ≤ (Δ ^ 2 / 4) * qNormSq w := by
  rw [inputReflProduct_run]
  exact effective_chord_gap_sq (isQProjector_inputProj v a) hL hw Δ

end QuantumQueryComplexity

end SourceQuantumOperationalGap

section SourceQuantumClockDetector

/-!
# The uniform-clock detector

The **suppression bridge**: the operational clock of `SourceQuantumClock` meets the
spectral estimate of `SourceQuantumClockGap`.  It needs those two and nothing else — in
particular not `SourceQuantumOperationalGap`, which is for *specializing* this to the
input reflection product, not for stating it.

The detector is `clockPhaseRefl R T = SELECTᴴ · clockRefl · SELECT`, and the two
facts about it are exactly the two extremes:

* **Completeness** (`SourceQuantumClock`): on a fixed vector it is the identity, exactly.
* **Soundness** (here): on the far window it is `-1` up to an error that shrinks
  like `1/T`:

      `‖D·u + u‖² ≤ 16/(T²Δ²)·‖x‖²`,   `u = uniformClock T (F x)`.

Both come from one algebraic identity, `D·u + u = 2·SELECTᴴ P SELECT u`: the
detector's deviation from `-1` **is** twice the averaging projector's output, so
soundness is precisely the statement that the vector average is small.  The `16`
is `4 · 4`: one factor from that `2`, squared, and one from `‖1 - Uᵀ‖ ≤ 2` inside
the suppression bound.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- **The detector's deviation from `-1` is twice the averaged state.**  This is
the identity behind everything below: `D·u + u = 2·SELECTᴴ P SELECT u`. -/
theorem clockPhaseRefl_run_mulVec_add (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ)
    (u : QBasis ι σ (ClockWork ι T W) → ℂ) :
    (clockPhaseRefl R T).run a *ᵥ u + u
      = (2 : ℂ) • (((selectPowers R T).run a)ᴴ
          *ᵥ (clockAvgProj T *ᵥ ((selectPowers R T).run a *ᵥ u))) := by
  have hSS : ((selectPowers R T).run a)ᴴ *ᵥ ((selectPowers R T).run a *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary
      ((selectPowers R T).run_mem_unitaryGroup a), Matrix.one_mulVec]
  rw [clockPhaseRefl_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, clockRefl,
    qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, hSS]
  module

lemma conjTranspose_mem_unitaryGroup {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact conjTranspose_mul_self_of_unitary hU

/-- **Soundness of the detector**, multiplied out.  On the far window the
detector is `-1` up to an error controlled by `1/(TΔ)`.  As with the suppression
bound it rests on, this form needs **no positivity hypothesis**: at `T = 0` the
factor `T²` kills the left side. -/
theorem qNormSq_clockPhaseRefl_add_le (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) (Δ : ℝ) (x : QBasis ι σ W → ℂ) :
    (T : ℝ) ^ 2 * Δ ^ 2
        * qNormSq ((clockPhaseRefl R T).run a
              *ᵥ uniformClock T (chordFarProj (R.run a) Δ *ᵥ x)
            + uniformClock T (chordFarProj (R.run a) Δ *ᵥ x))
      ≤ 16 * qNormSq x := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · -- an empty clock: the left side carries the factor `T² = 0`
    subst hT
    have hq := qNormSq_nonneg x
    have h0 : ((0 : ℕ) : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, zero_mul, zero_mul]
    linarith
  have hU := R.run_mem_unitaryGroup a
  have hSu := (selectPowers R T).run_mem_unitaryGroup a
  -- the deviation is twice the averaged state, whose norm is the vector average
  have hdev := clockPhaseRefl_run_mulVec_add R T a
    (uniformClock T (chordFarProj (R.run a) Δ *ᵥ x))
  have havg : clockAvgProj T *ᵥ ((selectPowers R T).run a
        *ᵥ uniformClock T (chordFarProj (R.run a) Δ *ᵥ x))
      = uniformClock T ((T : ℂ)⁻¹
          • ∑ c : Fin T, (R.run a) ^ (c : ℕ) *ᵥ (chordFarProj (R.run a) Δ *ᵥ x)) :=
    clockAvgProj_mulVec_selectPowers_uniformClock R T a _
  rw [hdev, havg, qNormSq_smul, qNormSq_mulVec (conjTranspose_mem_unitaryGroup hSu),
    qNormSq_uniformClock hT]
  have hsupp := qNormSq_avg_pow_chordFar hU Δ T x
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h2]
  nlinarith [hsupp]

/-- **Soundness of the detector**, in divided form:
`‖D·u + u‖² ≤ 16/(T²Δ²)·‖x‖²`. -/
theorem qNormSq_clockPhaseRefl_add_le_div (R : QRoutine ι σ W) {T : ℕ} (hT : 0 < T)
    (a : ι → σ) {Δ : ℝ} (hΔ : 0 < Δ) (x : QBasis ι σ W → ℂ) :
    qNormSq ((clockPhaseRefl R T).run a
          *ᵥ uniformClock T (chordFarProj (R.run a) Δ *ᵥ x)
        + uniformClock T (chordFarProj (R.run a) Δ *ᵥ x))
      ≤ 16 / ((T : ℝ) ^ 2 * Δ ^ 2) * qNormSq x := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hpos : (0 : ℝ) < (T : ℝ) ^ 2 * Δ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm]
  exact qNormSq_clockPhaseRefl_add_le R T a Δ x

end QuantumQueryComplexity

end SourceQuantumClockDetector

section SourceQuantumInputDetector

/-!
# The detector for the input reflection product

The specialization, and the only file that needs both the suppression bridge
(`SourceQuantumClockDetector`) and the effective gap for the operational product
(`SourceQuantumOperationalGap`).  Everything upstream stays generic: `ClockDetector`
knows nothing about input reflections, `OperationalGap` nothing about clocks.

Three facts, which together are the detector's guarantee on `P w`:

* **Cost.**  `4(T-1)` queries, exactly.  `inputReflProduct` costs `2` because
  the `L`-side reflection is a fixed, zero-query `ofUnitary`, and conjugating
  `SELECT` doubles `(T-1)·2`.  If both sides were input-dependent this would be
  `8(T-1)`.
* **The far part is large.**  The effective gap bounds the *near* part of `P w`
  by `(Δ²/4)‖w‖²`, so by the Pythagorean decomposition the far part carries at
  least `‖P w‖² - (Δ²/4)‖w‖²`.
* **The detector reads `-1` there**, up to `16/(T²Δ²)·‖P w‖²`.

Completeness is `clockPhaseRefl_run_mulVec_uniformClock_of_fixed`: on a vector
fixed by the reflection product the detector is *exactly* the identity, so the
two verdicts are separated with no error on one side.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- **The exact cost of the input detector**: `4(T-1)` queries. -/
theorem clockPhaseRefl_len_inputReflProduct (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (T : ℕ) :
    (clockPhaseRefl (inputReflProduct v L hL) T).len = 4 * (T - 1) := by
  rw [clockPhaseRefl_len, inputReflProduct_len]
  ring

/-- **The far window carries what the effective gap leaves.**  The near part of
`P w` is at most `(Δ²/4)‖w‖²`, so the far part — the part the detector sees — is
at least `‖P w‖²` minus that. -/
theorem le_qNormSq_chordFar_inputProj (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (a : ι → σ)
    {w : QBasis ι σ W → ℂ} (hw : L *ᵥ w = 0) (Δ : ℝ) :
    qNormSq (inputProj v a *ᵥ w) - (Δ ^ 2 / 4) * qNormSq w
      ≤ qNormSq (chordFarProj ((inputReflProduct v L hL).run a) Δ
          *ᵥ (inputProj v a *ᵥ w)) := by
  have hdec := qNormSq_chord_decomp ((inputReflProduct v L hL).run a) Δ
    (inputProj v a *ᵥ w)
  have hnear := effective_chord_gap_sq_inputReflProduct v L hL a hw Δ
  linarith

/-- **The input detector reads `-1` on the far window**, multiplied out — and,
like the bound it specializes, with no positivity hypothesis. -/
theorem qNormSq_clockPhaseRefl_add_le_inputReflProduct (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (T : ℕ)
    (a : ι → σ) (Δ : ℝ) (w : QBasis ι σ W → ℂ) :
    (T : ℝ) ^ 2 * Δ ^ 2
        * qNormSq ((clockPhaseRefl (inputReflProduct v L hL) T).run a
              *ᵥ uniformClock T (chordFarProj ((inputReflProduct v L hL).run a) Δ
                  *ᵥ (inputProj v a *ᵥ w))
            + uniformClock T (chordFarProj ((inputReflProduct v L hL).run a) Δ
                *ᵥ (inputProj v a *ᵥ w)))
      ≤ 16 * qNormSq (inputProj v a *ᵥ w) :=
  qNormSq_clockPhaseRefl_add_le (inputReflProduct v L hL) T a Δ (inputProj v a *ᵥ w)

/-- **The input detector reads `-1` on the far window**, in divided form. -/
theorem qNormSq_clockPhaseRefl_add_le_div_inputReflProduct
    (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) {T : ℕ}
    (hT : 0 < T) (a : ι → σ) {Δ : ℝ} (hΔ : 0 < Δ) (w : QBasis ι σ W → ℂ) :
    qNormSq ((clockPhaseRefl (inputReflProduct v L hL) T).run a
          *ᵥ uniformClock T (chordFarProj ((inputReflProduct v L hL).run a) Δ
              *ᵥ (inputProj v a *ᵥ w))
        + uniformClock T (chordFarProj ((inputReflProduct v L hL).run a) Δ
            *ᵥ (inputProj v a *ᵥ w)))
      ≤ 16 / ((T : ℝ) ^ 2 * Δ ^ 2) * qNormSq (inputProj v a *ᵥ w) :=
  qNormSq_clockPhaseRefl_add_le_div (inputReflProduct v L hL) hT a hΔ
    (inputProj v a *ᵥ w)

end QuantumQueryComplexity

end SourceQuantumInputDetector

section SourceQuantumStateConversion

/-!
# Witness states for state conversion

The detector of `SourceQuantumInputDetector` distinguishes two
kinds of vector: those **fixed** by the reflection product `R_P R_L`, which it
reports as `+1` exactly, and those in the **far window**, which it reports as
`-1` up to `16/(T²Δ²)`.  State conversion has to supply both, from a dual
adversary solution.

This section fixes the *contracts* — what a construction must prove — and derives
everything that follows from them formally, so that the construction itself has
a single, sharp target.

## The positive side

A positive witness for the input `a` is a state `φ` with

    inputProj v a *ᵥ φ = φ        and        L *ᵥ φ = φ.

Both reflections then fix `φ`, hence so does `inputReflProduct`, hence the
detector is **exactly** the identity on `uniformClock T φ`.  No estimate is
involved on this side, which is the point.

**The witness is not the bare target.**  In the corrected LMRSS construction the
fixed point is `φₓ = t₊ + (witness-workspace term)`, not `t₊` itself: `t₊` alone
is in general *not* fixed by `inputProj v a`, since being fixed means the
oracle-rotated state is orthogonal to **every** generator `v i`, which the
workspace term is exactly what arranges.  Building the algorithm around bare
`t₊` would be a real error, not a normalization detail, so the overlap
`⟪t₊, φₓ⟫` is a separate obligation of the construction rather than something
this interface can assume.

`inputProj_mulVec_eq_self_iff` reduces the first contract to one inner product
per generator, which is the form a construction can discharge.

## The negative side

A negative witness is a `w` with `L *ᵥ w = 0`.  That is precisely the hypothesis
of `effective_chord_gap_sq_inputReflProduct`, so the near component of `P w` is
at most `(Δ²/4)‖w‖²` and — by `le_qNormSq_chordFar_inputProj` — the far window
carries the rest.

That is the *spectral* half of the negative side, and it is all this interface
supplies.  It is **not** all the construction owes.  Two further obligations
stay with the concrete witness, and neither is formal:

* a bound on `‖w‖²`, since the effective gap charges `(Δ²/4)‖w‖²` against
  `‖P w‖²` — a negative witness of uncontrolled norm buys nothing;
* the identification of `inputProj v a *ᵥ w` with the intended `t₋` direction.
  As on the positive side, `w` carries a correction term beyond `t₋`, and what
  has to be shown is that `inputProj` *kills* that term, leaving the direction
  the algorithm measures.

So the asymmetry between the two sides is real but small: the positive side ends
in an exact fixed-point identity, the negative side in two estimates.  Both are
quantitative facts about a particular construction, which is why neither lives
in `IsPosWitness`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-! ## Being fixed by the input projector -/

/-- **Fixed by the input projector = orthogonal to every generator, after the
query.**  `inputProj v a` conjugates the complement projector by one oracle call
on each side, so its fixed space is the pullback along the oracle of the
orthogonal complement of the generators. -/
theorem inputProj_mulVec_eq_self_iff (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ)
    (φ : QBasis ι σ W → ℂ) :
    inputProj v a *ᵥ φ = φ ↔ ∀ i, qInner (v i) (oracleMat a *ᵥ φ) = 0 := by
  have hO : ∀ ψ : QBasis ι σ W → ℂ, oracleMat a *ᵥ (oracleMat a *ᵥ ψ) = ψ := fun ψ => by
    rw [Matrix.mulVec_mulVec, oracleMat_mul_self, Matrix.one_mulVec]
  have hsplit : inputProj v a *ᵥ φ
      = oracleMat a *ᵥ (subProj (rawSpan v)ᗮ *ᵥ (oracleMat a *ᵥ φ)) := by
    rw [inputProj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hsplit]
  constructor
  · intro h
    have h2 := congrArg (fun ψ => oracleMat a *ᵥ ψ) h
    simp only [hO] at h2
    exact (mem_rawSpan_orthogonal_iff v _).mp
      ((subProj_mulVec_eq_self_iff _ _).mp h2)
  · intro h
    rw [(subProj_mulVec_eq_self_iff _ _).mpr ((mem_rawSpan_orthogonal_iff v _).mpr h),
      hO]

/-! ## The positive witness -/

/-- **A positive witness** for the input `a`: fixed by the input projector and by
`L`.  These are the two contracts a state-conversion construction must
discharge; everything below is formal consequence. -/
structure IsPosWitness (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (a : ι → σ)
    (φ : QBasis ι σ W → ℂ) : Prop where
  /-- The oracle-rotated witness is orthogonal to every generator. -/
  inputFixed : inputProj v a *ᵥ φ = φ
  /-- The witness lies in the fixed space of `L`. -/
  fixedL : L *ᵥ φ = φ

namespace IsPosWitness

variable {v : ι' → (QBasis ι σ W → ℂ)} {L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
  {a : ι → σ} {φ : QBasis ι σ W → ℂ}

/-- Build a witness from the generator-orthogonality form. -/
theorem of_inner (h : ∀ i, qInner (v i) (oracleMat a *ᵥ φ) = 0) (hL : L *ᵥ φ = φ) :
    IsPosWitness v L a φ :=
  ⟨(inputProj_mulVec_eq_self_iff v a φ).mpr h, hL⟩

/-- **The input reflection fixes the witness.** -/
theorem inputRefl_run_mulVec (h : IsPosWitness v L a φ) :
    (inputRefl v).run a *ᵥ φ = φ := by
  rw [inputRefl_run_eq_qRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, h.inputFixed]
  module

/-- **The `L`-reflection fixes the witness.** -/
theorem qRefl_mulVec (h : IsPosWitness v L a φ) : qRefl L *ᵥ φ = φ := by
  rw [qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h.fixedL]
  module

/-- **The reflection product fixes the witness.**  Both factors do, so the
product does — and this is the hypothesis the detector's completeness theorem
asks for. -/
theorem inputReflProduct_run_mulVec (h : IsPosWitness v L a φ)
    (hL : IsQProjector L) : (inputReflProduct v L hL).run a *ᵥ φ = φ := by
  rw [inputReflProduct_run, ← Matrix.mulVec_mulVec, h.qRefl_mulVec,
    ← inputRefl_run_eq_qRefl, h.inputRefl_run_mulVec]

/-- **Detector completeness, immediately.**  On a uniform clock over a positive
witness the detector is exactly the identity — no error term, at cost
`4(T-1)`. -/
theorem clockPhaseRefl_run_mulVec_uniformClock (h : IsPosWitness v L a φ)
    (hL : IsQProjector L) {T : ℕ} (hT : 0 < T) :
    (clockPhaseRefl (inputReflProduct v L hL) T).run a *ᵥ uniformClock T φ
      = uniformClock T φ :=
  clockPhaseRefl_run_mulVec_uniformClock_of_fixed _ hT a
    (h.inputReflProduct_run_mulVec hL)

/-- The witness lies in the near window for every `Δ`: it is fixed, so its chord
distance is zero. -/
theorem chordNearProj_mulVec (h : IsPosWitness v L a φ) (hL : IsQProjector L)
    (Δ : ℝ) :
    chordNearProj ((inputReflProduct v L hL).run a) Δ *ᵥ φ = φ :=
  chordNearProj_mulVec_of_fixed _ Δ (h.inputReflProduct_run_mulVec hL)

/-- …and therefore contributes nothing to the far window, which is what keeps
the two verdicts apart. -/
theorem chordFarProj_mulVec (h : IsPosWitness v L a φ) (hL : IsQProjector L)
    (Δ : ℝ) :
    chordFarProj ((inputReflProduct v L hL).run a) Δ *ᵥ φ = 0 :=
  chordFarProj_mulVec_of_fixed _ Δ (h.inputReflProduct_run_mulVec hL)

end IsPosWitness

/-! ## Generators are killed by the input projector

`inputProj v a` is `oracleMat a` conjugating the projector onto
`(rawSpan v)ᗮ`.  A generator, carried through the oracle, therefore lands on
the span itself and is annihilated.  This is the one fact the uniform
witness's projector contracts need, and it is generic: nothing about the
particular family `v` enters. -/

/-- **The fixed space of `inputProj`**, in the form a witness can check: one
inner product per generator, no spans. -/
theorem inputProj_mulVec_of_forall_qInner_eq_zero {ι σ W ι' : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W]
    (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) {ψ : QBasis ι σ W → ℂ}
    (h : ∀ p, qInner (v p) (oracleMat a *ᵥ ψ) = 0) :
    inputProj v a *ᵥ ψ = ψ := by
  exact (inputProj_mulVec_eq_self_iff v a ψ).mpr h

theorem inputProj_mulVec_oracle_generator {ι σ W ι' : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W]
    (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) (p : ι') :
    inputProj v a *ᵥ (oracleMat a *ᵥ v p) = 0 := by
  have hmem : (WithLp.toLp 2 (v p) : EuclideanSpace ℂ (QBasis ι σ W))
      ∈ ((rawSpan v)ᗮ)ᗮ :=
    Submodule.le_orthogonal_orthogonal _ (Submodule.subset_span ⟨p, rfl⟩)
  have hzero : subProj (rawSpan v)ᗮ *ᵥ v p = 0 :=
    subProj_mulVec_of_mem_orthogonal _ hmem
  have hinv : oracleMat a *ᵥ (oracleMat a *ᵥ v p) = v p := by
    rw [Matrix.mulVec_mulVec, oracleMat_mul_self, Matrix.one_mulVec]
  rw [inputProj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, hzero,
    Matrix.mulVec_zero]

end QuantumQueryComplexity

end SourceQuantumStateConversion

section SourceQuantumUniformWitness

/-!
# The coherent target states

These coherent targets fix the normalization used by the uniform extraction.
The Boolean witness construction is retained in `SourceQuantumWitness`.

The output register must not be indexed by `O` — `O` is an arbitrary
decidable type with no `Fintype` — but it need not be: only the **image** of
`f` is ever occupied, and `Set.range f` is finite whenever `X` is, whatever
`O` is.  So the workspace is `Option ↥(Set.range f)`: one "common"
coordinate beside one coordinate per attained output.  (`X = ∅` is handled
separately by the caller; `[Nonempty O]` is what keeps the readout total.)

The target states are

    t_{x±} = (|common⟩ ± |f x⟩) / √2

and the identity that drives the whole construction is

    ⟪t_{y−}, t_{x+}⟫ = ½·[f y ≠ f x].

**The `½` is load-bearing.**  It is what forces the witness scaling to be

    φ_x = t_{x+} + α·V_x,        w_y = t_{y−} − (2α)⁻¹·U_y,

since then `(2α)⁻¹·α = ½` cancels the `½` above against
`⟪U_y, V_x⟫ = [f y ≠ f x]`, giving **exact** orthogonality `⟪w_y, φ_x⟫ = 0`.
Dropping the `½` — scaling by `α⁻¹` instead — would destroy that
cancellation, and the resulting norm bound `1 + 2α⁻²c` is in any case four
times looser than the correct `1 + c/(2α²)`.

These states are literally the alphabet gadget of `SourceQuantumUniformAlphabet`
applied to the alphabet `Set.range f` and rescaled by `(√2)⁻¹`: the `½` in
the overlap is exactly that rescaling squared.  So the `(1, ±e)`
factorization does double duty — packets on `σ`, targets on `range f` — and
the two `½`s that cancel have a common origin.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {X O : Type} [Fintype X] [DecidableEq O] {f : X → O}

/-- The attained output of `x`, as an element of the finite workspace. -/
@[expose]
def rangeElem (f : X → O) (x : X) : ↥(Set.range f) := ⟨f x, ⟨x, rfl⟩⟩

omit [DecidableEq O] [Fintype X] in
@[simp] lemma rangeElem_val (f : X → O) (x : X) :
    ((rangeElem f x : ↥(Set.range f)) : O) = f x := rfl

omit [DecidableEq O] [Fintype X] in
lemma rangeElem_eq_iff (f : X → O) (x y : X) :
    rangeElem f x = rangeElem f y ↔ f x = f y := by
  rw [rangeElem, rangeElem, Subtype.ext_iff]

/-- The `+` target state `(|common⟩ + |f x⟩)/√2`. -/
noncomputable def tPlus (f : X → O) (x : X) : Option ↥(Set.range f) → ℝ :=
  (Real.sqrt 2)⁻¹ • uniformLeft (rangeElem f x)

/-- The `−` target state `(|common⟩ − |f x⟩)/√2`. -/
noncomputable def tMinus (f : X → O) (x : X) : Option ↥(Set.range f) → ℝ :=
  (Real.sqrt 2)⁻¹ • uniformRight (rangeElem f x)

lemma inv_sqrt_two_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- The normalization fact in the form the conversion bounds consume. -/
theorem normSq_inv_sqrt_two :
    Complex.normSq ((((Real.sqrt 2)⁻¹ : ℝ)) : ℂ) = 1 / 2 := by
  rw [Complex.normSq_ofReal]
  exact inv_sqrt_two_sq

/-- **The `+` and `−` targets are orthogonal on matching outputs.** -/
theorem tPlus_dotProduct_tMinus (f : X → O) (x y : X) :
    tPlus f x ⬝ᵥ tMinus f y = if f x = f y then 0 else 1 / 2 := by
  rw [tPlus, tMinus, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq, uniform_dotProduct]
  by_cases hxy : f x = f y
  · rw [ite_eq_left ((rangeElem_eq_iff f x y).mpr hxy), ite_eq_left hxy]
    norm_num
  · rw [ite_eq_right (fun h => hxy ((rangeElem_eq_iff f x y).mp h)), ite_eq_right hxy]
    norm_num

/-- **The target states are unit vectors.** -/
theorem tPlus_normSq (f : X → O) (x : X) : tPlus f x ⬝ᵥ tPlus f x = 1 := by
  rw [tPlus, smul_dotProduct, dotProduct_smul, uniformLeft_normSq,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq]
  norm_num

theorem tMinus_normSq (f : X → O) (x : X) : tMinus f x ⬝ᵥ tMinus f x = 1 := by
  rw [tMinus, smul_dotProduct, dotProduct_smul, uniformRight_normSq,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq]
  norm_num

/-- **The driving identity**: `⟪t_{y−}, t_{x+}⟫ = ½·[f y ≠ f x]`.  The `½` is
what forces the `(2α)⁻¹` in the witness scaling. -/
theorem tMinus_dotProduct_tPlus (f : X → O) (x y : X) :
    tMinus f y ⬝ᵥ tPlus f x = if f x = f y then 0 else 1 / 2 := by
  rw [tMinus, tPlus, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq,
    dotProduct_comm (uniformRight (rangeElem f y)) (uniformLeft (rangeElem f x)),
    uniform_dotProduct]
  by_cases hxy : f x = f y
  · rw [ite_eq_left ((rangeElem_eq_iff f x y).mpr hxy), ite_eq_left hxy]
    norm_num
  · rw [ite_eq_right (fun h => hxy ((rangeElem_eq_iff f x y).mp h)), ite_eq_right hxy]
    norm_num

/-- The same identity in the form the orthogonality computation uses: the
overlap is `½` exactly on the pairs the dual constraint has to separate. -/
theorem tMinus_dotProduct_tPlus_of_ne (f : X → O) {x y : X} (h : f x ≠ f y) :
    tMinus f y ⬝ᵥ tPlus f x = 1 / 2 := by
  rw [tMinus_dotProduct_tPlus, ite_eq_right h]

theorem tMinus_dotProduct_tPlus_of_eq (f : X → O) {x y : X} (h : f x = f y) :
    tMinus f y ⬝ᵥ tPlus f x = 0 := by
  rw [tMinus_dotProduct_tPlus, ite_eq_left h]

/-! ## The common and output vectors

The conversion combines the two signed targets through

    common = (t_{x+} + t_{x−})/√2        out(f x) = (t_{x+} − t_{x−})/√2,

which are exactly the constant coordinate and the attained-output
coordinate: the algorithm starts on the input-**independent** `common`
state, and the detector carries it onto the output-labelled unit vector.
Distinct outputs give orthogonal `out` vectors, which is what the final
readout measures — one coherent conversion, never one detector per
output. -/

/-- The common initial vector: the constant coordinate alone. -/
@[expose]
def commonVec {R : Type} : Option R → ℝ
  | none => 1
  | some _ => 0

/-- The output-labelled vector: the coordinate of one attained output. -/
@[expose]
def outVec {R : Type} [DecidableEq R] (r : R) : Option R → ℝ
  | none => 0
  | some s => if s = r then 1 else 0

@[simp] lemma commonVec_none {R : Type} : commonVec (R := R) none = 1 := rfl

@[simp] lemma commonVec_some {R : Type} (r : R) :
    commonVec (some r) = 0 := rfl

@[simp] lemma outVec_none {R : Type} [DecidableEq R] (r : R) :
    outVec r none = 0 := rfl

@[simp] lemma outVec_some {R : Type} [DecidableEq R] (r s : R) :
    outVec r (some s) = if s = r then 1 else 0 := rfl

/-- The common vector is a unit vector. -/
theorem commonVec_dotProduct_commonVec {R : Type} [Fintype R] :
    (commonVec (R := R)) ⬝ᵥ commonVec = 1 := by
  rw [dotProduct, Fintype.sum_option]
  simp

/-- **The output vectors are orthonormal**: the pairing is the equality
indicator. -/
theorem outVec_dotProduct_outVec {R : Type} [Fintype R] [DecidableEq R]
    (r r' : R) : outVec r ⬝ᵥ outVec r' = if r = r' then 1 else 0 := by
  rw [dotProduct, Fintype.sum_option]
  have hterm : ∀ s : R, outVec r (some s) * outVec r' (some s)
      = if s = r then (if r = r' then (1 : ℝ) else 0) else 0 := by
    intro s
    rw [outVec_some, outVec_some]
    by_cases hs : s = r
    · rw [ite_eq_left hs, ite_eq_left hs, one_mul, hs]
    · rw [ite_eq_right hs, ite_eq_right hs, zero_mul]
  rw [Finset.sum_congr rfl fun s _ => hterm s]
  simp

/-- The common and output vectors are orthogonal. -/
theorem commonVec_dotProduct_outVec {R : Type} [Fintype R] [DecidableEq R]
    (r : R) : commonVec ⬝ᵥ outVec r = 0 := by
  rw [dotProduct, Fintype.sum_option]
  simp

theorem outVec_dotProduct_commonVec {R : Type} [Fintype R] [DecidableEq R]
    (r : R) : outVec r ⬝ᵥ commonVec = 0 := by
  rw [dotProduct, Fintype.sum_option]
  simp

omit [Fintype X] in
/-- **`(t₊ + t₋)/√2` is exactly the common vector** — the `x`-dependence
cancels. -/
theorem smul_tPlus_add_tMinus (f : X → O) (x : X) :
    (Real.sqrt 2)⁻¹ • (tPlus f x + tMinus f x) = commonVec := by
  funext s
  cases s with
  | none =>
    simp only [Pi.smul_apply, Pi.add_apply, tPlus, tMinus, smul_eq_mul,
      uniformLeft_none, uniformRight_none, commonVec_none]
    linear_combination 2 * inv_sqrt_two_sq
  | some r =>
    simp only [Pi.smul_apply, Pi.add_apply, tPlus, tMinus, smul_eq_mul,
      uniformLeft_some, uniformRight_some, commonVec_some]
    by_cases h : r = rangeElem f x
    · rw [ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      ring

omit [Fintype X] in
/-- **`(t₊ − t₋)/√2` is exactly the output-labelled vector.** -/
theorem smul_tPlus_sub_tMinus (f : X → O) (x : X) :
    (Real.sqrt 2)⁻¹ • (tPlus f x - tMinus f x) = outVec (rangeElem f x) := by
  funext s
  cases s with
  | none =>
    simp only [Pi.smul_apply, Pi.sub_apply, tPlus, tMinus, smul_eq_mul,
      uniformLeft_none, uniformRight_none, outVec_none]
    ring
  | some r =>
    simp only [Pi.smul_apply, Pi.sub_apply, tPlus, tMinus, smul_eq_mul,
      uniformLeft_some, uniformRight_some, outVec_some]
    by_cases h : r = rangeElem f x
    · rw [ite_eq_left h, ite_eq_left h]
      linear_combination 2 * inv_sqrt_two_sq
    · rw [ite_eq_right h, ite_eq_right h]
      ring

/-! ## The tagged query packets

The packet register is one `Option σ` block **per pair `(i, k)`** — every
pair carries its own flag coordinate.  A shared flag would make different
blocks overlap, and the whole point of the construction is that they do not.

    g_{i,k}         = idleFlag_{i,k} + activeBlank_{i,k}
    leftAtom_{i,k,a}  = idleFlag_{i,k} + answer_{i,k,a}      (the oracle image)
    rightAtom_{i,k,a} = idleFlag_{i,k} − answer_{i,k,a}

Inside a block these are exactly `uniformLeft` and `uniformRight`, so the
`[a ≠ b]` factorization is inherited blockwise, and distinct blocks are
orthogonal.  The ambient space is the target register **direct-summed** with
the packet blocks, which makes every target/packet cross term vanish by
construction. -/

section Packets

variable {R ι σ K : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]

/-- The ambient index: the target register, direct-summed with one
`Option σ` packet block per `(i, k)`. -/
abbrev UBasis (R ι σ K : Type) : Type :=
  Option R ⊕ ((ι × K) × Option σ)

/-- A target-register vector, embedded. -/
def uTarget (t : Option R → ℝ) : UBasis R ι σ K → ℂ :=
  Sum.elim (fun s => ((t s : ℝ) : ℂ)) fun _ => 0

omit [DecidableEq K] [DecidableEq R] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype R]
    [Fintype ι] [Fintype σ] in
lemma uTarget_add (t t' : Option R → ℝ) :
    uTarget (ι := ι) (σ := σ) (K := K) (t + t')
      = uTarget t + uTarget t' := by
  classical
  funext b
  cases b with
  | inl s => simp [uTarget]
  | inr q => simp [uTarget]

omit [DecidableEq K] [DecidableEq R] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype R]
    [Fintype ι] [Fintype σ] in
lemma uTarget_sub (t t' : Option R → ℝ) :
    uTarget (ι := ι) (σ := σ) (K := K) (t - t')
      = uTarget t - uTarget t' := by
  classical
  funext b
  cases b with
  | inl s => simp [uTarget]
  | inr q => simp [uTarget]

omit [DecidableEq K] [DecidableEq R] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype R]
    [Fintype ι] [Fintype σ] in
/-- Real scaling of the target vector is complex scaling of its
embedding. -/
lemma uTarget_realSmul (r : ℝ) (t : Option R → ℝ) :
    uTarget (ι := ι) (σ := σ) (K := K) (r • t)
      = ((r : ℝ) : ℂ) • uTarget t := by
  classical
  funext b
  cases b with
  | inl s => simp [uTarget]
  | inr q => simp [uTarget]

/-- A real vector placed in the packet block `p`, zero elsewhere.  Every
block carries its own flag coordinate, which is what keeps distinct blocks
orthogonal. -/
def blockVec (p : ι × K) (w : Option σ → ℝ) : UBasis R ι σ K → ℂ :=
  Sum.elim (fun _ => 0) fun q => if q.1 = p then ((w q.2 : ℝ) : ℂ) else 0

omit [DecidableEq R] [DecidableEq σ] in
/-- **The one computation the packet layer needs**: blocks are orthogonal,
and inside a block the pairing is the real one. -/
theorem qInner_blockVec (p p' : ι × K) (w w' : Option σ → ℝ) :
    qInner (blockVec (R := R) p w) (blockVec p' w')
      = if p = p' then ((w ⬝ᵥ w' : ℝ) : ℂ) else 0 := by
  classical
  rw [qInner_def, Fintype.sum_sum_type]
  have hL : (∑ s : Option R, star (blockVec (R := R) p w (Sum.inl s))
      * blockVec (R := R) p' w' (Sum.inl s)) = 0 := by
    simp [blockVec]
  rw [hL, zero_add, Fintype.sum_prod_type]
  by_cases hb : p = p'
  · subst hb
    rw [ite_eq_left rfl]
    have hterm : ∀ r : ι × K, (∑ s : Option σ,
          star (blockVec (R := R) p w (Sum.inr (r, s)))
            * blockVec (R := R) p w' (Sum.inr (r, s)))
        = if r = p then ((w ⬝ᵥ w' : ℝ) : ℂ) else 0 := by
      intro r
      by_cases hr : r = p
      · rw [ite_eq_left hr]
        have hs : ∀ s : Option σ,
            star (blockVec (R := R) p w (Sum.inr (r, s)))
              * blockVec (R := R) p w' (Sum.inr (r, s))
            = ((w s * w' s : ℝ) : ℂ) := by
          intro s
          simp only [blockVec, Sum.elim_inr, ite_eq_left hr]
          rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
        rw [Finset.sum_congr rfl fun s _ => hs s, ← Complex.ofReal_sum,
          ← dotProduct]
      · rw [ite_eq_right hr]
        refine Finset.sum_eq_zero fun s _ => ?_
        simp only [blockVec, Sum.elim_inr, ite_eq_right hr]
        simp
    rw [Finset.sum_congr rfl fun r _ => hterm r,
      Finset.sum_ite_eq' Finset.univ p (fun _ => ((w ⬝ᵥ w' : ℝ) : ℂ)),
      ite_eq_left (Finset.mem_univ _)]
  · rw [ite_eq_right hb]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    simp only [blockVec, Sum.elim_inr]
    by_cases hr : r = p
    · rw [ite_eq_left hr, ite_eq_right (fun h => hb (hr.symm.trans h))]
      simp
    · rw [ite_eq_right hr]
      simp

/-- `idleFlag_{i,k} + answer_{i,k,a}`: the oracle image of the tagged
generator `g_{i,k} = idleFlag_{i,k} + activeBlank_{i,k}`. -/
def leftAtom (i : ι) (k : K) (a : σ) : UBasis R ι σ K → ℂ :=
  blockVec (i, k) (uniformLeft a)

/-- `idleFlag_{i,k} − answer_{i,k,a}`. -/
def rightAtom (i : ι) (k : K) (a : σ) : UBasis R ι σ K → ℂ :=
  blockVec (i, k) (uniformRight a)

omit [DecidableEq R] in
/-- **The blockwise factorization**: distinct blocks are orthogonal, and
inside a block the pairing is the inequality indicator. -/
theorem qInner_leftAtom_rightAtom (i : ι) (k : K) (a : σ) (j : ι) (l : K)
    (b : σ) :
    qInner (leftAtom (R := R) i k a) (rightAtom j l b)
      = if (i, k) = (j, l) then (if a = b then 0 else 1) else 0 := by
  classical
  rw [leftAtom, rightAtom, qInner_blockVec, uniform_dotProduct]
  by_cases hb : (i, k) = (j, l)
  · rw [ite_eq_left hb, ite_eq_left hb]
    by_cases hab : a = b <;> simp [hab]
  · rw [ite_eq_right hb, ite_eq_right hb]

omit [DecidableEq R] in
/-- **Each atom has squared norm `2`** — independently of the alphabet. -/
theorem qInner_leftAtom_self (i : ι) (k : K) (a : σ) :
    qInner (leftAtom (R := R) i k a) (leftAtom i k a) = 2 := by
  classical
  rw [leftAtom, qInner_blockVec, ite_eq_left rfl, uniformLeft_normSq]
  norm_num

omit [DecidableEq R] in
theorem qInner_rightAtom_self (i : ι) (k : K) (a : σ) :
    qInner (rightAtom (R := R) i k a) (rightAtom i k a) = 2 := by
  classical
  rw [rightAtom, qInner_blockVec, ite_eq_left rfl, uniformRight_normSq]
  norm_num

omit [DecidableEq R] [DecidableEq σ] in
/-- **Targets and packets never interfere**: they sit in complementary
summands. -/
@[simp] theorem qInner_uTarget_blockVec (t : Option R → ℝ) (p : ι × K)
    (w : Option σ → ℝ) :
    qInner (uTarget (ι := ι) (σ := σ) (K := K) t) (blockVec p w) = 0 := by
  classical
  rw [qInner_def, Fintype.sum_sum_type]
  simp [uTarget, blockVec]

omit [DecidableEq R] [DecidableEq σ] in
@[simp] theorem qInner_blockVec_uTarget (p : ι × K) (w : Option σ → ℝ)
    (t : Option R → ℝ) :
    qInner (blockVec (R := R) p w) (uTarget t) = 0 := by
  classical
  rw [qInner_def, Fintype.sum_sum_type]
  simp [uTarget, blockVec]

end Packets

/-! ## The packets of a dual solution

`U_x` and `V_x` are the two dual families spent against the tagged atoms —
`u` on the left (oracle images), `v` on the right — *without* swapping the
families.  One bilinear computation (`qInner_sum_blockVec`) serves both the
cross pairing and the norms, exactly as `qInner_blockVec` served the atoms. -/

section Packets2

variable {R ι σ K X : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]
  [Fintype X]

omit [DecidableEq R] [DecidableEq σ] in
/-- **The one bilinear computation of the packet layer.**  Block-diagonal by
construction, so only the diagonal survives. -/
theorem qInner_sum_blockVec (c d : ι × K → ℝ) (w w' : ι × K → Option σ → ℝ) :
    qInner (∑ p : ι × K, ((c p : ℝ) : ℂ) • blockVec (R := R) p (w p))
        (∑ p : ι × K, ((d p : ℝ) : ℂ) • blockVec (R := R) p (w' p))
      = ((∑ p : ι × K, c p * d p * (w p ⬝ᵥ w' p) : ℝ) : ℂ) := by
  classical
  rw [qInner_sum_left]
  have hrow : ∀ p : ι × K,
      qInner (((c p : ℝ) : ℂ) • blockVec (R := R) p (w p))
          (∑ q : ι × K, ((d q : ℝ) : ℂ) • blockVec (R := R) q (w' q))
        = ((c p * d p * (w p ⬝ᵥ w' p) : ℝ) : ℂ) := by
    intro p
    rw [qInner_smul_left, qInner_sum_right]
    have hin : ∀ q : ι × K,
        qInner (blockVec (R := R) p (w p)) (((d q : ℝ) : ℂ) • blockVec q (w' q))
          = if q = p then ((d p * (w p ⬝ᵥ w' p) : ℝ) : ℂ) else 0 := by
      intro q
      rw [qInner_smul_right, qInner_blockVec]
      by_cases hq : p = q
      · rw [ite_eq_left hq, ite_eq_left hq.symm, ← hq]
        push_cast
        ring
      · rw [ite_eq_right hq, ite_eq_right (fun h => hq h.symm)]
        ring
    rw [Finset.sum_congr rfl fun q _ => hin q,
      Finset.sum_ite_eq' Finset.univ p
        (fun _ => ((d p * (w p ⬝ᵥ w' p) : ℝ) : ℂ)),
      ite_eq_left (Finset.mem_univ _), Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun p _ => hrow p, ← Complex.ofReal_sum]

/-- The left packet: the `u`-family against the oracle images. -/
noncomputable def packetU (u : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    UBasis R ι σ K → ℂ :=
  ∑ p : ι × K, ((u x p.1 p.2 : ℝ) : ℂ) • blockVec p (uniformLeft (read x p.1))

/-- The right packet: the `v`-family against the flipped atoms. -/
noncomputable def packetV (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    UBasis R ι σ K → ℂ :=
  ∑ p : ι × K, ((v x p.1 p.2 : ℝ) : ℂ) • blockVec p (uniformRight (read x p.1))

omit [DecidableEq R] [Fintype X] in
/-- **The cross pairing is the dual constraint's left-hand side**, verbatim
and with the families unswapped. -/
theorem qInner_packetU_packetV (u v : X → ι → K → ℝ) (read : X → ι → σ)
    (y x : X) :
    qInner (packetU (R := R) u read y) (packetV v read x)
      = ((∑ i, if read y i = read x i then 0
            else ∑ k, u y i k * v x i k : ℝ) : ℂ) := by
  classical
  rw [packetU, packetV, qInner_sum_blockVec]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : read y i = read x i
  · rw [ite_eq_left hi]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [uniform_dotProduct, ite_eq_left hi]
    ring
  · rw [ite_eq_right hi]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [uniform_dotProduct, ite_eq_right hi]
    ring

omit [DecidableEq R] in
/-- The same, evaluated on a feasible dual solution: the packets realise the
inequality indicator of the **outputs**. -/
theorem qInner_packetU_packetV_of_dualPairOn {O : Type} [DecidableEq O]
    {read : X → ι → σ} {f : X → O} (P : DualPairOn read K f) (y x : X) :
    qInner (packetU (R := R) P.u read y) (packetV P.v read x)
      = if f y = f x then 0 else 1 := by
  classical
  rw [qInner_packetU_packetV, P.constraint y x]
  by_cases h : f y = f x <;> simp [h]

omit [DecidableEq R] [Fintype X] in
/-- **The exact norms**: `‖U_x‖² = 2·∑ u²`, no alphabet anywhere. -/
theorem qInner_packetU_self (u : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (packetU (R := R) u read x) (packetU u read x)
      = ((2 * ∑ p : ι × K, u x p.1 p.2 * u x p.1 p.2 : ℝ) : ℂ) := by
  classical
  rw [packetU, qInner_sum_blockVec]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [uniformLeft_normSq]
  ring

omit [DecidableEq R] [Fintype X] in
theorem qInner_packetV_self (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (packetV (R := R) v read x) (packetV v read x)
      = ((2 * ∑ p : ι × K, v x p.1 p.2 * v x p.1 p.2 : ℝ) : ℂ) := by
  classical
  rw [packetV, qInner_sum_blockVec]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [uniformRight_normSq]
  ring

omit [DecidableEq R] [Fintype X] in
/-- Targets never meet packets. -/
@[simp] theorem qInner_uTarget_packetU (t : Option R → ℝ)
    (u : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (uTarget (ι := ι) (σ := σ) (K := K) t) (packetU u read x) = 0 := by
  classical
  rw [packetU, qInner_sum_right]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [qInner_smul_right, qInner_uTarget_blockVec, mul_zero]

omit [DecidableEq R] [Fintype X] in
@[simp] theorem qInner_uTarget_packetV (t : Option R → ℝ)
    (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (uTarget (ι := ι) (σ := σ) (K := K) t) (packetV v read x) = 0 := by
  classical
  rw [packetV, qInner_sum_right]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [qInner_smul_right, qInner_uTarget_blockVec, mul_zero]

omit [DecidableEq R] [Fintype X] in
@[simp] theorem qInner_packetU_uTarget (u : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) (t : Option R → ℝ) :
    qInner (packetU (R := R) u read x) (uTarget t) = 0 := by
  classical
  rw [packetU, qInner_sum_left]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [qInner_smul_left, qInner_blockVec_uTarget, mul_zero]

end Packets2

/-! ## Two convenience pairings

`qInner_uTarget_uTarget` transfers every target norm and overlap from the
real computation of the first section without repeating the real-to-complex
step; `qInner_packetV_uTarget` makes the `‖φ‖²` expansion symmetric. -/

section TargetPairings

variable {R ι σ K X : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]
  [Fintype X]

omit [DecidableEq K] [DecidableEq R] [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem qInner_uTarget_uTarget (t t' : Option R → ℝ) :
    qInner (uTarget (ι := ι) (σ := σ) (K := K) t) (uTarget t')
      = ((t ⬝ᵥ t' : ℝ) : ℂ) := by
  classical
  rw [qInner_def, Fintype.sum_sum_type]
  have hR : (∑ p : (ι × K) × Option σ,
      star (uTarget (R := R) (ι := ι) (σ := σ) (K := K) t
          ((Sum.inr p : UBasis R ι σ K)))
        * uTarget (ι := ι) (σ := σ) (K := K) t' (Sum.inr p)) = 0 := by
    simp [uTarget]
  rw [hR, add_zero]
  have hL : ∀ s : Option R,
      star (uTarget (R := R) (ι := ι) (σ := σ) (K := K) t
          ((Sum.inl s : UBasis R ι σ K)))
        * uTarget (ι := ι) (σ := σ) (K := K) t' (Sum.inl s)
        = ((t s * t' s : ℝ) : ℂ) := by
    intro s
    simp only [uTarget, Sum.elim_inl]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [Finset.sum_congr rfl fun s _ => hL s, ← Complex.ofReal_sum, ← dotProduct]

omit [DecidableEq R] [Fintype X] in
@[simp] theorem qInner_packetV_uTarget (v : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) (t : Option R → ℝ) :
    qInner (packetV (R := R) v read x) (uTarget t) = 0 := by
  classical
  rw [packetV, qInner_sum_left]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [qInner_smul_left, qInner_blockVec_uTarget, mul_zero]

end TargetPairings

/-! ## Operational realization

`UBasis` is an abstract Hilbert basis: it cannot be handed to `oracleMat` or
`inputProj`, which live on `QBasis`.  The realization places it inside a
genuine query basis whose workspace is

    UWork R ι K = Option R ⊕ (ι × K)

— the target register, or the name of a packet block — by

    target s            ↦ (none,   none,   Sum.inl s)
    block (i,k), ⊥      ↦ (none,   none,   Sum.inr (i,k))
    block (i,k), some a ↦ (some i, some a, Sum.inr (i,k))

so a block's flag coordinate is *idle* (no index queried) and its answer
coordinates are *active at the block's own index*.  That is exactly what
makes the oracle carry the physical generator

    gen (i,k) = |⊥, ⊥, (i,k)⟩ + |i, ⊥, (i,k)⟩

onto the `leftAtom` packet: the second summand is the active-blank register,
which the transposition oracle fills with `some (a i)`.

The embedding is injective but not surjective; `uRealize` extends by zero,
which is why it preserves `qInner` and `qNormSq` on the nose. -/

section Realization

variable {R ι σ K : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]

/-- The workspace of the realized space: the target register, or the name of
a packet block. -/
abbrev UWork (R ι K : Type) : Type := Option R ⊕ (ι × K)

instance instUWorkDecidableEq {R ι K : Type} [DecidableEq R] [DecidableEq ι]
    [DecidableEq K] : DecidableEq (UWork R ι K) :=
  inferInstanceAs (DecidableEq (Option R ⊕ (ι × K)))

instance instUWorkFintype {R ι K : Type} [Fintype R] [Fintype ι] [Fintype K] :
    Fintype (UWork R ι K) :=
  inferInstanceAs (Fintype (Option R ⊕ (ι × K)))

/-- The realized query basis. -/
abbrev UQBasis (R ι σ K : Type) : Type := QBasis ι σ (UWork R ι K)

/-- The realization: place an abstract vector in the query basis, extending
by zero off the embedded coordinates. -/
@[expose]
def uRealize (ψ : UBasis R ι σ K → ℂ) : UQBasis R ι σ K → ℂ := fun q =>
  match q with
  | (none, none, Sum.inl s) => ψ (Sum.inl s)
  | (none, none, Sum.inr p) => ψ (Sum.inr (p, none))
  | (some i, some a, Sum.inr p) =>
      if p.1 = i then ψ (Sum.inr (p, some a)) else 0
  | _ => 0

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
@[simp] lemma uRealize_target (ψ : UBasis R ι σ K → ℂ) (s : Option R) :
    uRealize ψ ((none, none, Sum.inl s) : UQBasis R ι σ K) = ψ (Sum.inl s) :=
  rfl

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
@[simp] lemma uRealize_flag (ψ : UBasis R ι σ K → ℂ) (p : ι × K) :
    uRealize ψ ((none, none, Sum.inr p) : UQBasis R ι σ K)
      = ψ (Sum.inr (p, none)) := rfl

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
@[simp] lemma uRealize_answer (ψ : UBasis R ι σ K → ℂ) (i : ι) (a : σ)
    (p : ι × K) :
    uRealize ψ ((some i, some a, Sum.inr p) : UQBasis R ι σ K)
      = if p.1 = i then ψ (Sum.inr (p, some a)) else 0 := rfl

/-- The embedding itself, as a function.  **Its image is not
oracle-invariant**: the oracle swaps a realized answer coordinate with the
*active-blank* coordinate `(some i, none, Sum.inr (i,k))`, which is
deliberately outside the image.  So there is no general theorem
`oracleMat a *ᵥ uRealize ψ = uRealize (…)` — that statement is false, and
only the generator-specific identities below hold. -/
def uEmb : UBasis R ι σ K → UQBasis R ι σ K
  | Sum.inl s => (none, none, Sum.inl s)
  | Sum.inr (p, none) => (none, none, Sum.inr p)
  | Sum.inr (p, some a) => (some p.1, some a, Sum.inr p)

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
@[simp] lemma uRealize_uEmb (ψ : UBasis R ι σ K → ℂ) (b : UBasis R ι σ K) :
    uRealize ψ (uEmb b) = ψ b := by
  obtain (s | ⟨p, a⟩) := b
  · rfl
  · cases a
    · rfl
    · change (if p.1 = p.1 then _ else _) = _
      rw [ite_eq_left rfl]

omit [DecidableEq K] [DecidableEq R] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype R]
    [Fintype ι] [Fintype σ] in
lemma uEmb_injective : Function.Injective (uEmb (R := R) (ι := ι) (σ := σ)
    (K := K)) := by
  classical
  rintro (s | ⟨p, a⟩) (s' | ⟨p', a'⟩) h
  · exact congrArg Sum.inl (by simpa [uEmb] using h)
  · cases a' <;> simp [uEmb] at h
  · cases a <;> simp [uEmb] at h
  · cases a <;> cases a' <;> simp [uEmb] at h ⊢ <;> tauto

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
/-- Off the image the realization vanishes — which is what makes it an
isometry. -/
lemma uRealize_eq_zero_of_forall_ne (ψ : UBasis R ι σ K → ℂ)
    {q : UQBasis R ι σ K} (h : ∀ b, uEmb b ≠ q) : uRealize ψ q = 0 := by
  classical
  by_contra hne
  obtain ⟨i, a, w⟩ := q
  cases i with
  | none =>
      cases a with
      | none =>
          cases w with
          | inl s => exact h (Sum.inl s) rfl
          | inr p => exact h (Sum.inr (p, none)) rfl
      | some a => exact hne rfl
  | some i =>
      cases a with
      | none => exact hne rfl
      | some a =>
          cases w with
          | inl s => exact hne rfl
          | inr p =>
              by_cases hp : p.1 = i
              · refine h (Sum.inr (p, some a)) ?_
                rw [uEmb, hp]
              · exact hne (by rw [uRealize_answer, ite_eq_right hp])

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] in
/-- **The master isometry.** -/
theorem qInner_uRealize (ψ φ : UBasis R ι σ K → ℂ) :
    qInner (uRealize ψ) (uRealize φ) = qInner ψ φ := by
  classical
  rw [qInner_def, qInner_def]
  have hsub : (∑ q : UQBasis R ι σ K, star (uRealize ψ q) * uRealize φ q)
      = ∑ q ∈ Finset.univ.image (uEmb (R := R) (ι := ι) (σ := σ) (K := K)),
          star (uRealize ψ q) * uRealize φ q := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro q _ hq
    rw [uRealize_eq_zero_of_forall_ne ψ (fun b hb => hq (by
      rw [Finset.mem_image]
      exact ⟨b, Finset.mem_univ b, hb⟩))]
    simp
  rw [hsub, Finset.sum_image fun b _ b' _ hbb => uEmb_injective hbb]
  exact Finset.sum_congr rfl fun b _ => by rw [uRealize_uEmb, uRealize_uEmb]

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] in
theorem qNormSq_uRealize (ψ : UBasis R ι σ K → ℂ) :
    qNormSq (uRealize ψ) = qNormSq ψ := by
  classical
  have h := qInner_uRealize ψ ψ
  rw [qInner_self, qInner_self] at h
  exact_mod_cast h

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
@[simp] lemma uRealize_zero :
    uRealize (0 : UBasis R ι σ K → ℂ) = 0 := by
  funext q
  obtain ⟨i, a, w⟩ := q
  cases i <;> cases a <;> cases w <;>
    simp only [uRealize, Pi.zero_apply];
    first
      | rfl
      | (split_ifs <;> simp)

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
lemma uRealize_add (ψ φ : UBasis R ι σ K → ℂ) :
    uRealize (ψ + φ) = uRealize ψ + uRealize φ := by
  funext q
  obtain ⟨i, a, w⟩ := q
  cases i <;> cases a <;> cases w <;>
    simp only [uRealize, Pi.add_apply] <;>
    first
      | rfl
      | (split_ifs <;> simp)
      | simp

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
lemma uRealize_sub (ψ φ : UBasis R ι σ K → ℂ) :
    uRealize (ψ - φ) = uRealize ψ - uRealize φ := by
  funext q
  obtain ⟨i, a, w⟩ := q
  cases i <;> cases a <;> cases w <;>
    simp only [uRealize, Pi.sub_apply] <;>
    first
      | rfl
      | (split_ifs <;> simp)
      | simp

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
lemma uRealize_sum {α : Type*} (s : Finset α) (F : α → (UBasis R ι σ K → ℂ)) :
    uRealize (∑ a ∈ s, F a) = ∑ a ∈ s, uRealize (F a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [uRealize_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, uRealize_add, ih]

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] [Fintype K] [Fintype R] [Fintype ι]
    [Fintype σ] in
lemma uRealize_smul (c : ℂ) (ψ : UBasis R ι σ K → ℂ) :
    uRealize (c • ψ) = c • uRealize ψ := by
  funext q
  obtain ⟨i, a, w⟩ := q
  cases i <;> cases a <;> cases w <;>
    simp only [uRealize, Pi.smul_apply, smul_eq_mul] <;>
    first
      | rfl
      | (split_ifs <;> simp)
      | simp

end Realization

/-! ## The physical generator

    idleFlag p     = |⊥, ⊥, p⟩
    activeBlank p  = |p.1, ⊥, p⟩
    uniformGen p   = idleFlag p + activeBlank p

The oracle fixes the idle summand (no index is queried there) and fills the
active blank with `some (a p.1)`, so it carries the generator exactly onto
the realized `leftAtom` packet.  This is the **generator-specific transport
identity** the construction uses — *arbitrary* `uRealize` transport is false
(the image is not oracle-invariant, and the active-blank coordinate is
precisely the off-image coordinate the oracle uses), though linear
combinations of generator identities of course still hold. -/

section Generator

variable {R ι σ K : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]

/-- `|⊥, ⊥, p⟩` — the block's flag, idle. -/
def idleFlag (p : ι × K) : UQBasis R ι σ K → ℂ :=
  qBasis ((none, none, Sum.inr p) : UQBasis R ι σ K)

/-- `|p.1, ⊥, p⟩` — the block's blank answer register, active at its own
index.  **Outside the image of `uRealize`**, by design. -/
def activeBlank (p : ι × K) : UQBasis R ι σ K → ℂ :=
  qBasis ((some p.1, none, Sum.inr p) : UQBasis R ι σ K)

/-- The tagged generator `g_{i,k}`. -/
def uniformGen (p : ι × K) : UQBasis R ι σ K → ℂ := idleFlag p + activeBlank p

omit [Fintype K] [Fintype R] [Fintype ι] [Fintype σ] in
/-- The realized `leftAtom` is a two-term basis sum. -/
lemma uRealize_leftAtom (i : ι) (k : K) (c : σ) :
    uRealize (leftAtom (R := R) i k c)
      = qBasis ((none, none, Sum.inr (i, k)) : UQBasis R ι σ K)
        + qBasis ((some i, some c, Sum.inr (i, k)) : UQBasis R ι σ K) := by
  classical
  funext q
  obtain ⟨j, x, w⟩ := q
  cases j with
  | none =>
      cases x with
      | none =>
          cases w with
          | inl s => simp [uRealize, leftAtom, blockVec, qBasis_apply]
          | inr p =>
              by_cases hp : p = (i, k)
              · subst hp
                simp [uRealize, leftAtom, blockVec, qBasis_apply]
              · simp [uRealize, leftAtom, blockVec, qBasis_apply, hp]
      | some x => cases w <;> simp [uRealize, qBasis_apply]
  | some j =>
      cases x with
      | none => cases w <;> simp [uRealize, qBasis_apply]
      | some x =>
          cases w with
          | inl s => simp [uRealize, qBasis_apply]
          | inr p =>
              by_cases hp : p = (i, k)
              · subst hp
                by_cases hj : j = i
                · subst hj
                  by_cases hx : x = c
                  · subst hx
                    simp [uRealize, leftAtom, blockVec, qBasis_apply]
                  · simp [uRealize, leftAtom, blockVec, qBasis_apply, hx]
                · simp [uRealize, qBasis_apply, hj,
                    Ne.symm hj]
              · simp [uRealize, leftAtom, blockVec, qBasis_apply, hp]

/-- **The generator-specific transport identity.** -/
theorem oracleMat_mulVec_uniformGen (a : ι → σ) (p : ι × K) :
    oracleMat a *ᵥ uniformGen (R := R) p
      = uRealize (leftAtom p.1 p.2 (a p.1)) := by
  rw [uniformGen, Matrix.mulVec_add, idleFlag, activeBlank, oracleMat,
    qPerm_mulVec_qBasis, qPerm_mulVec_qBasis, uRealize_leftAtom,
    oraclePerm_apply, oraclePerm_apply, oracleMap_none, oracleMap_some,
    Equiv.swap_apply_left]

/-- **The scalar pullback the projector proof consumes**: testing a realized
vector against a generator, through the oracle, is testing it against the
`leftAtom` packet. -/
theorem qInner_uniformGen_oracle_uRealize (a : ι → σ) (p : ι × K)
    (ψ : UBasis R ι σ K → ℂ) :
    qInner (uniformGen p) (oracleMat a *ᵥ uRealize ψ)
      = qInner (leftAtom p.1 p.2 (a p.1)) ψ := by
  rw [← QRoutine.oracleMat_conjTranspose a, ← qInner_mulVec_left,
    oracleMat_mulVec_uniformGen, qInner_uRealize]

omit [DecidableEq R] in
/-- **The per-generator cancellation.**  `inputProj` asks orthogonality
against *each* generator separately, so the aggregate `⟪U, V⟫` identity is
not enough: this is the statement that on the *same* input the letters agree
in every block, so every term of `V_x` is killed. -/
theorem qInner_leftAtom_packetV_same {X : Type}
    (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) (i : ι) (k : K) :
    qInner (leftAtom (R := R) i k (read x i)) (packetV v read x) = 0 := by
  classical
  rw [packetV, qInner_sum_right]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [qInner_smul_right, leftAtom, qInner_blockVec]
  by_cases hq : (i, k) = q
  · rw [ite_eq_left hq, ← hq, uniform_dotProduct, ite_eq_left rfl]
    simp
  · rw [ite_eq_right hq, mul_zero]

end Generator

/-! ## The realized states, and their contracts

Named realized states, with their pairings and norms transported through the
isometry immediately — after this section nothing downstream needs to know
how the realization is built. -/

section Realized

variable {R ι σ K X : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]
  [Fintype X]

/-- A realized target state. -/
noncomputable def realizedTarget (t : Option R → ℝ) : UQBasis R ι σ K → ℂ :=
  uRealize (uTarget (ι := ι) (σ := σ) (K := K) t)

/-- The realized `u`-packet. -/
noncomputable def realizedPacketU (u : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) : UQBasis R ι σ K → ℂ :=
  uRealize (packetU (R := R) u read x)

/-- The realized `v`-packet. -/
noncomputable def realizedPacketV (v : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) : UQBasis R ι σ K → ℂ :=
  uRealize (packetV (R := R) v read x)

/-! ### Transported pairings and norms -/

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] in
@[simp] theorem qInner_realizedTarget (t t' : Option R → ℝ) :
    qInner (realizedTarget (ι := ι) (σ := σ) (K := K) t) (realizedTarget t')
      = ((t ⬝ᵥ t' : ℝ) : ℂ) := by
  classical
  rw [realizedTarget, realizedTarget, qInner_uRealize, qInner_uTarget_uTarget]

omit [DecidableEq R] [Fintype X] in
@[simp] theorem qInner_realizedTarget_realizedPacketU (t : Option R → ℝ)
    (u : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (realizedTarget (ι := ι) (σ := σ) (K := K) t)
      (realizedPacketU u read x) = 0 := by
  classical
  rw [realizedTarget, realizedPacketU, qInner_uRealize, qInner_uTarget_packetU]

omit [DecidableEq R] [Fintype X] in
@[simp] theorem qInner_realizedTarget_realizedPacketV (t : Option R → ℝ)
    (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (realizedTarget (ι := ι) (σ := σ) (K := K) t)
      (realizedPacketV v read x) = 0 := by
  classical
  rw [realizedTarget, realizedPacketV, qInner_uRealize, qInner_uTarget_packetV]

omit [DecidableEq R] [Fintype X] in
@[simp] theorem qInner_realizedPacketU_realizedTarget (u : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) (t : Option R → ℝ) :
    qInner (realizedPacketU (R := R) u read x) (realizedTarget t) = 0 := by
  classical
  rw [realizedPacketU, realizedTarget, qInner_uRealize, qInner_packetU_uTarget]

omit [DecidableEq R] [Fintype X] in
@[simp] theorem qInner_realizedPacketV_realizedTarget (v : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) (t : Option R → ℝ) :
    qInner (realizedPacketV (R := R) v read x) (realizedTarget t) = 0 := by
  classical
  rw [realizedPacketV, realizedTarget, qInner_uRealize, qInner_packetV_uTarget]

omit [DecidableEq R] in
theorem qInner_realizedPacketU_realizedPacketV
    {O : Type} [DecidableEq O] {read : X → ι → σ} {f : X → O}
    (P : DualPairOn read K f) (y x : X) :
    qInner (realizedPacketU (R := R) P.u read y) (realizedPacketV P.v read x)
      = if f y = f x then 0 else 1 := by
  classical
  rw [realizedPacketU, realizedPacketV, qInner_uRealize,
    qInner_packetU_packetV_of_dualPairOn]

omit [DecidableEq R] [Fintype X] in
theorem qInner_realizedPacketU_self (u : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qInner (realizedPacketU (R := R) u read x) (realizedPacketU u read x)
      = ((2 * ∑ p : ι × K, u x p.1 p.2 * u x p.1 p.2 : ℝ) : ℂ) := by
  classical
  rw [realizedPacketU, qInner_uRealize, qInner_packetU_self]

omit [DecidableEq R] [Fintype X] in
theorem qInner_realizedPacketV_self (v : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qInner (realizedPacketV (R := R) v read x) (realizedPacketV v read x)
      = ((2 * ∑ p : ι × K, v x p.1 p.2 * v x p.1 p.2 : ℝ) : ℂ) := by
  classical
  rw [realizedPacketV, qInner_uRealize, qInner_packetV_self]

/-! ### The operational form of the `u`-packet -/

omit [Fintype X] in
/-- **The `u`-packet is the oracle applied to a combination of generators.**
This is what puts it inside the killed space of `inputProj`. -/
theorem realizedPacketU_eq_sum_oracleGen (u : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) :
    realizedPacketU (R := R) u read x
      = oracleMat (read x)
        *ᵥ ∑ p : ι × K, ((u x p.1 p.2 : ℝ) : ℂ) • uniformGen (R := R) p := by
  classical
  rw [realizedPacketU, packetU, uRealize_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [uRealize_smul, Matrix.mulVec_smul, oracleMat_mulVec_uniformGen]
  rfl

/-! ### The projector contracts -/

omit [Fintype X] in
/-- **The `u`-packet is killed.** -/
theorem inputProj_mulVec_realizedPacketU (u : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) :
    inputProj (uniformGen (R := R) (ι := ι) (σ := σ) (K := K)) (read x)
        *ᵥ realizedPacketU u read x = 0 := by
  classical
  rw [realizedPacketU_eq_sum_oracleGen, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul,
    inputProj_mulVec_oracle_generator, smul_zero]

omit [Fintype X] in
/-- **The `v`-packet is fixed.** -/
theorem inputProj_mulVec_realizedPacketV (v : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) :
    inputProj (uniformGen (R := R) (ι := ι) (σ := σ) (K := K)) (read x)
        *ᵥ realizedPacketV v read x = realizedPacketV v read x := by
  refine inputProj_mulVec_of_forall_qInner_eq_zero _ _ fun p => ?_
  rw [realizedPacketV, qInner_uniformGen_oracle_uRealize,
    qInner_leftAtom_packetV_same]

/-- **Targets are fixed.** -/
theorem inputProj_mulVec_realizedTarget (t : Option R → ℝ) (a : ι → σ) :
    inputProj (uniformGen (R := R) (ι := ι) (σ := σ) (K := K)) a
        *ᵥ realizedTarget t = realizedTarget t := by
  refine inputProj_mulVec_of_forall_qInner_eq_zero _ _ fun p => ?_
  rw [realizedTarget, qInner_uniformGen_oracle_uRealize, leftAtom,
    qInner_blockVec_uTarget]

/-! ### Real-valued norm corollaries -/

omit [DecidableEq K] [DecidableEq R] [DecidableEq σ] in
theorem qNormSq_realizedTarget (t : Option R → ℝ) :
    qNormSq (realizedTarget (ι := ι) (σ := σ) (K := K) t) = t ⬝ᵥ t := by
  classical
  have h := qInner_realizedTarget (ι := ι) (σ := σ) (K := K) t t
  rw [qInner_self] at h
  exact_mod_cast h

omit [DecidableEq R] [Fintype X] in
theorem qNormSq_realizedPacketU (u : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qNormSq (realizedPacketU (R := R) u read x)
      = 2 * ∑ p : ι × K, u x p.1 p.2 * u x p.1 p.2 := by
  classical
  have h := qInner_realizedPacketU_self (R := R) u read x
  rw [qInner_self] at h
  exact_mod_cast h

omit [DecidableEq R] [Fintype X] in
theorem qNormSq_realizedPacketV (v : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qNormSq (realizedPacketV (R := R) v read x)
      = 2 * ∑ p : ι × K, v x p.1 p.2 * v x p.1 p.2 := by
  classical
  have h := qInner_realizedPacketV_self (R := R) v read x
  rw [qInner_self] at h
  exact_mod_cast h

end Realized

/-! ## The scaled witnesses

    φ_x = t_{x+} + α·V_x
    w_x = t_{x−} − (2α)⁻¹·U_x
    ψ_x = 2α·t_{x−} − U_x  ( = 2α·w_x when α ≠ 0)

`α : ℝ`, deliberately: a complex scaling would drag conjugation into the
cancellation.  `⟪ψ_y, φ_x⟫ = 0` holds for **every** `α`: the target term
contributes `2α · ½·[f y ≠ f x] = α·[f y ≠ f x]`, and the packet term
contributes `α · ⟪U_y, V_x⟫ = α·[f y ≠ f x]`, with opposite signs.

One **global** projector `L = spanProj (uniformPhi P α)` indexed by all
promise inputs — not one per output. -/

section Scaled

variable {ι σ K X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq O]
  {read : X → ι → σ} {f : X → O}

/-- The realized `+` target. -/
noncomputable def realizedTPlus (f : X → O) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTarget (ι := ι) (σ := σ) (K := K) (tPlus f x)

/-- The realized `−` target. -/
noncomputable def realizedTMinus (f : X → O) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTarget (ι := ι) (σ := σ) (K := K) (tMinus f x)

/-- `φ_x = t_{x+} + α·V_x`. -/
noncomputable def uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTPlus (K := K) f x + ((α : ℝ) : ℂ) • realizedPacketV P.v read x

/-- `w_x = t_{x−} − (2α)⁻¹·U_x`. -/
noncomputable def uniformW (P : DualPairOn read K f) (α : ℝ) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTMinus (K := K) f x
    - (((2 * α)⁻¹ : ℝ) : ℂ) • realizedPacketU P.u read x

/-- `ψ_x = 2α·t_{x−} − U_x`. -/
noncomputable def uniformPsi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  ((2 * α : ℝ) : ℂ) • realizedTMinus (K := K) f x - realizedPacketU P.u read x

/-- **The exact orthogonality**, for every `α`. -/
theorem qInner_uniformPsi_uniformPhi (P : DualPairOn read K f) (α : ℝ)
    (y x : X) :
    qInner (uniformPsi (K := K) P α y) (uniformPhi P α x) = 0 := by
  classical
  rw [uniformPsi, uniformPhi, qInner_sub_left, qInner_smul_left,
    qInner_add_right, qInner_add_right, qInner_smul_right, qInner_smul_right,
    realizedTMinus, realizedTPlus, qInner_realizedTarget,
    qInner_realizedTarget_realizedPacketV,
    qInner_realizedPacketU_realizedTarget,
    qInner_realizedPacketU_realizedPacketV P y x, tMinus_dotProduct_tPlus]
  by_cases hxy : f x = f y
  · rw [ite_eq_left hxy, ite_eq_left hxy.symm]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  · rw [ite_eq_right hxy, ite_eq_right (fun h => hxy h.symm)]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring

omit [Fintype σ] in
/-- `ψ = 2α·w` once `α ≠ 0`. -/
theorem uniformPsi_eq_twoAlpha_smul_uniformW (P : DualPairOn read K f)
    {α : ℝ} (hα : α ≠ 0) (x : X) :
    uniformPsi (K := K) P α x = ((2 * α : ℝ) : ℂ) • uniformW P α x := by
  have h2 : (2 * α : ℝ) ≠ 0 := by
    simp [hα]
  rw [uniformW, uniformPsi, smul_sub, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ h2]
  norm_num

/-- Hence `⟪w_y, φ_x⟫ = 0` for `α ≠ 0`. -/
theorem qInner_uniformW_uniformPhi (P : DualPairOn read K f) {α : ℝ}
    (hα : α ≠ 0) (y x : X) :
    qInner (uniformW (K := K) P α y) (uniformPhi P α x) = 0 := by
  have h2 : ((2 * α : ℝ) : ℂ) ≠ 0 := by
    simp [hα]
  have h := qInner_uniformPsi_uniformPhi (K := K) P α y x
  rw [uniformPsi_eq_twoAlpha_smul_uniformW P hα, qInner_smul_left] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (by simpa using h') h2
  · exact h'

/-- The reversed pairing, by conjugation. -/
theorem qInner_uniformPhi_uniformW (P : DualPairOn read K f) {α : ℝ}
    (hα : α ≠ 0) (y x : X) :
    qInner (uniformPhi (K := K) P α y) (uniformW P α x) = 0 := by
  have h := qInner_uniformW_uniformPhi (K := K) P hα x y
  rw [← qInner_conj, h, star_zero]

/-- **The global projector**, indexed by all promise inputs. -/
noncomputable def uniformL (P : DualPairOn read K f) (α : ℝ) :
    Matrix (UQBasis ↥(Set.range f) ι σ K) (UQBasis ↥(Set.range f) ι σ K) ℂ :=
  spanProj (uniformPhi (K := K) P α)

theorem isQProjector_uniformL (P : DualPairOn read K f) (α : ℝ) :
    IsQProjector (uniformL (K := K) P α) :=
  isQProjector_spanProj _

theorem uniformL_mulVec_uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    uniformL (K := K) P α *ᵥ uniformPhi P α x = uniformPhi P α x :=
  spanProj_mulVec_self _ x

theorem uniformL_mulVec_uniformW (P : DualPairOn read K f) {α : ℝ}
    (hα : α ≠ 0) (x : X) :
    uniformL (K := K) P α *ᵥ uniformW P α x = 0 := by
  refine subProj_mulVec_of_mem_orthogonal _ ?_
  exact (mem_rawSpan_orthogonal_iff _ _).mpr fun y =>
    qInner_uniformPhi_uniformW P hα y x

/-! ### The exact norms

Orthogonality of target and packet makes both a Pythagorean sum. -/

private lemma qNormSq_add_real_smul_of_orthogonal {H : Type} [Fintype H]
     (A B : H → ℂ) (r : ℝ) (h1 : qInner A B = 0)
    (h2 : qInner B A = 0) :
    qNormSq (A + ((r : ℝ) : ℂ) • B) = qNormSq A + r ^ 2 * qNormSq B := by
  classical
  have h : qInner (A + ((r : ℝ) : ℂ) • B) (A + ((r : ℝ) : ℂ) • B)
      = qInner A A + ((r ^ 2 : ℝ) : ℂ) * qInner B B := by
    rw [qInner_add_left, qInner_add_right, qInner_add_right, qInner_smul_left,
      qInner_smul_right, qInner_smul_left, qInner_smul_right, h1, h2]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [qInner_self, qInner_self, qInner_self] at h
  exact_mod_cast h

/-- `‖φ_x‖² = 1 + 2α²·(the `v`-mass)` — no hypothesis on `α`. -/
theorem qNormSq_uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    qNormSq (uniformPhi (K := K) P α x)
      = 1 + 2 * α ^ 2 * ∑ p : ι × K, P.v x p.1 p.2 * P.v x p.1 p.2 := by
  rw [uniformPhi, realizedTPlus, qNormSq_add_real_smul_of_orthogonal _ _ _
      (qInner_realizedTarget_realizedPacketV _ _ _ _)
      (qInner_realizedPacketV_realizedTarget _ _ _ _),
    qNormSq_realizedTarget, tPlus_normSq, qNormSq_realizedPacketV]
  ring

theorem qNormSq_uniformPhi_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) (α : ℝ) (x : X) :
    qNormSq (uniformPhi (K := K) P α x) ≤ 1 + 2 * α ^ 2 * c := by
  rw [qNormSq_uniformPhi]
  have hmass : (∑ p : ι × K, P.v x p.1 p.2 * P.v x p.1 p.2) ≤ c := by
    simpa only [Fintype.sum_prod_type] using hP.2 x
  nlinarith [sq_nonneg α]

/-- `‖w_x‖² = 1 + (2α)⁻²·2·(the `u`-mass)` — valid for **every** `α`
(at `α = 0` the inverse is `0`, so this reads `‖w‖² = 1`). -/
theorem qNormSq_uniformW (P : DualPairOn read K f) (α : ℝ) (x : X) :
    qNormSq (uniformW (K := K) P α x)
      = 1 + ((2 * α)⁻¹) ^ 2
        * (2 * ∑ p : ι × K, P.u x p.1 p.2 * P.u x p.1 p.2) := by
  rw [uniformW, realizedTMinus, sub_eq_add_neg, ← neg_smul,
    ← Complex.ofReal_neg,
    qNormSq_add_real_smul_of_orthogonal _ _ _
      (qInner_realizedTarget_realizedPacketU _ _ _ _)
      (qInner_realizedPacketU_realizedTarget _ _ _ _),
    qNormSq_realizedTarget, tMinus_normSq, qNormSq_realizedPacketU, neg_sq]

/-- The displayed form, for `α ≠ 0`. -/
theorem qNormSq_uniformW_of_ne_zero (P : DualPairOn read K f) {α : ℝ}
    (hα : α ≠ 0) (x : X) :
    qNormSq (uniformW (K := K) P α x)
      = 1 + (∑ p : ι × K, P.u x p.1 p.2 * P.u x p.1 p.2) / (2 * α ^ 2) := by
  rw [qNormSq_uniformW]
  have h2 : (2 * α) ^ 2 = 4 * α ^ 2 := by ring
  have hne : (α : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hα
  field_simp [h2]

theorem qNormSq_uniformW_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) {α : ℝ} (hα : α ≠ 0) (x : X) :
    qNormSq (uniformW (K := K) P α x) ≤ 1 + c / (2 * α ^ 2) := by
  rw [qNormSq_uniformW_of_ne_zero P hα]
  have hmass : (∑ p : ι × K, P.u x p.1 p.2 * P.u x p.1 p.2) ≤ c := by
    simpa only [Fintype.sum_prod_type] using hP.1 x
  have hpos : (0 : ℝ) < 2 * α ^ 2 := by positivity
  gcongr

/-! ### The input-projector contracts -/

theorem inputProj_mulVec_uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    inputProj (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
        (read x) *ᵥ uniformPhi P α x = uniformPhi P α x := by
  rw [uniformPhi, Matrix.mulVec_add, Matrix.mulVec_smul, realizedTPlus,
    inputProj_mulVec_realizedTarget, inputProj_mulVec_realizedPacketV]

theorem inputProj_mulVec_uniformW (P : DualPairOn read K f) (α : ℝ) (x : X) :
    inputProj (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
        (read x) *ᵥ uniformW P α x = realizedTMinus f x := by
  rw [uniformW, Matrix.mulVec_sub, Matrix.mulVec_smul, realizedTMinus,
    inputProj_mulVec_realizedTarget, inputProj_mulVec_realizedPacketU,
    smul_zero, sub_zero]

/-- **`φ` is a positive witness.** -/
theorem isPosWitness_uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    IsPosWitness (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
      (uniformL P α) (read x) (uniformPhi P α x) :=
  ⟨inputProj_mulVec_uniformPhi P α x, uniformL_mulVec_uniformPhi P α x⟩

/-! ### Realized-target wrappers -/

omit [DecidableEq K] [DecidableEq σ] in
@[simp] theorem qNormSq_realizedTPlus (f : X → O) (x : X) :
    qNormSq (realizedTPlus (ι := ι) (σ := σ) (K := K) f x) = 1 := by
  classical
  rw [realizedTPlus, qNormSq_realizedTarget, tPlus_normSq]

omit [DecidableEq K] [DecidableEq σ] in
@[simp] theorem qNormSq_realizedTMinus (f : X → O) (x : X) :
    qNormSq (realizedTMinus (ι := ι) (σ := σ) (K := K) f x) = 1 := by
  classical
  rw [realizedTMinus, qNormSq_realizedTarget, tMinus_normSq]

omit [DecidableEq K] [DecidableEq σ] in
/-- `t₊ ⟂ t₋` on matching outputs — in particular for the same input. -/
theorem qInner_realizedTPlus_realizedTMinus (f : X → O) (x y : X) :
    qInner (realizedTPlus (ι := ι) (σ := σ) (K := K) f x) (realizedTMinus f y)
      = if f x = f y then 0 else ((1 / 2 : ℝ) : ℂ) := by
  classical
  rw [realizedTPlus, realizedTMinus, qInner_realizedTarget,
    tPlus_dotProduct_tMinus]
  by_cases hxy : f x = f y <;> simp [hxy]

omit [DecidableEq K] [DecidableEq σ] in
theorem qInner_realizedTMinus_realizedTPlus (f : X → O) (x y : X) :
    qInner (realizedTMinus (ι := ι) (σ := σ) (K := K) f x) (realizedTPlus f y)
      = if f y = f x then 0 else ((1 / 2 : ℝ) : ℂ) := by
  classical
  rw [realizedTMinus, realizedTPlus, qInner_realizedTarget,
    tMinus_dotProduct_tPlus]
  by_cases hxy : f y = f x <;> simp [hxy]

omit [DecidableEq K] [DecidableEq σ] in
@[simp] theorem qInner_realizedTPlus_realizedTMinus_self (f : X → O) (x : X) :
    qInner (realizedTPlus (ι := ι) (σ := σ) (K := K) f x) (realizedTMinus f x)
      = 0 := by
  classical
  rw [qInner_realizedTPlus_realizedTMinus, ite_eq_left rfl]

omit [DecidableEq K] [DecidableEq σ] in
@[simp] theorem qInner_realizedTMinus_realizedTPlus_self (f : X → O) (x : X) :
    qInner (realizedTMinus (ι := ι) (σ := σ) (K := K) f x) (realizedTPlus f x)
      = 0 := by
  classical
  rw [qInner_realizedTMinus_realizedTPlus, ite_eq_left rfl]

/-- The target overlap the readout reads: `⟪t_{x+}, φ_x⟫ = 1`. -/
theorem qInner_realizedTPlus_uniformPhi (P : DualPairOn read K f) (α : ℝ)
    (x : X) :
    qInner (realizedTPlus (K := K) f x) (uniformPhi P α x) = 1 := by
  rw [uniformPhi, qInner_add_right, qInner_smul_right, realizedTPlus,
    qInner_realizedTarget, qInner_realizedTarget_realizedPacketV,
    tPlus_normSq]
  norm_num

/-! ### The common and output states, realized

The conversion's initial state is input-independent; its target is labelled
by the output alone.  Both are unit vectors, and distinct outputs give
orthogonal targets — the coherent readout geometry, with no cardinality of
`O` anywhere. -/

/-- The realized common initial state. -/
noncomputable def realizedCommon (f : X → O) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTarget (ι := ι) (σ := σ) (K := K)
    (commonVec (R := ↥(Set.range f)))

/-- The realized output-labelled target state. -/
noncomputable def realizedOut (f : X → O) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTarget (ι := ι) (σ := σ) (K := K) (outVec (rangeElem f x))

omit [DecidableEq K] [DecidableEq σ] [Fintype K] [Fintype X] [Fintype ι] [Fintype σ] in
/-- `common = (t₊ + t₋)/√2`, realized — for **every** `x`. -/
theorem realizedCommon_eq_smul (f : X → O) (x : X) :
    realizedCommon (ι := ι) (σ := σ) (K := K) f
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          (realizedTPlus (K := K) f x + realizedTMinus (K := K) f x) := by
  classical
  have h : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (realizedTPlus (K := K) f x + realizedTMinus (K := K) f x)
      = realizedCommon (ι := ι) (σ := σ) (K := K) f := by
    rw [realizedTPlus, realizedTMinus, realizedTarget, realizedTarget,
      ← uRealize_add, ← uTarget_add, ← uRealize_smul, ← uTarget_realSmul,
      smul_tPlus_add_tMinus f x, realizedCommon, realizedTarget]
  exact h.symm

omit [DecidableEq K] [DecidableEq σ] [Fintype K] [Fintype X] [Fintype ι] [Fintype σ] in
/-- `out(f x) = (t₊ − t₋)/√2`, realized. -/
theorem realizedOut_eq_smul (f : X → O) (x : X) :
    realizedOut (ι := ι) (σ := σ) (K := K) f x
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          (realizedTPlus (K := K) f x - realizedTMinus (K := K) f x) := by
  classical
  have h : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (realizedTPlus (K := K) f x - realizedTMinus (K := K) f x)
      = realizedOut (ι := ι) (σ := σ) (K := K) f x := by
    rw [realizedTPlus, realizedTMinus, realizedTarget, realizedTarget,
      ← uRealize_sub, ← uTarget_sub, ← uRealize_smul, ← uTarget_realSmul,
      smul_tPlus_sub_tMinus f x, realizedOut, realizedTarget]
  exact h.symm

omit [DecidableEq K] [DecidableEq σ] in
@[simp] theorem qNormSq_realizedCommon (f : X → O) :
    qNormSq (realizedCommon (ι := ι) (σ := σ) (K := K) f) = 1 := by
  classical
  rw [realizedCommon, qNormSq_realizedTarget, commonVec_dotProduct_commonVec]

omit [DecidableEq K] [DecidableEq σ] in
@[simp] theorem qNormSq_realizedOut (f : X → O) (x : X) :
    qNormSq (realizedOut (ι := ι) (σ := σ) (K := K) f x) = 1 := by
  classical
  rw [realizedOut, qNormSq_realizedTarget, outVec_dotProduct_outVec,
    ite_eq_left rfl]

omit [DecidableEq K] [DecidableEq σ] in
/-- **The output states are labelled by the output**: the overlap is the
equality indicator, which is what the final readout measures. -/
theorem qInner_realizedOut_realizedOut (f : X → O) (x y : X) :
    qInner (realizedOut (ι := ι) (σ := σ) (K := K) f x) (realizedOut f y)
      = if f x = f y then 1 else 0 := by
  classical
  rw [realizedOut, realizedOut, qInner_realizedTarget,
    outVec_dotProduct_outVec]
  by_cases h : f x = f y
  · rw [ite_eq_left ((rangeElem_eq_iff f x y).mpr h), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (fun hc => h ((rangeElem_eq_iff f x y).mp hc)), ite_eq_right h]
    norm_num

omit [DecidableEq K] [DecidableEq σ] in
@[simp] theorem qInner_realizedCommon_realizedOut (f : X → O) (x : X) :
    qInner (realizedCommon (ι := ι) (σ := σ) (K := K) f)
      (realizedOut f x) = 0 := by
  classical
  rw [realizedCommon, realizedOut, qInner_realizedTarget,
    commonVec_dotProduct_outVec, Complex.ofReal_zero]

omit [DecidableEq K] [DecidableEq σ] in
@[simp] theorem qInner_realizedOut_realizedCommon (f : X → O) (x : X) :
    qInner (realizedOut (ι := ι) (σ := σ) (K := K) f x)
      (realizedCommon f) = 0 := by
  classical
  rw [realizedCommon, realizedOut, qInner_realizedTarget,
    outVec_dotProduct_commonVec, Complex.ofReal_zero]

omit [DecidableEq K] [DecidableEq σ] [Fintype K] [Fintype X] [Fintype ι] [Fintype σ] in
/-- **The output state is supported on its own label**: off the target
coordinate `(⊥, ⊥, inl (some (f x)))` the realized output state vanishes.
This is exactly what the final readout consumes. -/
theorem realizedOut_apply_of_ne (f : X → O) (x : X)
    {q : UQBasis ↥(Set.range f) ι σ K}
    (hq : q.2.2 ≠ Sum.inl (some (rangeElem f x))) :
    realizedOut (ι := ι) (σ := σ) (K := K) f x q = 0 := by
  classical
  obtain ⟨i, a, w⟩ := q
  rw [realizedOut, realizedTarget]
  cases i with
  | none =>
    cases a with
    | none =>
      cases w with
      | inl s =>
        rw [uRealize_target]
        have hs : s ≠ some (rangeElem f x) := fun h => hq (by rw [h])
        cases s with
        | none => simp [uTarget]
        | some t =>
          have ht : t ≠ rangeElem f x := fun h => hs (by rw [h])
          simp [uTarget, ht]
      | inr p => rfl
    | some a => cases w <;> rfl
  | some i =>
    cases a with
    | none => cases w <;> rfl
    | some a =>
      cases w with
      | inl s => rfl
      | inr p => simp [uRealize_answer, uTarget]

end Scaled

end QuantumQueryComplexity

end SourceQuantumUniformWitness

section SourceQuantumWitness

/-!
# The witness states, built from a dual adversary solution

From a `DualPairOn read K f` this section constructs the
generators, the fixed subspace, and both witness families, and discharges the
`IsPosWitness` contracts from the dual's feasibility identity.

## The layout

The workspace is `Option K`: the dual's register, plus a slot `none` used as a
flag.  Three kinds of basis point matter, and the oracle is what separates them:

    τ         = (none, none, none)              the target, in the idle sector
    b i k     = (some i, none, some k)          blank answer — the generators
    e i s k   = (some i, some s, some k)        the answer register holds `s`

The **generators are the blank-answer states** `b i k`.  That single choice is
what makes the whole construction work, because the transposition oracle sends

    O_x (b i k) = e i (read x i) k,

so `span {O_x · gen}` is the span of the *true-answer* states of `x` — the
input-dependent subspace, produced by conjugation rather than by fiat.  By
`inputProj_mulVec_eq_self_iff`, a state is fixed by `inputProj gen (read x)`
exactly when it **vanishes at every true-answer point of `x`**.

## The two witnesses

    posWitness x = τ  -  ∑_{i,k} u x i k · (∑_{s ≠ read x i} e i s k)
    negWitness y = τ  +  ∑_{i,k} v y i k · e i (read y i) k

The positive witness puts the dual's `u x` on every **false** answer letter, so
it vanishes on the true-answer points of `x` and the first contract is immediate.
The negative witness puts the dual's `v y` on the **true** answer letters of `y`,
so it is `τ` plus a correction supported exactly where `inputProj gen (read y)`
kills.

They meet only where the two inputs disagree, and there the dual's feasibility
identity

    ∑ i, [read x i ≠ read y i] · ∑ k, u x i k · v y i k  =  [f x ≠ f y]

says precisely what is needed:

    ⟪posWitness x, negWitness y⟫ = 1 - [f x ≠ f y] = [f x = f y].

So distinct outputs give **orthogonal** witnesses.  Taking `L` to be the
projector onto the span of the positive witnesses of the inputs with `f x = o`
then fixes every positive witness and annihilates every negative one — the two
`IsPosWitness` contracts, and the negative side's `L *ᵥ w = 0`, all from one
inner product.

The `|σ| - 1` in `qNormSq_posWitness` is the price of spreading `u x i k` over
every false letter: the construction cannot know which letter `y` will read.  It
is `1` for a Boolean alphabet.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ X O K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype X] [DecidableEq X] [DecidableEq O] [Fintype K] [DecidableEq K]

/-! ## States of the construction's shape

Every state below is `α` on the target and `A i s k` on the answer-letter
points.  Proving the inner product and the norm once, for this shape, is what
keeps the rest of the file free of basis manipulation. -/

/-- A state of the construction's shape. -/
@[expose]
def scState (α : ℂ) (A : ι → σ → K → ℂ) : QBasis ι σ (Option K) → ℂ
  | (none, none, none) => α
  | (some i, some s, some k) => A i s k
  | _ => 0

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype ι] [Fintype σ] in
@[simp] lemma scState_target (α : ℂ) (A : ι → σ → K → ℂ) :
    scState α A ((none, none, none) : QBasis ι σ (Option K)) = α := rfl

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype ι] [Fintype σ] in
@[simp] lemma scState_letter (α : ℂ) (A : ι → σ → K → ℂ) (i : ι) (s : σ) (k : K) :
    scState α A ((some i, some s, some k) : QBasis ι σ (Option K)) = A i s k := rfl

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype ι] [Fintype σ] in
@[simp] lemma scState_idle_reg (α : ℂ) (A : ι → σ → K → ℂ) (k : K) :
    scState α A ((none, none, some k) : QBasis ι σ (Option K)) = 0 := rfl

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype ι] [Fintype σ] in
@[simp] lemma scState_idle_letter (α : ℂ) (A : ι → σ → K → ℂ) (s : σ) (w : Option K) :
    scState α A ((none, some s, w) : QBasis ι σ (Option K)) = 0 := by
  cases w <;> rfl

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype ι] [Fintype σ] in
@[simp] lemma scState_blank (α : ℂ) (A : ι → σ → K → ℂ) (i : ι) (w : Option K) :
    scState α A ((some i, none, w) : QBasis ι σ (Option K)) = 0 := by
  cases w <;> rfl

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype ι] [Fintype σ] in
@[simp] lemma scState_flag (α : ℂ) (A : ι → σ → K → ℂ) (i : ι) (s : σ) :
    scState α A ((some i, some s, none) : QBasis ι σ (Option K)) = 0 := rfl

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] in
/-- **The inner product of two states of this shape.** -/
theorem qInner_scState (α β : ℂ) (A B : ι → σ → K → ℂ) :
    qInner (scState α A) (scState β B)
      = star α * β + ∑ i : ι, ∑ s : σ, ∑ k : K, star (A i s k) * B i s k := by
  classical
  simp [qInner_def, Fintype.sum_prod_type, Fintype.sum_option]

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] in
/-- **The squared norm of a state of this shape.** -/
theorem qNormSq_scState (α : ℂ) (A : ι → σ → K → ℂ) :
    qNormSq (scState α A)
      = Complex.normSq α + ∑ i : ι, ∑ s : σ, ∑ k : K, Complex.normSq (A i s k) := by
  classical
  simp [qNormSq_def, Fintype.sum_prod_type, Fintype.sum_option]

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype ι] [Fintype σ] in
lemma scState_add (α β : ℂ) (A B : ι → σ → K → ℂ) :
    scState (α + β) (fun i s k => A i s k + B i s k)
      = scState α A + scState (K := K) β B := by
  classical
  funext p
  obtain ⟨(_ | i), (_ | s), (_ | k)⟩ := p <;> simp

/-! ## The generators and the target -/

/-- **The generators**: the blank-answer states, one per index and dual
register. -/
def scGen : ι × K → (QBasis ι σ (Option K) → ℂ) :=
  fun j => qBasis ((some j.1, none, some j.2) : QBasis ι σ (Option K))

/-- The target: the flag state of the idle sector. -/
def scTarget : QBasis ι σ (Option K) → ℂ := scState 1 (fun _ _ _ => (0 : ℂ))

lemma qInner_qBasis_left {H : Type} [Fintype H] [DecidableEq H] (p : H) (ψ : H → ℂ) :
    qInner (qBasis p) ψ = ψ p := by
  rw [qInner_def, Finset.sum_eq_single p]
  · rw [qBasis_apply, ite_eq_left rfl, star_one, one_mul]
  · intro h _ hh
    rw [qBasis_apply, ite_eq_right hh, star_zero, zero_mul]
  · simp

/-- **What the generators test.**  Pairing a generator against a state read
through the oracle picks out the amplitude at a *true-answer* point. -/
theorem qInner_scGen_oracle (a : ι → σ) (φ : QBasis ι σ (Option K) → ℂ) (i : ι) (k : K) :
    qInner (scGen (i, k)) (oracleMat a *ᵥ φ) = φ (some i, some (a i), some k) := by
  rw [scGen, qInner_qBasis_left, oracleMat_mulVec_apply, oracleMap_blank]

/-- **Being fixed by the input projector is vanishing on the true answers.** -/
theorem inputProj_scGen_mulVec_eq_self_iff (a : ι → σ) (φ : QBasis ι σ (Option K) → ℂ) :
    inputProj scGen a *ᵥ φ = φ ↔ ∀ i k, φ (some i, some (a i), some k) = 0 := by
  rw [inputProj_mulVec_eq_self_iff]
  constructor
  · intro h i k
    rw [← qInner_scGen_oracle a φ i k]
    exact h (i, k)
  · rintro h ⟨i, k⟩
    rw [qInner_scGen_oracle]
    exact h i k

/-! ## The two witness families -/

variable (read : X → ι → σ) (f : X → O)

/-- **The positive witness** for `x`: the target, minus the dual's `u x` spread
over every *false* answer letter. -/
def posWitness (P : DualPairOn read K f) (x : X) : QBasis ι σ (Option K) → ℂ :=
  scState 1 (fun i s k => if s = read x i then 0 else -(P.u x i k : ℂ))

/-- **The negative witness** for `y`: the target, plus the dual's `v y` on the
*true* answer letters. -/
def negWitness (P : DualPairOn read K f) (y : X) : QBasis ι σ (Option K) → ℂ :=
  scState 1 (fun i s k => if s = read y i then (P.v y i k : ℂ) else 0)

/-- The negative witness's correction term, supported exactly on the true-answer
points of `y`. -/
def negCorr (P : DualPairOn read K f) (y : X) : QBasis ι σ (Option K) → ℂ :=
  scState 0 (fun i s k => if s = read y i then (P.v y i k : ℂ) else 0)

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] [Fintype σ] in
lemma negWitness_eq_target_add (P : DualPairOn read K f) (y : X) :
    negWitness read f P y = scTarget + negCorr read f P y := by
  classical
  funext p
  obtain ⟨(_ | i), (_ | s), (_ | k)⟩ := p <;>
    simp [negWitness, negCorr, scTarget]

/-! ## The dual constraint, as an inner product

The one computation the construction rests on. -/

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] in
/-- **Distinct outputs give orthogonal witnesses.**  This *is* the dual's
feasibility identity, read as an inner product. -/
theorem qInner_posWitness_negWitness (P : DualPairOn read K f) (x y : X) :
    qInner (posWitness read f P x) (negWitness read f P y)
      = if f x = f y then 1 else 0 := by
  classical
  rw [posWitness, negWitness, qInner_scState]
  have hterm : ∀ i : ι,
      (∑ s : σ, ∑ k : K,
        star (if s = read x i then (0 : ℂ) else -(P.u x i k : ℂ))
          * (if s = read y i then (P.v y i k : ℂ) else 0))
        = -(((if read x i = read y i then 0 else ∑ k, P.u x i k * P.v y i k : ℝ)) : ℂ) := by
    intro i
    rw [Finset.sum_eq_single (read y i)]
    · by_cases h : read x i = read y i
      · rw [ite_eq_left h, Complex.ofReal_zero, neg_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [ite_eq_left h.symm, star_zero, zero_mul]
      · rw [ite_eq_right h, Complex.ofReal_sum]
        rw [show -(∑ k : K, ((P.u x i k * P.v y i k : ℝ) : ℂ))
              = ∑ k : K, -(((P.u x i k * P.v y i k : ℝ) : ℂ)) from by simp]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ite_eq_right fun hcc => h hcc.symm, ite_eq_left rfl]
        simp
    · intro s _ hs
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [ite_eq_right hs, mul_zero]
    · simp
  simp only [hterm]
  rw [show (∑ i : ι, -(((if read x i = read y i then 0
        else ∑ k, P.u x i k * P.v y i k : ℝ)) : ℂ))
      = -(∑ i : ι, (((if read x i = read y i then 0
        else ∑ k, P.u x i k * P.v y i k : ℝ)) : ℂ)) from by simp]
  rw [← Complex.ofReal_sum, P.constraint x y]
  by_cases h : f x = f y <;> simp [h]

/-! ## The positive contracts -/

omit [DecidableEq X] in
/-- **The positive witness vanishes on the true answers of its own input**, which
is the first contract. -/
theorem inputProj_mulVec_posWitness (P : DualPairOn read K f) (x : X) :
    inputProj scGen (read x) *ᵥ posWitness read f P x = posWitness read f P x := by
  rw [inputProj_scGen_mulVec_eq_self_iff]
  intro i k
  rw [posWitness, scState_letter, ite_eq_left rfl]

/-- **The fixed subspace**: the span of the positive witnesses of the inputs that
`f` sends to `o`. -/
noncomputable def scKer (P : DualPairOn read K f) (o : O) :
    Matrix (QBasis ι σ (Option K)) (QBasis ι σ (Option K)) ℂ :=
  subProj (rawSpan (fun x : {x : X // f x = o} => posWitness read f P x.1))

omit [DecidableEq X] in
theorem isQProjector_scKer (P : DualPairOn read K f) (o : O) :
    IsQProjector (scKer read f P o) := isQProjector_subProj _

omit [DecidableEq X] in
/-- **The fixed subspace fixes the positive witnesses**, which is the second
contract. -/
theorem scKer_mulVec_posWitness (P : DualPairOn read K f) {o : O} {x : X}
    (hx : f x = o) : scKer read f P o *ᵥ posWitness read f P x
      = posWitness read f P x :=
  spanProj_mulVec_self (fun x : {x : X // f x = o} => posWitness read f P x.1) ⟨x, hx⟩

omit [DecidableEq X] in
/-- **Both contracts**, so the detector of `SourceQuantumInputDetector` answers `+1` on
this witness exactly, at cost `4(T-1)`. -/
theorem isPosWitness_posWitness (P : DualPairOn read K f) {o : O} {x : X}
    (hx : f x = o) :
    IsPosWitness scGen (scKer read f P o) (read x) (posWitness read f P x) := by
  classical
  exact ⟨inputProj_mulVec_posWitness read f P x, scKer_mulVec_posWitness read f P hx⟩

/-! ## The negative side -/

omit [DecidableEq X] in
/-- **The fixed subspace annihilates the negative witnesses.**  This is the
hypothesis `effective_chord_gap_sq_inputReflProduct` asks for, and it is exactly
the orthogonality supplied by the dual constraint. -/
theorem scKer_mulVec_negWitness (P : DualPairOn read K f) {o : O} {y : X}
    (hy : f y ≠ o) : scKer read f P o *ᵥ negWitness read f P y = 0 := by
  classical
  refine subProj_mulVec_of_mem_orthogonal _ ?_
  rw [mem_rawSpan_orthogonal_iff]
  rintro ⟨x, hx⟩
  rw [qInner_posWitness_negWitness, ite_eq_right]
  rw [hx]
  exact fun h => hy h.symm

/-- A projector kills anything orthogonal to its own image of that vector.  This
is the general fact; it is stated here because nothing upstream needs it yet. -/
lemma mulVec_eq_zero_of_qInner_eq_zero {H : Type} [Fintype H]
    {P : Matrix H H ℂ} (hP : IsQProjector P) {ψ : H → ℂ}
    (h : qInner (P *ᵥ ψ) ψ = 0) : P *ᵥ ψ = 0 := by
  classical
  have h1 : qInner (P *ᵥ ψ) (P *ᵥ ψ) = 0 := by
    rw [qInner_mulVec_left, Matrix.mulVec_mulVec, hP.1, hP.2, ← qInner_conj, h, star_zero]
  rw [qInner_self] at h1
  exact qNormSq_eq_zero_iff.mp (by exact_mod_cast h1)

omit [DecidableEq X] in
/-- **The input projector kills the negative witness's correction term**, which
is supported exactly on the true-answer points it annihilates. -/
theorem inputProj_mulVec_negCorr (P : DualPairOn read K f) (y : X) :
    inputProj scGen (read y) *ᵥ negCorr read f P y = 0 := by
  refine mulVec_eq_zero_of_qInner_eq_zero (isQProjector_inputProj _ _) ?_
  have hfix : inputProj scGen (read y) *ᵥ (inputProj scGen (read y) *ᵥ negCorr read f P y)
      = inputProj scGen (read y) *ᵥ negCorr read f P y := by
    rw [Matrix.mulVec_mulVec, (isQProjector_inputProj scGen (read y)).2]
  have hvan := (inputProj_scGen_mulVec_eq_self_iff (read y) _).mp hfix
  simp only [negCorr] at hvan
  rw [qInner_def]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨(_ | i), (_ | s), (_ | k)⟩ := p <;>
    simp only [negCorr, scState_target, scState_letter, scState_idle_reg,
      scState_idle_letter, scState_blank, scState_flag, mul_zero]
  by_cases hs : s = read y i
  · rw [hs, hvan i k, star_zero, zero_mul]
  · rw [ite_eq_right hs, mul_zero]

omit [DecidableEq X] in
/-- **The negative witness is the target, up to what the input projector
kills.**  This is the negative side's projected-direction obligation. -/
theorem inputProj_mulVec_negWitness (P : DualPairOn read K f) (y : X) :
    inputProj scGen (read y) *ᵥ negWitness read f P y = scTarget := by
  classical
  have hτ : inputProj scGen (read y) *ᵥ (scTarget : QBasis ι σ (Option K) → ℂ) = scTarget :=
    (inputProj_scGen_mulVec_eq_self_iff (read y) _).mpr fun i k => by
      rw [scTarget, scState_letter]
  rw [negWitness_eq_target_add, Matrix.mulVec_add, hτ, inputProj_mulVec_negCorr, add_zero]

/-! ## Overlap and norms

The exact algebra above says nothing about *size*; these are the estimates the
query bound will consume. -/

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] in
/-- **The positive witness has overlap exactly `1` with the target.**  The
correction term lives entirely off the target, so nothing is lost. -/
theorem qInner_scTarget_posWitness (P : DualPairOn read K f) (x : X) :
    qInner scTarget (posWitness read f P x) = 1 := by
  classical
  rw [scTarget, posWitness, qInner_scState]
  simp

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] in
/-- **The negative witness's norm is `1` plus the dual's `v`-mass.** -/
theorem qNormSq_negWitness (P : DualPairOn read K f) (y : X) :
    qNormSq (negWitness read f P y)
      = 1 + ∑ i : ι, ∑ k : K, P.v y i k * P.v y i k := by
  classical
  rw [negWitness, qNormSq_scState]
  have hi : ∀ i : ι, (∑ s : σ, ∑ k : K,
      Complex.normSq (if s = read y i then (P.v y i k : ℂ) else 0))
      = ∑ k : K, P.v y i k * P.v y i k := by
    intro i
    rw [Finset.sum_eq_single (read y i)]
    · exact Finset.sum_congr rfl fun k _ => by
        rw [ite_eq_left rfl, Complex.normSq_ofReal]
    · intro s _ hs
      exact Finset.sum_eq_zero fun k _ => by rw [ite_eq_right hs, Complex.normSq_zero]
    · simp
  simp only [hi]
  norm_num

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] in
/-- **The positive witness's norm**, exactly: `1` plus the dual's `u`-mass, once
per *false* letter. -/
theorem qNormSq_posWitness (P : DualPairOn read K f) (x : X) :
    qNormSq (posWitness read f P x)
      = 1 + ∑ i : ι, ∑ s : σ, (if s = read x i then 0
          else ∑ k : K, P.u x i k * P.u x i k) := by
  classical
  rw [posWitness, qNormSq_scState]
  have hi : ∀ (i : ι) (s : σ), (∑ k : K,
      Complex.normSq (if s = read x i then (0 : ℂ) else -(P.u x i k : ℂ)))
      = if s = read x i then 0 else ∑ k : K, P.u x i k * P.u x i k := by
    intro i s
    by_cases h : s = read x i
    · rw [ite_eq_left h]
      exact Finset.sum_eq_zero fun k _ => by rw [ite_eq_left h, Complex.normSq_zero]
    · rw [ite_eq_right h]
      exact Finset.sum_congr rfl fun k _ => by
        rw [ite_eq_right h, Complex.normSq_neg, Complex.normSq_ofReal]
  simp only [hi]
  norm_num

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] in
/-- The negative witness is short: `‖w‖² ≤ 1 + c` for a dual of cost `c`. -/
theorem qNormSq_negWitness_le {c : ℝ} (P : DualPairOn read K f) (hP : P.IsCostLe c)
    (y : X) : qNormSq (negWitness read f P y) ≤ 1 + c := by
  classical
  rw [qNormSq_negWitness]
  have := hP.2 y
  linarith

end QuantumQueryComplexity

end SourceQuantumWitness

section SourceQuantumDetection

/-!
# The detector on the witness states: the two acceptance estimates

The last quantitative step of the state-conversion construction.
`SourceQuantumWitness` built the witness states from a `DualPairOn` and discharged the
exact contracts; this section adds the *estimates* and combines them with the
fidelity bounds of `SourceQuantumFidelity` into the two numbers the eventual
measurement reads: for the detector `D = scDetector` at clock length `T` and
the initial state `u = uniformClock T scTarget`,

* **`f x = o`** (`le_re_qInner_scDetector_of_eq`):
  `Re⟪u, D_x u⟫ ≥ 2/(1 + (|σ|−1)cu) − 1`, from the exact fixed point
  `posWitness x`, its overlap `⟪τ, φₓ⟫ = 1`, and its norm
  `‖φₓ‖² ≤ 1 + (|σ|−1)cu`;
* **`f y ≠ o`** (`re_qInner_scDetector_le_of_ne`):
  `Re⟪u, D_y u⟫ ≤ (Δ/2)√(1+cv) + 4/(TΔ) − (1 − (Δ²/4)(1+cv))`, from the
  effective gap applied to `negWitness y` (whose input projection is exactly
  `τ`) and the uniform-clock suppression on the far window.

With `Δ ~ 1/√(1+cv)` and `T ~ 1/Δ ~ √(1+cv)` the second bound is `≈ −1` while the
first is `≈ +1` for small `(|σ|−1)cu` — the separation a Hadamard test turns
into a bounded-error measurement.  Choosing those parameters, and the dual
rescaling `DualPairOn.scale` that balances `cu` against `cv`, is the algorithm
extraction's job; this section keeps every bound parametric.

The clock geometry those estimates ride on — the isometry
`qInner_uniformClock`, additivity `uniformClock_add`, and their companions —
is supplied by `SourceQuantumClock` and is shared with the uniform extraction.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-! ## Rescaling a dual pair -/

namespace DualPairOn

variable {ι σ X O K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype X] [DecidableEq X] [DecidableEq O] [Fintype K]
  [DecidableEq K] {read : X → ι → σ} {f : X → O}

/-- **Rescaling a dual pair**: `u ↦ αu`, `v ↦ α⁻¹v`.  Feasibility is
scale-invariant, and the two sides' masses trade against each other — the
balancing device of the algorithm extraction. -/
@[expose]
noncomputable def scale (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0) :
    DualPairOn read K f where
  u x i k := α * P.u x i k
  v y i k := α⁻¹ * P.v y i k
  constraint x y := by
    rw [← P.constraint x y]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : read x i = read y i
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show α * P.u x i k * (α⁻¹ * P.v y i k)
          = (α * α⁻¹) * (P.u x i k * P.v y i k) from by ring,
        mul_inv_cancel₀ hα, one_mul]

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] [Fintype σ] in
@[simp] lemma scale_u (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0)
    (x : X) (i : ι) (k : K) : (P.scale hα).u x i k = α * P.u x i k := rfl

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] [Fintype σ] in
@[simp] lemma scale_v (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0)
    (y : X) (i : ι) (k : K) : (P.scale hα).v y i k = α⁻¹ * P.v y i k := rfl

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] [Fintype σ] in
/-- The `u`-mass scales by `α²`. -/
lemma scale_u_mass (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0) (x : X) :
    ∑ i, ∑ k, (P.scale hα).u x i k * (P.scale hα).u x i k
      = α ^ 2 * ∑ i, ∑ k, P.u x i k * P.u x i k := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [scale_u]; ring

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] [Fintype σ] in
/-- The `v`-mass scales by `α⁻²`. -/
lemma scale_v_mass (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0) (y : X) :
    ∑ i, ∑ k, (P.scale hα).v y i k * (P.scale hα).v y i k
      = (α⁻¹) ^ 2 * ∑ i, ∑ k, P.v y i k * P.v y i k := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [scale_v]; ring

end DualPairOn

/-! ## The witness norms, bounded -/

variable {ι σ X O K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype X] [DecidableEq X] [DecidableEq O] [Fintype K]
  [DecidableEq K]

variable (read : X → ι → σ) (f : X → O)

omit [DecidableEq K] [DecidableEq ι] [DecidableEq σ] in
@[simp] lemma qNormSq_scTarget :
    qNormSq (scTarget : QBasis ι σ (Option K) → ℂ) = 1 := by
  classical
  rw [scTarget, qNormSq_scState]
  simp

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] in
/-- The positive witness is at least a unit vector. -/
theorem one_le_qNormSq_posWitness (P : DualPairOn read K f) (x : X) :
    1 ≤ qNormSq (posWitness read f P x) := by
  classical
  rw [qNormSq_posWitness]
  have h : 0 ≤ ∑ i : ι, ∑ s : σ, (if s = read x i then 0
      else ∑ k : K, P.u x i k * P.u x i k) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ => ?_
    by_cases hs : s = read x i
    · rw [ite_eq_left hs]
    · rw [ite_eq_right hs]
      exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
  linarith

omit [DecidableEq K] [DecidableEq X] [DecidableEq ι] in
/-- **The positive witness is short**: `‖φₓ‖² ≤ 1 + (|σ|−1)·cu` when the
dual's `u`-mass at `x` is at most `cu`.  The `|σ|−1` is the price of spreading
`u x` over every false letter; it is `1` for a Boolean alphabet. -/
theorem qNormSq_posWitness_le [Nonempty σ] {cu : ℝ} (P : DualPairOn read K f)
    (x : X) (hcu : ∑ i, ∑ k, P.u x i k * P.u x i k ≤ cu) :
    qNormSq (posWitness read f P x)
      ≤ 1 + ((Fintype.card σ : ℝ) - 1) * cu := by
  classical
  rw [qNormSq_posWitness]
  have hrow : ∀ i : ι, (∑ s : σ, if s = read x i then 0
        else ∑ k : K, P.u x i k * P.u x i k)
      = ((Fintype.card σ : ℝ) - 1) * ∑ k : K, P.u x i k * P.u x i k := by
    intro i
    have h1 : ∀ s : σ, (if s = read x i then (0 : ℝ)
          else ∑ k : K, P.u x i k * P.u x i k)
        = (∑ k : K, P.u x i k * P.u x i k)
          - (if s = read x i then ∑ k : K, P.u x i k * P.u x i k else 0) := by
      intro s
      by_cases hs : s = read x i <;> simp [hs]
    rw [Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_sub_distrib,
      Finset.sum_const,
      Finset.sum_ite_eq' Finset.univ (read x i)
        (fun _ => ∑ k : K, P.u x i k * P.u x i k),
      ite_eq_left (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => hrow i, ← Finset.mul_sum]
  have hσ : (0 : ℝ) ≤ (Fintype.card σ : ℝ) - 1 := by
    have h1 : 1 ≤ Fintype.card σ := Fintype.card_pos_iff.mpr ‹Nonempty σ›
    have h2 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by exact_mod_cast h1
    linarith
  have := mul_le_mul_of_nonneg_left hcu hσ
  linarith

/-! ## The detector -/

/-- **The detector for output `o`**: the uniform-clock phase detector of the
reflection product built from the witness construction's generators and the
span of the positive witnesses of `f⁻¹(o)`.  Cost: `4(T−1)` queries. -/
@[expose]
noncomputable def scDetector (P : DualPairOn read K f) (o : O) (T : ℕ) :
    QRoutine ι σ (ClockWork ι T (Option K)) :=
  clockPhaseRefl (inputReflProduct scGen (scKer read f P o)
    (isQProjector_scKer read f P o)) T

omit [DecidableEq X] in
lemma scDetector_eq (P : DualPairOn read K f) (o : O) (T : ℕ) :
    scDetector read f P o T
      = clockPhaseRefl (inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)) T := rfl

omit [DecidableEq X] in
@[simp] theorem scDetector_len (P : DualPairOn read K f) (o : O) (T : ℕ) :
    (scDetector read f P o T).len = 4 * (T - 1) :=
  clockPhaseRefl_len_inputReflProduct _ _ _ T

/-! ## The negative input, prepared

For `f y ≠ o` the fixed subspace annihilates `negWitness y`, whose input
projection is exactly the target.  So the effective gap bounds the near part
*of the target itself*, and the detector's far-window guarantee applies to the
rest — with `‖·‖² = 1` on the right of both. -/

omit [DecidableEq X] in
/-- **The near part of the target is small** on a negative input:
`‖N_Δ τ‖² ≤ (Δ²/4)(1 + cv)`. -/
theorem qNormSq_chordNear_scTarget_le (P : DualPairOn read K f) {o : O}
    {y : X} (hy : f y ≠ o) {cv : ℝ}
    (hcv : ∑ i, ∑ k, P.v y i k * P.v y i k ≤ cv) (Δ : ℝ) :
    qNormSq (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      ≤ Δ ^ 2 / 4 * (1 + cv) := by
  classical
  have h := effective_chord_gap_sq_inputReflProduct scGen (scKer read f P o)
    (isQProjector_scKer read f P o) (read y)
    (scKer_mulVec_negWitness read f P hy) Δ
  rw [inputProj_mulVec_negWitness] at h
  have hwn : qNormSq (negWitness read f P y) ≤ 1 + cv := by
    rw [qNormSq_negWitness]; linarith
  calc qNormSq (chordNearProj _ Δ *ᵥ scTarget)
      ≤ Δ ^ 2 / 4 * qNormSq (negWitness read f P y) := h
    _ ≤ Δ ^ 2 / 4 * (1 + cv) :=
        mul_le_mul_of_nonneg_left hwn (by positivity)

omit [DecidableEq X] in
/-- **The detector reads `−1` on the target's far part**, up to `16/(T²Δ²)`.
(The bound holds for every input; only its use is specific to `f y ≠ o`.) -/
theorem qNormSq_scDetector_far_add_le (P : DualPairOn read K f) (o : O)
    (y : X) {T : ℕ} (hT : 0 < T) {Δ : ℝ} (hΔ : 0 < Δ) :
    qNormSq ((scDetector read f P o T).run (read y)
        *ᵥ uniformClock T (chordFarProj
            ((inputReflProduct scGen (scKer read f P o)
              (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      + uniformClock T (chordFarProj
          ((inputReflProduct scGen (scKer read f P o)
            (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget))
      ≤ 16 / ((T : ℝ) ^ 2 * Δ ^ 2) := by
  classical
  have h := qNormSq_clockPhaseRefl_add_le_div_inputReflProduct scGen
    (scKer read f P o) (isQProjector_scKer read f P o) hT (read y) hΔ
    (negWitness read f P y)
  rw [inputProj_mulVec_negWitness, qNormSq_scTarget, mul_one] at h
  rw [scDetector_eq]
  exact h

/-! ## The two acceptance estimates -/

omit [DecidableEq X] in
/-- **The detector accepts a positive input**: for `f x = o`,
`Re⟪u, D u⟫ ≥ 2/(1 + (|σ|−1)cu) − 1` on `u = uniformClock T scTarget`. -/
theorem le_re_qInner_scDetector_of_eq [Nonempty σ] (P : DualPairOn read K f)
    {o : O} {x : X} (hx : f x = o) {T : ℕ} (hT : 0 < T) {cu : ℝ}
    (hcu : ∑ i, ∑ k, P.u x i k * P.u x i k ≤ cu) :
    2 / (1 + ((Fintype.card σ : ℝ) - 1) * cu) - 1
      ≤ (qInner (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
          ((scDetector read f P o T).run (read x)
            *ᵥ uniformClock T scTarget)).re := by
  classical
  have hUnit := (scDetector read f P o T).run_mem_unitaryGroup (read x)
  have hfix : (scDetector read f P o T).run (read x)
      *ᵥ uniformClock T (posWitness read f P x)
      = uniformClock T (posWitness read f P x) := by
    rw [scDetector_eq]
    exact (isPosWitness_posWitness read f P hx).clockPhaseRefl_run_mulVec_uniformClock
      (isQProjector_scKer read f P o) hT
  have hkey := le_mul_re_qInner_mulVec_of_fixed hUnit hfix
    (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
  -- the three scalar inputs
  have hb : qInner (uniformClock T (posWitness read f P x))
      (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ)) = 1 := by
    rw [qInner_uniformClock hT]
    have h := congrArg star (qInner_scTarget_posWitness read f P x)
    rwa [qInner_conj, star_one] at h
  have hτn : qNormSq (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
      = 1 := by
    rw [qNormSq_uniformClock hT, qNormSq_scTarget]
  rw [hb, hτn, Complex.normSq_one] at hkey
  -- hkey : 2·1·N − N²·1 ≤ N²·Re, with N the witness norm
  set N : ℝ := qNormSq (uniformClock T (posWitness read f P x)) with hN
  set Re : ℝ := (qInner (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
      ((scDetector read f P o T).run (read x)
        *ᵥ uniformClock T scTarget)).re with hRe
  have hN1 : 1 ≤ N := by
    rw [hN, qNormSq_uniformClock hT]
    exact one_le_qNormSq_posWitness read f P x
  have hNM : N ≤ 1 + ((Fintype.card σ : ℝ) - 1) * cu := by
    rw [hN, qNormSq_uniformClock hT]
    exact qNormSq_posWitness_le read f P x hcu
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hM0 : (0 : ℝ) < 1 + ((Fintype.card σ : ℝ) - 1) * cu :=
    lt_of_lt_of_le one_pos (hN1.trans hNM)
  have hkey' : 2 * N - N ^ 2 ≤ N ^ 2 * Re := by
    calc 2 * N - N ^ 2 = 2 * 1 * N - N ^ 2 * 1 := by ring
      _ ≤ N ^ 2 * Re := hkey
  -- divide out one `N`, then trade `N` for its upper bound
  have hstep1 : 2 ≤ N * Re + N := by
    have hh : N * (2 - N) ≤ N * (N * Re) := by
      calc N * (2 - N) = 2 * N - N ^ 2 := by ring
        _ ≤ N ^ 2 * Re := hkey'
        _ = N * (N * Re) := by ring
    have := le_of_mul_le_mul_left hh hN0
    linarith
  have hRe1 : (0 : ℝ) ≤ Re + 1 := by
    by_contra hneg
    have hneg' : Re + 1 < 0 := lt_of_not_ge hneg
    nlinarith [hstep1, hN0]
  have hstep2 : 2 ≤ (1 + ((Fintype.card σ : ℝ) - 1) * cu) * Re
      + (1 + ((Fintype.card σ : ℝ) - 1) * cu) := by
    nlinarith [hstep1, mul_nonneg (sub_nonneg.mpr hNM) hRe1]
  rw [sub_le_iff_le_add, div_le_iff₀ hM0]
  linarith [hstep2]

omit [DecidableEq X] in
/-- **The detector rejects a negative input**: for `f y ≠ o`,
`Re⟪u, D u⟫ ≤ (Δ/2)√(1+cv) + 4/(TΔ) − (1 − (Δ²/4)(1+cv))` on
`u = uniformClock T scTarget`. -/
theorem re_qInner_scDetector_le_of_ne (P : DualPairOn read K f) {o : O}
    {y : X} (hy : f y ≠ o) {T : ℕ} (hT : 0 < T) {Δ : ℝ} (hΔ : 0 < Δ)
    {cv : ℝ} (hcv : ∑ i, ∑ k, P.v y i k * P.v y i k ≤ cv) :
    (qInner (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
        ((scDetector read f P o T).run (read y)
          *ᵥ uniformClock T scTarget)).re
      ≤ Δ / 2 * Real.sqrt (1 + cv) + 4 / ((T : ℝ) * Δ)
        - (1 - Δ ^ 2 / 4 * (1 + cv)) := by
  classical
  have hcv0 : (0 : ℝ) ≤ cv :=
    le_trans (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => mul_self_nonneg _) hcv
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  -- the near/far split of the target
  have hsum : chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ
          *ᵥ (scTarget : QBasis ι σ (Option K) → ℂ)
      + chordFarProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget
      = scTarget := by
    rw [← Matrix.add_mulVec, chordNearProj_add_chordFarProj, Matrix.one_mulVec]
  have horth : qInner
      (uniformClock T (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget))
      (uniformClock T (chordFarProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)) = 0 := by
    rw [qInner_uniformClock hT, chordFarProj]
    exact qInner_mulVec_one_sub_mulVec (isQProjector_chordNearProj _ Δ) _
  have hUnit := (scDetector read f P o T).run_mem_unitaryGroup (read y)
  have hkey := re_qInner_mulVec_le_of_perp hUnit horth
  rw [← uniformClock_add, hsum] at hkey
  -- the norms
  have hu1 : qNormSq (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
      = 1 := by rw [qNormSq_uniformClock hT, qNormSq_scTarget]
  rw [hu1, Real.sqrt_one, one_mul, one_mul] at hkey
  have hnear := qNormSq_chordNear_scTarget_le read f P hy hcv Δ
  have hN' : Real.sqrt (qNormSq (uniformClock T (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)))
      ≤ Δ / 2 * Real.sqrt (1 + cv) := by
    rw [qNormSq_uniformClock hT]
    calc Real.sqrt (qNormSq (chordNearProj _ Δ *ᵥ scTarget))
        ≤ Real.sqrt (Δ ^ 2 / 4 * (1 + cv)) := Real.sqrt_le_sqrt hnear
      _ = Δ / 2 * Real.sqrt (1 + cv) := by
          rw [show Δ ^ 2 / 4 * (1 + cv) = (Δ / 2) ^ 2 * (1 + cv) from by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have herr := qNormSq_scDetector_far_add_le read f P o y hT hΔ
  have hE' : Real.sqrt (qNormSq ((scDetector read f P o T).run (read y)
        *ᵥ uniformClock T (chordFarProj
            ((inputReflProduct scGen (scKer read f P o)
              (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      + uniformClock T (chordFarProj
          ((inputReflProduct scGen (scKer read f P o)
            (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)))
      ≤ 4 / ((T : ℝ) * Δ) := by
    calc Real.sqrt (qNormSq _) ≤ Real.sqrt (16 / ((T : ℝ) ^ 2 * Δ ^ 2)) :=
        Real.sqrt_le_sqrt herr
      _ = 4 / ((T : ℝ) * Δ) := by
          rw [show (16 : ℝ) / ((T : ℝ) ^ 2 * Δ ^ 2)
              = (4 / ((T : ℝ) * Δ)) ^ 2 from by
            rw [div_pow]; congr 1 <;> ring,
            Real.sqrt_sq (div_nonneg (by norm_num)
              (mul_nonneg hT0.le hΔ.le))]
  have hdec : qNormSq (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      + qNormSq (chordFarProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      = 1 := by
    have h := qNormSq_chord_decomp
      ((inputReflProduct scGen (scKer read f P o)
        (isQProjector_scKer read f P o)).run (read y)) Δ
      (scTarget : QBasis ι σ (Option K) → ℂ)
    rw [qNormSq_scTarget] at h
    linarith
  have hF' : -(qNormSq (uniformClock T (chordFarProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)))
      ≤ -(1 - Δ ^ 2 / 4 * (1 + cv)) := by
    rw [qNormSq_uniformClock hT]
    linarith [hdec, hnear]
  have hNn : (0 : ℝ) ≤ Real.sqrt (qNormSq (uniformClock T (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget))) :=
    Real.sqrt_nonneg _
  linarith [hkey, hN', hE', hF']

end QuantumQueryComplexity

end SourceQuantumDetection

section SourceQuantumUniformConversion

/-!
# The uniform detector and its conversion errors

The detector of the cardinality-free construction: the clocked phase
reflection of the reflection product built from the physical generators and
the one global projector `uniformL P α`, at exactly `4(T-1)` queries.  The
two signed conversion errors are

    e₊ = D·clock(t_{x+}) − clock(t_{x+}),
    e₋ = D·clock(t_{x−}) + clock(t_{x−}),

and this section proves the three conversion-distance facts:

* the positive bound `‖e₊‖² ≤ 8α²c` — the detector fixes the clocked
  witness `clock(φ_x)` **exactly**, so on the bare target the error is the
  moved packet, `e₊ = α·(1 − D)·clock(V_x)`, one unitary-move bound away
  from the `v`-mass that `P.IsCostLe` controls.  A `T = 0` split
  (`uniformClock_zero`) keeps the statement free of any positivity
  hypothesis on `T`;
* the negative bound `‖e₋‖ ≤ Δ√(1 + c/(2α²)) + 4/(TΔ)` by one near/far
  split of the `−` target, the only statement needing `hα`, `hT`, `hΔ`;
* the **combination**: the end-to-end error `D·clock(common) − clock(out)`
  is `(e₊ + e₋)/√2` by pure linearity, and `e₊ ⟂ e₋` **exactly** — the
  detector is self-adjoint and unitary — so its squared norm is the exact
  half-sum `(‖e₊‖² + ‖e₋‖²)/2`, never a triangle bound.

## Nested register instances

Named canonical instances for `QBasis`, `CtrlWork`, and `UWork` keep the
nested register types within the default instance-search limit. The proofs
retain the same finite types and oracle model.

-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ K X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq O]
  {read : X → ι → σ} {f : X → O}

/-- **The uniform detector**: the clocked phase reflection of the reflection
product `R_P·R_L`, for the physical generators and the global projector
`uniformL P α`. -/
@[expose]
noncomputable def uniformDetector (P : DualPairOn read K f) (α : ℝ) (T : ℕ) :
    QRoutine ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) :=
  clockPhaseRefl (inputReflProduct
    (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
    (uniformL P α) (isQProjector_uniformL P α)) T

/-- The unfolding equation, so nothing downstream unfolds the definition. -/
theorem uniformDetector_eq (P : DualPairOn read K f) (α : ℝ) (T : ℕ) :
    uniformDetector P α T
      = clockPhaseRefl (inputReflProduct
          (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
          (uniformL P α) (isQProjector_uniformL P α)) T := rfl

/-- **The exact cost of the uniform detector**: `4(T-1)` queries. -/
@[simp] theorem uniformDetector_len (P : DualPairOn read K f) (α : ℝ) (T : ℕ) :
    (uniformDetector P α T).len = 4 * (T - 1) := by
  rw [uniformDetector_eq, clockPhaseRefl_len_inputReflProduct]

/-- **The detector fixes the clocked witness exactly** — `φ_x` is a positive
witness, so this is completeness with no error term. -/
theorem uniformDetector_run_mulVec_uniformClock_uniformPhi
    (P : DualPairOn read K f) (α : ℝ) {T : ℕ} (hT : 0 < T) (x : X) :
    (uniformDetector P α T).run (read x)
        *ᵥ uniformClock T (uniformPhi P α x)
      = uniformClock T (uniformPhi P α x) := by
  rw [uniformDetector_eq]
  exact (isPosWitness_uniformPhi P α x).clockPhaseRefl_run_mulVec_uniformClock
    (isQProjector_uniformL P α) hT

/-! ## The two conversion errors -/

/-- `e₊ = D·clock(t_{x+}) − clock(t_{x+})`: the deviation of the detector
from `+1` on the clocked `+` target. -/
noncomputable def uniformPlusError (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) : QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) → ℂ :=
  (uniformDetector P α T).run (read x)
      *ᵥ uniformClock T (realizedTPlus (K := K) f x)
    - uniformClock T (realizedTPlus (K := K) f x)

/-- `e₋ = D·clock(t_{x−}) + clock(t_{x−})`: the deviation of the detector
from `-1` on the clocked `−` target.  The `+` is the sign of the detector's
`-1` verdict. -/
noncomputable def uniformMinusError (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) : QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) → ℂ :=
  (uniformDetector P α T).run (read x)
      *ᵥ uniformClock T (realizedTMinus (K := K) f x)
    + uniformClock T (realizedTMinus (K := K) f x)

/-! ## The positive bound -/

/-- **The rearranged plus error**: the detector fixes `clock(φ_x)` and
`φ_x = t_{x+} + α·V_x`, so the error on the bare target is the moved packet,
`e₊ = α·(1 − D)·clock(V_x)`. -/
theorem uniformPlusError_eq (P : DualPairOn read K f) (α : ℝ) {T : ℕ}
    (hT : 0 < T) (x : X) :
    uniformPlusError P α T x
      = ((α : ℝ) : ℂ) •
          ((1 - (uniformDetector P α T).run (read x))
            *ᵥ uniformClock T (realizedPacketV P.v read x)) := by
  have hfix := uniformDetector_run_mulVec_uniformClock_uniformPhi P α hT x
  have hphi : uniformClock T (uniformPhi P α x)
      = uniformClock T (realizedTPlus (K := K) f x)
        + ((α : ℝ) : ℂ) • uniformClock T (realizedPacketV P.v read x) := by
    rw [show uniformPhi P α x
          = realizedTPlus (K := K) f x
            + ((α : ℝ) : ℂ) • realizedPacketV P.v read x from rfl,
      uniformClock_add, uniformClock_smul]
  rw [hphi, Matrix.mulVec_add, Matrix.mulVec_smul] at hfix
  rw [show uniformPlusError P α T x
        = (uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (realizedTPlus (K := K) f x)
          - uniformClock T (realizedTPlus (K := K) f x) from rfl,
    Matrix.sub_mulVec, Matrix.one_mulVec]
  linear_combination (norm := module) hfix

/-- **The positive conversion bound**: `‖e₊‖² ≤ 8α²c`.  No hypothesis on `T`
or `α`: the `T = 0` clock is zero, and the bound's sign comes from the cost
hypothesis itself. -/
theorem qNormSq_uniformPlusError_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) (α : ℝ) (T : ℕ) (x : X) :
    qNormSq (uniformPlusError P α T x) ≤ 8 * α ^ 2 * c := by
  have hmass : (∑ p : ι × K, P.v x p.1 p.2 * P.v x p.1 p.2) ≤ c := by
    simpa only [Fintype.sum_prod_type] using hP.2 x
  have hc : 0 ≤ c :=
    le_trans (Finset.sum_nonneg fun p _ => mul_self_nonneg _) hmass
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    rw [show uniformPlusError P α 0 x
          = (uniformDetector P α 0).run (read x)
              *ᵥ uniformClock 0 (realizedTPlus (K := K) f x)
            - uniformClock 0 (realizedTPlus (K := K) f x) from rfl,
      uniformClock_zero, Matrix.mulVec_zero, sub_zero, qNormSq_zero]
    exact mul_nonneg (by positivity) hc
  · let D := (uniformDetector P α T).run (read x)
    let V := realizedPacketV (R := ↥(Set.range f)) P.v read x
    have heq : uniformPlusError P α T x
        = ((α : ℝ) : ℂ) • ((1 - D) *ᵥ uniformClock T V) :=
      uniformPlusError_eq P α hT x
    have hD : D ∈ Matrix.unitaryGroup
        (QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K))) ℂ :=
      (uniformDetector P α T).run_mem_unitaryGroup (read x)
    have hmove := qNormSq_one_sub_pow_mulVec_le hD 1 (uniformClock T V)
    rw [pow_one] at hmove
    have hclock : qNormSq (uniformClock T V) = qNormSq V :=
      qNormSq_uniformClock hT V
    have hV : qNormSq V = 2 * ∑ p : ι × K, P.v x p.1 p.2 * P.v x p.1 p.2 :=
      qNormSq_realizedPacketV (R := ↥(Set.range f)) P.v read x
    have hE : qNormSq ((1 - D) *ᵥ uniformClock T V) ≤ 8 * c := by
      rw [hclock, hV] at hmove
      linarith
    rw [heq, qNormSq_smul, Complex.normSq_ofReal]
    calc α * α * qNormSq ((1 - D) *ᵥ uniformClock T V)
        ≤ α * α * (8 * c) :=
          mul_le_mul_of_nonneg_left hE (mul_self_nonneg α)
      _ = 8 * α ^ 2 * c := by ring

/-! ## The negative bound

`w_x` is a negative witness — `uniformL` kills it — and `inputProj` sends it
to the bare `−` target, so the effective gap and the divided detector bound
apply to the near/far split of `t_{x−}` directly:

* the near part is small — `‖N‖² ≤ (Δ²/4)‖w_x‖²` by
  `effective_chord_gap_sq_inputReflProduct` — so its detector error costs
  at most `2‖N‖`;
* on the far part the detector reads `-1` up to `4/(TΔ)`, by
  `qNormSq_clockPhaseRefl_add_le_div_inputReflProduct` and `‖t_{x−}‖ = 1`.

One near/far triangle inequality combines the two.  This is the only place
`hα`, `hT`, `hΔ` are genuinely needed. -/

/-- The near part of the realized `−` target, at window `Δ`. -/
noncomputable def uniformNear (P : DualPairOn read K f) (α : ℝ) (Δ : ℝ)
    (x : X) : UQBasis ↥(Set.range f) ι σ K → ℂ :=
  chordNearProj ((inputReflProduct
      (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
      (uniformL P α) (isQProjector_uniformL P α)).run (read x)) Δ
    *ᵥ realizedTMinus (K := K) f x

/-- The far part of the realized `−` target, at window `Δ`. -/
noncomputable def uniformFar (P : DualPairOn read K f) (α : ℝ) (Δ : ℝ)
    (x : X) : UQBasis ↥(Set.range f) ι σ K → ℂ :=
  chordFarProj ((inputReflProduct
      (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
      (uniformL P α) (isQProjector_uniformL P α)).run (read x)) Δ
    *ᵥ realizedTMinus (K := K) f x

/-- **The near/far split of the `−` target.** -/
theorem uniformNear_add_uniformFar (P : DualPairOn read K f) (α : ℝ) (Δ : ℝ)
    (x : X) :
    uniformNear P α Δ x + uniformFar P α Δ x
      = realizedTMinus (K := K) f x := by
  rw [uniformNear, uniformFar, ← Matrix.add_mulVec,
    chordNearProj_add_chordFarProj, Matrix.one_mulVec]

/-- **The near part is small**: the effective gap charges it to `‖w_x‖²`,
which the cost hypothesis bounds. -/
theorem qNormSq_uniformNear_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) {α : ℝ} (hα : α ≠ 0) (Δ : ℝ) (x : X) :
    qNormSq (uniformNear P α Δ x)
      ≤ Δ ^ 2 / 4 * (1 + c / (2 * α ^ 2)) := by
  have hgap := effective_chord_gap_sq_inputReflProduct
    (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
    (uniformL P α) (isQProjector_uniformL P α) (read x)
    (uniformL_mulVec_uniformW P hα x) Δ
  rw [inputProj_mulVec_uniformW] at hgap
  rw [uniformNear]
  calc qNormSq (chordNearProj ((inputReflProduct
          (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
          (uniformL P α) (isQProjector_uniformL P α)).run (read x)) Δ
        *ᵥ realizedTMinus (K := K) f x)
      ≤ Δ ^ 2 / 4 * qNormSq (uniformW P α x) := hgap
    _ ≤ Δ ^ 2 / 4 * (1 + c / (2 * α ^ 2)) :=
        mul_le_mul_of_nonneg_left (qNormSq_uniformW_le P hP hα x)
          (by positivity)

/-- **The detector reads `-1` on the far part**, up to `16/(T²Δ²)` — the
`−` target is a unit vector, so no witness norm enters. -/
theorem qNormSq_uniformDetector_far_add_le (P : DualPairOn read K f) (α : ℝ)
    {T : ℕ} (hT : 0 < T) {Δ : ℝ} (hΔ : 0 < Δ) (x : X) :
    qNormSq ((uniformDetector P α T).run (read x)
          *ᵥ uniformClock T (uniformFar P α Δ x)
        + uniformClock T (uniformFar P α Δ x))
      ≤ 16 / ((T : ℝ) ^ 2 * Δ ^ 2) := by
  have h := qNormSq_clockPhaseRefl_add_le_div_inputReflProduct
    (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
    (uniformL P α) (isQProjector_uniformL P α) hT (read x) hΔ
    (uniformW P α x)
  rw [inputProj_mulVec_uniformW, qNormSq_realizedTMinus, mul_one] at h
  rw [uniformDetector_eq, uniformFar]
  exact h

/-- **The negative conversion bound**:
`‖e₋‖ ≤ Δ·√(1 + c/(2α²)) + 4/(TΔ)`, by one near/far triangle
inequality. -/
theorem sqrt_qNormSq_uniformMinusError_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) {α : ℝ} (hα : α ≠ 0) {T : ℕ} (hT : 0 < T) {Δ : ℝ}
    (hΔ : 0 < Δ) (x : X) :
    Real.sqrt (qNormSq (uniformMinusError P α T x))
      ≤ Δ * Real.sqrt (1 + c / (2 * α ^ 2)) + 4 / ((T : ℝ) * Δ) := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  -- e₋ splits along the near/far decomposition of the `−` target
  have hsplit : uniformMinusError P α T x
      = ((uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (uniformNear P α Δ x)
          + uniformClock T (uniformNear P α Δ x))
        + ((uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (uniformFar P α Δ x)
          + uniformClock T (uniformFar P α Δ x)) := by
    rw [show uniformMinusError P α T x
          = (uniformDetector P α T).run (read x)
              *ᵥ uniformClock T (realizedTMinus (K := K) f x)
            + uniformClock T (realizedTMinus (K := K) f x) from rfl,
      ← uniformNear_add_uniformFar P α Δ x, uniformClock_add,
      Matrix.mulVec_add]
    abel
  -- the near error: both summands are moved unit-length copies of `N`
  have hnear : Real.sqrt (qNormSq ((uniformDetector P α T).run (read x)
          *ᵥ uniformClock T (uniformNear P α Δ x)
        + uniformClock T (uniformNear P α Δ x)))
      ≤ Δ * Real.sqrt (1 + c / (2 * α ^ 2)) := by
    have htri := sqrt_qNormSq_add_le
      ((uniformDetector P α T).run (read x)
        *ᵥ uniformClock T (uniformNear P α Δ x))
      (uniformClock T (uniformNear P α Δ x))
    have hU : qNormSq ((uniformDetector P α T).run (read x)
          *ᵥ uniformClock T (uniformNear P α Δ x))
        = qNormSq (uniformClock T (uniformNear P α Δ x)) :=
      qNormSq_mulVec
        ((uniformDetector P α T).run_mem_unitaryGroup (read x)) _
    rw [hU, qNormSq_uniformClock hT] at htri
    have hN : Real.sqrt (qNormSq (uniformNear P α Δ x))
        ≤ Δ / 2 * Real.sqrt (1 + c / (2 * α ^ 2)) := by
      calc Real.sqrt (qNormSq (uniformNear P α Δ x))
          ≤ Real.sqrt (Δ ^ 2 / 4 * (1 + c / (2 * α ^ 2))) :=
            Real.sqrt_le_sqrt (qNormSq_uniformNear_le P hP hα Δ x)
        _ = Δ / 2 * Real.sqrt (1 + c / (2 * α ^ 2)) := by
            rw [show Δ ^ 2 / 4 * (1 + c / (2 * α ^ 2))
                = (Δ / 2) ^ 2 * (1 + c / (2 * α ^ 2)) from by ring,
              Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    linarith [htri, hN]
  -- the far error: the divided detector bound, square-rooted
  have hfar : Real.sqrt (qNormSq ((uniformDetector P α T).run (read x)
          *ᵥ uniformClock T (uniformFar P α Δ x)
        + uniformClock T (uniformFar P α Δ x)))
      ≤ 4 / ((T : ℝ) * Δ) := by
    calc Real.sqrt (qNormSq ((uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (uniformFar P α Δ x)
          + uniformClock T (uniformFar P α Δ x)))
        ≤ Real.sqrt (16 / ((T : ℝ) ^ 2 * Δ ^ 2)) :=
          Real.sqrt_le_sqrt
            (qNormSq_uniformDetector_far_add_le P α hT hΔ x)
      _ = 4 / ((T : ℝ) * Δ) := by
          rw [show (16 : ℝ) / ((T : ℝ) ^ 2 * Δ ^ 2)
              = (4 / ((T : ℝ) * Δ)) ^ 2 from by
            rw [div_pow]; congr 1 <;> ring,
            Real.sqrt_sq (div_nonneg (by norm_num)
              (mul_nonneg hT0.le hΔ.le))]
  have htotal := sqrt_qNormSq_add_le
    ((uniformDetector P α T).run (read x)
        *ᵥ uniformClock T (uniformNear P α Δ x)
      + uniformClock T (uniformNear P α Δ x))
    ((uniformDetector P α T).run (read x)
        *ᵥ uniformClock T (uniformFar P α Δ x)
      + uniformClock T (uniformFar P α Δ x))
  rw [hsplit]
  linarith [htotal, hnear, hfar]

/-! ## The combined conversion error

The end-to-end error runs the detector on the clocked input-independent
`common` state against the clocked output-labelled target; by linearity it
is `(e₊ + e₋)/√2`.  The two signed errors are **exactly orthogonal**: the
detector is self-adjoint (a reflection conjugated by a unitary) and
unitary, so in

    ⟪e₊, e₋⟫ = ⟪Ds₊, Ds₋⟫ + ⟪Ds₊, s₋⟫ − ⟪s₊, Ds₋⟫ − ⟪s₊, s₋⟫

the outer terms cancel by unitarity and the middle terms by
self-adjointness.  The conversion error is therefore the exact half-sum
`½(‖e₊‖² + ‖e₋‖²)` — a triangle bound here would not support `8192`. -/

/-- **The detector is self-adjoint**, inherited from
`clockPhaseRefl_run_conjTranspose`. -/
theorem uniformDetector_run_conjTranspose (P : DualPairOn read K f) (α : ℝ)
    (T : ℕ) (a : ι → σ) :
    ((uniformDetector P α T).run a)ᴴ = (uniformDetector P α T).run a := by
  rw [uniformDetector_eq]
  exact clockPhaseRefl_run_conjTranspose _ T a

/-- **The two signed errors are orthogonal** — exactly, for every `T` and
`α`. -/
theorem qInner_uniformPlusError_uniformMinusError (P : DualPairOn read K f)
    (α : ℝ) (T : ℕ) (x : X) :
    qInner (uniformPlusError P α T x) (uniformMinusError P α T x) = 0 := by
  let D := (uniformDetector P α T).run (read x)
  let sp := uniformClock T (realizedTPlus (ι := ι) (σ := σ) (K := K) f x)
  let sm := uniformClock T (realizedTMinus (ι := ι) (σ := σ) (K := K) f x)
  have hD : D ∈ Matrix.unitaryGroup
      (QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K))) ℂ :=
    (uniformDetector P α T).run_mem_unitaryGroup (read x)
  have hDH : Dᴴ = D := uniformDetector_run_conjTranspose P α T (read x)
  have h1 : qInner (D *ᵥ sp) (D *ᵥ sm) = qInner sp sm :=
    qInner_mulVec_mulVec hD sp sm
  have h2 : qInner (D *ᵥ sp) sm = qInner sp (D *ᵥ sm) := by
    rw [qInner_mulVec_left, hDH]
  rw [show uniformPlusError P α T x = D *ᵥ sp - sp from rfl,
    show uniformMinusError P α T x = D *ᵥ sm + sm from rfl,
    qInner_sub_left, qInner_add_right, qInner_add_right, h1, h2]
  ring

/-- **The end-to-end conversion error**: the detector applied to the clocked
input-independent common state, against the clocked output-labelled
target. -/
noncomputable def uniformConvError (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) : QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) → ℂ :=
  (uniformDetector P α T).run (read x)
      *ᵥ uniformClock T (realizedCommon (K := K) f)
    - uniformClock T (realizedOut (K := K) f x)

/-- **The conversion error is the scaled sum of the signed errors** — pure
linearity, no hypotheses at all. -/
theorem uniformConvError_eq (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) :
    uniformConvError P α T x
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          (uniformPlusError P α T x + uniformMinusError P α T x) := by
  rw [show uniformConvError P α T x
        = (uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (realizedCommon (K := K) f)
          - uniformClock T (realizedOut (K := K) f x) from rfl,
    realizedCommon_eq_smul (K := K) f x, realizedOut_eq_smul (K := K) f x,
    uniformClock_smul, uniformClock_smul, uniformClock_add,
    uniformClock_sub, Matrix.mulVec_smul, Matrix.mulVec_add,
    show uniformPlusError P α T x
        = (uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (realizedTPlus (K := K) f x)
          - uniformClock T (realizedTPlus (K := K) f x) from rfl,
    show uniformMinusError P α T x
        = (uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (realizedTMinus (K := K) f x)
          + uniformClock T (realizedTMinus (K := K) f x) from rfl]
  module

/-- **The exact half-sum**: with `e₊ ⟂ e₋`,
`‖err‖² = (‖e₊‖² + ‖e₋‖²)/2` — an equality, not a triangle bound. -/
theorem qNormSq_uniformConvError (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) :
    qNormSq (uniformConvError P α T x)
      = (qNormSq (uniformPlusError P α T x)
          + qNormSq (uniformMinusError P α T x)) / 2 := by
  rw [uniformConvError_eq, qNormSq_smul, normSq_inv_sqrt_two, qNormSq_add,
    qInner_uniformPlusError_uniformMinusError P α T x, Complex.zero_re]
  ring

/-- **The combined conversion bound** — the two component estimates through
the exact half-sum; the only statement needing all three parameter
hypotheses. -/
theorem qNormSq_uniformConvError_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) {α : ℝ} (hα : α ≠ 0) {T : ℕ} (hT : 0 < T) {Δ : ℝ}
    (hΔ : 0 < Δ) (x : X) :
    qNormSq (uniformConvError P α T x)
      ≤ (8 * α ^ 2 * c
          + (Δ * Real.sqrt (1 + c / (2 * α ^ 2)) + 4 / ((T : ℝ) * Δ)) ^ 2)
        / 2 := by
  have hplus := qNormSq_uniformPlusError_le P hP α T x
  have hminus : qNormSq (uniformMinusError P α T x)
      ≤ (Δ * Real.sqrt (1 + c / (2 * α ^ 2)) + 4 / ((T : ℝ) * Δ)) ^ 2 := by
    have h := sqrt_qNormSq_uniformMinusError_le P hP hα hT hΔ x
    have h2 := mul_self_le_mul_self (Real.sqrt_nonneg _) h
    rw [Real.mul_self_sqrt (qNormSq_nonneg _), ← pow_two] at h2
    exact h2
  rw [qNormSq_uniformConvError]
  linarith

/-! ## The parameters

With `B = 1 + c`:

    α = (√(128B))⁻¹,   Δ = (64B)⁻¹,   T = ⌈2048B⌉.

Then `8α²c = c/(16B) ≤ 1/16`; the near coefficient `1 + c/(2α²) = 1 + 64cB
≤ 64B²` so the near term is at most `Δ·8B = 1/8`; `TΔ ≥ 2048B/(64B) = 32`
so the far term is at most `1/8`; hence `‖e₋‖² ≤ 1/16` and the combined
squared conversion distance is at most `(1/16 + 1/16)/2 = 1/16` — at
`4(T − 1) ≤ 8192(1 + c)` queries — the
`uniformExtractionConstant`, attained.  Only `Δ` and `α` balance against `c`; the
budget hypothesis is just `0 ≤ c`. -/

/-- The witness scale: `α = (√(128(1+c)))⁻¹`. -/
noncomputable def uniformAlpha (c : ℝ) : ℝ :=
  (Real.sqrt (128 * (1 + c)))⁻¹

/-- The window: `Δ = (64(1+c))⁻¹`. -/
noncomputable def uniformDelta (c : ℝ) : ℝ := (64 * (1 + c))⁻¹

/-- The clock: `T = ⌈2048(1+c)⌉`. -/
noncomputable def uniformT (c : ℝ) : ℕ := ⌈(2048 : ℝ) * (1 + c)⌉₊

lemma uniformAlpha_ne_zero {c : ℝ} (hc : 0 ≤ c) : uniformAlpha c ≠ 0 := by
  rw [uniformAlpha]
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))

lemma uniformAlpha_sq {c : ℝ} (hc : 0 ≤ c) :
    uniformAlpha c ^ 2 = (128 * (1 + c))⁻¹ := by
  rw [uniformAlpha, inv_pow,
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 128 * (1 + c))]

lemma uniformDelta_pos {c : ℝ} (hc : 0 ≤ c) : 0 < uniformDelta c := by
  rw [uniformDelta]
  exact inv_pos.mpr (by linarith)

lemma uniformT_pos {c : ℝ} (hc : 0 ≤ c) : 0 < uniformT c := by
  rw [uniformT]
  exact Nat.ceil_pos.mpr (by linarith)

/-- **The instantiated conversion bound**: at the chosen parameters the
squared conversion distance is at most `1/16`, for every promise input. -/
theorem qNormSq_uniformConvError_le_sixteenth (P : DualPairOn read K f)
    {c : ℝ} (hP : P.IsCostLe c) (hc : 0 ≤ c) (x : X) :
    qNormSq (uniformConvError P (uniformAlpha c) (uniformT c) x)
      ≤ 1 / 16 := by
  have hB0 : (0 : ℝ) < 1 + c := by linarith
  have hα := uniformAlpha_ne_zero hc
  have hαsq := uniformAlpha_sq hc
  have hT := uniformT_pos hc
  have hΔ := uniformDelta_pos hc
  have h := qNormSq_uniformConvError_le P hP hα hT hΔ x
  -- the positive budget: `8α²c = c/(16(1+c)) ≤ 1/16`
  have h1 : 8 * uniformAlpha c ^ 2 * c ≤ 1 / 16 := by
    rw [hαsq, show (8 : ℝ) * (128 * (1 + c))⁻¹ * c
          = 8 * c / (128 * (1 + c)) from by rw [div_eq_mul_inv]; ring,
      div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 16)]
    linarith
  -- the near coefficient: `1 + c/(2α²) = 1 + 64c(1+c) ≤ 64(1+c)²`
  have hval : 1 + c / (2 * uniformAlpha c ^ 2) ≤ 64 * (1 + c) ^ 2 := by
    rw [hαsq, show c / (2 * (128 * (1 + c))⁻¹) = 64 * c * (1 + c) from by
      rw [div_eq_mul_inv, mul_inv, inv_inv]; ring]
    nlinarith
  have hsqrt : Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2))
      ≤ 8 * (1 + c) := by
    calc Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2))
        ≤ Real.sqrt (64 * (1 + c) ^ 2) := Real.sqrt_le_sqrt hval
      _ = 8 * (1 + c) := by
          rw [show (64 : ℝ) * (1 + c) ^ 2 = (8 * (1 + c)) ^ 2 from by ring,
            Real.sqrt_sq (by positivity)]
  -- the near term: `Δ·8(1+c) = 1/8`
  have hnear : uniformDelta c
      * Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2)) ≤ 1 / 8 := by
    have h8 : uniformDelta c * (8 * (1 + c)) = 1 / 8 := by
      rw [uniformDelta, mul_inv, show (64 : ℝ)⁻¹ * (1 + c)⁻¹ * (8 * (1 + c))
          = 64⁻¹ * 8 * ((1 + c)⁻¹ * (1 + c)) from by ring,
        inv_mul_cancel₀ hB0.ne', mul_one]
      norm_num
    calc uniformDelta c * Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2))
        ≤ uniformDelta c * (8 * (1 + c)) :=
          mul_le_mul_of_nonneg_left hsqrt hΔ.le
      _ = 1 / 8 := h8
  -- the far term: `TΔ ≥ 32`
  have hTge : (2048 : ℝ) * (1 + c) ≤ (uniformT c : ℝ) := by
    rw [uniformT]
    exact Nat.le_ceil _
  have hTΔ : (32 : ℝ) ≤ (uniformT c : ℝ) * uniformDelta c := by
    have h32 : (2048 : ℝ) * (1 + c) * uniformDelta c = 32 := by
      rw [uniformDelta, mul_inv, show (2048 : ℝ) * (1 + c)
          * (64⁻¹ * (1 + c)⁻¹) = 2048 * 64⁻¹ * ((1 + c) * (1 + c)⁻¹) from by
        ring, mul_inv_cancel₀ hB0.ne', mul_one]
      norm_num
    calc (32 : ℝ) = 2048 * (1 + c) * uniformDelta c := h32.symm
      _ ≤ (uniformT c : ℝ) * uniformDelta c :=
          mul_le_mul_of_nonneg_right hTge hΔ.le
  have hfar : 4 / ((uniformT c : ℝ) * uniformDelta c) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  -- square the `e₋` budget and combine through the exact half-sum
  have hn0 : 0 ≤ uniformDelta c
      * Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2)) :=
    mul_nonneg hΔ.le (Real.sqrt_nonneg _)
  have hf0 : 0 ≤ 4 / ((uniformT c : ℝ) * uniformDelta c) := by
    have : (0 : ℝ) < (uniformT c : ℝ) * uniformDelta c := by linarith
    positivity
  have hsq : (uniformDelta c * Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2))
      + 4 / ((uniformT c : ℝ) * uniformDelta c)) ^ 2 ≤ 1 / 16 := by
    nlinarith [hnear, hfar, hn0, hf0]
  linarith

/-- **The detector at the chosen clock stays within the acceptance
budget**: `4(T − 1) ≤ 8192(1 + c)` — the
`uniformExtractionConstant` is attained. -/
theorem uniformDetector_len_uniformT_le (P : DualPairOn read K f) (α : ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    ((uniformDetector P α (uniformT c)).len : ℝ) ≤ 8192 * (1 + c) := by
  have hT : 0 < uniformT c := uniformT_pos hc
  have hceil : ((uniformT c : ℕ) : ℝ) < 2048 * (1 + c) + 1 := by
    rw [uniformT]
    exact Nat.ceil_lt_add_one (by linarith)
  rw [uniformDetector_len, Nat.cast_mul, Nat.cast_sub hT]
  push_cast
  linarith

end QuantumQueryComplexity

end SourceQuantumUniformConversion

section SourceQuantumUniformExtraction

/-!
# The uniform extraction

The packaging of the cardinality-free construction: the detector run on the
clocked input-independent `common` state, with the readout announcing the
label held in the target register, is an algorithm computing `f` on the
promise with error `1/16` — within `8192(1 + c)` queries.

The acceptance statement `exists_algorithm_of_dualPairOn_uniform` has the
required scope, every clause load-bearing:

* arbitrary **decidable** output `O`, no `[Fintype O]`;
* `uniformExtractionConstant = 8192`, one fixed absolute constant —
  independent of `|σ|`, `|O|`, `|range f|`;
* `[Nonempty O]` (the readout needs a junk label off the target register)
  and `0 ≤ c` are genuine hypotheses;
* promise-native, and no appeal to general-output strong duality.

The correctness chain is three moves: the algorithm's final state is
`D·clock(common)`, which is within squared distance `1/16` of
`clock(out(f x))` (`qNormSq_uniformConvError_le_sixteenth`); the clocked
output state announces `f x` **surely** (its support carries the label in
the target register — `realizedOut_apply_of_ne` through
`uniformClock_apply_eq_zero`); and the distance-to-success bridge
(`le_qProb_of_qNormSq_sub_le`, output-cardinality-free by design) converts
the distance into the success probability `≥ 1 − 1/16`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ K X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq O]
  {read : X → ι → σ} {f : X → O}

/-- **The uniform extraction constant** — one fixed absolute constant, never
a free variable. -/
@[expose]
def uniformExtractionConstant : ℝ := 8192

/-! ## The readout -/

/-- The label of one workspace coordinate: the output held in the target
register, or the junk label `o₀` anywhere else. -/
@[expose]
def uniformLabel (f : X → O) (o₀ : O) :
    UWork ↥(Set.range f) ι K → O
  | Sum.inl (some r) => (r : O)
  | Sum.inl none => o₀
  | Sum.inr _ => o₀

omit [DecidableEq K] [DecidableEq O] [DecidableEq ι] [Fintype K] [Fintype X] [Fintype ι] in
@[simp] lemma uniformLabel_inl_some (f : X → O) (o₀ : O)
    (r : ↥(Set.range f)) :
    uniformLabel (ι := ι) (K := K) f o₀ (Sum.inl (some r)) = (r : O) := rfl

/-- **The readout**: announce the label held in the target register of the
clocked workspace. -/
def uniformReadout (f : X → O) (o₀ : O) (T : ℕ) :
    QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) → O :=
  fun b => uniformLabel f o₀ b.2.2.2.2.2

omit [DecidableEq K] [DecidableEq O] [DecidableEq ι] [DecidableEq σ] [Fintype K] [Fintype X]
    [Fintype ι] [Fintype σ] in
lemma uniformReadout_apply (f : X → O) (o₀ : O) (T : ℕ)
    (b : QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K))) :
    uniformReadout f o₀ T b = uniformLabel f o₀ b.2.2.2.2.2 := by
  classical
  exact rfl

omit [DecidableEq K] [DecidableEq σ] [Fintype K] [Fintype X] [Fintype ι] [Fintype σ] in
/-- **The clocked output state announces its label surely**: it is its own
restriction to the `f x`-sector of the readout. -/
theorem qRestrict_uniformClock_realizedOut (o₀ : O) (T : ℕ) (x : X) :
    qRestrict (uniformReadout (ι := ι) (σ := σ) (K := K) f o₀ T) (f x)
        (uniformClock T (realizedOut (K := K) f x))
      = uniformClock T (realizedOut (K := K) f x) := by
  classical
  funext b
  rw [qRestrict]
  by_cases hb : uniformReadout (ι := ι) (σ := σ) (K := K) f o₀ T b = f x
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb]
    refine ((uniformClock_apply_eq_zero T _ ?_)).symm
    refine realizedOut_apply_of_ne f x ?_
    intro hw
    apply hb
    rw [uniformReadout_apply, hw, uniformLabel_inl_some, rangeElem_val]

/-! ## The algorithm -/

/-- **The uniform extraction algorithm**: prepare the clocked common state,
run the detector, read the target register. -/
noncomputable def uniformAlg (P : DualPairOn read K f) (α : ℝ) (o₀ : O)
    (T : ℕ) (hT : 0 < T) :
    QAlg ι σ O (ClockWork ι T (UWork ↥(Set.range f) ι K)) :=
  (uniformDetector P α T).toAlg
    (uniformClock T (realizedCommon (K := K) f))
    (by rw [IsQState, qNormSq_uniformClock hT, qNormSq_realizedCommon])
    (uniformReadout f o₀ T)

/-- **The uniform algorithm computes `f`** at the chosen parameters: error
`1/16` on the promise, in exactly `4(T − 1)` queries. -/
theorem uniformAlg_computes (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) (hc : 0 ≤ c) (o₀ : O) :
    ComputesWithErrorOn
      (uniformAlg P (uniformAlpha c) o₀ (uniformT c) (uniformT_pos hc))
      (4 * (uniformT c - 1)) read f (1 / 16) := by
  intro x
  have hT : 0 < uniformT c := uniformT_pos hc
  -- the final state is the detector on the clocked common state
  have hlen : (uniformDetector P (uniformAlpha c) (uniformT c)).len
      = 4 * (uniformT c - 1) := uniformDetector_len P (uniformAlpha c) _
  have hstate : (uniformAlg P (uniformAlpha c) o₀ (uniformT c) hT).state
        (read x) (4 * (uniformT c - 1))
      = (uniformDetector P (uniformAlpha c) (uniformT c)).run (read x)
          *ᵥ uniformClock (uniformT c) (realizedCommon (K := K) f) := by
    rw [uniformAlg, ← hlen]
    exact QRoutine.toAlg_state_len _ _ _ _ _
  -- it is within squared distance 1/16 of the clocked output state
  have hdist : qNormSq ((uniformAlg P (uniformAlpha c) o₀ (uniformT c)
          hT).state (read x) (4 * (uniformT c - 1))
        - uniformClock (uniformT c) (realizedOut (K := K) f x))
      ≤ 1 / 16 := by
    rw [hstate]
    exact qNormSq_uniformConvError_le_sixteenth P hP hc x
  -- the final state is a unit vector
  have hone : qNormSq ((uniformAlg P (uniformAlpha c) o₀ (uniformT c)
        hT).state (read x) (4 * (uniformT c - 1))) = 1 :=
    (uniformAlg P (uniformAlpha c) o₀ (uniformT c) hT).state_isQState
      (read x) _
  -- the bridge to the announced probability
  have hbridge := le_qProb_of_qNormSq_sub_le
    (uniformReadout (ι := ι) (σ := σ) (K := K) f o₀ (uniformT c)) (f x)
    (qRestrict_uniformClock_realizedOut (K := K) o₀ (uniformT c) x) hdist
  have hgoal : 1 - 1 / 16
      ≤ qProb (uniformReadout (ι := ι) (σ := σ) (K := K) f o₀ (uniformT c))
          ((uniformAlg P (uniformAlpha c) o₀ (uniformT c) hT).state (read x)
            (4 * (uniformT c - 1))) (f x) := by
    linarith
  exact hgoal

/-! ## The acceptance statement -/

omit [DecidableEq K] in
/-- **A dual solution is an algorithm, with no cardinality anywhere**: cost
`c` yields error `1/16` within `uniformExtractionConstant·(1 + c)` queries —
independent of `|σ|`, `|O|` and `|range f|`, for any decidable output type. -/
theorem exists_algorithm_of_dualPairOn_uniform [Nonempty O]
    (P : DualPairOn read K f) {c : ℝ} (hP : P.IsCostLe c) (hc : 0 ≤ c) :
    ∃ q ∈ QueryCounts read f (1 / 16),
      (q : ℝ) ≤ uniformExtractionConstant * (1 + c) := by
  classical
  obtain ⟨o₀⟩ := (inferInstance : Nonempty O)
  refine ⟨4 * (uniformT c - 1),
    mem_queryCounts (uniformAlg_computes P hP hc o₀), ?_⟩
  have h := uniformDetector_len_uniformT_le P (uniformAlpha c) hc
  rw [uniformDetector_len] at h
  rw [uniformExtractionConstant]
  exact h

end QuantumQueryComplexity

end SourceQuantumUniformExtraction

section SourceQuantumUpperBound

/-!
# The dual-to-algorithm upper bound

The extraction: a feasible `DualPairOn read K f` for a **Boolean** `f` becomes
a quantum query algorithm.  The algorithm is nothing but the Hadamard test of
the `o = true` detector on the target state,

    scAlg = hadTest (scDetector read f P true T) (uniformClock T scTarget),

at exactly `4(T−1)` queries, and its correctness is the two acceptance
estimates of `SourceQuantumDetection` pushed through `hadTest_prob_true/false`:

* `scAlg_computes` — the **parametric** correctness: any `(T, Δ, cu, cv, ε)`
  satisfying the two explicit inequalities gives
  `ComputesWithErrorOn (scAlg …) (4(T−1)) read f ε`;
* `exists_algorithm_of_dualPairOn` — the **endgame**: a dual of cost `c > 0`
  is compiled, after the `scale` balancing `α² = (16|σ|c)⁻¹` and the choices
  `Δ = (16√B)⁻¹`, `T = ⌈2048√B⌉` for `B = 1 + 16|σ|c²`, into membership

      4(T−1) ∈ QueryCounts read f (1/16),   4(T−1) ≤ 8192·(1 + 4√|σ|·c),

  with the `qQueryOn` corollary `qQueryOn_le_of_dualPairOn`.  For a Boolean
  alphabet `√|σ| = √2`, so the bound is `O(c)` with an explicit constant.

The error budget of the endgame, for the record: positive side
`s·cu = (|σ|−1)/(16|σ|) ≤ 1/16`, so the acceptance is at least
`1/(1 + 1/16) = 16/17 ≥ 15/16`; negative side
`1/64 + 1/64 + 1/2048 = 65/2048 ≤ 1/16`.  Nothing is tight — the constants
are chosen round, not small.

The output convention: `scAlg` announces `true` on constructive interference
(control `0`), which is the `f x = true` side because `scKer read f P true`
spans the positive witnesses of `f⁻¹(true)`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ X K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

variable (read : X → ι → σ) (f : X → Bool)

omit [DecidableEq K] [DecidableEq σ] in
lemma isQState_uniformClock_scTarget {T : ℕ} (hT : 0 < T) :
    IsQState (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ)) := by
  classical
  rw [IsQState, qNormSq_uniformClock hT, qNormSq_scTarget]

/-- **The extracted algorithm**: the Hadamard test of the `o = true` detector
on the target state.  Cost: exactly `4(T−1)` queries. -/
noncomputable def scAlg (P : DualPairOn read K f) (T : ℕ) (hT : 0 < T) :
    QAlg ι σ Bool (CtrlWork ι (ClockWork ι T (Option K))) :=
  hadTest (scDetector read f P true T) (uniformClock T scTarget)
    (isQState_uniformClock_scTarget hT)

omit [DecidableEq X] in
/-- **Parametric correctness of the extracted algorithm.**  The two
hypotheses are exactly the two acceptance estimates' final forms; any
parameter choice satisfying them gives a bounded-error algorithm. -/
theorem scAlg_computes [Nonempty σ] (P : DualPairOn read K f)
    {T : ℕ} (hT : 0 < T) {Δ : ℝ} (hΔ : 0 < Δ) {cu cv ε : ℝ}
    (hcu : ∀ x, ∑ i, ∑ k, P.u x i k * P.u x i k ≤ cu)
    (hcv : ∀ y, ∑ i, ∑ k, P.v y i k * P.v y i k ≤ cv)
    (hpos : 1 - ε ≤ 1 / (1 + ((Fintype.card σ : ℝ) - 1) * cu))
    (hneg : Δ / 4 * Real.sqrt (1 + cv) + 2 / ((T : ℝ) * Δ)
      + Δ ^ 2 / 8 * (1 + cv) ≤ ε) :
    ComputesWithErrorOn (scAlg read f P T hT) (4 * (T - 1)) read f ε := by
  classical
  intro x
  have hlen : (scDetector read f P true T).len = 4 * (T - 1) :=
    scDetector_len read f P true T
  rw [scAlg, ← hlen]
  cases hfx : f x with
  | true =>
      rw [hadTest_prob_true]
      have hRe := le_re_qInner_scDetector_of_eq read f P hfx hT (hcu x)
      have hb : 2 / (1 + ((Fintype.card σ : ℝ) - 1) * cu)
          = 2 * (1 / (1 + ((Fintype.card σ : ℝ) - 1) * cu)) := by ring
      linarith [hRe, hpos, hb]
  | false =>
      rw [hadTest_prob_false]
      have hRe := re_qInner_scDetector_le_of_ne read f P
        (show f x ≠ true by simp [hfx]) hT hΔ (hcv x)
      have hb1 : Δ / 2 * Real.sqrt (1 + cv)
          = 2 * (Δ / 4 * Real.sqrt (1 + cv)) := by ring
      have hb2 : (4 : ℝ) / ((T : ℝ) * Δ) = 2 * (2 / ((T : ℝ) * Δ)) := by ring
      have hb3 : Δ ^ 2 / 4 * (1 + cv) = 2 * (Δ ^ 2 / 8 * (1 + cv)) := by ring
      linarith [hRe, hneg, hb1, hb2, hb3]

/-! ## The endgame: choosing the parameters

Balance with `α² = (16|σ|c)⁻¹`, detect at radius `Δ = (16√B)⁻¹` with clock
`T = ⌈2048√B⌉`, where `B = 1 + 16|σ|c²`. -/

section Endgame

variable [Nonempty σ]

omit [DecidableEq σ] in
private lemma card_pos : (0 : ℝ) < (Fintype.card σ : ℝ) := by
  exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty σ›

omit [DecidableEq K] [DecidableEq X] in
/-- **A dual solution of cost `c` is an algorithm**: error `1/16`, at most
`8192(1 + 4√|σ|·c)` queries. -/
theorem exists_algorithm_of_dualPairOn {c : ℝ} (P : DualPairOn read K f)
    (hP : P.IsCostLe c) (hc : 0 < c) :
    ∃ q ∈ QueryCounts read f (1 / 16),
      (q : ℝ) ≤ 8192 * (1 + 4 * Real.sqrt (Fintype.card σ) * c) := by
  classical
  have hσ : (0 : ℝ) < (Fintype.card σ : ℝ) := card_pos (σ := σ)
  -- the balancing scale
  set z : ℝ := 16 * (Fintype.card σ : ℝ) * c with hz
  have hz0 : 0 < z := by positivity
  have hα0 : Real.sqrt z ≠ 0 := by
    positivity
  set Q : DualPairOn read K f := P.scale (α := (Real.sqrt z)⁻¹)
    (inv_ne_zero hα0) with hQ
  have hαsq : ((Real.sqrt z)⁻¹) ^ 2 = z⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hz0.le]
  -- the balanced masses
  have hcu : ∀ x, ∑ i, ∑ k, Q.u x i k * Q.u x i k
      ≤ (16 * (Fintype.card σ : ℝ))⁻¹ := by
    intro x
    rw [hQ, DualPairOn.scale_u_mass, hαsq]
    have h1 : z⁻¹ * (∑ i, ∑ k, P.u x i k * P.u x i k) ≤ z⁻¹ * c :=
      mul_le_mul_of_nonneg_left (hP.1 x) (by positivity)
    calc z⁻¹ * (∑ i, ∑ k, P.u x i k * P.u x i k) ≤ z⁻¹ * c := h1
      _ = (16 * (Fintype.card σ : ℝ))⁻¹ := by
          rw [hz]
          field_simp
  have hcv : ∀ y, ∑ i, ∑ k, Q.v y i k * Q.v y i k
      ≤ 16 * (Fintype.card σ : ℝ) * c ^ 2 := by
    intro y
    rw [hQ, DualPairOn.scale_v_mass, inv_inv, Real.sq_sqrt hz0.le]
    have h1 : z * (∑ i, ∑ k, P.v y i k * P.v y i k) ≤ z * c :=
      mul_le_mul_of_nonneg_left (hP.2 y) hz0.le
    calc z * (∑ i, ∑ k, P.v y i k * P.v y i k) ≤ z * c := h1
      _ = 16 * (Fintype.card σ : ℝ) * c ^ 2 := by rw [hz]; ring
  -- the detection parameters
  set B : ℝ := 1 + 16 * (Fintype.card σ : ℝ) * c ^ 2 with hB
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hB]
    nlinarith [hσ, sq_nonneg c]
  have hBs1 : (1 : ℝ) ≤ Real.sqrt B := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hB1
  have hBs0 : (0 : ℝ) < Real.sqrt B := lt_of_lt_of_le one_pos hBs1
  set T : ℕ := ⌈(2048 : ℝ) * Real.sqrt B⌉₊ with hTdef
  have hT : 0 < T := by
    rw [hTdef]
    exact Nat.ceil_pos.mpr (by positivity)
  have hTge : (2048 : ℝ) * Real.sqrt B ≤ (T : ℝ) := by
    rw [hTdef]; exact Nat.le_ceil _
  have hTle : (T : ℝ) ≤ 2048 * Real.sqrt B + 1 := by
    rw [hTdef]
    exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
  set Δ : ℝ := (16 * Real.sqrt B)⁻¹ with hΔdef
  have hΔ : 0 < Δ := by rw [hΔdef]; positivity
  -- the two error-budget inequalities
  have hpos : 1 - (1 / 16 : ℝ)
      ≤ 1 / (1 + ((Fintype.card σ : ℝ) - 1) * (16 * (Fintype.card σ : ℝ))⁻¹) := by
    have hle : ((Fintype.card σ : ℝ) - 1) * (16 * (Fintype.card σ : ℝ))⁻¹
        ≤ 1 / 16 := by
      rw [div_eq_mul_inv, show ((Fintype.card σ : ℝ) - 1)
          * (16 * (Fintype.card σ : ℝ))⁻¹
          = (((Fintype.card σ : ℝ) - 1) / (Fintype.card σ : ℝ)) * 16⁻¹ from by
        rw [mul_inv]; ring]
      have h2 : ((Fintype.card σ : ℝ) - 1) / (Fintype.card σ : ℝ) ≤ 1 := by
        rw [div_le_one hσ]; linarith
      nlinarith [h2]
    have hden : (0 : ℝ) < 1 + ((Fintype.card σ : ℝ) - 1)
        * (16 * (Fintype.card σ : ℝ))⁻¹ := by
      have h0 : (0 : ℝ) ≤ ((Fintype.card σ : ℝ) - 1)
          * (16 * (Fintype.card σ : ℝ))⁻¹ := by
        have h1 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by
          exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty σ›
        have : (0 : ℝ) ≤ (Fintype.card σ : ℝ) - 1 := by linarith
        positivity
      linarith
    rw [le_div_iff₀ hden]
    nlinarith [hle]
  have hsqB : Real.sqrt B * Real.sqrt B = B :=
    Real.mul_self_sqrt (by linarith)
  have hneg : Δ / 4 * Real.sqrt (1 + 16 * (Fintype.card σ : ℝ) * c ^ 2)
      + 2 / ((T : ℝ) * Δ) + Δ ^ 2 / 8
        * (1 + 16 * (Fintype.card σ : ℝ) * c ^ 2) ≤ 1 / 16 := by
    rw [← hB]
    have e1 : Δ / 4 * Real.sqrt B = 1 / 64 := by
      rw [hΔdef]
      field_simp
      linarith [hsqB]
    have e2 : Δ ^ 2 / 8 * B = 1 / 2048 := by
      rw [hΔdef, inv_pow, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ B)]
      rw [show ((16 : ℝ) ^ 2 * B)⁻¹ / 8 * B = B / B * (2048 : ℝ)⁻¹ from by
        rw [mul_inv]; ring]
      rw [div_self (by linarith : B ≠ 0)]
      norm_num
    have e3 : 2 / ((T : ℝ) * Δ) ≤ 1 / 64 := by
      have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
      have hTΔval : (T : ℝ) * Δ = (T : ℝ) / (16 * Real.sqrt B) := by
        rw [hΔdef, div_eq_mul_inv]
      rw [hTΔval, div_div_eq_mul_div,
        div_le_div_iff₀ hT0 (by norm_num : (0 : ℝ) < 64)]
      calc 2 * (16 * Real.sqrt B) * 64 = 2048 * Real.sqrt B := by ring
        _ ≤ (T : ℝ) := hTge
        _ = 1 * (T : ℝ) := (one_mul _).symm
    linarith [e1, e2, e3]
  -- assemble
  have halg := scAlg_computes read f Q hT hΔ hcu hcv hpos hneg
  refine ⟨4 * (T - 1), mem_queryCounts halg, ?_⟩
  -- the query count, bounded
  have hT1 : ((4 * (T - 1) : ℕ) : ℝ) = 4 * ((T : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hT]
    norm_num
  have hBle : Real.sqrt B ≤ 1 + 4 * Real.sqrt (Fintype.card σ) * c := by
    have hsq : B ≤ (1 + 4 * Real.sqrt (Fintype.card σ) * c) ^ 2 := by
      have hs : Real.sqrt (Fintype.card σ) * Real.sqrt (Fintype.card σ)
          = (Fintype.card σ : ℝ) := Real.mul_self_sqrt hσ.le
      have hs0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_nonneg _
      rw [hB]
      nlinarith [hs, hs0, hc.le]
    calc Real.sqrt B ≤ Real.sqrt ((1 + 4 * Real.sqrt (Fintype.card σ) * c) ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = 1 + 4 * Real.sqrt (Fintype.card σ) * c := by
          rw [Real.sqrt_sq (by positivity)]
  rw [hT1]
  calc 4 * ((T : ℝ) - 1) ≤ 4 * (2048 * Real.sqrt B) := by linarith [hTle]
    _ = 8192 * Real.sqrt B := by ring
    _ ≤ 8192 * (1 + 4 * Real.sqrt (Fintype.card σ) * c) := by linarith [hBle]

omit [DecidableEq K] [DecidableEq X] in
/-- **The `qQueryOn` corollary**: `Q_{1/16}(f) ≤ 8192(1 + 4√|σ|·c)` for any
dual of cost `c`. -/
theorem qQueryOn_le_of_dualPairOn {c : ℝ} (P : DualPairOn read K f)
    (hP : P.IsCostLe c) (hc : 0 < c) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 8192 * (1 + 4 * Real.sqrt (Fintype.card σ) * c) := by
  classical
  obtain ⟨q, hq, hqle⟩ := exists_algorithm_of_dualPairOn read f P hP hc
  have h1 : qQueryOn read f (1 / 16) ≤ q := Nat.sInf_le hq
  have h2 : (qQueryOn read f (1 / 16) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  linarith [h2, hqle]

end Endgame

end QuantumQueryComplexity

end SourceQuantumUpperBound

section SourceQuantumUniformHasDual

/-!
# Uniform extraction: the `HasDualOn` wrappers

The bundled form of the cardinality-free extraction.  `HasDualOn` hides the
dual dimension type and is defined in `SourcePromiseHasDual` in `Adversary`.
These wrappers connect it to the operational constructions in `StateConversion`.

Both wrappers are one destructuring away from
`exists_algorithm_of_dualPairOn_uniform`: any bundled dual solution of cost
`c` gives `Q_{1/16}(f) ≤ 8192(1 + c)`, and `Q_{1/3}` by error
monotonicity — for **any decidable output type**, with no `|σ|`, `|O|` or
`|range f|` anywhere.
-/

namespace QuantumQueryComplexity

variable {ι σ X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype X] [DecidableEq O]
  {read : X → ι → σ} {f : X → O}

/-- **Cardinality-free extraction from a bundled dual**:
`Q_{1/16}(f) ≤ 8192(1 + c)` for any decidable output type. -/
theorem qQueryOn_le_of_hasDualOn_uniform [Nonempty O] {c : ℝ}
    (h : HasDualOn read f c) (hc : 0 ≤ c) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ uniformExtractionConstant * (1 + c) := by
  obtain ⟨K, hK, P, hP⟩ := h
  let _ := hK
  let _ := Classical.decEq K
  obtain ⟨q, hq, hqle⟩ := exists_algorithm_of_dualPairOn_uniform P hP hc
  have h1 : qQueryOn read f (1 / 16) ≤ q := Nat.sInf_le hq
  have h2 : (qQueryOn read f (1 / 16) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  linarith

/-- The bounded-error form, by error monotonicity. -/
theorem qQueryOn_third_le_of_hasDualOn_uniform [Nonempty O] {c : ℝ}
    (h : HasDualOn read f c) (hc : 0 ≤ c) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + c) := by
  obtain ⟨K, hK, P, hP⟩ := h
  let _ := hK
  let _ := Classical.decEq K
  obtain ⟨q, hq, hqle⟩ := exists_algorithm_of_dualPairOn_uniform P hP hc
  have h1 : qQueryOn read f (1 / 3) ≤ q :=
    Nat.sInf_le (queryCounts_mono (by norm_num) hq)
  have h2 : (qQueryOn read f (1 / 3) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  linarith

end QuantumQueryComplexity

end SourceQuantumUniformHasDual
