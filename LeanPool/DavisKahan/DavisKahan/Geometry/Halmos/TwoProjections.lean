/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Halmos two-projection decomposition

This file develops the operator-valued form of Halmos' two-subspace theorem.
For two orthogonally complemented complex Hilbert subspaces `U` and `V`, the
ambient space splits into four elementary intersection summands and the
orthogonal generic remainder.  Both orthogonal projections reduce the generic
remainder.

The associated positive cosine and sine squares are

`C² = P Q P + Pᗮ Qᗮ Pᗮ`,
`S² = P Qᗮ P + Pᗮ Q Pᗮ = (P - Q)²`,

and satisfy `C² + S² = 1`.  The positive square root of `C²` is the modulus of
the canonical intertwiner `QP + QᗮPᗮ`.

The later scalar direct-integral presentation is obtained by applying the
spectral theorem to the positive cosine on the generic summand.  Keeping the
geometric decomposition and the operator algebra separate avoids duplicating
the two-projection argument.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

section RCLikeGeometry

/-! ## Complemented intersections and orthogonal sums -/

/-- The intersection of two orthogonally complemented subspaces again admits
an orthogonal projection. -/
noncomputable instance instHasOrthogonalProjectionInf
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : (K ⊓ L).HasOrthogonalProjection := by
  have hKclosed : IsClosed (K : Set H) :=
    K.isComplete_coe_of_hasOrthogonalProjection.isClosed
  have hLclosed : IsClosed (L : Set H) :=
    L.isComplete_coe_of_hasOrthogonalProjection.isClosed
  have hclosed : IsClosed (((K ⊓ L : Submodule 𝕜 H) : Set H)) := by
    change IsClosed ((K : Set H) ∩ (L : Set H))
    exact hKclosed.inter hLclosed
  let : CompleteSpace ↥(K ⊓ L) := hclosed.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace (K ⊓ L)

omit [CompleteSpace H] in
/-- An orthogonal sum of complemented subspaces is complemented. -/
theorem hasOrthogonalProjection_sup_of_le_orthogonal
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (hKL : K ≤ Lᗮ) :
    (K ⊔ L).HasOrthogonalProjection := by
  refine ⟨?_⟩
  intro x
  obtain ⟨k, hk, hxk⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal (K := K) x
  obtain ⟨l, hl, hrl⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal (K := L) (x - k)
  have hlK : l ∈ Kᗮ := by
    intro y hy
    exact inner_eq_zero_symm.mp (hKL hy l hl)
  have hrK : x - k - l ∈ Kᗮ := Kᗮ.sub_mem hxk hlK
  refine ⟨k + l, Submodule.mem_sup.mpr ⟨k, hk, l, hl, rfl⟩, ?_⟩
  have hres : x - (k + l) = x - k - l := by abel
  rw [hres, Submodule.mem_orthogonal]
  intro y hy
  rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, rfl⟩
  rw [inner_add_left, hrK a ha, hrl b hb, zero_add]

omit [CompleteSpace H] in
/-- Membership in the orthogonal complement of a span is tested on the spanning
set alone.

A general inner-product fact, kept here because the Halmos development
repeatedly cuts subspaces out of an orthonormal family by a condition on the
index set and then has to recognize the complement. -/
theorem mem_orthogonal_span {S : Set H} {x : H} :
    x ∈ (Submodule.span 𝕜 S)ᗮ ↔ ∀ y ∈ S, ⟪y, x⟫_𝕜 = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h y hy
    exact h y (Submodule.subset_span hy)
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => exact inner_zero_left x
    | add a c _ _ ha hc => rw [inner_add_left, ha, hc, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]


/-! ## Elementary and generic Halmos summands -/

/-- `U ∩ V`. -/
noncomputable abbrev halmosCommonPart (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  U ⊓ V

/-- `U ∩ Vᗮ`. -/
noncomputable abbrev halmosSourceDefect (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  U ⊓ Vᗮ

/-- `Uᗮ ∩ V`. -/
noncomputable abbrev halmosTargetDefect (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  Uᗮ ⊓ V

/-- `Uᗮ ∩ Vᗮ`. -/
noncomputable abbrev halmosExteriorPart (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  Uᗮ ⊓ Vᗮ

/-- The sum of the four elementary Halmos summands. -/
noncomputable abbrev halmosTrivialPart (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  (halmosCommonPart U V ⊔ halmosSourceDefect U V) ⊔
    (halmosTargetDefect U V ⊔ halmosExteriorPart U V)

/-- The generic Halmos remainder. -/
noncomputable abbrev halmosGenericPart (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  (halmosTrivialPart U V)ᗮ

omit [CompleteSpace H] in
/-- **Complementing the second subspace permutes the four elementary summands**, so it
leaves their sum — and hence the generic remainder — unchanged.  `U ⊓ V` swaps with
`U ⊓ Vᗮ`, and `Uᗮ ⊓ V` with `Uᗮ ⊓ Vᗮ`.

This is the subspace-level counterpart of the multiplicity-level statement used by
Corollary 3.1's defect-block form. -/
theorem halmosTrivialPart_orthogonal_right (U V : Submodule 𝕜 H)
    [V.HasOrthogonalProjection] :
    halmosTrivialPart U Vᗮ = halmosTrivialPart U V := by
  change (U ⊓ Vᗮ ⊔ U ⊓ Vᗮᗮ) ⊔ (Uᗮ ⊓ Vᗮ ⊔ Uᗮ ⊓ Vᗮᗮ) =
    (U ⊓ V ⊔ U ⊓ Vᗮ) ⊔ (Uᗮ ⊓ V ⊔ Uᗮ ⊓ Vᗮ)
  rw [Submodule.orthogonal_orthogonal V, sup_comm (U ⊓ Vᗮ) (U ⊓ V),
    sup_comm (Uᗮ ⊓ Vᗮ) (Uᗮ ⊓ V)]

omit [CompleteSpace H] in
/-- The generic Halmos remainder is unchanged by complementing the second subspace. -/
theorem halmosGenericPart_orthogonal_right (U V : Submodule 𝕜 H)
    [V.HasOrthogonalProjection] :
    halmosGenericPart U Vᗮ = halmosGenericPart U V := by
  change (halmosTrivialPart U Vᗮ)ᗮ = (halmosTrivialPart U V)ᗮ
  rw [halmosTrivialPart_orthogonal_right U V]

/-- The common part `U ⊓ V` is orthogonally complemented. -/
noncomputable instance instHasOrthogonalProjectionHalmosCommonPart
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (halmosCommonPart U V).HasOrthogonalProjection := by
  change (U ⊓ V).HasOrthogonalProjection
  infer_instance

/-- The source defect `U ⊓ Vᗮ` is orthogonally complemented. -/
noncomputable instance instHasOrthogonalProjectionHalmosSourceDefect
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (halmosSourceDefect U V).HasOrthogonalProjection := by
  change (U ⊓ Vᗮ).HasOrthogonalProjection
  infer_instance

/-- The target defect `Uᗮ ⊓ V` is orthogonally complemented. -/
noncomputable instance instHasOrthogonalProjectionHalmosTargetDefect
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (halmosTargetDefect U V).HasOrthogonalProjection := by
  change (Uᗮ ⊓ V).HasOrthogonalProjection
  infer_instance

/-- The exterior part `Uᗮ ⊓ Vᗮ` is orthogonally complemented.  These four
instances are what let the elementary summands carry projections of their own,
which the decomposition argument then adds up. -/
noncomputable instance instHasOrthogonalProjectionHalmosExteriorPart
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (halmosExteriorPart U V).HasOrthogonalProjection := by
  change (Uᗮ ⊓ Vᗮ).HasOrthogonalProjection
  infer_instance

omit [CompleteSpace H] in
/-- The common part is where both subspaces meet. -/
@[simp]
theorem mem_halmosCommonPart {U V : Submodule 𝕜 H} {x : H} :
    x ∈ halmosCommonPart U V ↔ x ∈ U ∧ x ∈ V := Iff.rfl

omit [CompleteSpace H] in
/-- The source defect is the part of `U` missed by `V`. -/
@[simp]
theorem mem_halmosSourceDefect {U V : Submodule 𝕜 H} {x : H} :
    x ∈ halmosSourceDefect U V ↔ x ∈ U ∧ x ∈ Vᗮ := Iff.rfl

omit [CompleteSpace H] in
/-- The target defect is the part of `V` missed by `U`. -/
@[simp]
theorem mem_halmosTargetDefect {U V : Submodule 𝕜 H} {x : H} :
    x ∈ halmosTargetDefect U V ↔ x ∈ Uᗮ ∧ x ∈ V := Iff.rfl

omit [CompleteSpace H] in
/-- The exterior part is where neither subspace reaches.  With the previous
three, these are the four *elementary* summands on which both projections act as
`0` or `1`; everything nontrivial happens on the generic remainder. -/
@[simp]
theorem mem_halmosExteriorPart {U V : Submodule 𝕜 H} {x : H} :
    x ∈ halmosExteriorPart U V ↔ x ∈ Uᗮ ∧ x ∈ Vᗮ := Iff.rfl

omit [CompleteSpace H] in
/-- Projection values on the common Halmos summand. -/
theorem projections_apply_of_mem_halmosCommonPart
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H} (hx : x ∈ halmosCommonPart U V) :
    U.starProjection x = x ∧ V.starProjection x = x :=
  ⟨U.starProjection_eq_self_iff.mpr hx.1,
    V.starProjection_eq_self_iff.mpr hx.2⟩

omit [CompleteSpace H] in
/-- Projection values on the source-defect Halmos summand. -/
theorem projections_apply_of_mem_halmosSourceDefect
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H} (hx : x ∈ halmosSourceDefect U V) :
    U.starProjection x = x ∧ V.starProjection x = 0 :=
  ⟨U.starProjection_eq_self_iff.mpr hx.1,
    (Submodule.starProjection_apply_eq_zero_iff V).mpr hx.2⟩

omit [CompleteSpace H] in
/-- Projection values on the target-defect Halmos summand. -/
theorem projections_apply_of_mem_halmosTargetDefect
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H} (hx : x ∈ halmosTargetDefect U V) :
    U.starProjection x = 0 ∧ V.starProjection x = x :=
  ⟨(Submodule.starProjection_apply_eq_zero_iff U).mpr hx.1,
    V.starProjection_eq_self_iff.mpr hx.2⟩

omit [CompleteSpace H] in
/-- Projection values on the exterior Halmos summand. -/
theorem projections_apply_of_mem_halmosExteriorPart
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H} (hx : x ∈ halmosExteriorPart U V) :
    U.starProjection x = 0 ∧ V.starProjection x = 0 :=
  ⟨(Submodule.starProjection_apply_eq_zero_iff U).mpr hx.1,
    (Submodule.starProjection_apply_eq_zero_iff V).mpr hx.2⟩

omit [CompleteSpace H] in
/-- The common and source-defect pieces are orthogonal. -/
theorem halmosCommon_le_sourceDefect_orthogonal
    (U V : Submodule 𝕜 H) :
    halmosCommonPart U V ≤ (halmosSourceDefect U V)ᗮ := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (hy.2 x hx.2)

omit [CompleteSpace H] in
/-- The common and target-defect pieces are orthogonal. -/
theorem halmosCommon_le_targetDefect_orthogonal
    (U V : Submodule 𝕜 H) :
    halmosCommonPart U V ≤ (halmosTargetDefect U V)ᗮ := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (hy.1 x hx.1)

omit [CompleteSpace H] in
/-- The common and exterior pieces are orthogonal. -/
theorem halmosCommon_le_exterior_orthogonal
    (U V : Submodule 𝕜 H) :
    halmosCommonPart U V ≤ (halmosExteriorPart U V)ᗮ := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (hy.1 x hx.1)

omit [CompleteSpace H] in
/-- The two defect pieces are orthogonal. -/
theorem halmosSourceDefect_le_targetDefect_orthogonal
    (U V : Submodule 𝕜 H) :
    halmosSourceDefect U V ≤ (halmosTargetDefect U V)ᗮ := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (hy.1 x hx.1)

omit [CompleteSpace H] in
/-- The source defect and exterior pieces are orthogonal. -/
theorem halmosSourceDefect_le_exterior_orthogonal
    (U V : Submodule 𝕜 H) :
    halmosSourceDefect U V ≤ (halmosExteriorPart U V)ᗮ := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (hy.1 x hx.1)

omit [CompleteSpace H] in
/-- The target defect and exterior pieces are orthogonal. -/
theorem halmosTargetDefect_le_exterior_orthogonal
    (U V : Submodule 𝕜 H) :
    halmosTargetDefect U V ≤ (halmosExteriorPart U V)ᗮ := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (hy.2 x hx.2)

/-- The trivial part — the join of all four elementary summands — is
orthogonally complemented.  Built from the four component instances, using that
the summands are mutually orthogonal, which is what makes the join well behaved. -/
noncomputable instance instHasOrthogonalProjectionHalmosTrivialPart
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (halmosTrivialPart U V).HasOrthogonalProjection := by
  let A := halmosCommonPart U V ⊔ halmosSourceDefect U V
  let B := halmosTargetDefect U V ⊔ halmosExteriorPart U V
  have hA : A.HasOrthogonalProjection :=
    hasOrthogonalProjection_sup_of_le_orthogonal
      (halmosCommonPart U V) (halmosSourceDefect U V)
      (halmosCommon_le_sourceDefect_orthogonal U V)
  have hB : B.HasOrthogonalProjection :=
    hasOrthogonalProjection_sup_of_le_orthogonal
      (halmosTargetDefect U V) (halmosExteriorPart U V)
      (halmosTargetDefect_le_exterior_orthogonal U V)
  let : A.HasOrthogonalProjection := hA
  let : B.HasOrthogonalProjection := hB
  apply hasOrthogonalProjection_sup_of_le_orthogonal A B
  intro x hx y hy
  rcases Submodule.mem_sup.mp hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  rcases Submodule.mem_sup.mp hy with ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [inner_add_left, inner_add_right, inner_add_right]
  rw [halmosCommon_le_targetDefect_orthogonal U V hx₁ y₁ hy₁,
    halmosCommon_le_exterior_orthogonal U V hx₁ y₂ hy₂,
    halmosSourceDefect_le_targetDefect_orthogonal U V hx₂ y₁ hy₁,
    halmosSourceDefect_le_exterior_orthogonal U V hx₂ y₂ hy₂]
  simp

/-- Orthogonal decomposition into the elementary part and generic remainder. -/
theorem halmosTrivialPart_sup_genericPart
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosTrivialPart U V ⊔ halmosGenericPart U V = ⊤ :=
  Submodule.sup_orthogonal_of_hasOrthogonalProjection

omit [CompleteSpace H] in
/-- The elementary and generic Halmos pieces are disjoint. -/
theorem halmosTrivialPart_disjoint_genericPart
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    Disjoint (halmosTrivialPart U V) (halmosGenericPart U V) :=
  (halmosTrivialPart U V).orthogonal_disjoint

omit [CompleteSpace H] in
/-- Any elementary subspace contained in the trivial part meets the generic
part only at zero. -/
theorem halmosGenericPart_inf_eq_bot_of_le_trivial
    (U V K : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hK : K ≤ halmosTrivialPart U V) :
    halmosGenericPart U V ⊓ K = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  exact inner_self_eq_zero.mp (hx.1 x (hK hx.2))

omit [CompleteSpace H] in
/-- The common part is contained in the elementary Halmos summand. -/
theorem halmosCommonPart_le_trivial
    (U V : Submodule 𝕜 H) :
    halmosCommonPart U V ≤ halmosTrivialPart U V := by
  intro x hx
  exact (le_sup_left :
      (halmosCommonPart U V ⊔ halmosSourceDefect U V) ≤
        halmosTrivialPart U V)
    ((le_sup_left : halmosCommonPart U V ≤
      halmosCommonPart U V ⊔ halmosSourceDefect U V) hx)

omit [CompleteSpace H] in
/-- The source defect is contained in the elementary Halmos summand. -/
theorem halmosSourceDefect_le_trivial
    (U V : Submodule 𝕜 H) :
    halmosSourceDefect U V ≤ halmosTrivialPart U V := by
  intro x hx
  exact (le_sup_left :
      (halmosCommonPart U V ⊔ halmosSourceDefect U V) ≤
        halmosTrivialPart U V)
    ((le_sup_right : halmosSourceDefect U V ≤
      halmosCommonPart U V ⊔ halmosSourceDefect U V) hx)

omit [CompleteSpace H] in
/-- The target defect is contained in the elementary Halmos summand. -/
theorem halmosTargetDefect_le_trivial
    (U V : Submodule 𝕜 H) :
    halmosTargetDefect U V ≤ halmosTrivialPart U V := by
  intro x hx
  exact (le_sup_right :
      (halmosTargetDefect U V ⊔ halmosExteriorPart U V) ≤
        halmosTrivialPart U V)
    ((le_sup_left : halmosTargetDefect U V ≤
      halmosTargetDefect U V ⊔ halmosExteriorPart U V) hx)

omit [CompleteSpace H] in
/-- The exterior part is contained in the elementary Halmos summand. -/
theorem halmosExteriorPart_le_trivial
    (U V : Submodule 𝕜 H) :
    halmosExteriorPart U V ≤ halmosTrivialPart U V := by
  intro x hx
  exact (le_sup_right :
      (halmosTargetDefect U V ⊔ halmosExteriorPart U V) ≤
        halmosTrivialPart U V)
    ((le_sup_right : halmosExteriorPart U V ≤
      halmosTargetDefect U V ⊔ halmosExteriorPart U V) hx)

/-! ## Reduction by the two projections -/

omit [CompleteSpace H] in
/-- A linear map preserving two subspaces preserves their supremum. -/
theorem map_mem_sup_of_invariant
    (T : H →L[𝕜] H) {K L : Submodule 𝕜 H}
    (hK : ∀ x ∈ K, T x ∈ K) (hL : ∀ x ∈ L, T x ∈ L)
    {x : H} (hx : x ∈ K ⊔ L) : T x ∈ K ⊔ L := by
  rcases Submodule.mem_sup.mp hx with ⟨k, hk, l, hl, rfl⟩
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨T k, hK k hk, T l, hL l hl, rfl⟩

omit [CompleteSpace H] in
/-- The source projection preserves the elementary Halmos summand. -/
theorem projection_mem_halmosTrivialPart_left
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H}
    (hx : x ∈ halmosTrivialPart U V) :
    U.starProjection x ∈ halmosTrivialPart U V := by
  apply map_mem_sup_of_invariant (U.starProjection)
  · intro y hy
    apply map_mem_sup_of_invariant (U.starProjection)
    · intro z hz
      rw [(projections_apply_of_mem_halmosCommonPart hz).1]
      exact hz
    · intro z hz
      rw [(projections_apply_of_mem_halmosSourceDefect hz).1]
      exact hz
    · exact hy
  · intro y hy
    apply map_mem_sup_of_invariant (U.starProjection)
    · intro z hz
      rw [(projections_apply_of_mem_halmosTargetDefect hz).1]
      exact zero_mem _
    · intro z hz
      rw [(projections_apply_of_mem_halmosExteriorPart hz).1]
      exact zero_mem _
    · exact hy
  · exact hx

omit [CompleteSpace H] in
/-- The target projection preserves the elementary Halmos summand. -/
theorem projection_mem_halmosTrivialPart_right
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H}
    (hx : x ∈ halmosTrivialPart U V) :
    V.starProjection x ∈ halmosTrivialPart U V := by
  apply map_mem_sup_of_invariant (V.starProjection)
  · intro y hy
    apply map_mem_sup_of_invariant (V.starProjection)
    · intro z hz
      rw [(projections_apply_of_mem_halmosCommonPart hz).2]
      exact hz
    · intro z hz
      rw [(projections_apply_of_mem_halmosSourceDefect hz).2]
      exact zero_mem _
    · exact hy
  · intro y hy
    apply map_mem_sup_of_invariant (V.starProjection)
    · intro z hz
      rw [(projections_apply_of_mem_halmosTargetDefect hz).2]
      exact hz
    · intro z hz
      rw [(projections_apply_of_mem_halmosExteriorPart hz).2]
      exact zero_mem _
    · exact hy
  · exact hx

omit [CompleteSpace H] in
/-- The source projection preserves the generic Halmos summand. -/
theorem projection_mem_halmosGenericPart_left
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H}
    (hx : x ∈ halmosGenericPart U V) :
    U.starProjection x ∈ halmosGenericPart U V := by
  have hred : U.starProjection.Reduces (halmosTrivialPart U V) :=
    ContinuousLinearMap.IsSymmetric.reduces_of_invariant
      U.starProjection_isSymmetric
      (fun y hy => projection_mem_halmosTrivialPart_left U V (x := y) hy)
  exact hred.2 x hx

omit [CompleteSpace H] in
/-- The target projection preserves the generic Halmos summand. -/
theorem projection_mem_halmosGenericPart_right
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H}
    (hx : x ∈ halmosGenericPart U V) :
    V.starProjection x ∈ halmosGenericPart U V := by
  have hred : V.starProjection.Reduces (halmosTrivialPart U V) :=
    ContinuousLinearMap.IsSymmetric.reduces_of_invariant
      V.starProjection_isSymmetric
      (fun y hy => projection_mem_halmosTrivialPart_right U V (x := y) hy)
  exact hred.2 x hx

omit [CompleteSpace H] in
/-- The generic Halmos summand reduces the source projection. -/
theorem projection_left_reduces_halmosGenericPart
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (U.starProjection).Reduces (halmosGenericPart U V) := by
  exact ContinuousLinearMap.IsSymmetric.reduces_of_invariant
    U.starProjection_isSymmetric
    (fun x hx => projection_mem_halmosGenericPart_left U V (x := x) hx)

omit [CompleteSpace H] in
/-- The generic Halmos summand reduces the target projection. -/
theorem projection_right_reduces_halmosGenericPart
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (V.starProjection).Reduces (halmosGenericPart U V) := by
  exact ContinuousLinearMap.IsSymmetric.reduces_of_invariant
    V.starProjection_isSymmetric
    (fun x hx => projection_mem_halmosGenericPart_right U V (x := x) hx)

omit [CompleteSpace H] in
/-- The source defect vanishes for an acute pair. -/
theorem halmosSourceDefect_eq_bot_of_isUniformlyAcute
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    halmosSourceDefect U V = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  have hPx : U.starProjection x = x := U.starProjection_eq_self_iff.mpr hx.1
  have hQx : V.starProjection x = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff V).mpr hx.2
  have happ : (U.starProjection - V.starProjection) x = x := by
    simp [hPx, hQx]
  have hle := (U.starProjection - V.starProjection).le_opNorm x
  rw [happ] at hle
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hgap : ‖U.starProjection - V.starProjection‖ < 1 := hacute
  nlinarith

omit [CompleteSpace H] in
/-- The target defect vanishes for an acute pair. -/
theorem halmosTargetDefect_eq_bot_of_isUniformlyAcute
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    halmosTargetDefect U V = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  have hPx : U.starProjection x = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).mpr hx.1
  have hQx : V.starProjection x = x := V.starProjection_eq_self_iff.mpr hx.2
  have happ : (U.starProjection - V.starProjection) x = -x := by
    simp [hPx, hQx]
  have hle := (U.starProjection - V.starProjection).le_opNorm x
  rw [happ, norm_neg] at hle
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hgap : ‖U.starProjection - V.starProjection‖ < 1 := hacute
  nlinarith

omit [CompleteSpace H] in
/-- For an acute pair the elementary part consists only of the common and
exterior summands. -/
theorem halmosTrivialPart_eq_common_sup_exterior_of_isUniformlyAcute
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    halmosTrivialPart U V = halmosCommonPart U V ⊔ halmosExteriorPart U V := by
  change
    (halmosCommonPart U V ⊔ halmosSourceDefect U V) ⊔
        (halmosTargetDefect U V ⊔ halmosExteriorPart U V) =
      halmosCommonPart U V ⊔ halmosExteriorPart U V
  rw [halmosSourceDefect_eq_bot_of_isUniformlyAcute U V hacute,
    halmosTargetDefect_eq_bot_of_isUniformlyAcute U V hacute]
  simp

/-! ## Projection algebra -/

omit [CompleteSpace H] in
/-- An orthogonal projection is idempotent: `P_U * P_U = P_U`.

This is the multiplicative form of `Submodule.orthogonalProjection` idempotence,
stated for the bundled operator `projection U` so that the two-projection
calculations below can rewrite inside products without unfolding. -/
@[simp]
theorem projection_sq
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    U.starProjection * U.starProjection = U.starProjection :=
  U.isIdempotentElem_starProjection

omit [CompleteSpace H] in
/-- `P Pᗮ = 0`: a projection annihilates its own complement. -/
@[simp]
theorem projection_mul_complementaryProjection
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    U.starProjection * (Uᗮ).starProjection = 0 := by
  rw [Submodule.starProjection_orthogonal']
  have hP := projection_sq U
  noncomm_ring [hP]

omit [CompleteSpace H] in
/-- `Pᗮ P = 0`, the other order. -/
@[simp]
theorem complementaryProjection_mul_projection
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    (Uᗮ).starProjection * U.starProjection = 0 := by
  rw [Submodule.starProjection_orthogonal']
  have hP := projection_sq U
  noncomm_ring [hP]

omit [CompleteSpace H] in
/-- The complementary projection is idempotent.  With the two annihilation
lemmas above, these are the rewrites the `noncomm_ring` steps in the cosine and
sine identities run on. -/
@[simp]
theorem complementaryProjection_sq
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    (Uᗮ).starProjection * (Uᗮ).starProjection =
      (Uᗮ).starProjection :=
  Uᗮ.isIdempotentElem_starProjection

/-! ## Halmos cosine and sine -/

/-- Squared cosine operator of the two-projection model. -/
noncomputable def halmosCosineSq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : H →L[𝕜] H :=
  U.starProjection * V.starProjection * U.starProjection +
    (Uᗮ).starProjection * (Vᗮ).starProjection *
      (Uᗮ).starProjection

/-- Squared sine operator of the two-projection model. -/
noncomputable def halmosSineSq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : H →L[𝕜] H :=
  U.starProjection * (Vᗮ).starProjection * U.starProjection +
    (Uᗮ).starProjection * V.starProjection * (Uᗮ).starProjection

omit [CompleteSpace H] in
/-- The sine square is the square of the projection difference. -/
theorem halmosSineSq_eq_projection_sub_sq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosSineSq U V =
      (U.starProjection - V.starProjection) * (U.starProjection - V.starProjection) := by
  change
    U.starProjection * Vᗮ.starProjection * U.starProjection +
      Uᗮ.starProjection * V.starProjection * Uᗮ.starProjection =
    (U.starProjection - V.starProjection) *
      (U.starProjection - V.starProjection)
  rw [Submodule.starProjection_orthogonal' U,
    Submodule.starProjection_orthogonal' V]
  have hP := projection_sq U
  have hQ := projection_sq V
  noncomm_ring [hP, hQ]

omit [CompleteSpace H] in
/-- The cosine and sine squares resolve the identity. -/
theorem halmosCosineSq_add_sineSq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosCosineSq U V + halmosSineSq U V = 1 := by
  change
    U.starProjection * V.starProjection * U.starProjection +
      Uᗮ.starProjection * Vᗮ.starProjection * Uᗮ.starProjection +
      (U.starProjection * Vᗮ.starProjection * U.starProjection +
        Uᗮ.starProjection * V.starProjection * Uᗮ.starProjection) = 1
  rw [Submodule.starProjection_orthogonal' U,
    Submodule.starProjection_orthogonal' V]
  have hP := projection_sq U
  have hQ := projection_sq V
  noncomm_ring [hP, hQ]

omit [CompleteSpace H] in
/-- The squared cosine is `1 - (P-Q)²`. -/
theorem halmosCosineSq_eq_one_sub_projection_sub_sq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosCosineSq U V =
      1 - (U.starProjection - V.starProjection) * (U.starProjection - V.starProjection) := by
  have hsum := halmosCosineSq_add_sineSq U V
  rw [halmosSineSq_eq_projection_sub_sq] at hsum
  exact eq_sub_of_add_eq hsum

omit [CompleteSpace H] in
/-- The squared cosine commutes with the source projection. -/
theorem halmosCosineSq_commute_projection
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    Commute (halmosCosineSq U V) (U.starProjection) := by
  rw [commute_iff_eq]
  let P : H →L[𝕜] H := U.starProjection
  let Pc : H →L[𝕜] H := (Uᗮ).starProjection
  let Q : H →L[𝕜] H := V.starProjection
  let Qc : H →L[𝕜] H := (Vᗮ).starProjection
  change (P * Q * P + Pc * Qc * Pc) * P =
    P * (P * Q * P + Pc * Qc * Pc)
  have hP : P * P = P := by simp [P]
  have hPPc : P * Pc = 0 := by
    simp [P, Pc]
  have hPcP : Pc * P = 0 := by
    simp [P, Pc]
  have hleft : (P * Q * P + Pc * Qc * Pc) * P = P * Q * P := by
    rw [add_mul]
    have h₁ : (P * Q * P) * P = P * Q * P := by
      rw [mul_assoc, hP]
    have h₂ : (Pc * Qc * Pc) * P = 0 := by
      rw [mul_assoc, hPcP, mul_zero]
    rw [h₁, h₂, add_zero]
  have hright : P * (P * Q * P + Pc * Qc * Pc) = P * Q * P := by
    rw [mul_add]
    have h₁ : P * (P * Q * P) = P * Q * P := by
      rw [mul_assoc P Q P, ← mul_assoc P P (Q * P), hP]
    have h₂ : P * (Pc * Qc * Pc) = 0 := by
      rw [mul_assoc Pc Qc Pc, ← mul_assoc P Pc (Qc * Pc), hPPc, zero_mul]
    rw [h₁, h₂, add_zero]
  exact hleft.trans hright.symm

omit [CompleteSpace H] in
/-- The squared sine commutes with the source projection. -/
theorem halmosSineSq_commute_projection
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    Commute (halmosSineSq U V) (U.starProjection) := by
  have hs : halmosSineSq U V = 1 - halmosCosineSq U V :=
    eq_sub_of_add_eq' (halmosCosineSq_add_sineSq U V)
  rw [hs]
  exact (Commute.one_left (U.starProjection)).sub_left
    (halmosCosineSq_commute_projection U V)


end RCLikeGeometry

section ComplexAbsoluteValue

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The squared sine is nonnegative.  This operator-order statement remains
complex-specific: the field-independent content used by the Halmos
decomposition is the square identity above, while Mathlib's ordered star-ring
instance for continuous operators is currently exposed at complex scalars. -/
theorem halmosSineSq_nonneg
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    0 ≤ halmosSineSq U V := by
  rw [halmosSineSq_eq_projection_sub_sq]
  let A : H →L[ℂ] H := U.starProjection - V.starProjection
  have hAstar : star A = A := by
    dsimp [A]
    rw [star_sub,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq]
  simpa only [hAstar] using star_mul_self_nonneg A

/-- The modulus of the canonical intertwiner is the positive Halmos cosine:
its square is `C²`. -/
theorem spectraCanonicalAbsoluteValue_sq_eq_halmosCosineSq
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) *
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) =
      halmosCosineSq U V := by
  rw [ContinuousLinearMap.modulus_mul_self_eq_star_mul_self,
    star_spectraCanonicalIntertwiner]
  let P : H →L[ℂ] H := U.starProjection
  let Pc : H →L[ℂ] H := (Uᗮ).starProjection
  let Q : H →L[ℂ] H := V.starProjection
  let Qc : H →L[ℂ] H := (Vᗮ).starProjection
  change (P * Q + Pc * Qc) * (Q * P + Qc * Pc) =
    P * Q * P + Pc * Qc * Pc
  have hQ : Q * Q = Q := by simp [Q]
  have hQQc : Q * Qc = 0 := by
    simp [Q, Qc]
  have hQcQ : Qc * Q = 0 := by
    simp [Q, Qc]
  have hQc : Qc * Qc = Qc := by
    simp [Qc]
  have h11 : (P * Q) * (Q * P) = P * Q * P := by
    calc
      (P * Q) * (Q * P) = P * ((Q * Q) * P) := by
        rw [mul_assoc P Q (Q * P), ← mul_assoc Q Q P]
      _ = P * (Q * P) := by rw [hQ]
      _ = P * Q * P := (mul_assoc P Q P).symm
  have h12 : (P * Q) * (Qc * Pc) = 0 := by
    rw [mul_assoc P Q (Qc * Pc), ← mul_assoc Q Qc Pc,
      hQQc, zero_mul, mul_zero]
  have h21 : (Pc * Qc) * (Q * P) = 0 := by
    rw [mul_assoc Pc Qc (Q * P), ← mul_assoc Qc Q P,
      hQcQ, zero_mul, mul_zero]
  have h22 : (Pc * Qc) * (Qc * Pc) = Pc * Qc * Pc := by
    calc
      (Pc * Qc) * (Qc * Pc) = Pc * ((Qc * Qc) * Pc) := by
        rw [mul_assoc Pc Qc (Qc * Pc), ← mul_assoc Qc Qc Pc]
      _ = Pc * (Qc * Pc) := by rw [hQc]
      _ = Pc * Qc * Pc := (mul_assoc Pc Qc Pc).symm
  calc
    (P * Q + Pc * Qc) * (Q * P + Qc * Pc) =
        (P * Q) * (Q * P) + (P * Q) * (Qc * Pc) +
          ((Pc * Qc) * (Q * P) + (Pc * Qc) * (Qc * Pc)) := by
      rw [add_mul, mul_add, mul_add]
    _ = P * Q * P + Pc * Qc * Pc := by
      rw [h11, h12, h21, h22, add_zero, zero_add]


end ComplexAbsoluteValue

end DavisKahan
end TauCeti
