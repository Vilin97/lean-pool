/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`TanTwoTheta.lean`).

Block identities and spectral repulsion (plan steps G2.1, G2.2a) formalized by
Claude Opus 4.8 (claude-opus-4-8[1m]); statement gate (G2.0) and the tan 2Θ
headline proof (G2.2b) by Claude Fable 5 (claude-fable-5[1m]);
the July 2026 completion campaign (Git history).

The subspace Davis–Kahan tan 2Θ theorem and its supporting bricks.  The
*vanishing-pinch* hypothesis — the perturbation has no diagonal block with
respect to a subspace `U` and its orthogonal complement — is expressed as an
operator identity (`P ∘ H ∘ P = 0`, `P S P = P T P`); spectral repulsion keeps
the perturbed spectrum out of the gap; and the headline
`tan_two_theta_norm_sub_le` is GKMV's sectorial proof distilled to
finite-dimensional elementary form (reflections, one invariant plane, a
trace-type cancellation — no polar decomposition, no spectral theorem for
unitaries, uniform over `ℝ` and `ℂ`).
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.Vector

/-! # The subspace tan 2Θ theorem: block identities and the gated statement

## Statement cross-check (statement-first gate, plan step G2.0)

The classical subspace tan 2Θ theorem, as recorded verbatim in
Grubišić–Kostrykin–Makarov–Veselić, *The Tan 2Θ theorem for indefinite
quadratic forms* (arXiv:1006.3190, Introduction), quoting Davis–Kahan (1970):
let `A± ≻ 0` be strictly positive bounded operators on `H±`, `W` bounded from
`H₋` to `H₊`, and

`A = [[A₊, 0], [0, −A₋]]`, `B = A + V = [[A₊, W], [W⋆, −A₋]]`

with respect to `H = H₊ ⊕ H₋`.  Then

`‖tan 2Θ‖ ≤ 2 ‖V‖ / d`  **and**  `spec(Θ) ⊂ [0, π/4)`,

where `Θ` is the operator angle between `Ran E_A(ℝ₊)` and `Ran E_B(ℝ₊)` and
`d = dist(spec A₊, spec (−A₋))`.  Equivalently (their eq. (1.2)):
`‖P − Q‖ ≤ sin (½ arctan (2‖V‖/d))`, which implies `‖P − Q‖ < √2/2`.
Distinctive features, mirrored exactly here:

* **the perturbation is off-diagonal** (vanishing pinch) — this is what buys
  `tan` over `sin`: the angle stays *strictly below* `π/4` no matter how large
  `‖V‖` is, so `tan 2Θ` never meets its pole.  The pole question raised at the
  gate is thereby resolved: at the subspace level no `|cos 2Θ|`
  absolute-value bookkeeping is needed (unlike the per-vector
  `tan_two_theta_le`, where a single eigenvector from the *other* spectral
  component sits at angle `> π/4`);
* **subordinated spectra**: the two diagonal blocks sit on opposite sides of
  a gap (here: quadratic form of `T` is `≥ b` on `U`, `≤ a` on `Uᗮ`), the
  classical hypothesis — not the general two-component separation of the
  KMM-school generalizations;
* **both sides' spectral bounds**: the hypotheses on the perturbed pair
  `(S, V)` mirror those on `(T, U)` with the *same* `a, b`.  This is not a
  loss of faithfulness: off-diagonal perturbations repel spectrum away from
  the gap (GKMV Theorem 2.4(ii): the whole interval `(a, b)` stays in the
  resolvent of `S`), so the matching spectral subspace of `S` satisfies these
  bounds automatically.  That *spectral repulsion* step is filed separately
  (plan step G2.2a), keeping the headline conditional and clean;
* the classical statement is **operator-norm**; DK III state the sin 2Θ
  theorem in every unitarily invariant norm, but the tan 2Θ record here is
  op-norm — a UI-norm upgrade is not asserted by the sources we checked and
  is therefore not part of the gated statement;
* sharpness: for `T = diag(1, −1)`, `H = [[0, w], [w, 0]]` the bound is an
  equality (`tan 2θ = w = 2‖H‖/d`), and `θ → π/4` only as `w → ∞`.

The conclusion is encoded pole-free through `t := ‖P − P̂‖ = sin θ_max`:
`t² < 1/2` (the strict `π/4` bound) and
`(b − a) · 2t√(1−t²) ≤ 2ε · (1 − 2t²)` (i.e. `δ sin 2Θ ≤ 2ε cos 2Θ`), which
together are equivalent to `tan 2θ_max ≤ 2ε/(b − a)`.

## Main results

* `TauCeti.starProjection_comp_comp_starProjection_eq_zero`: a perturbation
  with vanishing `U`-diagonal form compresses to zero, `P ∘ H ∘ P = 0`.
* `TauCeti.starProjection_comp_comp_starProjection_congr`: two operators
  whose `U`-diagonal forms agree have equal `U`-diagonal blocks,
  `P ∘ S ∘ P = P ∘ T ∘ P`.
* `TauCeti.eigenvalue_notMem_gap_of_diagonal_form` (plan step G2.2a):
  spectral repulsion — no eigenvalue in the open form gap.
* `TauCeti.tan_two_theta_norm_sub_le` (plan step G2.2b): the subspace
  tan 2Θ theorem, gated statement above.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
* L. Grubišić, V. Kostrykin, K. A. Makarov, K. Veselić, *The Tan 2Θ theorem
  for indefinite quadratic forms*, J. Spectr. Theory 3 (2013); arXiv:1006.3190.
* A. Seelmann, *Notes on the sin 2Θ theorem*, Integr. Equ. Oper. Theory 79
  (2014); arXiv:1310.2036 (for the operator-angle formalism).
-/

namespace TauCeti
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **A perturbation with vanishing `U`-diagonal form compresses to zero.**  If
`⟪u, H u'⟫ = 0` for all `u, u' ∈ U`, then `P ∘ H ∘ P = 0`, `P` the orthogonal
projection onto `U`.  (Only the right-slot vanishing is used: `H (P x)` lands in
`Uᗮ`, which `P` then kills.) -/
theorem starProjection_comp_comp_starProjection_eq_zero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {H : E →ₗ[𝕜] E}
    (hH : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0) :
    (U.starProjection : E →ₗ[𝕜] E) ∘ₗ H ∘ₗ (U.starProjection : E →ₗ[𝕜] E) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply]
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  exact fun u hu => hH u hu _ (U.starProjection_apply_mem x)

/-- **Equal `U`-diagonal forms give equal `U`-diagonal blocks.**  If
`⟪u, S u'⟫ = ⟪u, T u'⟫` for all `u, u' ∈ U`, then `P ∘ S ∘ P = P ∘ T ∘ P`.
Applying this to `Uᗮ` yields the complementary block identity
`(1−P) ∘ S ∘ (1−P) = (1−P) ∘ T ∘ (1−P)` (`Submodule.starProjection_orthogonal`).
This is the operator form of the vanishing-pinch hypothesis of
`tan_two_theta_le_of_mem`. -/
theorem starProjection_comp_comp_starProjection_congr
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {S T : E →ₗ[𝕜] E}
    (h : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, S u'⟫_𝕜 = ⟪u, T u'⟫_𝕜) :
    (U.starProjection : E →ₗ[𝕜] E) ∘ₗ S ∘ₗ (U.starProjection : E →ₗ[𝕜] E)
      = (U.starProjection : E →ₗ[𝕜] E) ∘ₗ T ∘ₗ (U.starProjection : E →ₗ[𝕜] E) := by
  have hH : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, (S - T) u'⟫_𝕜 = 0 := fun u hu u' hu' => by
    rw [LinearMap.sub_apply, inner_sub_right, h u hu u' hu', sub_self]
  have hzero := starProjection_comp_comp_starProjection_eq_zero U hH
  rw [← sub_eq_zero]
  have hexp : (U.starProjection : E →ₗ[𝕜] E) ∘ₗ S ∘ₗ (U.starProjection : E →ₗ[𝕜] E)
      - (U.starProjection : E →ₗ[𝕜] E) ∘ₗ T ∘ₗ (U.starProjection : E →ₗ[𝕜] E)
      = (U.starProjection : E →ₗ[𝕜] E) ∘ₗ (S - T) ∘ₗ (U.starProjection : E →ₗ[𝕜] E) := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [hexp, hzero]

section ReflectionAlgebra

variable {T : E →ₗ[𝕜] E}

/-- Pythagoras for the orthogonal projection: `‖P_K x‖² + ‖x − P_K x‖² = ‖x‖²`.
Auxiliary. -/
private theorem norm_sq_starProjection_add_norm_sq_sub (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (x : E) :
    ‖K.starProjection x‖ ^ 2 + ‖x - K.starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  have horth : ⟪K.starProjection x, x - K.starProjection x⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem x)
      (K.sub_starProjection_mem_orthogonal x)
  have hx : K.starProjection x + (x - K.starProjection x) = x := by abel
  calc ‖K.starProjection x‖ ^ 2 + ‖x - K.starProjection x‖ ^ 2
      = ‖K.starProjection x + (x - K.starProjection x)‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := 𝕜), horth, map_zero]; ring
    _ = ‖x‖ ^ 2 := by rw [hx]

/-- The reflection through `K`, with the doubling written as a `𝕜`-scalar.
Auxiliary. -/
private theorem reflection_apply_ofNat_smul (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (w : E) : K.reflection w = (2 : 𝕜) • K.starProjection w - w := by
  rw [Submodule.reflection_apply, ← Nat.cast_smul_eq_nsmul 𝕜]
  norm_num

/-- The reflection through a subspace is self-adjoint.  Auxiliary. -/
private theorem inner_reflection_left_eq_right (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (v w : E) : ⟪K.reflection v, w⟫_𝕜 = ⟪v, K.reflection w⟫_𝕜 := by
  simp only [reflection_apply_ofNat_smul, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, map_ofNat, K.inner_starProjection_left_eq_right]

/-- A symmetric operator commutes with the projection onto an invariant
subspace.  Auxiliary. -/
private theorem starProjection_map_comm (hT : T.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hUinv : ∀ u ∈ U, T u ∈ U) (w : E) :
    U.starProjection (T w) = T (U.starProjection w) := by
  have hsplit : T w = T (U.starProjection w) + T (w - U.starProjection w) := by
    rw [← map_add]; congr 1; abel
  rw [hsplit, map_add,
    Submodule.starProjection_eq_self_iff.mpr (hUinv _ (U.starProjection_apply_mem w)),
    (Submodule.starProjection_apply_eq_zero_iff U).mpr
      (map_mem_orthogonal_of_forall_map_mem hT hUinv (U.sub_starProjection_mem_orthogonal w)),
    add_zero]

/-- A symmetric operator commutes with the reflection through an invariant
subspace.  Auxiliary. -/
private theorem reflection_map_comm (hT : T.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hUinv : ∀ u ∈ U, T u ∈ U) (w : E) :
    U.reflection (T w) = T (U.reflection w) := by
  rw [reflection_apply_ofNat_smul, reflection_apply_ofNat_smul,
    starProjection_map_comm hT hUinv, map_sub, map_smul]

/-- An operator that is off-diagonal with respect to `U ⊕ Uᗮ` (vanishing pinch
on both diagonal blocks) anticommutes with the reflection through `U`.
Auxiliary. -/
private theorem reflection_map_anticomm {H : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection]
    (hHU : ∀ x ∈ U, ∀ y ∈ U, ⟪x, H y⟫_𝕜 = 0)
    (hHUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ, ⟪x, H y⟫_𝕜 = 0) (w : E) :
    U.reflection (H w) = -(H (U.reflection w)) := by
  have hPHP : U.starProjection (H (U.starProjection w)) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
    exact fun u hu => hHU u hu _ (U.starProjection_apply_mem w)
  have hQ : H (w - U.starProjection w) ∈ Uᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    exact fun u hu => hHUperp u hu _ (U.sub_starProjection_mem_orthogonal w)
  rw [Submodule.orthogonal_orthogonal] at hQ
  have hPH : U.starProjection (H w) = H w - H (U.starProjection w) := by
    calc U.starProjection (H w)
        = U.starProjection (H (U.starProjection w))
            + U.starProjection (H (w - U.starProjection w)) := by
          rw [← map_add, ← map_add]
          congr 2
          abel
      _ = H (w - U.starProjection w) := by
          rw [hPHP, zero_add, Submodule.starProjection_eq_self_iff.mpr hQ]
      _ = H w - H (U.starProjection w) := by rw [map_sub]
  rw [reflection_apply_ofNat_smul, reflection_apply_ofNat_smul, hPH, map_sub, map_smul]
  module

/-- The reflected quadratic form of a symmetric operator with a `[a, b]`-split
diagonal form is bounded below by the half-gap: if `T` is at least `b` on the
invariant `U` and at most `a` on `Uᗮ`, then
`re ⟪w, J (T w − c w)⟫ ≥ (b−a)/2 · ‖w‖²` for `J` the reflection through `U` and
`c = (a+b)/2` the midpoint.  Auxiliary. -/
private theorem le_re_inner_reflection_map (hT : T.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hUinv : ∀ u ∈ U, T u ∈ U) {a b : ℝ}
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) (w : E) :
    (b - a) / 2 * ‖w‖ ^ 2
      ≤ RCLike.re ⟪w, U.reflection (T w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜 := by
  have hUperp : ∀ u ∈ Uᗮ, T u ∈ Uᗮ := fun u hu =>
    map_mem_orthogonal_of_forall_map_mem hT hUinv hu
  have hpU : U.starProjection w ∈ U := U.starProjection_apply_mem w
  have hmU : w - U.starProjection w ∈ Uᗮ := U.sub_starProjection_mem_orthogonal w
  have hpyth := norm_sq_starProjection_add_norm_sq_sub U w
  have hwsum : w = U.starProjection w + (w - U.starProjection w) := by abel
  set p : E := U.starProjection w with hp
  set m : E := w - U.starProjection w with hm
  have hTp : T p - (((a + b) / 2 : ℝ) : 𝕜) • p ∈ U :=
    Submodule.sub_mem _ (hUinv _ hpU) (U.smul_mem _ hpU)
  have hTm : T m - (((a + b) / 2 : ℝ) : 𝕜) • m ∈ Uᗮ :=
    Submodule.sub_mem _ (hUperp _ hmU) (Uᗮ.smul_mem _ hmU)
  rw [← inner_reflection_left_eq_right]
  have hJw : U.reflection w = p - m := by
    rw [reflection_apply_ofNat_smul, ← hp, hm]
    module
  have hsplitT : T w - (((a + b) / 2 : ℝ) : 𝕜) • w
      = (T p - (((a + b) / 2 : ℝ) : 𝕜) • p) + (T m - (((a + b) / 2 : ℝ) : 𝕜) • m) := by
    conv_lhs => rw [hwsum]
    rw [map_add]
    module
  rw [hJw, hsplitT]
  simp only [inner_add_right, inner_sub_left]
  rw [Submodule.inner_right_of_mem_orthogonal hpU hTm,
    Submodule.inner_left_of_mem_orthogonal hTp hmU]
  simp only [inner_sub_right, inner_smul_right, map_add, map_sub, map_neg,
    RCLike.re_ofReal_mul, inner_self_eq_norm_sq, sub_zero, zero_sub]
  have h1 := hUb _ hpU
  have h2 := hUa _ hmU
  have hswap1 : RCLike.re ⟪p, T p⟫_𝕜 = RCLike.re ⟪T p, p⟫_𝕜 := by
    rw [← inner_conj_symm, RCLike.conj_re]
  have hswap2 : RCLike.re ⟪m, T m⟫_𝕜 = RCLike.re ⟪T m, m⟫_𝕜 := by
    rw [← inner_conj_symm, RCLike.conj_re]
  have hpyth' : (b - a) / 2 * ‖p‖ ^ 2 + (b - a) / 2 * ‖m‖ ^ 2 = (b - a) / 2 * ‖w‖ ^ 2 := by
    linear_combination (b - a) / 2 * hpyth
  linarith [h1, h2, hswap1, hswap2, hpyth']

/-- **The anticommutator of two reflections, in terms of the projection
difference.**

`R_U R_V + R_V R_U = 2 - 4 (P_U - P_V)²` for any two subspaces with orthogonal
projections.  This is the algebraic identity that makes a *double* angle appear:
composing the two reflections in either order and symmetrising leaves exactly the
square of the projection difference, and `(P_U - P_V)²` is the operator whose
spectrum the double-angle bounds are about.

Nothing here is finite-dimensional or about eigenvalues; it was seven lines
inside `eigen_cos_two_theta_bound`, where a reader looking for *why* reflections
produce a double angle would not find it. -/
theorem reflection_add_reflection_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    U.reflection (V.reflection x) + V.reflection (U.reflection x) =
      (2 : 𝕜) • x - (4 : 𝕜) •
        ((U.starProjection - V.starProjection : E →L[𝕜] E)
          ((U.starProjection - V.starProjection : E →L[𝕜] E) x)) := by
  have hPP : U.starProjection (U.starProjection x) = U.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hPvPv : V.starProjection (V.starProjection x) = V.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  simp only [reflection_apply_ofNat_smul, sub_apply, map_sub, map_smul, hPP, hPvPv]
  module

end ReflectionAlgebra

section Headline

variable [FiniteDimensional 𝕜 E] [CompleteSpace E] {T S : E →ₗ[𝕜] E}

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- **Spectral repulsion (plan step G2.2a).**  If the diagonal form of a
symmetric `S` is `≥ b` on a subspace `U` and `≤ a` on `Uᗮ` (`a < b`), then no
eigenvalue of `S` lies in the open gap `(a, b)`: every real eigenvalue `μ`
satisfies `μ ≤ a ∨ b ≤ μ`.  This is the mechanism behind the off-diagonal
(vanishing-pinch) hypothesis of the tan 2Θ theorem: such a perturbation keeps
`S = T + H`'s spectrum out of the gap (GKMV Thm 2.4(ii)), because the pinch
makes `S`'s diagonal blocks equal `T`'s, `⟪u, S u⟫ = ⟪u, T u⟫`.  Proof: split
the eigenvector `x = P x + (1−P) x =: p + m`; the eigen-equation gives
`μ‖p‖² = s₁ + r` and `μ‖m‖² = r + s₂` with `s₁ = re⟪Sp,p⟫ ≥ b‖p‖²`,
`s₂ = re⟪Sm,m⟫ ≤ a‖m‖²`, `r = re⟪Sp,m⟫`; eliminating `r` gives
`(μ−a)‖m‖² ≤ r ≤ (μ−b)‖p‖²`, incompatible with `a < μ < b` and `‖p‖,‖m‖ > 0`
(the degenerate `p = 0` / `m = 0` cases put `x` in `Uᗮ` / `U` directly). -/
theorem eigenvalue_notMem_gap_of_diagonal_form (hS : S.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] {a b : ℝ}
    (hUb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪S u, u⟫_𝕜)
    (hUa : ∀ w ∈ Uᗮ, RCLike.re ⟪S w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    {x : E} (hx : x ≠ 0) {μ : ℝ} (hμ : S x = (μ : 𝕜) • x) :
    μ ≤ a ∨ b ≤ μ := by
  set p := U.starProjection x with hpdef
  set m := x - U.starProjection x with hmdef
  have hpU : p ∈ U := U.starProjection_apply_mem x
  have hmU : m ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hsplit : x = p + m := by rw [hpdef, hmdef]; abel
  have hmp : ⟪m, p⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hpU hmU
  have hpm : ⟪p, m⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hpU hmU
  -- `⟪S x, y⟫ = μ ⟪x, y⟫` and the form-symmetry `re⟪S y, z⟫ = re⟪S z, y⟫`.
  have hSxy : ∀ y, ⟪S x, y⟫_𝕜 = (μ : 𝕜) * ⟪x, y⟫_𝕜 := fun y => by
    rw [hμ, inner_smul_left, RCLike.conj_ofReal]
  have hform : ∀ y z, RCLike.re ⟪S y, z⟫_𝕜 = RCLike.re ⟪S z, y⟫_𝕜 := fun y z => by
    rw [hS y z, ← RCLike.conj_re ⟪y, S z⟫_𝕜, inner_conj_symm]
  -- `re⟪S x, x'⟫ = μ ‖x'‖²`-style values and the block decompositions.
  have hval : ∀ y, RCLike.re ⟪S x, y⟫_𝕜 = μ * RCLike.re ⟪x, y⟫_𝕜 := fun y => by
    rw [hSxy y, RCLike.re_ofReal_mul]
  -- Degenerate cases.
  rcases eq_or_ne p 0 with hp0 | hp0n
  · left
    have hxU : x ∈ Uᗮ := by rw [hsplit, hp0, zero_add]; exact hmU
    have hle := hUa x hxU
    rw [hval x, inner_self_eq_norm_sq] at hle
    have hxpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    nlinarith [hle, hxpos]
  rcases eq_or_ne m 0 with hm0 | hm0n
  · right
    have hxU : x ∈ U := by rw [hsplit, hm0, add_zero]; exact hpU
    have hle := hUb x hxU
    rw [hval x, inner_self_eq_norm_sq] at hle
    have hxpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    nlinarith [hle, hxpos]
  -- Both blocks nonzero.
  have hp2 : (0 : ℝ) < ‖p‖ ^ 2 := pow_pos (norm_pos_iff.mpr hp0n) 2
  have hq2 : (0 : ℝ) < ‖m‖ ^ 2 := pow_pos (norm_pos_iff.mpr hm0n) 2
  have hval_p : RCLike.re ⟪S x, p⟫_𝕜 = μ * ‖p‖ ^ 2 := by
    -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved: at
    -- least one lemma here has to fire at one occurrence, in order, and simp's normal form loses
    -- the intermediate shape.
    rw [hval p, hsplit, inner_add_left, map_add, inner_self_eq_norm_sq, hmp, map_zero, add_zero]
  have hval_m : RCLike.re ⟪S x, m⟫_𝕜 = μ * ‖m‖ ^ 2 := by
    -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved: at
    -- least one lemma here has to fire at one occurrence, in order, and simp's normal form loses
    -- the intermediate shape.
    rw [hval m, hsplit, inner_add_left, map_add, hpm, map_zero, zero_add, inner_self_eq_norm_sq]
  have decomp_p : RCLike.re ⟪S x, p⟫_𝕜
      = RCLike.re ⟪S p, p⟫_𝕜 + RCLike.re ⟪S p, m⟫_𝕜 := by
    rw [hsplit, map_add, inner_add_left, map_add, hform m p]
  have decomp_m : RCLike.re ⟪S x, m⟫_𝕜
      = RCLike.re ⟪S p, m⟫_𝕜 + RCLike.re ⟪S m, m⟫_𝕜 := by
    rw [hsplit, map_add, inner_add_left, map_add]
  have heq_p : μ * ‖p‖ ^ 2 = RCLike.re ⟪S p, p⟫_𝕜 + RCLike.re ⟪S p, m⟫_𝕜 := by
    rw [← decomp_p, hval_p]
  have heq_m : μ * ‖m‖ ^ 2 = RCLike.re ⟪S p, m⟫_𝕜 + RCLike.re ⟪S m, m⟫_𝕜 := by
    rw [← decomp_m, hval_m]
  have hr_le : RCLike.re ⟪S p, m⟫_𝕜 ≤ (μ - b) * ‖p‖ ^ 2 := by
    nlinarith [hUb p hpU, heq_p]
  have hr_ge : (μ - a) * ‖m‖ ^ 2 ≤ RCLike.re ⟪S p, m⟫_𝕜 := by
    nlinarith [hUa m hmU, heq_m]
  by_contra hc
  push Not at hc
  nlinarith [hr_le, hr_ge, mul_pos (show (0 : ℝ) < μ - a by linarith [hc.1]) hq2,
    mul_pos (show (0 : ℝ) < b - μ by linarith [hc.2]) hp2]

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- `w ↦ Ĵ(S w − c w)` is additive.

It is a composition of linear maps, so this and `reflectionShift_smul` below hold
with **no hypothesis on `S`, `V` or the shift at all** -- neither symmetry nor
invariance.  Stated separately because inside a proof they read as steps needing
the ambient hypotheses, and a reader then has to check whether they do. -/
private theorem reflectionShift_add (S : E →ₗ[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (c : ℝ) (v w : E) :
    V.reflection (S (v + w) - ((c : ℝ) : 𝕜) • (v + w))
      = V.reflection (S v - ((c : ℝ) : 𝕜) • v)
        + V.reflection (S w - ((c : ℝ) : 𝕜) • w) := by
  rw [← map_add]
  congr 1
  rw [map_add, smul_add]
  abel

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- `w ↦ Ĵ(S w − c w)` is real-homogeneous.  See `reflectionShift_add`. -/
private theorem reflectionShift_smul (S : E →ₗ[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (c : ℝ) (t : ℝ) (w : E) :
    V.reflection (S ((t : 𝕜) • w) - ((c : ℝ) : 𝕜) • ((t : 𝕜) • w))
      = (t : 𝕜) • V.reflection (S w - ((c : ℝ) : 𝕜) • w) := by
  rw [← map_smul]
  congr 1
  rw [map_smul, smul_sub, smul_comm]

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- A reflection is an isometry, so a bound on `S − T` bounds every form built
from `J(S − T)`.  The only input is the norm bound itself. -/
private theorem norm_inner_reflection_sub_le {S T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] {ε : ℝ} (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (v w : E) :
    ‖⟪v, U.reflection ((S - T) w)⟫_𝕜‖ ≤ ε * (‖v‖ * ‖w‖) := by
  calc ‖⟪v, U.reflection ((S - T) w)⟫_𝕜‖
      ≤ ‖v‖ * ‖U.reflection ((S - T) w)‖ := norm_inner_le_norm _ _
    _ = ‖v‖ * ‖(S - T) w‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖v‖ * (ε * ‖w‖) := mul_le_mul_of_nonneg_left (hε w) (norm_nonneg v)
    _ = ε * (‖v‖ * ‖w‖) := by ring

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- The eigenvector analysis behind the tan 2Θ theorem (plan step G2.2b).  At
a unit eigenvector `x` of `(P − P̂)²` with eigenvalue `ν`, write `J, Ĵ` for the
reflections through `U, V` and `c, d` for the midpoint and half-gap.  The
operator identity `(JĴ)·(Ĵ(S−c)) = J(S−c)` splits into the symmetric part
`J(T−c)` (coercive with constant `d`, by the vanishing pinch) and the skew
part `J(S−T)` (of norm at most `ε`), while `Ĵ(S−c)` is itself symmetric and
`d`-coercive.  Evaluating these forms on the `JĴ`-invariant plane spanned by
`x` and `y = JĴx` — concretely, on the pairs `(x,x)`, `(w₂,w₂)` and
`(sx − w₂, sx + w₂)` for `w₂ = y − γx`, `γ = ⟪x, y⟫`, `s = ‖w₂‖` — makes every
cross-Gram term cancel and yields `μ₀ (s²r₁ + r₂) ≥ 2ds²` and
`(s²r₁ + r₂)² (s² + ν'²) ≤ 4ε²s⁴` for the `cos 2Θ`-eigenvalue `μ₀ = 1 − 2ν`
(`ν' = im γ`, `r`'s the diagonal `Ĵ(S−c)`-form values), whence `μ₀ > 0` and
the sharp tangent bound `d²(1−μ₀²) ≤ ε²μ₀²`.  Auxiliary. -/
private theorem eigen_cos_two_theta_bound (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b ε : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hVb : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜)
    (hVa : ∀ x ∈ Vᗮ, RCLike.re ⟪S x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, ∀ y ∈ U, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hHUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖)
    {x : E} {ν : ℝ} (hxn : ‖x‖ = 1)
    (hYx : (U.starProjection - V.starProjection : E →L[𝕜] E)
        ((U.starProjection - V.starProjection : E →L[𝕜] E) x) = (ν : 𝕜) • x) :
    0 < 1 - 2 * ν ∧
      ((b - a) / 2) ^ 2 * (1 - (1 - 2 * ν) ^ 2) ≤ ε ^ 2 * (1 - 2 * ν) ^ 2 := by
  have hd : (0 : ℝ) < (b - a) / 2 := by linarith
  -- commutation, anticommutation, bridges
  have hJT : ∀ w, U.reflection (T w - (((a + b) / 2 : ℝ) : 𝕜) • w)
      = T (U.reflection w) - (((a + b) / 2 : ℝ) : 𝕜) • U.reflection w := fun w => by
    rw [map_sub, map_smul, reflection_map_comm hT hUinv]
  have hJvS : ∀ w, V.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)
      = S (V.reflection w) - (((a + b) / 2 : ℝ) : 𝕜) • V.reflection w := fun w => by
    rw [map_sub, map_smul, reflection_map_comm hS hVinv]
  have hJH : ∀ w, U.reflection ((S - T) w) = -((S - T) (U.reflection w)) :=
    fun w => reflection_map_anticomm hHU hHUperp w
  have hbrA : ∀ v w, ⟪v, U.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜
      = ⟪V.reflection (U.reflection v),
          V.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜 := by
    intro v w
    rw [← inner_reflection_left_eq_right U]
    exact (LinearIsometryEquiv.inner_map_map V.reflection _ _).symm
  have hbrB : ∀ v w, ⟪v, S (U.reflection w) - (((a + b) / 2 : ℝ) : 𝕜) • U.reflection w⟫_𝕜
      = ⟪V.reflection (S v - (((a + b) / 2 : ℝ) : 𝕜) • v),
          V.reflection (U.reflection w)⟫_𝕜 := by
    intro v w
    have h1 : ⟪v, S (U.reflection w) - (((a + b) / 2 : ℝ) : 𝕜) • U.reflection w⟫_𝕜
        = ⟪S v - (((a + b) / 2 : ℝ) : 𝕜) • v, U.reflection w⟫_𝕜 := by
      rw [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        RCLike.conj_ofReal, hS]
    rw [h1]
    exact (LinearIsometryEquiv.inner_map_map V.reflection _ _).symm
  -- assembled doubled forms
  --
  -- `hAA` and `hKF` are one argument run twice with opposite signs: `J(S−c)`
  -- against `S(J·)−cJ·` adds to `2·J(T−c)` and subtracts to `2·J(S−T)`, because
  -- `J` commutes with `T−c` and anticommutes with `S−T`.  The splitting of
  -- `S − c` that both need is the same, so it is named once.
  have hsplit : ∀ w, S w - (((a + b) / 2 : ℝ) : 𝕜) • w
      = (T w - (((a + b) / 2 : ℝ) : 𝕜) • w) + (S - T) w := fun w => by
    simp only [LinearMap.sub_apply]; abel
  have hAA : ∀ v w,
      ⟪V.reflection (U.reflection v),
          V.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜
        + ⟪V.reflection (S v - (((a + b) / 2 : ℝ) : 𝕜) • v),
            V.reflection (U.reflection w)⟫_𝕜
      = 2 * ⟪v, U.reflection (T w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜 := by
    intro v w
    have hAK : U.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)
        + (S (U.reflection w) - (((a + b) / 2 : ℝ) : 𝕜) • U.reflection w)
        = (2 : 𝕜) • U.reflection (T w - (((a + b) / 2 : ℝ) : 𝕜) • w) := by
      rw [hsplit w, map_add, hJH, hJT]
      simp only [LinearMap.sub_apply]
      module
    rw [← hbrA, ← hbrB, ← inner_add_right, hAK, inner_smul_right]
  have hKF : ∀ v w,
      ⟪V.reflection (U.reflection v),
          V.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜
        - ⟪V.reflection (S v - (((a + b) / 2 : ℝ) : 𝕜) • v),
            V.reflection (U.reflection w)⟫_𝕜
      = 2 * ⟪v, U.reflection ((S - T) w)⟫_𝕜 := by
    intro v w
    have hKK : U.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)
        - (S (U.reflection w) - (((a + b) / 2 : ℝ) : 𝕜) • U.reflection w)
        = (2 : 𝕜) • U.reflection ((S - T) w) := by
      rw [hsplit w, map_add, hJT, hJH]
      simp only [LinearMap.sub_apply]
      module
    rw [← hbrA, ← hbrB, ← inner_sub_right, hKK, inner_smul_right]
  have hKb : ∀ v w, ‖⟪v, U.reflection ((S - T) w)⟫_𝕜‖ ≤ ε * (‖v‖ * ‖w‖) :=
    norm_inner_reflection_sub_le hε
  have hRform : ∀ w, (b - a) / 2 * ‖w‖ ^ 2
      ≤ RCLike.re ⟪w, V.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜 :=
    fun w => le_re_inner_reflection_map hS hVinv hVb hVa w
  have hAform : ∀ w, (b - a) / 2 * ‖w‖ ^ 2
      ≤ RCLike.re ⟪w, U.reflection (T w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜 :=
    fun w => le_re_inner_reflection_map hT hUinv hUb hUa w
  have hRsym : ∀ v w, ⟪V.reflection (S v - (((a + b) / 2 : ℝ) : 𝕜) • v), w⟫_𝕜
      = ⟪v, V.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w)⟫_𝕜 := by
    intro v w
    -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved: at
    -- least one lemma here has to fire at one occurrence, in order, and simp's normal form loses
    -- the intermediate shape.
    rw [inner_reflection_left_eq_right, hJvS w, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, RCLike.conj_ofReal, hS]
  have hRadd : ∀ v w, V.reflection (S (v + w) - (((a + b) / 2 : ℝ) : 𝕜) • (v + w))
      = V.reflection (S v - (((a + b) / 2 : ℝ) : 𝕜) • v)
        + V.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w) :=
    reflectionShift_add S V ((a + b) / 2)
  have hRsmul : ∀ (t : ℝ) w, V.reflection (S ((t : 𝕜) • w)
        - (((a + b) / 2 : ℝ) : 𝕜) • ((t : 𝕜) • w))
      = (t : 𝕜) • V.reflection (S w - (((a + b) / 2 : ℝ) : 𝕜) • w) :=
    reflectionShift_smul S V ((a + b) / 2)
  -- the invariant plane
  set y : E := U.reflection (V.reflection x) with hydef
  set z : E := V.reflection (U.reflection x) with hzdef
  set γ : 𝕜 := ⟪x, y⟫_𝕜 with hγdef
  set ν' : ℝ := RCLike.im γ with hν'def
  have hyn : ‖y‖ = 1 := by
    rw [hydef, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, hxn]
  have hJJsum : y + z = ((2 * (1 - 2 * ν) : ℝ) : 𝕜) • x := by
    rw [hydef, hzdef, reflection_add_reflection_comm U V x, hYx,
      show ((2 * (1 - 2 * ν) : ℝ) : 𝕜) = (2 : 𝕜) - (4 : 𝕜) * (ν : 𝕜) from by push_cast; ring]
    module
  have hz' : z = ((2 * (1 - 2 * ν) : ℝ) : 𝕜) • x - y := by rw [← hJJsum]; abel
  have hγconj : ⟪x, z⟫_𝕜 = (starRingEnd 𝕜) γ := by
    rw [hγdef, hydef, hzdef]
    calc ⟪x, V.reflection (U.reflection x)⟫_𝕜
        = ⟪V.reflection x, U.reflection x⟫_𝕜 := by rw [← inner_reflection_left_eq_right]
      _ = (starRingEnd 𝕜) ⟪U.reflection x, V.reflection x⟫_𝕜 := by rw [← inner_conj_symm]
      _ = (starRingEnd 𝕜) ⟪x, U.reflection (V.reflection x)⟫_𝕜 := by
          rw [inner_reflection_left_eq_right]
  have hγre : RCLike.re γ = 1 - 2 * ν := by
    have h2 : γ + (starRingEnd 𝕜) γ = ((2 * (1 - 2 * ν) : ℝ) : 𝕜) := by
      -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved:
      -- at least one lemma here has to fire at one occurrence, in order, and simp's normal form
      -- loses the intermediate shape.
      rw [← hγconj, hγdef, ← inner_add_right, hJJsum, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hxn]
      norm_num
    have h3 := congrArg RCLike.re h2
    rw [map_add, RCLike.conj_re, RCLike.ofReal_re] at h3
    linarith
  have hsumγ : ((2 * (1 - 2 * ν) : ℝ) : 𝕜) = γ + (starRingEnd 𝕜) γ := by
    rw [RCLike.add_conj, hγre]
    push_cast
    ring
  have hγsq : ‖γ‖ ^ 2 = (1 - 2 * ν) ^ 2 + ν' ^ 2 := by
    rw [← RCLike.normSq_eq_def', RCLike.normSq_apply, hγre, hν'def]
    ring
  -- the second basis direction and its geometry
  set w₂ : E := y - γ • x with hw₂def
  have hzw : z = (starRingEnd 𝕜) γ • x - w₂ := by
    rw [hz', hsumγ, hw₂def, add_smul]
    abel
  have hxw₂ : ⟪x, w₂⟫_𝕜 = 0 := by
    rw [hw₂def, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hxn, ← hγdef]
    norm_num
  have hs2 : ‖w₂‖ ^ 2 = 1 - ‖γ‖ ^ 2 := by
    have hyx : ⟪y, γ • x⟫_𝕜 = ((‖γ‖ ^ 2 : ℝ) : 𝕜) := by
      rw [inner_smul_right, show ⟪y, x⟫_𝕜 = (starRingEnd 𝕜) γ from by
        rw [hγdef, ← inner_conj_symm], RCLike.mul_conj]
      push_cast
      ring
    simp only [hw₂def, norm_sub_sq (𝕜 := 𝕜), hyn, norm_smul, hxn, hyx, RCLike.ofReal_re]
    ring
  have hw' : V.reflection (U.reflection w₂) = ((‖w₂‖ ^ 2 : ℝ) : 𝕜) • x + γ • w₂ := by
    have hJvJy : V.reflection (U.reflection y) = x := by
      rw [hydef, Submodule.reflection_reflection, Submodule.reflection_reflection]
    simp only [hw₂def, map_sub, map_sub, map_smul, map_smul, hJvJy, ← hzdef, hzw, smul_sub,
      smul_smul, RCLike.mul_conj,
      show ((‖γ‖ : ℝ) : 𝕜) ^ 2 = 1 - ((‖w₂‖ ^ 2 : ℝ) : 𝕜) from by
        rw [show ((‖γ‖ : ℝ) : 𝕜) ^ 2 = ((‖γ‖ ^ 2 : ℝ) : 𝕜) from by push_cast; ring, hs2]
        push_cast
        ring]
    module
  -- fold the scalar entries of the `Ĵ(S−c)`-form
  set Q₁ : 𝕜 := ⟪x, V.reflection (S x - (((a + b) / 2 : ℝ) : 𝕜) • x)⟫_𝕜 with hQ₁def
  set Q₂ : 𝕜 := ⟪w₂, V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂)⟫_𝕜 with hQ₂def
  set G : 𝕜 := ⟪x, V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂)⟫_𝕜 with hGdef
  have hQ₁conj : (starRingEnd 𝕜) Q₁ = Q₁ := by
    rw [hQ₁def, inner_conj_symm, hRsym]
  have hQ₂conj : (starRingEnd 𝕜) Q₂ = Q₂ := by
    rw [hQ₂def, inner_conj_symm, hRsym]
  set r₁ : ℝ := RCLike.re Q₁ with hr₁def
  set r₂ : ℝ := RCLike.re Q₂ with hr₂def
  have hQ₁real : Q₁ = ((r₁ : ℝ) : 𝕜) := (RCLike.conj_eq_iff_re.mp hQ₁conj).symm
  have hQ₂real : Q₂ = ((r₂ : ℝ) : 𝕜) := (RCLike.conj_eq_iff_re.mp hQ₂conj).symm
  have hr₁d : (b - a) / 2 ≤ r₁ := by
    have h9 := hRform x
    rw [hxn, one_pow, mul_one, ← hQ₁def, ← hr₁def] at h9
    exact h9
  have hr₂d : (b - a) / 2 * ‖w₂‖ ^ 2 ≤ r₂ := by
    have h9 := hRform w₂
    rw [← hQ₂def, ← hr₂def] at h9
    exact h9
  -- cross-entry flips
  have hw₂Rx : ⟪w₂, V.reflection (S x - (((a + b) / 2 : ℝ) : 𝕜) • x)⟫_𝕜
      = (starRingEnd 𝕜) G := by
    rw [hGdef, ← hRsym, ← inner_conj_symm]
  have hF1 : ⟪V.reflection (S x - (((a + b) / 2 : ℝ) : 𝕜) • x), x⟫_𝕜 = Q₁ := by
    rw [hRsym, ← hQ₁def]
  have hF2 : ⟪V.reflection (S x - (((a + b) / 2 : ℝ) : 𝕜) • x), w₂⟫_𝕜 = G := by
    rw [hRsym, ← hGdef]
  have hF3 : ⟪V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂), x⟫_𝕜
      = (starRingEnd 𝕜) G := by
    rw [hRsym, hw₂Rx]
  have hF4 : ⟪V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂), w₂⟫_𝕜 = Q₂ := by
    rw [hRsym, ← hQ₂def]
  -- the four expansions of the plane's `R`-entries
  have hE1 : ⟪z, V.reflection (S x - (((a + b) / 2 : ℝ) : 𝕜) • x)⟫_𝕜
      = γ * Q₁ - (starRingEnd 𝕜) G := by
    rw [hzw, inner_sub_left, inner_smul_left, RCLike.conj_conj, hw₂Rx, ← hQ₁def]
  have hE2 : ⟪V.reflection (S x - (((a + b) / 2 : ℝ) : 𝕜) • x), z⟫_𝕜
      = (starRingEnd 𝕜) γ * Q₁ - G := by
    rw [← inner_conj_symm, hE1, map_sub, map_mul, RCLike.conj_conj, hQ₁conj]
  have hE3 : ⟪V.reflection (U.reflection w₂),
        V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂)⟫_𝕜
      = ((‖w₂‖ ^ 2 : ℝ) : 𝕜) * G + (starRingEnd 𝕜) γ * Q₂ := by
    simp only [hw', inner_add_left, inner_smul_left, inner_smul_left, RCLike.conj_ofReal,
      ← hGdef, ← hQ₂def]
  have hE4 : ⟪V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂),
        V.reflection (U.reflection w₂)⟫_𝕜
      = ((‖w₂‖ ^ 2 : ℝ) : 𝕜) * (starRingEnd 𝕜) G + γ * Q₂ := by
    -- Left as a `rw` chain on purpose: `simp only` with this same list rejects `← inner_conj_symm`
    -- as a possibly-looping simp theorem. A reversed rewrite applied once, in position, is what
    -- `rw` is for.
    rw [← inner_conj_symm, hE3, map_add, map_mul, map_mul, RCLike.conj_ofReal,
      RCLike.conj_conj, hQ₂conj]
  -- I1: the (x,x) coercivity
  have hI1 : (b - a) / 2 ≤ (1 - 2 * ν) * r₁ - RCLike.re G := by
    have hAAxx := hAA x x
    rw [← hzdef, hE1, hE2] at hAAxx
    have hL : γ * Q₁ - (starRingEnd 𝕜) G + ((starRingEnd 𝕜) γ * Q₁ - G)
        = ((2 * (1 - 2 * ν) * r₁ : ℝ) : 𝕜) - (G + (starRingEnd 𝕜) G) := by
      rw [hQ₁real, show ((2 * (1 - 2 * ν) * r₁ : ℝ) : 𝕜)
          = (γ + (starRingEnd 𝕜) γ) * ((r₁ : ℝ) : 𝕜) from by rw [← hsumγ]; push_cast; ring]
      ring
    rw [hL] at hAAxx
    have h5 := congrArg RCLike.re hAAxx
    have hre1 : RCLike.re (((2 * (1 - 2 * ν) * r₁ : ℝ) : 𝕜) - (G + (starRingEnd 𝕜) G))
        = 2 * (1 - 2 * ν) * r₁ - 2 * RCLike.re G := by
      rw [map_sub, map_add, RCLike.conj_re, RCLike.ofReal_re]
      ring
    have hre2 : RCLike.re (2 * ⟪x, U.reflection (T x - (((a + b) / 2 : ℝ) : 𝕜) • x)⟫_𝕜)
        = 2 * RCLike.re ⟪x, U.reflection (T x - (((a + b) / 2 : ℝ) : 𝕜) • x)⟫_𝕜 := by
      rw [two_mul, map_add, two_mul]
    rw [hre1, hre2] at h5
    have h9 := hAform x
    rw [hxn, one_pow, mul_one] at h9
    linarith
  -- I2: the (w₂,w₂) coercivity
  have hI2 : (b - a) / 2 * ‖w₂‖ ^ 2 ≤ (1 - 2 * ν) * r₂ + ‖w₂‖ ^ 2 * RCLike.re G := by
    have hAAww := hAA w₂ w₂
    rw [hE3, hE4] at hAAww
    have hL : ((‖w₂‖ ^ 2 : ℝ) : 𝕜) * G + (starRingEnd 𝕜) γ * Q₂
          + (((‖w₂‖ ^ 2 : ℝ) : 𝕜) * (starRingEnd 𝕜) G + γ * Q₂)
        = ((2 * (1 - 2 * ν) * r₂ : ℝ) : 𝕜)
          + ((‖w₂‖ ^ 2 : ℝ) : 𝕜) * (G + (starRingEnd 𝕜) G) := by
      rw [hQ₂real, show ((2 * (1 - 2 * ν) * r₂ : ℝ) : 𝕜)
          = (γ + (starRingEnd 𝕜) γ) * ((r₂ : ℝ) : 𝕜) from by rw [← hsumγ]; push_cast; ring]
      ring
    rw [hL] at hAAww
    have h5 := congrArg RCLike.re hAAww
    have hre1 : RCLike.re (((2 * (1 - 2 * ν) * r₂ : ℝ) : 𝕜)
          + ((‖w₂‖ ^ 2 : ℝ) : 𝕜) * (G + (starRingEnd 𝕜) G))
        = 2 * (1 - 2 * ν) * r₂ + ‖w₂‖ ^ 2 * (2 * RCLike.re G) := by
      rw [map_add, RCLike.ofReal_re, RCLike.re_ofReal_mul, map_add, RCLike.conj_re]
      ring
    have hre2 : RCLike.re (2 * ⟪w₂, U.reflection (T w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂)⟫_𝕜)
        = 2 * RCLike.re ⟪w₂, U.reflection (T w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂)⟫_𝕜 := by
      rw [two_mul, map_add, two_mul]
    rw [hre1, hre2] at h5
    have h9 := hAform w₂
    linarith
  -- the skew form on the tilted pair
  have hV2 : (((‖w₂‖ ^ 2 : ℝ) : 𝕜) * Q₁ + Q₂)
        * (γ - (starRingEnd 𝕜) γ - ((2 * ‖w₂‖ : ℝ) : 𝕜))
      = 2 * ⟪((‖w₂‖ : ℝ) : 𝕜) • x - w₂,
          U.reflection ((S - T) (((‖w₂‖ : ℝ) : 𝕜) • x + w₂))⟫_𝕜 := by
    rw [← hKF]
    have harg1 : V.reflection (U.reflection (((‖w₂‖ : ℝ) : 𝕜) • x - w₂))
        = ((‖w₂‖ : ℝ) : 𝕜) • z - (((‖w₂‖ ^ 2 : ℝ) : 𝕜) • x + γ • w₂) := by
      rw [map_sub, map_sub, map_smul, map_smul, ← hzdef, hw']
    have harg2 : V.reflection (S (((‖w₂‖ : ℝ) : 𝕜) • x + w₂)
          - (((a + b) / 2 : ℝ) : 𝕜) • (((‖w₂‖ : ℝ) : 𝕜) • x + w₂))
        = ((‖w₂‖ : ℝ) : 𝕜) • V.reflection (S x - (((a + b) / 2 : ℝ) : 𝕜) • x)
          + V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂) := by
      rw [hRadd, hRsmul]
    have harg3 : V.reflection (S (((‖w₂‖ : ℝ) : 𝕜) • x - w₂)
          - (((a + b) / 2 : ℝ) : 𝕜) • (((‖w₂‖ : ℝ) : 𝕜) • x - w₂))
        = ((‖w₂‖ : ℝ) : 𝕜) • V.reflection (S x - (((a + b) / 2 : ℝ) : 𝕜) • x)
          - V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂) := by
      have hsub : (((‖w₂‖ : ℝ) : 𝕜) • x - w₂)
          = (((‖w₂‖ : ℝ) : 𝕜) • x + (-1 : 𝕜) • w₂) := by
        module
      have hneg : V.reflection (S ((-1 : 𝕜) • w₂)
            - (((a + b) / 2 : ℝ) : 𝕜) • ((-1 : 𝕜) • w₂))
          = (-1 : 𝕜) • V.reflection (S w₂ - (((a + b) / 2 : ℝ) : 𝕜) • w₂) := by
        rw [← map_smul]
        congr 1
        rw [map_smul]
        module
      rw [hsub, hRadd, hRsmul, hneg]
      module
    have harg4 : V.reflection (U.reflection (((‖w₂‖ : ℝ) : 𝕜) • x + w₂))
        = ((‖w₂‖ : ℝ) : 𝕜) • z + (((‖w₂‖ ^ 2 : ℝ) : 𝕜) • x + γ • w₂) := by
      rw [map_add, map_add, map_smul, map_smul, ← hzdef, hw']
    rw [harg1, harg2, harg3, harg4, hzw]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, RCLike.conj_ofReal, RCLike.conj_conj]
    simp only [hw₂Rx, hF1, hF2, hF3, hF4, ← hQ₁def, ← hQ₂def, ← hGdef]
    push_cast
    ring
  -- norm bound on the tilted skew form
  have hn1 : ‖((‖w₂‖ : ℝ) : 𝕜) • x - w₂‖ ^ 2 = 2 * ‖w₂‖ ^ 2 := by
    simp only [norm_sub_sq (𝕜 := 𝕜), inner_smul_left, RCLike.conj_ofReal, hxw₂, mul_zero,
      norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w₂), hxn]
    simp only [map_zero]
    ring
  have hn2 : ‖((‖w₂‖ : ℝ) : 𝕜) • x + w₂‖ ^ 2 = 2 * ‖w₂‖ ^ 2 := by
    simp only [norm_add_sq (𝕜 := 𝕜), inner_smul_left, RCLike.conj_ofReal, hxw₂, mul_zero,
      norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w₂), hxn]
    simp only [map_zero]
    ring
  have hV2norm : ‖(((‖w₂‖ ^ 2 : ℝ) : 𝕜) * Q₁ + Q₂)
        * (γ - (starRingEnd 𝕜) γ - ((2 * ‖w₂‖ : ℝ) : 𝕜))‖
      ≤ 2 * (ε * (2 * ‖w₂‖ ^ 2)) := by
    rw [hV2]
    have hprod : ‖((‖w₂‖ : ℝ) : 𝕜) • x - w₂‖ * ‖((‖w₂‖ : ℝ) : 𝕜) • x + w₂‖
        = 2 * ‖w₂‖ ^ 2 := by
      have hnn : (0 : ℝ) ≤ ‖((‖w₂‖ : ℝ) : 𝕜) • x - w₂‖ * ‖((‖w₂‖ : ℝ) : 𝕜) • x + w₂‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      apply (sq_eq_sq₀ hnn
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ‖w₂‖))).mp
      calc
        (‖((‖w₂‖ : ℝ) : 𝕜) • x - w₂‖ * ‖((‖w₂‖ : ℝ) : 𝕜) • x + w₂‖) ^ 2
            = ‖((‖w₂‖ : ℝ) : 𝕜) • x - w₂‖ ^ 2
                * ‖((‖w₂‖ : ℝ) : 𝕜) • x + w₂‖ ^ 2 := by ring
        _ = (2 * ‖w₂‖ ^ 2) * (2 * ‖w₂‖ ^ 2) := by rw [hn1, hn2]
        _ = (2 * ‖w₂‖ ^ 2) ^ 2 := by ring
    calc ‖2 * ⟪((‖w₂‖ : ℝ) : 𝕜) • x - w₂,
            U.reflection ((S - T) (((‖w₂‖ : ℝ) : 𝕜) • x + w₂))⟫_𝕜‖
        = 2 * ‖⟪((‖w₂‖ : ℝ) : 𝕜) • x - w₂,
            U.reflection ((S - T) (((‖w₂‖ : ℝ) : 𝕜) • x + w₂))⟫_𝕜‖ := by
          rw [norm_mul, RCLike.norm_ofNat]
      _ ≤ 2 * (ε * (‖((‖w₂‖ : ℝ) : 𝕜) • x - w₂‖ * ‖((‖w₂‖ : ℝ) : 𝕜) • x + w₂‖)) := by
          have := hKb (((‖w₂‖ : ℝ) : 𝕜) • x - w₂) (((‖w₂‖ : ℝ) : 𝕜) • x + w₂)
          linarith
      _ = 2 * (ε * (2 * ‖w₂‖ ^ 2)) := by rw [hprod]
  -- extract the two real components of the tilted skew form
  have hG2 : (r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2 * (‖w₂‖ ^ 2 + ν' ^ 2)
      ≤ 4 * (ε ^ 2 * (‖w₂‖ ^ 2) ^ 2) := by
    have hval : ((‖w₂‖ ^ 2 : ℝ) : 𝕜) * Q₁ + Q₂ = ((r₁ * ‖w₂‖ ^ 2 + r₂ : ℝ) : 𝕜) := by
      rw [hQ₁real, hQ₂real]
      push_cast
      ring
    have hre : RCLike.re (((r₁ * ‖w₂‖ ^ 2 + r₂ : ℝ) : 𝕜)
          * (γ - (starRingEnd 𝕜) γ - ((2 * ‖w₂‖ : ℝ) : 𝕜)))
        = (r₁ * ‖w₂‖ ^ 2 + r₂) * (-(2 * ‖w₂‖)) := by
      rw [RCLike.re_ofReal_mul, map_sub, map_sub, RCLike.conj_re, RCLike.ofReal_re]
      ring
    have him : RCLike.im (((r₁ * ‖w₂‖ ^ 2 + r₂ : ℝ) : 𝕜)
          * (γ - (starRingEnd 𝕜) γ - ((2 * ‖w₂‖ : ℝ) : 𝕜)))
        = (r₁ * ‖w₂‖ ^ 2 + r₂) * (2 * ν') := by
      simp only [← RCLike.real_smul_eq_coe_mul, RCLike.smul_im, map_sub, map_sub, RCLike.conj_im,
        RCLike.ofReal_im, ← hν'def]
      ring
    have hnormsq : ‖((r₁ * ‖w₂‖ ^ 2 + r₂ : ℝ) : 𝕜)
          * (γ - (starRingEnd 𝕜) γ - ((2 * ‖w₂‖ : ℝ) : 𝕜))‖ ^ 2
        = ((r₁ * ‖w₂‖ ^ 2 + r₂) * (2 * ‖w₂‖)) ^ 2
          + ((r₁ * ‖w₂‖ ^ 2 + r₂) * (2 * ν')) ^ 2 := by
      rw [← RCLike.normSq_eq_def', RCLike.normSq_apply, hre, him]
      ring
    have hbound : ‖((r₁ * ‖w₂‖ ^ 2 + r₂ : ℝ) : 𝕜)
          * (γ - (starRingEnd 𝕜) γ - ((2 * ‖w₂‖ : ℝ) : 𝕜))‖
        ≤ 2 * (ε * (2 * ‖w₂‖ ^ 2)) := by
      rw [← hval]
      exact hV2norm
    have hbound2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    rw [hnormsq] at hbound2
    have hscaled :
        (4 : ℝ) * ((r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2 * (‖w₂‖ ^ 2 + ν' ^ 2))
          ≤ 4 * (4 * (ε ^ 2 * (‖w₂‖ ^ 2) ^ 2)) := by
      calc
        (4 : ℝ) * ((r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2 * (‖w₂‖ ^ 2 + ν' ^ 2))
            = ((r₁ * ‖w₂‖ ^ 2 + r₂) * (2 * ‖w₂‖)) ^ 2
              + ((r₁ * ‖w₂‖ ^ 2 + r₂) * (2 * ν')) ^ 2 := by ring
        _ ≤ (2 * (ε * (2 * ‖w₂‖ ^ 2))) ^ 2 := hbound2
        _ = 4 * (4 * (ε ^ 2 * (‖w₂‖ ^ 2) ^ 2)) := by ring
    exact le_of_mul_le_mul_left hscaled (by norm_num : (0 : ℝ) < 4)
  -- the coercivity inequality on the tilted pair
  have hG1 : 2 * ((b - a) / 2) * ‖w₂‖ ^ 2 ≤ (1 - 2 * ν) * (r₁ * ‖w₂‖ ^ 2 + r₂) := by
    have h10 := mul_le_mul_of_nonneg_right hI1 (sq_nonneg ‖w₂‖)
    calc
      2 * ((b - a) / 2) * ‖w₂‖ ^ 2
          = ((b - a) / 2) * ‖w₂‖ ^ 2 + ((b - a) / 2) * ‖w₂‖ ^ 2 := by ring
      _ ≤ ((1 - 2 * ν) * r₁ - RCLike.re G) * ‖w₂‖ ^ 2
          + ((1 - 2 * ν) * r₂ + ‖w₂‖ ^ 2 * RCLike.re G) := add_le_add h10 hI2
      _ = (1 - 2 * ν) * (r₁ * ‖w₂‖ ^ 2 + r₂) := by ring
  -- split on the degenerate plane
  rcases eq_or_ne w₂ 0 with hw₂0 | hw₂0
  · -- `y = γ x`: one-dimensional case, `1 − μ₀² = ν'²`
    have hG0 : G = 0 := by
      rw [hGdef, hw₂0]
      simp
    have hγ1 : ‖γ‖ ^ 2 = 1 := by
      have h11 := hs2
      rw [hw₂0, norm_zero] at h11
      linarith only [h11]
    have hI1' : (b - a) / 2 ≤ (1 - 2 * ν) * r₁ := by
      have := hI1
      rw [hG0, map_zero] at this
      linarith
    -- the `(x, x)` skew test
    have hKxx := hKF x x
    simp only [← hzdef, hE1, hE2, hG0, map_zero, sub_zero, sub_zero] at hKxx
    have hkval : (γ - (starRingEnd 𝕜) γ) * ((r₁ : ℝ) : 𝕜)
        = 2 * ⟪x, U.reflection ((S - T) x)⟫_𝕜 := by
      rw [← hKxx, hQ₁real]
      ring
    have hknorm : ‖(γ - (starRingEnd 𝕜) γ) * ((r₁ : ℝ) : 𝕜)‖ ≤ 2 * ε := by
      rw [hkval, norm_mul, RCLike.norm_ofNat]
      have h12 := hKb x x
      rw [hxn, mul_one, mul_one] at h12
      linarith
    have hkre : RCLike.re ((γ - (starRingEnd 𝕜) γ) * ((r₁ : ℝ) : 𝕜)) = 0 := by
      rw [mul_comm, RCLike.re_ofReal_mul, map_sub, RCLike.conj_re]
      ring
    have hkim : RCLike.im ((γ - (starRingEnd 𝕜) γ) * ((r₁ : ℝ) : 𝕜)) = 2 * ν' * r₁ := by
      rw [mul_comm, ← RCLike.real_smul_eq_coe_mul, RCLike.smul_im, map_sub, RCLike.conj_im,
        ← hν'def]
      ring
    have hksq : (2 * ν' * r₁) ^ 2 ≤ (2 * ε) ^ 2 := by
      have h12 : ‖(γ - (starRingEnd 𝕜) γ) * ((r₁ : ℝ) : 𝕜)‖ ^ 2 = (2 * ν' * r₁) ^ 2 := by
        rw [← RCLike.normSq_eq_def', RCLike.normSq_apply, hkre, hkim]
        ring
      rw [← h12]
      exact pow_le_pow_left₀ (norm_nonneg _) hknorm 2
    have hdecomp : (1 - 2 * ν) ^ 2 + ν' ^ 2 = 1 := by
      rw [← hγsq]
      exact hγ1
    constructor
    · nlinarith only [hI1', hr₁d, hd]
    · nlinarith only [hksq, hdecomp, sq_nonneg ν', hd, hI1', hr₁d,
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd.le hI1' 2) (sq_nonneg ν'),
        mul_le_mul_of_nonneg_left hksq (sq_nonneg (1 - 2 * ν)), sq_nonneg ε]
  · -- nondegenerate plane: conclude from `hG1`, `hG2`
    have hspos : (0 : ℝ) < ‖w₂‖ := norm_pos_iff.mpr hw₂0
    have hs2pos : (0 : ℝ) < ‖w₂‖ ^ 2 := by positivity
    have hApos : (0 : ℝ) < r₁ * ‖w₂‖ ^ 2 + r₂ := by
      nlinarith only [hr₁d, hr₂d, hd, hs2pos]
    have hdecomp : ‖w₂‖ ^ 2 + ν' ^ 2 = 1 - (1 - 2 * ν) ^ 2 := by
      have h13 := hγsq
      have h14 := hs2
      linarith
    have hμpos : 0 < 1 - 2 * ν := by
      nlinarith only [hG1, hApos, hd, hs2pos]
    refine ⟨hμpos, ?_⟩
    have hG1sq := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ 2 * ((b - a) / 2) * ‖w₂‖ ^ 2) hG1 2
    rw [hdecomp] at hG2
    have hG2scaled := mul_le_mul_of_nonneg_left hG2 (sq_nonneg ((b - a) / 2))
    have hG1sqScaled := mul_le_mul_of_nonneg_left hG1sq (sq_nonneg ε)
    have hA2pos : (0 : ℝ) < (r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2 := pow_pos hApos 2
    have hscaled :
        (r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2
            * (((b - a) / 2) ^ 2 * (1 - (1 - 2 * ν) ^ 2))
          ≤ (r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2
            * (ε ^ 2 * (1 - 2 * ν) ^ 2) := by
      calc
        (r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2
              * (((b - a) / 2) ^ 2 * (1 - (1 - 2 * ν) ^ 2))
            = ((b - a) / 2) ^ 2
              * ((r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2 * (1 - (1 - 2 * ν) ^ 2)) := by ring
        _ ≤ ((b - a) / 2) ^ 2 * (4 * (ε ^ 2 * (‖w₂‖ ^ 2) ^ 2)) := hG2scaled
        _ = ε ^ 2 * (2 * ((b - a) / 2) * ‖w₂‖ ^ 2) ^ 2 := by ring
        _ ≤ ε ^ 2 * ((1 - 2 * ν) * (r₁ * ‖w₂‖ ^ 2 + r₂)) ^ 2 := hG1sqScaled
        _ = (r₁ * ‖w₂‖ ^ 2 + r₂) ^ 2 * (ε ^ 2 * (1 - 2 * ν) ^ 2) := by ring
    exact le_of_mul_le_mul_left hscaled hA2pos

omit [CompleteSpace E] in
/-- **The subspace Davis–Kahan tan 2Θ theorem (plan step G2.2b).**  `T, S`
symmetric; `U` a `T`-invariant subspace with
the form of `T` at least `b` on `U` and at most `a` on `Uᗮ`; `V` an
`S`-invariant subspace with the mirrored bounds for `S` (discharged for the
spectral choice of `V` by spectral repulsion, plan step G2.2a); the
perturbation `S − T` **off-diagonal** with respect to `U ⊕ Uᗮ` (vanishing
pinch) and of norm at most `ε`.  Conclusion, with
`t := ‖P − P̂‖ = sin θ_max`: the angle stays strictly below `π/4`
(`t² < 1/2`) and `(b − a) sin 2θ_max ≤ 2 ε cos 2θ_max` — together,
`tan 2θ_max ≤ 2ε/(b − a)`.  See the module docstring for the
literature cross-check.

Proof: this is GKMV's sectorial argument (arXiv:1006.3190, Thm 3.1),
distilled to finite-dimensional elementary form.  With `X := P − P̂` and
`C := 1 − 2X²` (the `cos 2Θ` operator, `2C = JĴ + ĴJ`), a maximal eigenvector
of `X∘X` bounds `t² = ‖X‖²` by `(1 − μ₀)/2` for its `C`-eigenvalue `μ₀`, and
`eigen_cos_two_theta_bound` supplies `μ₀ > 0` together with the sharp
`(b−a)/2 · √(1−μ₀²) ≤ ε μ₀`; monotonicity of `τ ↦ 4τ(1−τ)` on `[0, 1/2]`
transports both along `t² ≤ (1−μ₀)/2`. -/
theorem tan_two_theta_norm_sub_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b ε : ℝ} (hab : a < b) (hε0 : 0 ≤ ε)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hVb : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜)
    (hVa : ∀ x ∈ Vᗮ, RCLike.re ⟪S x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, ∀ y ∈ U, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hHUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2 < 1 / 2 ∧
      (b - a) * (2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖
          * Real.sqrt (1 - ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2))
        ≤ 2 * ε * (1 - 2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2) := by
  set X : E →L[𝕜] E := U.starProjection - V.starProjection with hXdef
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hX0 : ‖X‖ = 0 := by
      rw [show X = 0 from ContinuousLinearMap.ext fun w => Subsingleton.elim _ _, norm_zero]
    rw [hX0]
    constructor
    · norm_num
    · rw [show (1 : ℝ) - (0:ℝ) ^ 2 = 1 by norm_num, Real.sqrt_one]
      have h0 : (0:ℝ) ≤ 2 * ε * (1 - 2 * (0:ℝ) ^ 2) := by
        norm_num
        positivity
      nlinarith [h0]
  · -- spectral apparatus for `Y := X ∘ X`
    have hXsym' : ∀ v w, ⟪X v, w⟫_𝕜 = ⟪v, X w⟫_𝕜 := by
      intro v w
      simp only [hXdef, sub_apply, inner_sub_left, inner_sub_right,
        U.inner_starProjection_left_eq_right, V.inner_starProjection_left_eq_right]
    set Y : E →ₗ[𝕜] E := ((X : E →ₗ[𝕜] E)) ∘ₗ ((X : E →ₗ[𝕜] E)) with hYdef
    have hYapp : ∀ w, Y w = X (X w) := fun w => rfl
    have hYsym : Y.IsSymmetric := by
      intro v w
      show ⟪X (X v), w⟫_𝕜 = ⟪v, X (X w)⟫_𝕜
      rw [hXsym' (X v) w, hXsym' v (X w)]
    have hn0 : 0 < Module.finrank 𝕜 E := Module.finrank_pos
    have : Nonempty (Fin (Module.finrank 𝕜 E)) := Fin.pos_iff_nonempty.mp hn0
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (hYsym.eigenvalues rfl)
      Finset.univ_nonempty
    have hxn : ‖hYsym.eigenvectorBasis rfl i₀‖ = 1 :=
      (hYsym.eigenvectorBasis rfl).orthonormal.1 i₀
    have hYx : X (X (hYsym.eigenvectorBasis rfl i₀))
        = ((hYsym.eigenvalues rfl i₀ : ℝ) : 𝕜) • hYsym.eigenvectorBasis rfl i₀ :=
      hYsym.apply_eigenvectorBasis rfl i₀
    set ν : ℝ := hYsym.eigenvalues rfl i₀ with hνdef
    -- `ν = ‖X x‖² ≥ 0`
    have hXx2 : ‖X (hYsym.eigenvectorBasis rfl i₀)‖ ^ 2 = ν := by
      have h1 : RCLike.re ⟪X (X (hYsym.eigenvectorBasis rfl i₀)),
            hYsym.eigenvectorBasis rfl i₀⟫_𝕜
          = ‖X (hYsym.eigenvectorBasis rfl i₀)‖ ^ 2 := by
        rw [hXsym' (X (hYsym.eigenvectorBasis rfl i₀)) (hYsym.eigenvectorBasis rfl i₀),
          inner_self_eq_norm_sq]
      rw [hYx, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
        inner_self_eq_norm_sq, hxn] at h1
      rw [← h1]
      ring
    have hν0 : (0 : ℝ) ≤ ν := hXx2 ▸ sq_nonneg _
    -- the Rayleigh bound `‖X‖² ≤ ν`
    have hXw2 : ∀ w, ‖X w‖ ^ 2 ≤ ν * ‖w‖ ^ 2 := by
      intro w
      have h1 : RCLike.re ⟪Y w, w⟫_𝕜 = ‖X w‖ ^ 2 := by
        show RCLike.re ⟪X (X w), w⟫_𝕜 = _
        rw [hXsym' (X w) w, inner_self_eq_norm_sq]
      have hpars : ∑ i, ‖(hYsym.eigenvectorBasis rfl).repr w i‖ ^ 2 = ‖w‖ ^ 2 := by
        simp_rw [OrthonormalBasis.repr_apply_apply]
        exact (hYsym.eigenvectorBasis rfl).sum_sq_norm_inner_right w
      calc ‖X w‖ ^ 2 = RCLike.re ⟪Y w, w⟫_𝕜 := h1.symm
        _ = ∑ i, hYsym.eigenvalues rfl i * ‖(hYsym.eigenvectorBasis rfl).repr w i‖ ^ 2 :=
            LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hYsym rfl w
        _ ≤ ∑ i, ν * ‖(hYsym.eigenvectorBasis rfl).repr w i‖ ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right (hi₀ i (Finset.mem_univ i)) (sq_nonneg _)
        _ = ν * ‖w‖ ^ 2 := by rw [← Finset.mul_sum, hpars]
    have ht2 : ‖X‖ ^ 2 ≤ ν := by
      have hb' : ‖X‖ ≤ Real.sqrt ν := by
        refine X.opNorm_le_bound (Real.sqrt_nonneg ν) fun w => ?_
        have h2 : ‖X w‖ ≤ Real.sqrt (ν * ‖w‖ ^ 2) := by
          rw [← Real.sqrt_sq (norm_nonneg (X w))]
          exact Real.sqrt_le_sqrt (hXw2 w)
        rwa [Real.sqrt_mul hν0, Real.sqrt_sq (norm_nonneg w)] at h2
      calc ‖X‖ ^ 2 ≤ Real.sqrt ν ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb' 2
        _ = ν := Real.sq_sqrt hν0
    -- the eigenvector analysis
    obtain ⟨hμpos, hkey⟩ := eigen_cos_two_theta_bound hT hS hUinv hVinv hab hUb hUa
      hVb hVa hHU hHUperp hε hxn hYx
    -- assembly
    have hν12 : ν ≤ 1 / 2 := by linarith
    have ht2' : ‖X‖ ^ 2 < 1 / 2 := by
      rcases lt_or_eq_of_le ht2 with h | h
      · linarith
      · linarith only [h, hμpos]
    refine ⟨ht2', ?_⟩
    have h1t : (0 : ℝ) ≤ 1 - ‖X‖ ^ 2 := by linarith only [ht2']
    have hμ1 : 1 - 2 * ν ≤ 1 := by linarith only [hν0]
    -- `2t√(1−t²) ≤ √(1−μ₀²)`
    have hstep1 : 2 * ‖X‖ * Real.sqrt (1 - ‖X‖ ^ 2) ≤ Real.sqrt (1 - (1 - 2 * ν) ^ 2) := by
      have h4 : (2 * ‖X‖ * Real.sqrt (1 - ‖X‖ ^ 2)) ^ 2 = 4 * ‖X‖ ^ 2 * (1 - ‖X‖ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt h1t]
        ring
      have h5 : 4 * ‖X‖ ^ 2 * (1 - ‖X‖ ^ 2) ≤ 1 - (1 - 2 * ν) ^ 2 := by
        have hleft : (0 : ℝ) ≤ ν - ‖X‖ ^ 2 := by linarith only [ht2]
        have hright : (0 : ℝ) ≤ 1 - ν - ‖X‖ ^ 2 := by linarith only [ht2', hν12]
        nlinarith only [mul_nonneg hleft hright]
      calc 2 * ‖X‖ * Real.sqrt (1 - ‖X‖ ^ 2)
          = Real.sqrt ((2 * ‖X‖ * Real.sqrt (1 - ‖X‖ ^ 2)) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ = Real.sqrt (4 * ‖X‖ ^ 2 * (1 - ‖X‖ ^ 2)) := by rw [h4]
        _ ≤ Real.sqrt (1 - (1 - 2 * ν) ^ 2) := Real.sqrt_le_sqrt h5
    -- `d √(1−μ₀²) ≤ ε μ₀`
    have hstep2 : (b - a) / 2 * Real.sqrt (1 - (1 - 2 * ν) ^ 2) ≤ ε * (1 - 2 * ν) := by
      have h6 : ((b - a) / 2 * Real.sqrt (1 - (1 - 2 * ν) ^ 2)) ^ 2
          ≤ (ε * (1 - 2 * ν)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by
          nlinarith only [hμ1, hμpos] : (0 : ℝ) ≤ 1 - (1 - 2 * ν) ^ 2)]
        simpa [mul_pow] using hkey
      have h7 := Real.sqrt_le_sqrt h6
      rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (mul_nonneg hε0 hμpos.le)] at h7
    have hstep3 : 1 - 2 * ν ≤ 1 - 2 * ‖X‖ ^ 2 := by linarith
    have hd0 : (0 : ℝ) ≤ (b - a) / 2 := by linarith
    calc (b - a) * (2 * ‖X‖ * Real.sqrt (1 - ‖X‖ ^ 2))
        = 2 * ((b - a) / 2 * (2 * ‖X‖ * Real.sqrt (1 - ‖X‖ ^ 2))) := by ring
      _ ≤ 2 * ((b - a) / 2 * Real.sqrt (1 - (1 - 2 * ν) ^ 2)) := by
          have := mul_le_mul_of_nonneg_left hstep1 hd0
          linarith
      _ ≤ 2 * (ε * (1 - 2 * ν)) := by linarith [hstep2]
      _ ≤ 2 * (ε * (1 - 2 * ‖X‖ ^ 2)) := by
          have := mul_le_mul_of_nonneg_left hstep3 hε0
          linarith
      _ = 2 * ε * (1 - 2 * ‖X‖ ^ 2) := by ring

end Headline

end TauCeti
