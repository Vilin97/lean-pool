/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.OperatorAngle
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.CompactOperator
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.KyFan
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.Schatten
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.TraceClass
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-!
# Symmetric norm ideals

Infinite-dimensional unitarily invariant norm statements live on compact
operator ideals, not on all bounded operators.  This file records the ideal
API needed to lift operator-norm Davis--Kahan estimates to Schatten, trace,
Hilbert--Schmidt, and general symmetric ideals.

Literature writeup: local TeX, Section 9.
-/


/-! ## Construction plan

Build this layer bottom-up from compact operators.

1. Use mathlib's compact continuous-linear maps and prove existence of singular
   values through the positive compact operator `T⋆T`.
2. Define the operator norm and Ky Fan gauges directly from the singular-value
   sequence; prove ideal inequalities and unitary invariance.
3. Define Schatten classes by summability of powers of singular values, with
   trace class and Hilbert--Schmidt as special cases.
4. Package each displayed norm only after completeness and the ideal property
   are available.  Prove finite-rank density before transferring finite
   Davis--Kahan estimates by approximation.
-/


/-! ## Weak-agent execution plan: symmetric ideals

Do not attempt the general `SymmetricNormIdeal` endpoint first.  Build a ladder
whose early stages can compile independently:

1. finite-rank continuous operators, with singular values defined by
   restriction to the finite-dimensional range/domain support;
2. compact operators and their singular-value sequence, using the compact
   positive spectral theorem for `T.adjoint ∘L T`;
3. Ky Fan gauges and the two ideal inequalities;
4. Schatten membership and norm for a fixed `p`;
5. completeness and finite-rank density;
6. the abstract symmetric-gauge ideal package.

Each ideal should be represented by a subtype carrying `mem`; define its norm
on the subtype instead of a total gauge plus repeated membership hypotheses.
Keep a coercion to bounded operators and prove composition/adjoint closure as
subtype constructors.  This will make later Sylvester statements readable.

The finite-to-compact transfer should approximate `T` by spectral truncations
of `|T|`, prove the Davis--Kahan inequality on each finite-rank truncation, and
pass to the ideal norm using completeness.  Do not assume operator-norm
convergence implies convergence in an arbitrary ideal norm.

Before general symmetric ideals, finish Hilbert--Schmidt and trace class as
test cases.  They expose missing summability and adjoint APIs without the full
symmetric-gauge representation theorem.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace
open DavisKahan.ExactSinTheta

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A symmetric norm ideal of bounded operators on a Hilbert space. -/
structure SymmetricNormIdeal where
  /-- Membership in the symmetric ideal of bounded operators. -/
  mem : (E →L[𝕜] E) → Prop
  /-- The real-valued norm gauge on the ideal. -/
  gauge : (E →L[𝕜] E) → ℝ
  zero_mem : mem 0
  add_mem : ∀ {A B}, mem A → mem B → mem (A + B)
  smul_mem : ∀ (c : 𝕜) {A}, mem A → mem (c • A)
  ideal_mem : ∀ (L R : E →L[𝕜] E) {A}, mem A → mem (L ∘L A ∘L R)
  adjoint_mem : ∀ {A}, mem A → mem A.adjoint
  nonneg : ∀ {A}, mem A → 0 ≤ gauge A
  gauge_zero : gauge 0 = 0
  gauge_eq_zero : ∀ {A}, mem A → gauge A = 0 → A = 0
  triangle : ∀ {A B}, mem A → mem B →
    gauge (A + B) ≤ gauge A + gauge B
  gauge_smul : ∀ (c : 𝕜) {A}, mem A →
    gauge (c • A) = ‖c‖ * gauge A
  gauge_adjoint : ∀ {A}, mem A → gauge A.adjoint = gauge A
  unitary_invariant : ∀ (U Uinv A : E →L[𝕜] E),
    TauCeti.LinearPMap.IsUnitaryOperator U → TauCeti.LinearPMap.IsUnitaryOperator Uinv →
    Uinv ∘L U = ContinuousLinearMap.id 𝕜 E →
    U ∘L Uinv = ContinuousLinearMap.id 𝕜 E →
    mem A → gauge (U ∘L A ∘L Uinv) = gauge A
  ideal_bound : ∀ (L R : E →L[𝕜] E) {A}, mem A →
    gauge (L ∘L A ∘L R) ≤ ‖L‖ * gauge A * ‖R‖
  opNorm_le_gauge : ∀ {A}, mem A → ‖A‖ ≤ gauge A
  gauge_complete : ∀ u : ℕ → (E →L[𝕜] E),
    (∀ n, mem (u n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      gauge (u m - u n) < ε) →
    ∃ A, mem A ∧ ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      gauge (u n - A) < ε

namespace SymmetricNormIdeal

/-! ### Concrete-ideal construction routes

* `operatorNorm`: take membership to be all bounded operators and discharge the
  fields with the ordinary operator norm, adjoint isometry, and composition
  submultiplicativity.
* `compactOperator`: restrict membership to compact operators and reuse the
  same gauge; closure under two-sided multiplication and completeness are the
  substantive seams.
* Schatten, trace-class, Hilbert--Schmidt, and Ky Fan gauges: construct singular
  values from the positive compact operator `A⋆A`, prove the ideal inequality
  and unitary invariance once at the sequence level, then instantiate the
  corresponding symmetric gauge.  Derive trace class and Hilbert--Schmidt from
  Schatten `p = 1` and `p = 2` instead of reproving every structure field.
-/

/-- Specialize a **canonical** operator ideal family to the square case on a
single Hilbert space.

The canonical family's gauge is `ℝ≥0∞`-valued, but `CanonicalRealView` already
supplies the `ℝ` view — `Mem`, `gaugeReal`, and the fourteen laws in exactly the
shape this structure's fields ask for — so the transcription is direct rather
than a re-proof.  `[IsComplete]` is what `gauge_complete` needs, and nothing
else here does.

Only `unitary_invariant` takes any work: the family supplies a two-sided
*bound*, and the equality comes from applying it in both directions with
`‖U‖, ‖Uinv‖ ≤ 1`. -/
noncomputable def ofCanonical
    (N : TauCeti.SymmetricOperatorIdealFamily (𝕜 := 𝕜))
    [N.toOperatorIdealFamily.IsComplete] :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) where
  mem A := N.Mem A
  gauge A := N.gaugeReal A
  zero_mem := N.zero_mem
  add_mem := N.add_mem
  smul_mem := N.smul_mem
  ideal_mem := fun L R => N.comp_mem L R
  adjoint_mem := N.adjoint_mem
  nonneg := N.gaugeReal_nonneg
  gauge_zero := N.gaugeReal_zero
  gauge_eq_zero := N.gaugeReal_eq_zero
  triangle := N.gaugeReal_add_le
  gauge_smul := N.gaugeReal_smul
  gauge_adjoint := N.gaugeReal_adjoint
  unitary_invariant := fun U Uinv A hU hUinv hUinvU _hUUinv hA => by
    have hUnorm : ‖U‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [one_mul]; exact le_of_eq (hU.1 x)
    have hUinvnorm : ‖Uinv‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [one_mul]; exact le_of_eq (hUinv.1 x)
    have shrink : ∀ (a b g : ℝ), a ≤ 1 → b ≤ 1 → 0 ≤ a → 0 ≤ b → 0 ≤ g →
        a * g * b ≤ g := by
      intro a b g ha hb ha0 hb0 hg0
      have h1 : a * g ≤ g := by nlinarith
      have h2 : 0 ≤ a * g := mul_nonneg ha0 hg0
      nlinarith
    have hforward : N.gaugeReal (U ∘L A ∘L Uinv) ≤ N.gaugeReal A :=
      (N.gaugeReal_comp_le U Uinv hA).trans
        (shrink _ _ _ hUnorm hUinvnorm (norm_nonneg _) (norm_nonneg _)
          (N.gaugeReal_nonneg hA))
    have hAeq : Uinv ∘L (U ∘L A ∘L Uinv) ∘L U = A := by
      ext x
      simp only [ContinuousLinearMap.comp_apply]
      have hx : Uinv (U x) = x := by
        have := congrArg (fun T : E →L[𝕜] E => T x) hUinvU
        simpa using this
      have hy : Uinv (U (A x)) = A x := by
        have := congrArg (fun T : E →L[𝕜] E => T (A x)) hUinvU
        simpa using this
      rw [hx, hy]
    have hbackward : N.gaugeReal A ≤ N.gaugeReal (U ∘L A ∘L Uinv) := by
      have h := N.gaugeReal_comp_le Uinv U (N.comp_mem U Uinv hA)
      rw [hAeq] at h
      exact h.trans
        (shrink _ _ _ hUinvnorm hUnorm (norm_nonneg _) (norm_nonneg _)
          (N.gaugeReal_nonneg (N.comp_mem U Uinv hA)))
    exact le_antisymm hforward hbackward
  ideal_bound := fun L R => N.gaugeReal_comp_le L R
  opNorm_le_gauge := N.opNorm_le_gaugeReal
  gauge_complete := N.gaugeReal_complete

/-- The operator norm ideal.

Built from `TauCeti.operatorNormFamily`, like every other entry in this
catalogue. -/
noncomputable def operatorNorm : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofCanonical (TauCeti.operatorNormFamily 𝕜)

/-! Concrete square ideals, each the diagonal restriction of the canonical
rectangular family of the same name. -/

/-- Compact operators with the ordinary operator norm. -/
noncomputable def compactOperator :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofCanonical (TauCeti.compactOperatorFamily 𝕜)

/-- Schatten `p` ideal induced by the canonical symmetric gauge. -/
noncomputable def schatten
    {p : ℝ} (hp : 1 ≤ p) :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofCanonical (TauCeti.schattenFamilySymmetric 𝕜 p hp)

/-- Trace-class ideal. -/
noncomputable def traceClass :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofCanonical (TauCeti.traceClassIdealFamily 𝕜)

/-- Hilbert--Schmidt ideal. -/
noncomputable def hilbertSchmidt : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofCanonical (TauCeti.hilbertSchmidtIdealFamily 𝕜)

/-- Ky Fan `k` gauge for positive `k`. -/
noncomputable def kyFan
    (k : ℕ) (hk : 0 < k) :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofCanonical (TauCeti.kyFanIdealFamily 𝕜 k hk)

/-- Unitary invariance of a symmetric ideal norm.

Ext-agent signature audit (GPT 5.6 High): Correct with explicit membership and two-sided
inverse data. The structure laws are deliberately restricted to ideal members; a real-valued
trace or Schatten gauge cannot satisfy norm laws on every bounded operator. The eventual
bundled ideal norm should make the equality a norm-isometry theorem.
-/
theorem gauge_unitary_conjugation
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U Uinv A : E →L[𝕜] E) (hA : I.mem A)
    (hU : TauCeti.LinearPMap.IsUnitaryOperator U)
    (hUinv : TauCeti.LinearPMap.IsUnitaryOperator Uinv)
    (hleft : Uinv ∘L U = ContinuousLinearMap.id 𝕜 E)
    (hright : U ∘L Uinv = ContinuousLinearMap.id 𝕜 E) :
    I.mem (U ∘L A ∘L Uinv) ∧
      I.gauge (U ∘L A ∘L Uinv) = I.gauge A :=
  ⟨I.ideal_mem U Uinv hA, I.unitary_invariant U Uinv A hU hUinv hleft hright hA⟩

omit [CompleteSpace E] in
/-- A unitary operator has operator norm at most `1`.

Stated as `≤ 1` rather than `= 1` on purpose: that is all the two-sided
invariance argument needs, and it avoids the nonzero-space side condition the
equality would carry. -/
theorem norm_le_one_of_isUnitaryOperator {W : E →L[𝕜] E}
    (hW : TauCeti.LinearPMap.IsUnitaryOperator W) : ‖W‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [hW.1 x, one_mul]

/-- **Two-sided unitary invariance of a symmetric ideal norm**: for *independent*
unitaries `U` and `V`, `gauge (U A V) = gauge A`.

`gauge_unitary_conjugation` above is the special case `V = U⁻¹`.  The two-sided
form is the one singular-value arguments need — two operators with the same
singular values are related by `A = U B V` with `U` and `V` unrelated, which
conjugation invariance does not cover.

No new structure field is required: `ideal_bound` gives `≤` because a unitary has
norm at most one, and applying it again to `A = U⁻¹ (U A V) V⁻¹` gives `≥`. -/
theorem gauge_two_sided_unitary
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U Uinv V Vinv A : E →L[𝕜] E) (hA : I.mem A)
    (hU : TauCeti.LinearPMap.IsUnitaryOperator U)
    (hUinv : TauCeti.LinearPMap.IsUnitaryOperator Uinv)
    (hV : TauCeti.LinearPMap.IsUnitaryOperator V)
    (hVinv : TauCeti.LinearPMap.IsUnitaryOperator Vinv)
    (hUl : Uinv ∘L U = ContinuousLinearMap.id 𝕜 E)
    (hVr : V ∘L Vinv = ContinuousLinearMap.id 𝕜 E) :
    I.mem (U ∘L A ∘L V) ∧ I.gauge (U ∘L A ∘L V) = I.gauge A := by
  refine ⟨I.ideal_mem U V hA, le_antisymm ?_ ?_⟩
  · calc I.gauge (U ∘L A ∘L V)
        ≤ ‖U‖ * I.gauge A * ‖V‖ := I.ideal_bound U V hA
      _ ≤ I.gauge A := by
          have h0 := I.nonneg hA
          have hUg : ‖U‖ * I.gauge A ≤ I.gauge A := by
            calc ‖U‖ * I.gauge A
                ≤ 1 * I.gauge A :=
                  mul_le_mul_of_nonneg_right
                    (norm_le_one_of_isUnitaryOperator hU) h0
              _ = I.gauge A := one_mul _
          calc ‖U‖ * I.gauge A * ‖V‖
              ≤ I.gauge A * ‖V‖ :=
                mul_le_mul_of_nonneg_right hUg (norm_nonneg V)
            _ ≤ I.gauge A * 1 :=
                mul_le_mul_of_nonneg_left
                  (norm_le_one_of_isUnitaryOperator hV) h0
            _ = I.gauge A := mul_one _
  · have hback : Uinv ∘L (U ∘L A ∘L V) ∘L Vinv = A := by
      have h : Uinv ∘L (U ∘L A ∘L V) ∘L Vinv
          = (Uinv ∘L U) ∘L A ∘L (V ∘L Vinv) := by
        ext x; rfl
      rw [h, hUl, hVr, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_id]
    calc I.gauge A
        = I.gauge (Uinv ∘L (U ∘L A ∘L V) ∘L Vinv) := by rw [hback]
      _ ≤ ‖Uinv‖ * I.gauge (U ∘L A ∘L V) * ‖Vinv‖ :=
          I.ideal_bound Uinv Vinv (I.ideal_mem U V hA)
      _ ≤ I.gauge (U ∘L A ∘L V) := by
          have h0 := I.nonneg (I.ideal_mem U V hA)
          have hUg : ‖Uinv‖ * I.gauge (U ∘L A ∘L V)
              ≤ I.gauge (U ∘L A ∘L V) := by
            calc ‖Uinv‖ * I.gauge (U ∘L A ∘L V)
                ≤ 1 * I.gauge (U ∘L A ∘L V) :=
                  mul_le_mul_of_nonneg_right
                    (norm_le_one_of_isUnitaryOperator hUinv) h0
              _ = I.gauge (U ∘L A ∘L V) := one_mul _
          calc ‖Uinv‖ * I.gauge (U ∘L A ∘L V) * ‖Vinv‖
              ≤ I.gauge (U ∘L A ∘L V) * ‖Vinv‖ :=
                mul_le_mul_of_nonneg_right hUg (norm_nonneg Vinv)
            _ ≤ I.gauge (U ∘L A ∘L V) * 1 :=
                mul_le_mul_of_nonneg_left
                  (norm_le_one_of_isUnitaryOperator hVinv) h0
            _ = I.gauge (U ∘L A ∘L V) := mul_one _

/-- Pinching is contractive for every symmetric norm ideal.

Lean proof route for a weaker agent:

1. Let `J=2P-I`; show `J` is unitary and `diagonalPart U A = (A+J A J)/2`.
2. Use ideal membership under left/right multiplication to obtain membership of `J A J` and the sum.
3. Apply unitary invariance, homogeneity, and the triangle inequality to get the sharp contraction bound.


Ext-agent signature audit (GPT 5.6 High): Correct for symmetric ideals. Reflection
averaging gives both membership and the sharp constant one.

Preferred dependency route: First realize ideal members as a complete normed space; then
use reflection averaging, two-sided ideal bounds, and unitary invariance.
-/
theorem gauge_diagonalPart_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : I.mem A) :
    I.mem (U.diagonalPart A) ∧
      I.gauge (U.diagonalPart A) ≤ I.gauge A := by
  let J := U.reflectionOperator
  have hJ : TauCeti.LinearPMap.IsUnitaryOperator J :=
    ⟨U.reflectionOperator_norm_map, U.reflectionOperator_surjective⟩
  have hJinv : J ∘L J = ContinuousLinearMap.id 𝕜 E :=
    Submodule.reflectionOperator_involutive U
  have hconjMem : I.mem (J ∘L A ∘L J) := I.ideal_mem J J hA
  have hconjGauge : I.gauge (J ∘L A ∘L J) = I.gauge A :=
    I.unitary_invariant J J A hJ hJ hJinv hJinv hA
  have hformula : (2 : 𝕜) • U.diagonalPart A = A + J ∘L A ∘L J :=
    Submodule.two_smul_diagonalPart_eq_add_reflectionConjugate U A
  have hsumMem : I.mem (A + J ∘L A ∘L J) := I.add_mem hA hconjMem
  have hhalf : ((2 : 𝕜)⁻¹) • ((2 : 𝕜) • U.diagonalPart A) =
      U.diagonalPart A := by module
  have hdiagMem : I.mem (U.diagonalPart A) := by
    rw [← hhalf, hformula]
    exact I.smul_mem _ hsumMem
  refine ⟨hdiagMem, ?_⟩
  have hscaled := I.gauge_smul (2 : 𝕜) hdiagMem
  rw [hformula, RCLike.norm_ofNat] at hscaled
  have htriangle := I.triangle hA hconjMem
  rw [hconjGauge] at htriangle
  nlinarith

/-- Off-diagonal extraction has norm at most one in the sharp symmetric-ideal
form used by the double-angle theorems.

Lean proof route for a weaker agent:

1. Use `offDiagonalPart U A = (A-J A J)/2` for the reflection `J=2P-I`.
2. Prove membership using the ideal axioms and scalar closure.
3. Apply unitary invariance and the triangle inequality exactly as in the pinching lemma.


Ext-agent signature audit (GPT 5.6 High): Correct for symmetric ideals. The
difference-of-unitary-conjugates formula gives the same sharp contraction as pinching.

Preferred dependency route: First realize ideal members as a complete normed space; then
use reflection averaging, two-sided ideal bounds, and unitary invariance.
-/
theorem gauge_offDiagonalPart_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : I.mem A) :
    I.mem (U.offDiagonalPart A) ∧
      I.gauge (U.offDiagonalPart A) ≤ I.gauge A := by
  let J := U.reflectionOperator
  have hJ : TauCeti.LinearPMap.IsUnitaryOperator J :=
    ⟨U.reflectionOperator_norm_map, U.reflectionOperator_surjective⟩
  have hJinv : J ∘L J = ContinuousLinearMap.id 𝕜 E :=
    Submodule.reflectionOperator_involutive U
  have hconjMem : I.mem (J ∘L A ∘L J) := I.ideal_mem J J hA
  have hnegConjMem : I.mem (-(J ∘L A ∘L J)) := by
    simpa using I.smul_mem (-1 : 𝕜) hconjMem
  have hconjGauge : I.gauge (J ∘L A ∘L J) = I.gauge A :=
    I.unitary_invariant J J A hJ hJ hJinv hJinv hA
  have hformula : (2 : 𝕜) • U.offDiagonalPart A = A - J ∘L A ∘L J :=
    Submodule.two_smul_offDiagonalPart_eq_sub_reflectionConjugate U A
  have hdiffMem : I.mem (A - J ∘L A ∘L J) := by
    simpa [sub_eq_add_neg] using I.add_mem hA hnegConjMem
  have hhalf : ((2 : 𝕜)⁻¹) • ((2 : 𝕜) • U.offDiagonalPart A) =
      U.offDiagonalPart A := by module
  have hoffMem : I.mem (U.offDiagonalPart A) := by
    rw [← hhalf, hformula]
    exact I.smul_mem _ hdiffMem
  refine ⟨hoffMem, ?_⟩
  have hscaled := I.gauge_smul (2 : 𝕜) hoffMem
  rw [hformula, RCLike.norm_ofNat] at hscaled
  have hnegGauge : I.gauge (-(J ∘L A ∘L J)) = I.gauge (J ∘L A ∘L J) := by
    have h := I.gauge_smul (-1 : 𝕜) hconjMem
    rw [neg_one_smul] at h
    simpa using h
  have htriangle : I.gauge (A - J ∘L A ∘L J) ≤
      I.gauge A + I.gauge (J ∘L A ∘L J) := by
    rw [sub_eq_add_neg]
    calc I.gauge (A + -(J ∘L A ∘L J))
          ≤ I.gauge A + I.gauge (-(J ∘L A ∘L J)) := I.triangle hA hnegConjMem
      _ = I.gauge A + I.gauge (J ∘L A ∘L J) := by rw [hnegGauge]
  rw [hconjGauge] at htriangle
  nlinarith

end SymmetricNormIdeal
end DavisKahanExt
end TauCeti
