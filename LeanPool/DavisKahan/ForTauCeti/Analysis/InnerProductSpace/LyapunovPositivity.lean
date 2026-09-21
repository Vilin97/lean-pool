/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# A Lyapunov positivity criterion

If `X` is self-adjoint, `G` is positive and injective, and the anticommutator
`X G + G X` is positive, then `X` is positive.

The invertible case is classical and immediate: conjugating by `G^(-1/2)` turns
the hypothesis into accretivity of an operator similar to `X`, and a self-adjoint
operator whose spectrum lies in the closed right half-plane is positive.  That
proof needs `G` bounded below, which is exactly what fails in the application.

The point of this module is that injectivity is enough.  The invertibility is
recovered from the *other* operator: on the spectral subspace where `X ≤ -β`, the
operator `-X` is bounded below by `β`, and running the classical argument there
forces the compression of `G` to have spectrum `{0}`, hence to vanish -- which
injectivity forbids.
-/

namespace TauCeti
namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A dissipative operator has spectrum in the closed left half-plane.**

The contrapositive of `isUnit_of_coercive`: at a point of the open right
half-plane the shifted operator is coercive, hence a unit, hence not spectral. -/
theorem spectrum_re_nonpos_of_dissipative (Z : H →L[ℂ] H)
    (h : ∀ x, RCLike.re ⟪Z x, x⟫_ℂ ≤ 0) :
    ∀ z ∈ spectrum ℂ Z, z.re ≤ 0 := by
  intro z hz
  by_contra hnot
  push Not at hnot
  have hcoer : ∀ x : H, z.re * ‖x‖ ^ 2 ≤
      RCLike.re ⟪(z • _root_.ContinuousLinearMap.id ℂ H - Z) x, x⟫_ℂ := by
    intro x
    have hz' : RCLike.re ⟪z • x, x⟫_ℂ = z.re * ‖x‖ ^ 2 := by
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp [RCLike.re_to_complex, pow_two]
    have hx := h x
    simp only [sub_apply, smul_apply,
      _root_.ContinuousLinearMap.id_apply, inner_sub_left, map_sub]
    rw [hz']
    linarith
  have hunit := TauCeti.ContinuousLinearMap.isUnit_of_coercive hnot hcoer
  rw [spectrum.mem_iff] at hz
  apply hz
  rw [Algebra.algebraMap_eq_smul_one]
  exact hunit

omit [CompleteSpace H] in
/-- The quadratic form of a nonnegative operator is nonnegative. -/
theorem re_inner_nonneg_of_nonneg {T : H →L[ℂ] H} (hT : (0 : H →L[ℂ] H) ≤ T) (x : H) :
    0 ≤ RCLike.re ⟪T x, x⟫_ℂ := by
  rw [_root_.ContinuousLinearMap.nonneg_iff_isPositive] at hT
  have := hT.2 x
  rwa [_root_.ContinuousLinearMap.reApplyInnerSelf_apply] at this

/-- **A positive invertible operator annihilates a positive one through a
nonpositive anticommutator.**

If `A ≥ 0` is invertible, `K ≥ 0`, and `A K + K A ≤ 0`, then `K = 0`.

Conjugating by `A^(-1/2)` turns the hypothesis into dissipativity of
`Z = A^(1/2) K A^(-1/2)`, so `Z` has spectrum in the closed left half-plane;
`Z` is similar to `K`, and `K ≥ 0` puts its spectrum in `[0, ∞)`.  The two force
`spectrum K = {0}`, and a self-adjoint operator whose spectral radius vanishes is
zero. -/
theorem eq_zero_of_anticommutator_nonpos {A K : H →L[ℂ] H}
    (hA : (0 : H →L[ℂ] H) ≤ A) (hAunit : IsUnit A) (hK : (0 : H →L[ℂ] H) ≤ K)
    (h : A * K + K * A ≤ 0) : K = 0 := by
  classical
  set R : H →L[ℂ] H := A ^ (1 / 2 : ℝ) with hRdef
  set Rinv : H →L[ℂ] H := A ^ (-1 / 2 : ℝ) with hRinvdef
  have hRinvR : Rinv * R = 1 := by
    calc Rinv * R = A ^ (-1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) := rfl
      _ = A ^ ((-1 / 2 : ℝ) + (1 / 2 : ℝ)) := (CFC.rpow_add hAunit).symm
      _ = A ^ (0 : ℝ) := by norm_num
      _ = 1 := CFC.rpow_zero A hA
  have hRRinv : R * Rinv = 1 := by
    calc R * Rinv = A ^ (1 / 2 : ℝ) * A ^ (-1 / 2 : ℝ) := rfl
      _ = A ^ ((1 / 2 : ℝ) + (-1 / 2 : ℝ)) := (CFC.rpow_add hAunit).symm
      _ = A ^ (0 : ℝ) := by norm_num
      _ = 1 := CFC.rpow_zero A hA
  have hRR : R * R = A := by
    calc R * R = A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) := rfl
      _ = A ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := (CFC.rpow_add hAunit).symm
      _ = A ^ (1 : ℝ) := by norm_num
      _ = A := CFC.rpow_one A hA
  have hRstar : star R = R :=
    (CFC.rpow_nonneg (a := A) (y := (1 / 2 : ℝ))).isSelfAdjoint.star_eq
  have hRinvstar : star Rinv = Rinv :=
    (CFC.rpow_nonneg (a := A) (y := (-1 / 2 : ℝ))).isSelfAdjoint.star_eq
  have hKstar : star K = K := (hK.isSelfAdjoint).star_eq
  set Z : H →L[ℂ] H := R * K * Rinv with hZdef
  have hZstar : star Z = Rinv * K * R := by
    rw [hZdef, star_mul, star_mul, hRstar, hRinvstar, hKstar, mul_assoc]
  -- the conjugated anticommutator
  have hconj : Z + star Z = Rinv * (A * K + K * A) * Rinv := by
    rw [hZstar, hZdef, mul_add, add_mul]
    congr 1
    · calc R * K * Rinv = (Rinv * R) * (R * K * Rinv) := by rw [hRinvR, one_mul]
        _ = Rinv * (A * K) * Rinv := by rw [← hRR]; noncomm_ring
    · calc Rinv * K * R = (Rinv * K * R) * (R * Rinv) := by rw [hRRinv, mul_one]
        _ = Rinv * (K * A) * Rinv := by rw [← hRR]; noncomm_ring
  -- dissipativity
  have hdiss : ∀ x : H, RCLike.re ⟪Z x, x⟫_ℂ ≤ 0 := by
    intro x
    have hnonpos : (0 : H →L[ℂ] H) ≤ -(A * K + K * A) := by
      simpa using neg_nonneg.mpr h
    have hform : RCLike.re ⟪(Z + star Z) x, x⟫_ℂ ≤ 0 := by
      rw [hconj]
      have happ : (Rinv * (A * K + K * A) * Rinv) x
          = Rinv ((A * K + K * A) (Rinv x)) := rfl
      rw [happ]
      have hadj : ⟪Rinv ((A * K + K * A) (Rinv x)), x⟫_ℂ
          = ⟪(A * K + K * A) (Rinv x), Rinv x⟫_ℂ := by
        rw [← _root_.ContinuousLinearMap.adjoint_inner_left]
        congr 1
        rw [← _root_.ContinuousLinearMap.star_eq_adjoint, hRinvstar]
      rw [hadj]
      have := re_inner_nonneg_of_nonneg hnonpos (Rinv x)
      rw [neg_apply, inner_neg_left, map_neg] at this
      linarith
    have hsplit : RCLike.re ⟪(Z + star Z) x, x⟫_ℂ = 2 * RCLike.re ⟪Z x, x⟫_ℂ := by
      rw [add_apply, inner_add_left, map_add]
      have hstarInner : RCLike.re ⟪star Z x, x⟫_ℂ = RCLike.re ⟪Z x, x⟫_ℂ := by
        rw [_root_.ContinuousLinearMap.star_eq_adjoint,
          _root_.ContinuousLinearMap.adjoint_inner_left]
        exact inner_re_symm x (Z x)
      rw [hstarInner]
      ring
    linarith [hform, hsplit ▸ hform]
  -- spectrum of `Z`, hence of `K`
  have hspecZ := spectrum_re_nonpos_of_dissipative Z hdiss
  have hRunit : IsUnit R := ⟨⟨R, Rinv, hRRinv, hRinvR⟩, rfl⟩
  have hRinvunit : IsUnit Rinv := ⟨⟨Rinv, R, hRinvR, hRRinv⟩, rfl⟩
  have hkey : ∀ z : ℂ, z • (1 : H →L[ℂ] H) - Z = R * (z • (1 : H →L[ℂ] H) - K) * Rinv := by
    intro z
    have hone : R * (z • (1 : H →L[ℂ] H)) * Rinv = z • (1 : H →L[ℂ] H) := by
      rw [mul_smul_comm, mul_one, smul_mul_assoc, hRRinv]
    rw [hZdef, mul_sub, sub_mul, hone]
  have hspecEq : spectrum ℂ K = spectrum ℂ Z := by
    ext z
    simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    constructor
    · intro hK' hZ'
      apply hK'
      have hthis : z • (1 : H →L[ℂ] H) - K = Rinv * (z • (1 : H →L[ℂ] H) - Z) * R := by
        rw [hkey z]
        calc z • (1 : H →L[ℂ] H) - K
            = Rinv * R * (z • (1 : H →L[ℂ] H) - K) * (Rinv * R) := by
              rw [hRinvR, one_mul, mul_one]
          _ = Rinv * (R * (z • (1 : H →L[ℂ] H) - K) * Rinv) * R := by noncomm_ring
      rw [hthis]
      exact (hRinvunit.mul hZ').mul hRunit
    · intro hZ' hK'
      apply hZ'
      rw [hkey z]
      exact (hRunit.mul hK').mul hRinvunit
  -- the spectrum of `K` is `{0}`
  have hKsa : IsSelfAdjoint K := hK.isSelfAdjoint
  have hzero : ∀ z ∈ spectrum ℂ K, ‖z‖₊ = 0 := by
    intro z hz
    have hre : z.re ≤ 0 := hspecZ z (hspecEq ▸ hz)
    have hz' : z ∈ (algebraMap ℝ ℂ) '' spectrum ℝ K := by
      rw [hKsa.spectrumRestricts.algebraMap_image]
      exact hz
    obtain ⟨r, hr, rfl⟩ := hz'
    have hrnn : 0 ≤ r := spectrum_nonneg_of_nonneg hK hr
    have hrle : r ≤ 0 := by simpa using hre
    have : r = 0 := le_antisymm hrle hrnn
    simp [this]
  have hrad : spectralRadius ℂ K = 0 := by
    rw [spectralRadius, ENNReal.iSup_eq_zero]
    intro z
    rw [ENNReal.iSup_eq_zero]
    intro hz
    exact_mod_cast hzero z hz
  have hnn : ‖K‖₊ = 0 := by
    have := (K.spectralRadius_eq_nnnorm hKsa).symm.trans hrad
    exact_mod_cast this
  exact nnnorm_eq_zero.mp hnn

/-- The anticommutator of two self-adjoint operators is self-adjoint. -/
theorem anticommutator_isSelfAdjoint (S T : H →L[ℂ] H)
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) : IsSelfAdjoint (S * T + T * S) := by
  rw [_root_.IsSelfAdjoint, star_add, star_mul, star_mul, hS.star_eq, hT.star_eq]
  abel

/-- **The Lyapunov positivity criterion.**

`X` self-adjoint, `G` positive and injective, and `X G + G X` positive together
force `X` positive.

Injectivity of `G` cannot be dropped: `X = diag(1, -1)` and `G = diag(1, 0)` have
`X G + G X = diag(2, 0) ≥ 0` with `X` indefinite.  But `G` is *not* assumed
bounded below, which is the whole point -- in the Davis--Kahan application `G` is
the inverse of an unbounded operator, so its spectrum reaches `0`.

The invertibility the classical argument wants is taken from `X` instead of from
`G`.  On the spectral subspace where `X ≤ -β` the operator `1 - P - X P` is
bounded below by `β/2`, and the compression of `G` there is annihilated by
`eq_zero_of_anticommutator_nonpos`; injectivity then forces that spectral
subspace to be trivial, for every `β > 0`. -/
theorem nonneg_of_lyapunov_nonneg {X G : H →L[ℂ] H}
    (hX : IsSelfAdjoint X) (hG : (0 : H →L[ℂ] H) ≤ G) (hGinj : Function.Injective G)
    (h : (0 : H →L[ℂ] H) ≤ X * G + G * X) : (0 : H →L[ℂ] H) ≤ X := by
  classical
  -- it is enough to bound the form below by `-β` for every small `β > 0`
  have hmain : ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ x : H,
      -β * ‖x‖ ^ 2 ≤ RCLike.re ⟪X x, x⟫_ℂ := by
    intro β hβ hβ1 x
    set P : H →L[ℂ] H :=
      (TauCeti.BorelCalculus.boundedPVM hX).proj (Set.Iic (-β)) measurableSet_Iic with hPdef
    have hPsa : IsSelfAdjoint P :=
      (TauCeti.BorelCalculus.boundedPVM hX).isSelfAdjoint_proj _ _
    have hPidem : P * P = P :=
      (TauCeti.BorelCalculus.boundedPVM hX).proj_idem _ _
    have hPcomm : X * P = P * X :=
      TauCeti.BorelCalculus.boundedPVM_proj_comm hX (Set.Iic (-β)) measurableSet_Iic
    -- the spectral form bound on the range of `P`
    have hPbound : ∀ v : H, RCLike.re ⟪X (P v), P v⟫_ℂ ≤ (-β / 2) * ‖P v‖ ^ 2 := by
      intro v
      refine TauCeti.BorelCalculus.re_inner_le_of_boundedPVM_proj_Ici_eq_zero hX (-β / 2) ?_
      have hdisj : Set.Ici (-β / 2) ∩ Set.Iic (-β) = (∅ : Set ℝ) := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 h2
        linarith
      have hmul := (TauCeti.BorelCalculus.boundedPVM hX).proj_inter
        (Set.Ici (-β / 2)) (Set.Iic (-β)) measurableSet_Ici measurableSet_Iic
      rw [(TauCeti.BorelCalculus.boundedPVM hX).proj_congr hdisj
        (measurableSet_Ici.inter measurableSet_Iic) MeasurableSet.empty,
        (TauCeti.BorelCalculus.boundedPVM hX).proj_empty] at hmul
      have := congrArg (fun T : H →L[ℂ] H => T v) hmul
      simpa [hPdef] using this
    -- pointwise consequences of `P` being a self-adjoint idempotent commuting with `X`
    have hPP : ∀ y : H, P (P y) = P y := fun y => by
      have := congrArg (fun T : H →L[ℂ] H => T y) hPidem
      simpa using this
    have hadjP : ∀ y z : H, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ := by
      intro y z
      conv_lhs => rw [← hPsa.star_eq]
      rw [_root_.ContinuousLinearMap.star_eq_adjoint,
        _root_.ContinuousLinearMap.adjoint_inner_left]
    have hXP : X * P = P * (X * P) := by
      calc X * P = X * (P * P) := by rw [hPidem]
        _ = (X * P) * P := by noncomm_ring
        _ = (P * X) * P := by rw [hPcomm]
        _ = P * (X * P) := by noncomm_ring
    have hPXP : ∀ y : H, P (X (P y)) = X (P y) := by
      intro y
      have := congrArg (fun T : H →L[ℂ] H => T y) hXP.symm
      simpa using this
    -- the positive invertible operator
    set A : H →L[ℂ] H := 1 - P - X * P with hAdef
    have hAsa : IsSelfAdjoint A := by
      rw [hAdef]
      refine (IsSelfAdjoint.sub (IsSelfAdjoint.sub (IsSelfAdjoint.one _) hPsa) ?_)
      rw [_root_.IsSelfAdjoint, star_mul, hPsa.star_eq, hX.star_eq, ← hPcomm]
    have hAcoer : ∀ v : H, (β / 2) * ‖v‖ ^ 2 ≤ RCLike.re ⟪A v, v⟫_ℂ := by
      intro v
      have hPv : ⟪P v, v⟫_ℂ = ⟪P v, P v⟫_ℂ := by
        calc ⟪P v, v⟫_ℂ = ⟪v, P v⟫_ℂ := hadjP v v
          _ = ⟪v, P (P v)⟫_ℂ := by rw [hPP v]
          _ = ⟪P v, P v⟫_ℂ := (hadjP v (P v)).symm
      have hXPv : ⟪(X * P) v, v⟫_ℂ = ⟪X (P v), P v⟫_ℂ := by
        change ⟪X (P v), v⟫_ℂ = _
        rw [← hPXP v, hadjP (X (P v)) v, hPXP v]
      have hself : RCLike.re ⟪P v, P v⟫_ℂ = ‖P v‖ ^ 2 :=
        inner_self_eq_norm_sq (𝕜 := ℂ) (P v)
      have hvv : RCLike.re ⟪v, v⟫_ℂ = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
      have hnorm : ‖P v‖ ≤ ‖v‖ := by
        have h1 : ‖P v‖ ^ 2 = RCLike.re ⟪P v, v⟫_ℂ := by rw [hPv, hself]
        have h2 : RCLike.re ⟪P v, v⟫_ℂ ≤ ‖P v‖ * ‖v‖ := by
          calc RCLike.re ⟪P v, v⟫_ℂ ≤ ‖⟪P v, v⟫_ℂ‖ := RCLike.re_le_norm _
            _ ≤ ‖P v‖ * ‖v‖ := norm_inner_le_norm _ _
        nlinarith [norm_nonneg (P v), norm_nonneg v]
      have hb := hPbound v
      have hA : RCLike.re ⟪A v, v⟫_ℂ
          = ‖v‖ ^ 2 - ‖P v‖ ^ 2 - RCLike.re ⟪X (P v), P v⟫_ℂ := by
        rw [hAdef]
        simp only [sub_apply, inner_sub_left, map_sub]
        rw [show ((1 : H →L[ℂ] H)) v = v from rfl, hXPv, hPv, hself, hvv]
      have hnormsq : ‖P v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        nlinarith [hnorm, norm_nonneg (P v), norm_nonneg v]
      rw [hA]
      nlinarith [hb, hnormsq, hβ, hβ1]
    have hAunit : IsUnit A :=
      TauCeti.ContinuousLinearMap.isUnit_of_coercive (by positivity) hAcoer
    have hAnonneg : (0 : H →L[ℂ] H) ≤ A := by
      rw [_root_.ContinuousLinearMap.nonneg_iff_isPositive]
      refine ⟨_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAsa, fun v => ?_⟩
      rw [_root_.ContinuousLinearMap.reApplyInnerSelf_apply]
      nlinarith [hAcoer v, norm_nonneg v, hβ]
    -- the compression of `G`
    set K : H →L[ℂ] H := P * G * P with hKdef
    have hKform : ∀ v : H, ⟪K v, v⟫_ℂ = ⟪G (P v), P v⟫_ℂ := by
      intro v
      change ⟪P (G (P v)), v⟫_ℂ = _
      rw [hadjP (G (P v)) v]
    have hKsa : IsSelfAdjoint K := by
      rw [hKdef, _root_.IsSelfAdjoint, star_mul, star_mul, hPsa.star_eq, hG.isSelfAdjoint.star_eq,
        mul_assoc]
    have hKnonneg : (0 : H →L[ℂ] H) ≤ K := by
      rw [_root_.ContinuousLinearMap.nonneg_iff_isPositive]
      refine ⟨_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hKsa, fun v => ?_⟩
      rw [_root_.ContinuousLinearMap.reApplyInnerSelf_apply, hKform]
      exact re_inner_nonneg_of_nonneg hG (P v)
    -- the compressed Lyapunov inequality
    have hcompress : ∀ v : H,
        RCLike.re ⟪(X * K + K * X) v, v⟫_ℂ
          = RCLike.re ⟪(X * G + G * X) (P v), P v⟫_ℂ := by
      intro v
      have hXK : ⟪(X * K) v, v⟫_ℂ = ⟪(X * G) (P v), P v⟫_ℂ := by
        change ⟪X (P (G (P v))), v⟫_ℂ = ⟪X (G (P v)), P v⟫_ℂ
        have hXPeq : X (P (G (P v))) = P (X (G (P v))) := by
          have := congrArg (fun T : H →L[ℂ] H => T (G (P v))) hPcomm
          simpa using this
        rw [hXPeq, hadjP (X (G (P v))) v]
      have hKX : ⟪(K * X) v, v⟫_ℂ = ⟪(G * X) (P v), P v⟫_ℂ := by
        change ⟪P (G (P (X v))), v⟫_ℂ = ⟪G (X (P v)), P v⟫_ℂ
        have hPXeq : P (X v) = X (P v) := by
          have := congrArg (fun T : H →L[ℂ] H => T v) hPcomm
          simpa using this.symm
        rw [hPXeq, hadjP (G (X (P v))) v]
      simp only [add_apply, inner_add_left, map_add]
      rw [hXK, hKX]
    have hAK : A * K + K * A = -(X * K + K * X) := by
      have hPK : P * K = K := by
        rw [hKdef]
        calc P * (P * G * P) = (P * P) * G * P := by noncomm_ring
          _ = P * G * P := by rw [hPidem]
      have hKP : K * P = K := by
        rw [hKdef]
        calc (P * G * P) * P = P * G * (P * P) := by noncomm_ring
          _ = P * G * P := by rw [hPidem]
      rw [hAdef]
      calc (1 - P - X * P) * K + K * (1 - P - X * P)
          = (K - P * K - X * (P * K)) + (K - K * P - (K * X) * P) := by noncomm_ring
        _ = -(X * K + K * X) := by
            rw [hPK, hKP]
            have hKXP : (K * X) * P = K * X := by
              calc (K * X) * P = K * (X * P) := by noncomm_ring
                _ = K * (P * X) := by rw [hPcomm]
                _ = (K * P) * X := by noncomm_ring
                _ = K * X := by rw [hKP]
            rw [hKXP]
            abel
    have hXKnonneg : (0 : H →L[ℂ] H) ≤ X * K + K * X := by
      rw [_root_.ContinuousLinearMap.nonneg_iff_isPositive]
      constructor
      · refine _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ?_
        exact anticommutator_isSelfAdjoint X K hX hKsa
      · intro v
        rw [_root_.ContinuousLinearMap.reApplyInnerSelf_apply, hcompress v]
        exact re_inner_nonneg_of_nonneg h (P v)
    have hAKnonpos : A * K + K * A ≤ 0 := by
      rw [hAK]
      exact neg_nonpos.mpr hXKnonneg
    have hK0 : K = 0 :=
      eq_zero_of_anticommutator_nonpos hAnonneg hAunit hKnonneg hAKnonpos
    -- injectivity kills the spectral subspace
    have hP0 : P x = 0 := by
      have hzero : ⟪G (P x), P x⟫_ℂ = 0 := by
        rw [← hKform, hK0]
        simp
      obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG
      have hGb : ∀ y : H, ⟪G y, y⟫_ℂ = ⟪b y, b y⟫_ℂ := by
        intro y
        rw [hb]
        change ⟪(star b) (b y), y⟫_ℂ = _
        rw [_root_.ContinuousLinearMap.star_eq_adjoint,
          _root_.ContinuousLinearMap.adjoint_inner_left]
      have hb0 : b (P x) = 0 := by
        have := hGb (P x)
        rw [hzero] at this
        exact inner_self_eq_zero.mp this.symm
      have hGP : G (P x) = 0 := by
        rw [hb]
        change (star b) (b (P x)) = 0
        rw [hb0]
        simp
      have : G (P x) = G 0 := by rw [hGP, map_zero]
      exact hGinj this
    have hfin := TauCeti.BorelCalculus.le_re_inner_of_boundedPVM_proj_Iic_eq_zero hX (-β)
      (show (TauCeti.BorelCalculus.boundedPVM hX).proj (Set.Iic (-β)) measurableSet_Iic x = 0
        from hP0)
    simpa [RCLike.re_to_complex] using hfin
  -- pass to the limit
  rw [_root_.ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hX, fun x => ?_⟩
  rw [_root_.ContinuousLinearMap.reApplyInnerSelf_apply]
  by_contra hc
  push Not at hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hc
  have hn : 0 < ‖x‖ ^ 2 := by positivity
  set r : ℝ := RCLike.re ⟪X x, x⟫_ℂ with hr
  set β : ℝ := min 1 (-r / (2 * ‖x‖ ^ 2)) with hβdef
  have hrneg : r < 0 := hc
  have hβpos : 0 < β := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβle : β ≤ -r / (2 * ‖x‖ ^ 2) := min_le_right _ _
  have hkey := hmain β hβpos hβ1 x
  have : -β * ‖x‖ ^ 2 ≥ r / 2 := by
    have hmul : β * ‖x‖ ^ 2 ≤ (-r / (2 * ‖x‖ ^ 2)) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hβle (by positivity)
    have hsimp : (-r / (2 * ‖x‖ ^ 2)) * ‖x‖ ^ 2 = -r / 2 := by
      field_simp
    rw [hsimp] at hmul
    linarith
  linarith

end ContinuousLinearMap
end TauCeti
