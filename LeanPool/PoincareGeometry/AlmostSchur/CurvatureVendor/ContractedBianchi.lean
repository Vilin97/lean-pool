/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

/- Adapted from Arthur Freitas Ramos's committed contracted-bianchi formalization.
Source commit: 12cebb809524d0cd185c6cd7bcb5b73d3562bce1
Source blob: d0b2de8b9b209bbdf16cae3e839239a6ed7b8857
Source path: contracted-bianchi/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ContractedBianchi.lean
See PROVENANCE.json for the exact extraction and local changes. -/

public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.Contractions

/-!
# Contracted second Bianchi identity

This file packages the covariant derivative of the curvature tensor at a point and contracts the
second Bianchi identity twice.  The derivative is written using the same corrected raw
commutator as `Bianchi.lean`; the correction terms are the covariant derivatives of all three
curvature arguments, so this is not an assumption of the contracted identity.

This file currently proves the cyclic identity for that corrected derivative.  The contraction
and the identification of the resulting traces with geometric Ricci and Einstein divergence
require additional results; they are not established in this file.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

section C3Extension

variable [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

lemma contMDiffOn_extend_baseSet_threeAlmostSchur {x : M} (v : TM x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% (extend E v))
      (trivializationAt E TM x).baseSet := by
  let t := trivializationAt E TM x
  suffices ContMDiffOn I 𝓘(ℝ, E) 3
      (fun y ↦ (t ⟨y, extend E v y⟩).2) t.baseSet by
    intro y hy
    rw [t.contMDiffWithinAt_section _ hy]
    exact this y hy
  let w : E := (t ⟨x, v⟩).2
  have hw : ContMDiffOn I 𝓘(ℝ, E) 3 (fun _y ↦ w) t.baseSet :=
    contMDiffOn_const
  exact hw.congr (fun y hy ↦ by
    change (t ⟨y, t.symm y w⟩).2 = w
    simpa using congrArg Prod.snd (t.apply_mk_symm hy w))

lemma smoothExtend_contMDiff_threeAlmostSchur (x : M) (v : TM x) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y
        (smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x v y)) := by
  let φ : SmoothBumpFunction I x := smoothExtendBumpAlmostSchur (I := I) (F := E) (V := TM) x
  have hφ : ContMDiff I 𝓘(ℝ) 3 (φ : M → ℝ) := by
    have hφω : ContMDiff I 𝓘(ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) (φ : M → ℝ) :=
      φ.contMDiff
    have hle : (3 : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
      exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ (⊤ : ℕ∞))
    exact hφω.of_le hle
  have hv : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% (extend E v))
      (trivializationAt E TM x).baseSet :=
    contMDiffOn_extend_baseSet_threeAlmostSchur (I := I) (E := E) (M := M) v
  simpa [smoothExtendAlmostSchur] using
    ContMDiffOn.smul_section_of_tsupport
      (u := (trivializationAt E TM x).baseSet)
      (n := 3) (ψ := (smoothExtendBumpAlmostSchur (I := I) (F := E) (V := TM) x : M → ℝ))
      hφ.contMDiffOn (trivializationAt E TM x).open_baseSet
      (tsupport_smoothExtendBump_subsetAlmostSchur (I := I) (F := E) (V := TM) x) hv

end C3Extension

section ContractedIdentity

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]

/- The pointwise covariant derivative of the curvature tensor, evaluated using canonical smooth
extensions.  `secondBianchiAuxAlmostSchur` is the corrected expression
`∇ₚ(R(a,b)c) - R(∇ₚa,b)c - R(a,∇ₚb)c - R(a,b)∇ₚc`. -/
noncomputable def curvatureCovariantDerivativeAlmostSchur (x : M)
    (p a b c : TM x) : TM x :=
  cov.secondBianchiAuxAlmostSchur
    (smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x p)
    (smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x a)
    (smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x b)
    (smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x c) x

noncomputable def curvatureCovariantDerivativeInnerAlmostSchur (x : M)
    (p a b c d : TM x) : ℝ :=
  inner ℝ (curvatureCovariantDerivativeAlmostSchur (cov := cov) x p a b c) d

theorem curvatureCovariantDerivativeInner_secondBianchiAlmostSchur (x : M)
    (hT : cov.torsion = 0)
    (p a b c d : TM x) :
    curvatureCovariantDerivativeInnerAlmostSchur (cov := cov) x p a b c d +
        curvatureCovariantDerivativeInnerAlmostSchur (cov := cov) x a b p c d +
        curvatureCovariantDerivativeInnerAlmostSchur (cov := cov) x b p a c d = 0 := by
  have h := cov.secondBianchiAux_apply_of_torsion_eq_zeroAlmostSchur
    (hT := hT)
    (x := x)
    (X := smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x p)
    (Y := smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x a)
    (Z := smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x b)
    (W := smoothExtendAlmostSchur (I := I) (F := E) (V := TM) x c)
    (smoothExtend_contMDiff_twoAlmostSchur (I := I) (F := E) (V := TM) x p)
    (smoothExtend_contMDiff_twoAlmostSchur (I := I) (F := E) (V := TM) x a)
    (smoothExtend_contMDiff_twoAlmostSchur (I := I) (F := E) (V := TM) x b)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x c)
  have hinner := congrArg (fun z : TM x ↦ inner ℝ z d) h
  simpa only [curvatureCovariantDerivativeInnerAlmostSchur, curvatureCovariantDerivativeAlmostSchur,
    inner_add_left, inner_zero_left] using hinner

end ContractedIdentity

end CovariantDerivative
