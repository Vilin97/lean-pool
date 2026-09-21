/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues

/-!
# Spectral decomposition of compact self-adjoint operators

A compact self-adjoint operator on a real or complex Hilbert space is the Hilbert sum of its
mutually orthogonal eigenspaces.  For a compact positive operator, the positive eigenvalues are
exactly the positive values of its approximation-number sequence.

The eigenspace Hilbert sum is the coordinate-free spectral decomposition.  It includes the kernel
as the zero eigenspace and therefore applies without an injectivity assumption or a separability
assumption on the ambient Hilbert space.  Compactness makes every nonzero eigenspace finite
dimensional; the zero eigenspace may have arbitrary Hilbert dimension.

## Main results

* `TauCeti.isHilbertSum_eigenspaces_of_compact_selfAdjoint`: the eigenspaces form a Hilbert sum.
* `TauCeti.compactSelfAdjointEigenspaceEquiv`: the canonical isometric equivalence from the
  ambient space to the `ℓ²`-sum of its eigenspaces.
* `TauCeti.compactSelfAdjointEigenspaceEquiv_apply`: the equivalence sends an eigenvector to the
  corresponding one-coordinate vector.
* `TauCeti.hasEigenvalue_approximationNumber_of_pos`: every positive approximation-number value of
  a compact positive self-adjoint operator is an eigenvalue.
* `TauCeti.exists_approximationNumber_eq_of_hasEigenvalue_pos`: every positive eigenvalue occurs in
  the approximation-number sequence.
* `TauCeti.hasEigenvalue_ofReal_pos_iff_exists_approximationNumber_eq`: the positive spectrum is
  exactly the range of the positive approximation-number sequence.

Together with `TauCeti.finrank_eigenspace_eq_card_approximationNumber_eq`, the last statement says
that approximation numbers enumerate the positive eigenvalues with their full multiplicities.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace TauCeti

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section SelfAdjoint

variable {A : E →L[𝕜] E}

/-- Eigenspaces of bounded operators are closed, hence complete in a complete source space. -/
private theorem completeSpace_eigenspace (A : E →L[𝕜] E) (μ : 𝕜) :
    CompleteSpace (eigenspace A.toLinearMap μ) := by
  let B : E →L[𝕜] E := A - μ • ContinuousLinearMap.id 𝕜 E
  have heq : eigenspace A.toLinearMap μ = LinearMap.ker B.toLinearMap := by
    ext x
    constructor
    · intro hx
      apply LinearMap.mem_ker.mpr
      change A x - μ • x = 0
      exact sub_eq_zero.mpr (Module.End.mem_eigenspace_iff.mp hx)
    · intro hx
      apply Module.End.mem_eigenspace_iff.mpr
      have hz := LinearMap.mem_ker.mp hx
      change A x - μ • x = 0 at hz
      exact sub_eq_zero.mp hz
  rw [heq]
  exact B.isClosed_ker.completeSpace_coe

/-- The eigenspaces of a compact self-adjoint operator form an orthogonal Hilbert sum of the
ambient Hilbert space. -/
theorem isHilbertSum_eigenspaces_of_compact_selfAdjoint
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A) :
    IsHilbertSum 𝕜 (fun μ : 𝕜 => eigenspace A.toLinearMap μ)
      (fun μ : 𝕜 => (eigenspace A.toLinearMap μ).subtypeₗᵢ) := by
  have hcomplete : ∀ μ : 𝕜, CompleteSpace (eigenspace A.toLinearMap μ) :=
    fun μ => completeSpace_eigenspace A μ
  let V : ∀ μ : 𝕜, eigenspace A.toLinearMap μ →ₗᵢ[𝕜] E :=
    fun μ => (eigenspace A.toLinearMap μ).subtypeₗᵢ
  have hrange : ∀ μ : 𝕜, LinearMap.range (V μ).toLinearMap =
      eigenspace A.toLinearMap μ := by
    intro μ
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, rfl⟩
      exact x.2
    · intro y hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hortho : OrthogonalFamily 𝕜 (fun μ : 𝕜 => eigenspace A.toLinearMap μ) V := by
    intro μ ν hμν x y
    exact hAs.isSymmetric.orthogonalFamily_eigenspaces hμν x y
  have htotal : ⊤ ≤ (⨆ μ : 𝕜, LinearMap.range (V μ).toLinearMap).topologicalClosure := by
    simp only [hrange]
    exact le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hAc
        hAs.isSymmetric)).symm
  have hsum : IsHilbertSum 𝕜 (fun μ : 𝕜 => eigenspace A.toLinearMap μ) V :=
    IsHilbertSum.mk hortho htotal
  simpa only [V] using hsum

/-- Canonical spectral coordinates for a compact self-adjoint operator: the ambient Hilbert space
is isometrically equivalent to the `ℓ²`-sum of its eigenspaces. -/
noncomputable def compactSelfAdjointEigenspaceEquiv
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A) :
    E ≃ₗᵢ[𝕜] lp (fun μ : 𝕜 => eigenspace A.toLinearMap μ) 2 :=
  (isHilbertSum_eigenspaces_of_compact_selfAdjoint hAc hAs).linearIsometryEquiv

/-- Spectral coordinates send a vector in the `μ`-eigenspace to the one-coordinate vector
supported at `μ`. -/
theorem compactSelfAdjointEigenspaceEquiv_apply
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A) (μ : 𝕜)
    (x : eigenspace A.toLinearMap μ) :
    compactSelfAdjointEigenspaceEquiv hAc hAs x = lp.single 2 μ x := by
  classical
  let hsum := isHilbertSum_eigenspaces_of_compact_selfAdjoint hAc hAs
  have hsingle : hsum.linearIsometryEquiv.symm (lp.single 2 μ x) = x :=
    hsum.linearIsometryEquiv_symm_apply_single x
  rw [compactSelfAdjointEigenspaceEquiv, ← hsingle,
    LinearIsometryEquiv.apply_symm_apply]

end SelfAdjoint

section Positive

variable {A : E →L[𝕜] E}

/-- Every positive approximation-number value of a compact positive self-adjoint operator is an
eigenvalue. -/
theorem hasEigenvalue_approximationNumber_of_pos
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) (n : ℕ)
    (hn : 0 < A.approximationNumber n) :
    Module.End.HasEigenvalue A.toLinearMap ((A.approximationNumber n : ℝ) : 𝕜) := by
  rw [Module.End.hasEigenvalue_iff]
  intro hbot
  have hclosed : n < finrank 𝕜 (eigenSpan A (Set.Ici (A.approximationNumber n))) :=
    (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hn n).mp le_rfl
  have hopen : ¬ n < finrank 𝕜 (eigenSpan A (Set.Ioi (A.approximationNumber n))) := by
    intro hlt
    have hstrict :=
      (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi hAc hAs hApos hn n).mpr hlt
    exact (lt_irrefl (A.approximationNumber n)) hstrict
  have hsplit := finrank_eigenSpan_Ici hAc hAs hn
  rw [hbot, finrank_bot, add_zero] at hsplit
  rw [hsplit] at hclosed
  exact hopen hclosed

/-- Every positive eigenvalue of a compact positive self-adjoint operator occurs as an
approximation number. -/
theorem exists_approximationNumber_eq_of_hasEigenvalue_pos
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : ℝ} (hμ : 0 < μ)
    (hEig : Module.End.HasEigenvalue A.toLinearMap (μ : 𝕜)) :
    ∃ n : ℕ, A.approximationNumber n = μ := by
  have hfdIci : FiniteDimensional 𝕜 (eigenSpan A (Set.Ici μ)) :=
    finiteDimensional_eigenSpan hAc hAs hμ fun s hs => hs
  have hfdEig : FiniteDimensional 𝕜 (eigenspace A.toLinearMap (μ : 𝕜)) :=
    Submodule.finiteDimensional_of_le
      (eigenspace_le_eigenSpan A (Set.mem_Ici.mpr le_rfl))
  have hEigSpace : eigenspace A.toLinearMap (μ : 𝕜) ≠ ⊥ :=
    (Module.End.hasEigenvalue_iff.mp hEig)
  have hEigRank : 0 < finrank 𝕜 (eigenspace A.toLinearMap (μ : 𝕜)) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hEigSpace (Submodule.finrank_eq_zero.mp hzero)
  let n : ℕ := finrank 𝕜 (eigenSpan A (Set.Ioi μ))
  have hsplit := finrank_eigenSpan_Ici hAc hAs hμ
  have hnclosed : n < finrank 𝕜 (eigenSpan A (Set.Ici μ)) := by
    rw [hsplit]
    omega
  have hge : μ ≤ A.approximationNumber n :=
    (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hμ n).mpr hnclosed
  have hnstrict : ¬ μ < A.approximationNumber n := by
    intro hlt
    have hopen :=
      (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi hAc hAs hApos hμ n).mp hlt
    exact (Nat.lt_irrefl n) (by simpa only [n] using hopen)
  exact ⟨n, le_antisymm (not_lt.mp hnstrict) hge⟩

/-- The positive eigenvalues of a compact positive self-adjoint operator are exactly the positive
values of its approximation-number sequence. -/
theorem hasEigenvalue_ofReal_pos_iff_exists_approximationNumber_eq
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : ℝ} (hμ : 0 < μ) :
    Module.End.HasEigenvalue A.toLinearMap (μ : 𝕜) ↔
      ∃ n : ℕ, A.approximationNumber n = μ := by
  constructor
  · exact exists_approximationNumber_eq_of_hasEigenvalue_pos hAc hAs hApos hμ
  · rintro ⟨n, hn⟩
    have hpos : 0 < A.approximationNumber n := hn.symm ▸ hμ
    have hEig := hasEigenvalue_approximationNumber_of_pos hAc hAs hApos n hpos
    simpa only [hn] using hEig

/-! ### An orthonormal eigenvector realization of the positive approximation sequence -/

/-- A fixed orthonormal basis of a positive eigenspace.  Naming this choice separately makes
repeated occurrences of the same eigenvalue use definitionally the same basis. -/
private noncomputable def positiveEigenspaceBasis
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (μ : ℝ) (hμ : 0 < μ) :
    OrthonormalBasis (Fin (finrank 𝕜 (eigenspace A.toLinearMap ((μ : ℝ) : 𝕜)))) 𝕜
      (eigenspace A.toLinearMap ((μ : ℝ) : 𝕜)) := by
  letI : FiniteDimensional 𝕜 (eigenSpan A (Set.Ici μ)) :=
    finiteDimensional_eigenSpan hAc hAs hμ fun s hs => hs
  letI : FiniteDimensional 𝕜 (eigenspace A.toLinearMap ((μ : ℝ) : 𝕜)) :=
    Submodule.finiteDimensional_of_le
      (eigenspace_le_eigenSpan A (Set.mem_Ici.mpr (le_refl μ)))
  exact stdOrthonormalBasis 𝕜 _

/-- The `j`th vector of the fixed positive eigenspace basis, coerced to the ambient space.
It is defined as zero beyond the finite multiplicity so its result type does not depend on `μ`. -/
private noncomputable def positiveEigenspaceVector
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (μ : ℝ) (hμ : 0 < μ) (j : ℕ) : E :=
  if hj : j < finrank 𝕜 (eigenspace A.toLinearMap ((μ : ℝ) : 𝕜)) then
    ((positiveEigenspaceBasis hAc hAs μ hμ ⟨j, hj⟩ :
      eigenspace A.toLinearMap ((μ : ℝ) : 𝕜)) : E)
  else 0

private theorem inner_positiveEigenspaceVector
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (μ : ℝ) (hμ : 0 < μ) {i j : ℕ}
    (hi : i < finrank 𝕜 (eigenspace A.toLinearMap ((μ : ℝ) : 𝕜)))
    (hj : j < finrank 𝕜 (eigenspace A.toLinearMap ((μ : ℝ) : 𝕜))) :
    ⟪positiveEigenspaceVector hAc hAs μ hμ i,
      positiveEigenspaceVector hAc hAs μ hμ j⟫_𝕜 = if i = j then 1 else 0 := by
  classical
  unfold positiveEigenspaceVector
  simp only [dite_eq_left hi, dite_eq_left hj]
  change ⟪(positiveEigenspaceBasis hAc hAs μ hμ) ⟨i, hi⟩,
      (positiveEigenspaceBasis hAc hAs μ hμ) ⟨j, hj⟩⟫_𝕜 = _
  simpa only [Fin.mk.injEq] using orthonormal_iff_ite.mp
    (positiveEigenspaceBasis hAc hAs μ hμ).orthonormal ⟨i, hi⟩ ⟨j, hj⟩

private theorem positiveEigenspaceVector_mem
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (μ : ℝ) (hμ : 0 < μ) (j : ℕ)
    (hj : j < finrank 𝕜 (eigenspace A.toLinearMap ((μ : ℝ) : 𝕜))) :
    positiveEigenspaceVector hAc hAs μ hμ j ∈
      eigenspace A.toLinearMap ((μ : ℝ) : 𝕜) := by
  classical
  unfold positiveEigenspaceVector
  rw [dite_eq_left hj]
  exact Subtype.property _

private theorem norm_positiveEigenspaceVector
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (μ : ℝ) (hμ : 0 < μ) (j : ℕ)
    (hj : j < finrank 𝕜 (eigenspace A.toLinearMap ((μ : ℝ) : 𝕜))) :
    ‖positiveEigenspaceVector hAc hAs μ hμ j‖ = 1 := by
  classical
  unfold positiveEigenspaceVector
  rw [dite_eq_left hj]
  exact (positiveEigenspaceBasis hAc hAs μ hμ).orthonormal.1 _

private theorem positiveApproximation_index_lt
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (n : ℕ) (hn : 0 < A.approximationNumber n) :
    n - finrank 𝕜 (eigenSpan A (Set.Ioi (A.approximationNumber n))) <
      finrank 𝕜 (eigenspace A.toLinearMap
        (((A.approximationNumber n : ℝ) : 𝕜))) := by
  have hM : finrank 𝕜 (eigenSpan A (Set.Ioi (A.approximationNumber n))) ≤ n := by
    by_contra h
    have hlt := (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi
      hAc hAs hApos hn n).mpr (Nat.lt_of_not_ge h)
    exact (lt_irrefl (A.approximationNumber n)) hlt
  have hN := (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici
    hAc hAs hApos hn n).mp le_rfl
  have hs := finrank_eigenSpan_Ici hAc hAs hn
  omega

/-- The canonical eigenvector occupying position `n` in the positive approximation-number
list of a compact positive operator.  Repeated values are assigned distinct vectors in their
finite-dimensional eigenspace by subtracting the number of strictly larger eigenvalues. -/
noncomputable def positiveApproximationEigenvector
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (n : ℕ) (hn : 0 < A.approximationNumber n) : E := by
  let μ := A.approximationNumber n
  let W := eigenspace A.toLinearMap ((μ : ℝ) : 𝕜)
  let M := finrank 𝕜 (eigenSpan A (Set.Ioi μ))
  let N := finrank 𝕜 (eigenSpan A (Set.Ici μ))
  have hM : M ≤ n := by
    by_contra h
    have hlt := (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi
      hAc hAs hApos hn n).mpr (Nat.lt_of_not_ge h)
    exact (lt_irrefl μ) hlt
  have hN : n < N :=
    (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hn n).mp le_rfl
  have hsplit : N = M + finrank 𝕜 W := by
    simpa only [N, M, W] using finrank_eigenSpan_Ici hAc hAs hn
  have hi : n - M < finrank 𝕜 W :=
    positiveApproximation_index_lt hAc hAs hApos n hn
  exact positiveEigenspaceVector hAc hAs μ hn (n - M)

/-- The selected vector lies in the eigenspace at the corresponding approximation value. -/
theorem positiveApproximationEigenvector_mem_eigenspace
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (n : ℕ) (hn : 0 < A.approximationNumber n) :
    positiveApproximationEigenvector hAc hAs hApos n hn ∈
      eigenspace A.toLinearMap (((A.approximationNumber n : ℝ) : 𝕜)) := by
  classical
  unfold positiveApproximationEigenvector
  exact positiveEigenspaceVector_mem hAc hAs _ _ _
    (positiveApproximation_index_lt hAc hAs hApos n hn)

/-- Each selected positive approximation eigenvector has unit norm. -/
theorem norm_positiveApproximationEigenvector
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (n : ℕ) (hn : 0 < A.approximationNumber n) :
    ‖positiveApproximationEigenvector hAc hAs hApos n hn‖ = 1 := by
  classical
  let μ := A.approximationNumber n
  unfold positiveApproximationEigenvector
  exact norm_positiveEigenspaceVector hAc hAs _ _ _
    (positiveApproximation_index_lt hAc hAs hApos n hn)

/-- The positive approximation-number eigenvectors form an orthonormal family. -/
theorem orthonormal_positiveApproximationEigenvector
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) :
    Orthonormal 𝕜 (fun n : {n : ℕ // 0 < A.approximationNumber n} =>
      positiveApproximationEigenvector hAc hAs hApos n n.2) := by
  classical
  rw [orthonormal_iff_ite]
  intro n m
  by_cases hnm : n = m
  · subst m
    rw [ite_eq_left rfl]
    exact inner_self_eq_one_of_norm_eq_one
      (norm_positiveApproximationEigenvector hAc hAs hApos n n.2)
  · rw [ite_eq_right hnm]
    let μ := A.approximationNumber n
    let ν := A.approximationNumber m
    by_cases hμν : μ = ν
    · dsimp only [μ, ν] at hμν
      unfold positiveApproximationEigenvector
      simp only [hμν]
      have hMn : finrank 𝕜 (eigenSpan A (Set.Ioi ν)) ≤ n := by
        by_contra h
        have hlt := (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi
          hAc hAs hApos (by simpa only [μ, hμν] using n.2) n).mpr (Nat.lt_of_not_ge h)
        exact (lt_irrefl ν) (by simpa only [μ, hμν] using hlt)
      have hMm : finrank 𝕜 (eigenSpan A (Set.Ioi ν)) ≤ m := by
        by_contra h
        have hlt := (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi
          hAc hAs hApos m.2 m).mpr (Nat.lt_of_not_ge h)
        exact (lt_irrefl ν) hlt
      have hi : n - finrank 𝕜 (eigenSpan A (Set.Ioi ν)) <
          finrank 𝕜 (eigenspace A.toLinearMap ((ν : ℝ) : 𝕜)) := by
        have hi0 := positiveApproximation_index_lt hAc hAs hApos n n.2
        have hIoi : eigenSpan A (Set.Ioi (A.approximationNumber n)) =
            eigenSpan A (Set.Ioi ν) := by
          change eigenSpan A (Set.Ioi (A.approximationNumber n)) =
            eigenSpan A (Set.Ioi (A.approximationNumber m))
          rw [hμν]
        have hEig : eigenspace A.toLinearMap
              (((A.approximationNumber n : ℝ) : 𝕜)) =
            eigenspace A.toLinearMap ((ν : ℝ) : 𝕜) := by
          change eigenspace A.toLinearMap (((A.approximationNumber n : ℝ) : 𝕜)) =
            eigenspace A.toLinearMap (((A.approximationNumber m : ℝ) : 𝕜))
          rw [hμν]
        rwa [hIoi, hEig] at hi0
      have hj : m - finrank 𝕜 (eigenSpan A (Set.Ioi ν)) <
          finrank 𝕜 (eigenspace A.toLinearMap ((ν : ℝ) : 𝕜)) := by
        exact positiveApproximation_index_lt hAc hAs hApos m m.2
      have hspan : eigenSpan A (Set.Ioi (A.approximationNumber n)) =
          eigenSpan A (Set.Ioi (A.approximationNumber m)) := by rw [hμν]
      rw [hspan]
      rw [inner_positiveEigenspaceVector hAc hAs ν (by simpa only [ν] using m.2) hi hj]
      rw [ite_eq_right]
      intro heq
      have : (n : ℕ) = m := by omega
      exact hnm (Subtype.ext this)
    · have hnmem := positiveApproximationEigenvector_mem_eigenspace
        hAc hAs hApos n n.2
      have hmmem := positiveApproximationEigenvector_mem_eigenspace
        hAc hAs hApos m m.2
      have hscalar : ((μ : ℝ) : 𝕜) ≠ ((ν : ℝ) : 𝕜) :=
        fun h => hμν (RCLike.ofReal_injective h)
      exact hAs.isSymmetric.orthogonalFamily_eigenspaces hscalar
        ⟨_, hnmem⟩ ⟨_, hmmem⟩

/-- The compact positive operator acts on its selected vector by the corresponding
approximation number. -/
theorem apply_positiveApproximationEigenvector
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (n : ℕ) (hn : 0 < A.approximationNumber n) :
    A (positiveApproximationEigenvector hAc hAs hApos n hn) =
      ((A.approximationNumber n : ℝ) : 𝕜) •
        positiveApproximationEigenvector hAc hAs hApos n hn :=
  Module.End.mem_eigenspace_iff.mp
    (positiveApproximationEigenvector_mem_eigenspace hAc hAs hApos n hn)

end Positive

end

end TauCeti
