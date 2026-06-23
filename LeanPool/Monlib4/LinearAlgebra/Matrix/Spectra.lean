/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.Matrix.Spectrum
import LeanPool.Monlib4.LinearAlgebra.Matrix.Basic
import LeanPool.Monlib4.LinearAlgebra.Matrix.IsAlmostHermitian
import LeanPool.Monlib4.LinearAlgebra.InnerAut

/-!
# Matrix Spectra

Spectral helpers for Hermitian and almost-Hermitian matrices.
-/

instance multisetCoe {α β : Type _} [Coe α β] : Coe (Multiset α) (Multiset β)
    where coe s := s.map (Coe.coe : α → β)

instance multisetCoeTC {α β : Type _} [CoeTC α β] : CoeTC (Multiset α) (Multiset β)
    where coe s := s.map (CoeTC.coe : α → β)

theorem Finset.val.map_coe {α β γ : Type _} (f : α → β) (s : Finset α) [CoeTC β γ] :
    (s.val.map f).map (fun x : β => (x : γ)) = s.val.map (fun x => (f x : γ)) := by
  simp only [Multiset.map_map, Function.comp_apply]

theorem Finset.val.map_coe' {α β γ : Type _} (f : α → β) (s : Finset α) [Coe β γ] :
    (s.val.map f).map (fun x : β => (x : γ)) = s.val.map (fun x => (f x : γ)) :=
  Finset.val.map_coe f s

noncomputable instance multisetCoeTCRToRCLike {𝕜 : Type _} [RCLike 𝕜] :
  CoeTC (Multiset ℝ) (Multiset 𝕜) :=
@multisetCoeTC ℝ 𝕜 ⟨RCLike.ofReal⟩
noncomputable instance multisetCoeRToRCLike {𝕜 : Type _} [RCLike 𝕜] :
  Coe (Multiset ℝ) (Multiset 𝕜) where
  coe := (@multisetCoeTCRToRCLike 𝕜 _).coe

namespace Matrix

variable {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix

/-- Choose a scalar and Hermitian matrix witnessing that an almost-Hermitian matrix is scalar
Hermitian. -/
noncomputable def _root_.Matrix.IsAlmostHermitian.scalarMatrix {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : 𝕜 × (Matrix n n 𝕜) := by
  choose! α y hy using hx
  exact ⟨α, y⟩

/-- The scalar chosen from an almost-Hermitian witness. -/
noncomputable def _root_.Matrix.IsAlmostHermitian.scalar {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : 𝕜 := hx.scalarMatrix.1

/-- The Hermitian matrix chosen from an almost-Hermitian witness. -/
noncomputable def _root_.Matrix.IsAlmostHermitian.matrix {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : Matrix n n 𝕜 := hx.scalarMatrix.2

theorem _root_.Matrix.IsAlmostHermitian.eq_smul_matrix {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : x = hx.scalar • hx.matrix := by
  rw [IsAlmostHermitian.scalar, IsAlmostHermitian.matrix, IsAlmostHermitian.scalarMatrix]
  generalize_proofs
  simp_all

theorem _root_.Matrix.IsAlmostHermitian.matrix_isHermitian {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : hx.matrix.IsHermitian := by
  rw [IsAlmostHermitian.matrix, IsAlmostHermitian.scalarMatrix]
  generalize_proofs
  simp_all

/-- Eigenvalues of the Hermitian factor, rescaled by the almost-Hermitian scalar. -/
noncomputable def _root_.Matrix.IsAlmostHermitian.eigenvalues {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) :
    n → 𝕜 :=
  fun i => hx.scalar • hx.matrix_isHermitian.eigenvalues i

/-- Multiset of eigenvalues for an almost-Hermitian matrix. -/
noncomputable def _root_.Matrix.IsAlmostHermitian.spectra {A : Matrix n n 𝕜}
    (hA : A.IsAlmostHermitian) :
    Multiset 𝕜 :=
  Finset.univ.val.map fun i => hA.eigenvalues i

/-- Multiset of real eigenvalues for a Hermitian matrix. -/
noncomputable def _root_.Matrix.IsHermitian.spectra {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : Multiset ℝ :=
  Finset.univ.val.map fun i => hA.eigenvalues i

theorem _root_.Matrix.IsHermitian.spectra_coe {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (hA.spectra : Multiset 𝕜) = Finset.univ.val.map fun i => hA.eigenvalues i := by
  simp only [Multiset.map_map, IsHermitian.spectra]

open scoped BigOperators

theorem _root_.Matrix.IsHermitian.mem_coe_spectra_diagonal {A : n → 𝕜}
    (hA : (diagonal A).IsHermitian)
    (x : 𝕜) :
    x ∈ (hA.spectra : Multiset 𝕜) ↔ ∃ i : n, A i = x := by
  rw [IsHermitian.spectra_coe]
  simp only [Multiset.mem_map, Finset.mem_univ_val, true_and, exists_exists_eq_and]
  have hset : RCLike.ofReal '' Set.range hA.eigenvalues = Set.range A := by
    rw [← hA.spectrum_eq_image_range, spectrum_diagonal]
  simpa [Set.mem_image, Set.mem_range] using Set.ext_iff.mp hset x

theorem _root_.Matrix.IsHermitian.spectra_set_eq_spectrum {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    {x : 𝕜 | x ∈ (hA.spectra : Multiset 𝕜)} = _root_.spectrum 𝕜 (toLin' A) := by
  ext x
  rw [IsHermitian.spectra_coe]
  simp only [Set.mem_setOf, Multiset.mem_map, Finset.mem_univ_val, true_and, exists_exists_eq_and]
  rw [spectrum_toLin', hA.spectrum_eq_image_range]
  simp [Set.mem_image, Set.mem_range]

theorem _root_.Matrix.IsHermitian.of_innerAut {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (U : unitaryGroup n 𝕜) :
    (innerAut U A).IsHermitian :=
  (innerAut_isHermitian_iff U A).mp hA

omit [Fintype n] [DecidableEq n] in
theorem isAlmostHermitian_iff_smul {A : Matrix n n 𝕜} :
    A.IsAlmostHermitian ↔ ∀ α : 𝕜, (α • A).IsAlmostHermitian := by
  constructor
  · rintro ⟨β, y, rfl, hy⟩ α
    rw [smul_smul]
    exact ⟨α * β, y, rfl, hy⟩
  · intro h
    specialize h 1
    rwa [one_smul] at h

omit [Fintype n] [DecidableEq n] in
theorem _root_.Matrix.IsAlmostHermitian.smul {A : Matrix n n 𝕜} (hA : A.IsAlmostHermitian)
    (α : 𝕜) :
    (α • A).IsAlmostHermitian :=
  isAlmostHermitian_iff_smul.mp hA _

theorem _root_.Matrix.IsAlmostHermitian.of_innerAut {A : Matrix n n 𝕜} (hA : A.IsAlmostHermitian)
    (U : unitaryGroup n 𝕜) : (innerAut U A).IsAlmostHermitian := by
  obtain ⟨α, y, rfl, hy⟩ := hA
  refine ⟨α, innerAut U y, ?_, hy.of_innerAut _⟩
  simp_rw [_root_.map_smul]

theorem isAlmostHermitian_iff_of_innerAut {A : Matrix n n 𝕜} (U : unitaryGroup n 𝕜) :
    A.IsAlmostHermitian ↔ (innerAut U A).IsAlmostHermitian := by
  refine ⟨fun h => h.of_innerAut _, ?_⟩
  rintro ⟨α, y, h, hy⟩
  rw [eq_comm, innerAut_eq_iff] at h
  rw [h, _root_.map_smul]
  clear h
  revert α
  rw [← isAlmostHermitian_iff_smul]
  apply IsAlmostHermitian.of_innerAut
  exact hy.isAlmostHermitian

/-- A matrix has almost equal spectra to another if a nonzero scalar multiple has equal spectra. -/
def _root_.Matrix.IsAlmostHermitian.HasAlmostEqualSpectraTo {x y : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian)
    (hy : y.IsAlmostHermitian) : Prop :=
  ∃ β : 𝕜ˣ, hx.spectra = (hy.smul β).spectra

end Matrix
