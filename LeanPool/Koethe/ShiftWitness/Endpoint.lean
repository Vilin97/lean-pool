/-
Copyright (c) 2026 Tom Adamczewski and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Algebra.Subalgebra.Unitization
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
/-!
# A nil ideal with a nonnilpotent two-by-two matrix

A fixed vector for `a₀ + t a₁ + t² a₂` yields a companion matrix with a
nonzero eigenvalue after inverting `1 - a₀`. Squaring puts every entry in the
nil ideal. No matrix-nilness principle is used.
-/

noncomputable section

namespace KoetheCounterexample
namespace ShiftWitness

universe u v w

section Companion

variable {K : Type u} [Field K] {M : Type v} [AddCommGroup M] [Module K M]
variable {R : Type w} [Ring R]

/-- The action of a matrix of represented ring elements on two copies of the
representation space. -/
def matrixAction (φ : R →+* Module.End K M) :
    Matrix (Fin 2) (Fin 2) R →+* Module.End K (Fin 2 → M) :=
  (endVecRingEquivMatrixEnd (Fin 2) K M).symm.toRingHom.comp φ.mapMatrix

@[simp] theorem matrixAction_apply (φ : R →+* Module.End K M)
    (H : Matrix (Fin 2) (Fin 2) R) (z : Fin 2 → M) (i : Fin 2) :
    matrixAction φ H z i = ∑ j, φ (H i j) (z j) := rfl

/-- A nonzero eigenvalue on a nonzero vector excludes nilpotence, without
finite-dimensionality assumptions. -/
theorem not_nilpotent_of_eigenvector (f : Module.End K M) (t : K) (z : M)
    (ht : t ≠ 0) (hz : z ≠ 0) (he : f z = t • z) : ¬ IsNilpotent f := by
  have hp : ∀ n : ℕ, (f ^ n) z = t ^ n • z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        simp only [pow_succ', Module.End.mul_apply, ih, map_smul, he, smul_smul]
        rw [mul_comm]
  rintro ⟨n, hn⟩
  have hz' : t ^ n • z = 0 := by rw [← hp n, hn]; rfl
  exact (smul_ne_zero (pow_ne_zero n ht) hz) hz'

/-- General companion-matrix endpoint. The scalar `t` lives in the
representation field, not necessarily in the ground field of the nil ideal. -/
theorem nonnil_matrix_of_fixed_vector
    (I : TwoSidedIdeal R) (hI : ∀ x ∈ I, IsNilpotent x)
    (φ : R →+* Module.End K M) (a : Fin 3 → R) (ha : ∀ i, a i ∈ I)
    (t : K) (ht : t ≠ 0) (z : M) (hz : z ≠ 0)
    (he : (φ (a 0) + t • φ (a 1) + t ^ 2 • φ (a 2)) z = z) :
    ∃ W : Matrix (Fin 2) (Fin 2) R,
      W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  obtain ⟨g, hg⟩ := (hI (a 0) (ha 0)).isUnit_one_sub.exists_left_inv
  let b : R := g * a 1
  let c : R := g * a 2
  have hb : b ∈ I := I.mul_mem_left g (a 1) (ha 1)
  have hc : c ∈ I := I.mul_mem_left g (a 2) (ha 2)
  have hleft : φ g * (1 - φ (a 0)) = 1 := by
    rw [← map_one φ, ← map_sub, ← map_mul, hg, map_one]
  have hrel : (1 - φ (a 0)) z = t • φ (a 1) z + t ^ 2 • φ (a 2) z := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply] at he
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    exact (sub_eq_iff_eq_add).mpr (by
      simpa [add_comm, add_left_comm, add_assoc] using he.symm)
  have hzrel : z = t • φ b z + t ^ 2 • φ c z := by
    calc
      z = (φ g * (1 - φ (a 0))) z := by rw [hleft]; rfl
      _ = φ g ((1 - φ (a 0)) z) := rfl
      _ = t • φ b z + t ^ 2 • φ c z := by
        rw [hrel, map_add, map_smul, map_smul]
        simp only [b, c, map_mul, Module.End.mul_apply]
  have hcomp : φ b z + t • φ c z = t⁻¹ • z := by
    conv_rhs => rw [hzrel]
    simp [smul_add, smul_smul, pow_two, ht]
  let H : Matrix (Fin 2) (Fin 2) R := !![b, c; 1, 0]
  let zz : Fin 2 → M := ![z, t • z]
  have hzz : zz ≠ 0 := by
    intro h
    apply hz
    exact congrFun h 0
  have heH : matrixAction φ H zz = t⁻¹ • zz := by
    ext i
    fin_cases i
    · simpa [H, zz, Fin.sum_univ_two, map_smul] using hcomp
    · simp [H, zz, Fin.sum_univ_two, smul_smul, ht]
  refine ⟨H ^ 2, ?_, ?_⟩
  · rw [TwoSidedIdeal.mem_matrix]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [H, pow_two, Matrix.mul_apply, Fin.sum_univ_two] using
        I.add_mem (I.mul_mem_right b b hb) hc
    · simpa [H, pow_two, Matrix.mul_apply, Fin.sum_univ_two] using I.mul_mem_right b c hb
    · simpa [H, pow_two, Matrix.mul_apply, Fin.sum_univ_two] using hb
    · simpa [H, pow_two, Matrix.mul_apply, Fin.sum_univ_two] using hc
  · intro hnil
    exact not_nilpotent_of_eigenvector (matrixAction φ H) t⁻¹ zz
      (inv_ne_zero ht) hzz heH (hnil.of_pow.map (matrixAction φ))

end Companion

section Unitization

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Nontrivial B] [Algebra k B]

/-- The canonical augmentation ideal in the unitization of a positive algebra. -/
def augmentationIdeal (A : NonUnitalSubalgebra k B) : TwoSidedIdeal (Unitization k A) :=
  TwoSidedIdeal.ker (Unitization.fstHom k A)

omit [Nontrivial B] in
@[simp] theorem mem_augmentationIdeal (A : NonUnitalSubalgebra k B) (x : Unitization k A) :
    x ∈ augmentationIdeal A ↔ x.fst = 0 := by
  rw [augmentationIdeal, TwoSidedIdeal.mem_ker]
  rfl

/-- A nil positive algebra omits the ambient identity. -/
theorem one_not_mem_of_nil (A : NonUnitalSubalgebra k B)
    (hA : ∀ x ∈ A, IsNilpotent x) : (1 : B) ∉ A := by
  intro h
  exact not_isNilpotent_one (hA 1 h)

/-- The augmentation ideal is nil. We reflect nilpotence along the faithful
unitization map instead of treating a nonunital algebra as if it had a unit. -/
theorem augmentationIdeal_nil (A : NonUnitalSubalgebra k B)
    (hA : ∀ x ∈ A, IsNilpotent x) :
    ∀ x ∈ augmentationIdeal A, IsNilpotent x := by
  intro x hx
  have hinj := NonUnitalSubalgebra.unitization_injective A (one_not_mem_of_nil A hA)
  apply (IsNilpotent.map_iff hinj).mp
  have hfst : x.fst = 0 := (mem_augmentationIdeal A x).mp hx
  simpa [NonUnitalSubalgebra.unitization_apply, hfst] using hA (x.snd : B) x.snd.property

/-- A nil nonunital subalgebra with a transcendental-scalar fixed vector gives
an actual nil ideal in a unital ring. The ring is its unitization; its action
need not be faithful, although nilness is reflected using the faithful natural
unitization map into the ambient algebra. -/
theorem exists_witness_of_nil_subalgebra
    {K : Type w} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    (A : NonUnitalSubalgebra k B) (hA : ∀ x ∈ A, IsNilpotent x)
    (φ : B →+* Module.End K M) (a : Fin 3 → B) (ha : ∀ i, a i ∈ A)
    (t : K) (ht : t ≠ 0) (z : M) (hz : z ≠ 0)
    (he : (φ (a 0) + t • φ (a 1) + t ^ 2 • φ (a 2)) z = z) :
    ∃ (R : Type (max u v)) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  let ψ : Unitization k A →+* Module.End K M :=
    φ.comp (NonUnitalSubalgebra.unitization A).toRingHom
  let a' : Fin 3 → Unitization k A := fun i => Unitization.inr ⟨a i, ha i⟩
  have ha' : ∀ i, a' i ∈ augmentationIdeal A := by
    intro i
    simp [a']
  have hψ : ∀ i, ψ (a' i) = φ (a i) := by
    intro i
    simp [ψ, a', NonUnitalSubalgebra.unitization_apply]
  have hI := augmentationIdeal_nil A hA
  refine ⟨Unitization k A, inferInstance, augmentationIdeal A, hI, ?_⟩
  apply nonnil_matrix_of_fixed_vector (augmentationIdeal A) hI ψ a' ha' t ht z hz
  simpa only [hψ] using he

end Unitization

end ShiftWitness
end KoetheCounterexample

end
