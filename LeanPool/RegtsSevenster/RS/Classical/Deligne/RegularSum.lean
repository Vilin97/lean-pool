/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ShapeAlgebra
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PackageAssembly
import LeanPool.RegtsSevenster.RS.Classical.SymFun.PieriChain

/-!
# The regular-representation dimension bound

For every `SchurPackage` and every size `n`, the central
idempotents of the shapes of size `n` are pairwise orthogonal and
sum to the identity of `ℂ[S_n]`; reading off the coefficient of
the identity permutation, the squares of the dimensions sum to
`n!` — the Wedderburn completeness of the blocks.  The
Cauchy–Schwarz-free consequences `n! ≤ (∑ dim)²` and
`√(n!) ≤ ∑ dim` are the forms consumed by the Deligne development
(Catégories tensorielles, 1.20).

The proof pins the package's characters: centrality makes them
class functions, and the Frobenius field determines a class
function completely, by linear independence of the completed
cycle-type monomials — so they agree with the Jacobi–Trudi
characters and the package idempotents are the native projectors.
Orthogonality then reduces, through the action table and the
faithfulness trick, to injectivity of the Schur specialisation
`μ ↦ diagramSchur μ`, proved by evaluating at genuine variable
families and extracting an alternant coefficient.  Completeness is
a dimension count in the centre of the group algebra against the
class sums, which are no more numerous than the shapes.
-/

namespace RS

open Finset Equiv

universe u

/-! ### Polynomial identities from evaluations

Two multivariate polynomials over `ℂ` agreeing at every point are
equal.  (Mathlib's `MvPolynomial.funext` is not part of the tree's
Mathlib footprint, so the finitely-many-variables case is rebuilt
here from the one-variable statement.) -/

section MvFunext

open MvPolynomial

/-- A multivariate polynomial over `ℂ` in finitely many variables
vanishing at every point is zero. -/
theorem mv_eval_zero_fin :
    ∀ (m : ℕ) (p : MvPolynomial (Fin m) ℂ),
      (∀ x : Fin m → ℂ, eval x p = 0) → p = 0 := by
  intro m
  induction m with
  | zero =>
    intro p hp
    obtain ⟨a, rfl⟩ := C_surjective (Fin 0) p
    rw [show a = eval finZeroElim (C a : MvPolynomial (Fin 0) ℂ)
      from (eval_C _).symm, hp finZeroElim, map_zero]
  | succ m ih =>
    intro p hp
    apply (finSuccEquiv ℂ m).injective
    rw [map_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_
      (Set.infinite_univ.image
        ((C_injective (Fin m) ℂ).injOn (s := Set.univ)))
    rintro _ ⟨r, -, rfl⟩
    change Polynomial.IsRoot _ (C r)
    rw [Polynomial.IsRoot]
    apply ih
    intro s
    have hcomm : eval s (Polynomial.eval (C r)
        ((finSuccEquiv ℂ m) p)) =
        Polynomial.eval r
          (Polynomial.map (eval s) ((finSuccEquiv ℂ m) p)) := by
      rw [Polynomial.eval_map, Polynomial.eval,
        Polynomial.hom_eval₂, RingHom.comp_id, eval_C]
    rw [hcomm, ← eval_eq_eval_mv_eval']
    exact hp _

/-- Two multivariate polynomials over `ℂ` in finitely many
variables agreeing at every point are equal. -/
theorem mv_funext_fin {m : ℕ} {p q : MvPolynomial (Fin m) ℂ}
    (h : ∀ x : Fin m → ℂ, eval x p = eval x q) : p = q := by
  rw [← sub_eq_zero]
  apply mv_eval_zero_fin
  intro x
  rw [map_sub, h x, sub_self]

/-- A multivariate polynomial over `ℂ` in countably many variables
vanishing at every point is zero. -/
theorem mv_eval_zero_nat (p : MvPolynomial ℕ ℂ)
    (hp : ∀ x : ℕ → ℂ, eval x p = 0) : p = 0 := by
  obtain ⟨m, f, hf, q, rfl⟩ := exists_fin_rename p
  suffices hq : q = 0 by rw [hq, map_zero]
  apply mv_eval_zero_fin
  intro y
  have hev := hp (Function.extend f y 0)
  rw [eval_rename] at hev
  rwa [show (Function.extend f y 0) ∘ f = y from
    funext fun i => hf.extend_apply _ _ _] at hev

end MvFunext

/-! ### Separation by the Schur specialisation

The Jacobi–Trudi determinant is stable under padding the row-length
vector with zero rows, evaluates at genuine power sums to the
polynomial Jacobi–Trudi determinant, and — through the bialternant
identity and the strict alternant coefficient — separates diagrams:
`μ ↦ diagramSchur μ` is injective. -/

section Separation

open MvPolynomial

/-- Rows of zero length do not change the Jacobi–Trudi
determinant: padding the row-length vector is invisible. -/
theorem det_newtonHZ_pad (t : ℕ → ℂ) (v : ℕ → ℕ) :
    ∀ (k : ℕ) {L : ℕ}, L ≤ k → (∀ i, L ≤ i → v i = 0) →
    (Matrix.of fun i j : Fin k =>
      newtonHZ t ((v i : ℤ) + (j : ℤ) - (i : ℤ))).det =
    (Matrix.of fun i j : Fin L =>
      newtonHZ t ((v i : ℤ) + (j : ℤ) - (i : ℤ))).det := by
  intro k
  induction k with
  | zero =>
    intro L hL _
    obtain rfl : L = 0 := Nat.le_zero.mp hL
    rfl
  | succ k ih =>
    intro L hL hv
    rcases Nat.lt_or_ge L (k + 1) with hLk | hLk
    swap
    · obtain rfl : L = k + 1 := le_antisymm hL hLk
      rfl
    have hLk' : L ≤ k := Nat.lt_succ_iff.mp hLk
    rw [Matrix.det_succ_row _ (Fin.last k)]
    rw [Finset.sum_eq_single (Fin.last k) ?side ?empty]
    · -- the surviving corner term
      have hcorner : (Matrix.of fun i j : Fin (k + 1) =>
          newtonHZ t ((v i : ℤ) + (j : ℤ) - (i : ℤ)))
            (Fin.last k) (Fin.last k) = 1 := by
        simp only [Matrix.of_apply, Fin.val_last]
        rw [hv k hLk']
        rw [show ((0 : ℕ) : ℤ) + (k : ℤ) - (k : ℤ) = ((0 : ℕ) : ℤ)
          from by omega]
        rw [newtonHZ_natCast, newtonH_zero]
      rw [hcorner, mul_one]
      have hsign : (-1 : ℂ) ^ (((Fin.last k : Fin (k + 1)) : ℕ) +
          ((Fin.last k : Fin (k + 1)) : ℕ)) = 1 := by
        rw [show (((Fin.last k : Fin (k + 1)) : ℕ) +
          ((Fin.last k : Fin (k + 1)) : ℕ)) = 2 * k from by
            rw [Fin.val_last]; ring]
        rw [pow_mul, neg_one_sq, one_pow]
      rw [hsign, one_mul]
      have hminor : ((Matrix.of fun i j : Fin (k + 1) =>
          newtonHZ t ((v i : ℤ) + (j : ℤ) - (i : ℤ))).submatrix
            (Fin.last k).succAbove (Fin.last k).succAbove) =
          Matrix.of fun i j : Fin k =>
            newtonHZ t ((v i : ℤ) + (j : ℤ) - (i : ℤ)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.submatrix_apply, Fin.succAbove_last,
          Matrix.of_apply, Fin.val_castSucc]
      rw [hminor, ih hLk' hv]
    · -- the other entries of the last row vanish
      intro j _ hj
      have hjlt : (j : ℕ) < k := by
        rcases Fin.lt_or_eq_of_le (Fin.le_last j) with h | h
        · exact Nat.lt_of_lt_of_le (Fin.lt_def.mp h)
            (le_of_eq (Fin.val_last k))
        · exact absurd h hj
      have hzero : (Matrix.of fun i j : Fin (k + 1) =>
          newtonHZ t ((v i : ℤ) + (j : ℤ) - (i : ℤ)))
            (Fin.last k) j = 0 := by
        simp only [Matrix.of_apply, Fin.val_last]
        rw [hv k hLk']
        refine newtonHZ_neg _ _ ?_
        omega
      rw [hzero, mul_zero, zero_mul]
    · intro habs
      exact absurd (Finset.mem_univ (Fin.last k)) habs

/-- Evaluating the complete homogeneous polynomial in all variables
gives the complete homogeneous value. -/
theorem eval_hSub_univ {k : ℕ} (x : Fin k → ℂ) (m : ℕ) :
    eval x (hSub (Finset.univ : Finset (Fin k)) m) = hVal x m := by
  classical
  rw [hSub, Finset.filter_true_of_mem
    (fun w _ => fun i _ => Finset.mem_univ i)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (eval x) (w.1.map X).prod =
    ((w.1.map X).map (eval x)).prod from
      (map_multiset_prod (eval x) _)]
  rw [Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun i _ => eval_X i

/-- Evaluating the `ℤ`-indexed complete homogeneous polynomial
gives the Newton lift of the power sums of the variables. -/
theorem eval_hSubZ_univ {k : ℕ} (x : Fin k → ℂ) (z : ℤ) :
    eval x (hSubZ (Finset.univ : Finset (Fin k)) z) =
      newtonHZ (pVal x) z := by
  rcases le_or_gt 0 z with hz | hz
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [hSubZ_natCast, newtonHZ_natCast, eval_hSub_univ,
      newtonH_pVal]
  · rw [hSubZ_neg _ _ hz, newtonHZ_neg _ _ hz, map_zero]

/-- The Jacobi–Trudi determinant of a diagram, evaluated at a
variable family, is the Schur specialisation at its power sums. -/
theorem eval_jtMat_det (lam : YoungDiagram) {k : ℕ}
    (hk : lam.colLen 0 ≤ k) (x : Fin k → ℂ) :
    eval x ((jtMat (fun i : Fin k => lam.rowLen (i : ℕ))).det) =
      diagramSchur lam (pVal x) := by
  rw [RingHom.map_det]
  have hentry : (eval x).mapMatrix
      (jtMat (fun i : Fin k => lam.rowLen (i : ℕ))) =
      Matrix.of fun i j : Fin k =>
        newtonHZ (pVal x) ((lam.rowLen (i : ℕ) : ℤ) +
          (j : ℤ) - (i : ℤ)) := by
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show jtMat (fun i : Fin k => lam.rowLen (i : ℕ)) i j =
      hSubZ Finset.univ ((lam.rowLen (i : ℕ) : ℤ) +
        ((j : Fin k) : ℕ) - (i : ℕ)) from rfl]
    rw [eval_hSubZ_univ]
    rfl
  rw [hentry]
  have hzero : ∀ i, lam.rowLens.length ≤ i → lam.rowLen i = 0 := by
    intro i hi
    by_contra hne
    have hmem : (i, 0) ∈ lam :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
    have := YoungDiagram.mem_iff_lt_colLen.mp hmem
    rw [YoungDiagram.length_rowLens] at hi
    omega
  have hLk : lam.rowLens.length ≤ k := by
    rw [YoungDiagram.length_rowLens]; exact hk
  rw [det_newtonHZ_pad (pVal x) (fun i => lam.rowLen i) k hLk hzero]
  rw [diagramSchur, schurDet]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [Matrix.of_apply, Matrix.of_apply]
  congr 1
  have hgr : lam.rowLens.get i = lam.rowLen (i : ℕ) := by
    rw [List.get_eq_getElem]
    exact YoungDiagram.get_rowLens
  omega

/-- **Injectivity of the Schur specialisation**: diagrams with the
same Schur values at every prospective power-sum sequence are
equal. -/
theorem diagramSchur_injective {lam mu : YoungDiagram}
    (h : ∀ t : ℕ → ℂ, diagramSchur lam t = diagramSchur mu t) :
    lam = mu := by
  classical
  set k := max (lam.colLen 0) (mu.colLen 0) with hk
  set vl : Fin k → ℕ := fun i => lam.rowLen (i : ℕ) with hvl
  set vm : Fin k → ℕ := fun i => mu.rowLen (i : ℕ) with hvm
  -- the polynomial Jacobi–Trudi determinants agree
  have hdet : (jtMat vl).det = (jtMat vm).det := by
    refine mv_funext_fin fun x => ?_
    rw [hvl, hvm, eval_jtMat_det lam (le_max_left _ _) x,
      eval_jtMat_det mu (le_max_right _ _) x, h]
  -- hence so do the alternants
  have halt : altDet (eVec lam k) = altDet (eVec mu k) := by
    rw [show altDet (eVec lam k) = (powMat vl).det from rfl,
      show altDet (eVec mu k) = (powMat vm).det from rfl,
      bialternant vl, bialternant vm, hdet]
  -- extract the diagonal coefficient of the `lam` alternant
  have h1 : (altDet (eVec lam k)).coeff (∑ i, Finsupp.single i (eVec lam k i)) = 1 := by
    rw [alternant_coeff_strict _ _ (eVec_strict lam k)
      (eVec_strict lam k), ite_eq_left rfl]
  rw [halt, alternant_coeff_strict _ _ (eVec_strict mu k)
    (eVec_strict lam k)] at h1
  have heVec : eVec mu k = eVec lam k := by
    by_contra hne
    rw [ite_eq_right hne] at h1
    exact zero_ne_one h1
  -- row lengths agree everywhere
  have hzero : ∀ (nu : YoungDiagram) (i : ℕ), nu.colLen 0 ≤ i →
      nu.rowLen i = 0 := by
    intro nu i hi
    by_contra hne
    have hmem : (i, 0) ∈ nu :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
    have := YoungDiagram.mem_iff_lt_colLen.mp hmem
    omega
  have hrow : ∀ i : ℕ, lam.rowLen i = mu.rowLen i := by
    intro i
    rcases Nat.lt_or_ge i k with hik | hik
    · have hfun := congrFun heVec ⟨i, hik⟩
      simp only [eVec] at hfun
      omega
    · rw [hzero lam i (le_trans (le_max_left _ _) hik),
        hzero mu i (le_trans (le_max_right _ _) hik)]
  -- and diagrams are determined by their row lengths
  have hcells : lam.cells = mu.cells := by
    refine Finset.ext fun c => ?_
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells]
    obtain ⟨i, j⟩ := c
    rw [YoungDiagram.mem_iff_lt_rowLen,
      YoungDiagram.mem_iff_lt_rowLen, hrow i]
  exact YoungDiagram.ext hcells

end Separation

/-! ### Transport along an equality of sizes

`Shape.e` recasts idempotents along `symCast` at an equality of
sizes; on coefficients this is relabelling of permutations along
`permCast`, which preserves products, inverses, and cycle types. -/

section Transport

/-- Relabelling of permutations along an equality of sizes. -/
def permCast {m n : ℕ} (h : m = n) :
    Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin n) :=
  Equiv.permCongr (finCongr h)

/-- At `rfl`, relabelling is the identity. -/
@[simp]
theorem permCast_rfl {n : ℕ} :
    permCast (rfl : n = n) = Equiv.refl (Equiv.Perm (Fin n)) := by
  refine Equiv.ext fun σ => ?_
  refine Equiv.ext fun y => ?_
  rw [permCast, finCongr_refl, Equiv.permCongr_apply]
  rfl

/-- Relabelling preserves products. -/
theorem permCast_mul {m n : ℕ} (h : m = n)
    (σ τ : Equiv.Perm (Fin m)) :
    permCast h (σ * τ) = permCast h σ * permCast h τ := by
  refine Equiv.ext fun y => ?_
  simp only [permCast, Equiv.permCongr_apply, Equiv.Perm.mul_apply,
    Equiv.symm_apply_apply]

/-- Relabelling fixes the identity. -/
theorem permCast_one {m n : ℕ} (h : m = n) :
    permCast h (1 : Equiv.Perm (Fin m)) = 1 := by
  refine Equiv.ext fun y => ?_
  simp only [permCast, Equiv.permCongr_apply]
  rw [Equiv.Perm.one_apply, Equiv.apply_symm_apply]
  rfl

/-- Relabelling preserves inverses. -/
theorem permCast_inv {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    permCast h σ⁻¹ = (permCast h σ)⁻¹ := by
  have hmul : permCast h σ⁻¹ * permCast h σ = 1 := by
    rw [← permCast_mul, inv_mul_cancel, permCast_one]
  exact (inv_eq_of_mul_eq_one_left hmul).symm

/-- Relabelling preserves cycle types. -/
theorem cycleType_permCast {m n : ℕ} (h : m = n)
    (σ : Equiv.Perm (Fin m)) :
    (permCast h σ).cycleType = σ.cycleType :=
  cycleType_permCongr (finCongr h) σ

/-- `symCast` at a reflexive inequality is the identity. -/
theorem symCast_le_refl {n : ℕ} (h : n ≤ n) (x : SymGroupAlgebra n) :
    symCast h x = x := by
  apply MonoidAlgebra.coeff_injective
  change Finsupp.mapDomain
    (⇑(Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h))) x.coeff = x.coeff
  have hid : ∀ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h)) σ = σ := by
    intro σ
    rw [Equiv.Perm.viaEmbeddingHom_apply]
    refine Equiv.ext fun y => ?_
    have hy : (Fin.castLEEmb h) y = y := Fin.ext (by simp)
    calc (σ.viaEmbedding (Fin.castLEEmb h)) y
        = (σ.viaEmbedding (Fin.castLEEmb h)) ((Fin.castLEEmb h) y) :=
          by rw [hy]
      _ = (Fin.castLEEmb h) (σ y) :=
          Equiv.Perm.viaEmbedding_apply σ _ y
      _ = σ y := hy ▸ rfl
  rw [show ⇑(Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h)) = id from
    funext hid]
  exact Finsupp.mapDomain_id

/-- Coefficients of a recast element are coefficients of the
original, at the relabelled permutation. -/
theorem symCast_apply_of_eq {m n : ℕ} (h : m = n)
    (x : SymGroupAlgebra m) (g : Equiv.Perm (Fin n)) :
    (symCast (le_of_eq h) x).coeff g = x.coeff ((permCast h).symm g) := by
  subst h
  rw [symCast_le_refl, permCast_rfl]
  rfl

/-- Recasting a class element relabels its coefficient
function. -/
theorem symCast_classElem_of_eq {m n : ℕ} (h : m = n)
    (c : Equiv.Perm (Fin m) → ℂ) :
    symCast (le_of_eq h) (classElem c) =
      classElem (fun g => c ((permCast h).symm g)) := by
  subst h
  rw [symCast_le_refl, permCast_rfl]
  rfl

end Transport

/-! ### Coefficients of the package idempotents

The coefficient function of `P.e μ`, the block-rank computation of
the identity coefficient, and the conjugation invariance of the
package's characters, forced by centrality. -/

section Coefficients

/-- `charIdempotent` is the class element of the normalised
character — no inversion invariance required. -/
theorem charIdempotent_eq_classElem' {n : ℕ} (d : ℕ)
    (χ : Equiv.Perm (Fin n) → ℂ) :
    charIdempotent d χ =
      classElem (fun π : Equiv.Perm (Fin n) =>
        ((d : ℂ) / (n.factorial : ℂ)) * χ π) := by
  rw [charIdempotent, classElem, Finset.smul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [smul_smul]
  rfl

/-- The coefficients of the central idempotent of a shape. -/
theorem SchurPackage.e_coeff (P : SchurPackage.{u})
    (μ : YoungDiagram) (π : Equiv.Perm (Fin μ.card)) :
    (P.e μ).coeff π =
      ((P.dim μ : ℂ) / (μ.card.factorial : ℂ)) * P.char μ π := by
  rw [SchurPackage.e_def, charIdempotent_eq_classElem',
    classElem_coeff]

/-- The block rank at the identity coefficient: the square of the
dimension is `n!` times the identity coefficient of the
idempotent. -/
theorem SchurPackage.dim_sq_eq_coeff_one (P : SchurPackage.{u})
    (μ : YoungDiagram) :
    ((P.dim μ : ℂ)) ^ 2 =
      (μ.card.factorial : ℂ) * (P.e μ).coeff 1 := by
  have h := finrank_range_mulLeft
    (G := Equiv.Perm (Fin μ.card)) (P.e μ) (P.idem μ)
  rw [SchurPackage.e_def] at h
  rw [P.block_rank μ] at h
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [← SchurPackage.e_def] at h
  exact_mod_cast h

/-- The package's character at the identity is the dimension. -/
theorem SchurPackage.char_one (P : SchurPackage.{u})
    (μ : YoungDiagram) :
    P.char μ 1 = (P.dim μ : ℂ) := by
  have h := P.dim_sq_eq_coeff_one μ
  rw [P.e_coeff μ 1] at h
  have hfac : ((μ.card.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hdim : ((P.dim μ : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (P.dim_pos μ))
  have h2 : ((P.dim μ : ℂ)) ^ 2 = (P.dim μ : ℂ) * P.char μ 1 := by
    rw [h]
    field_simp
  rw [sq] at h2
  exact (mul_left_cancel₀ hdim h2).symm

/-- The central idempotents are nonzero. -/
theorem SchurPackage.e_ne_zero (P : SchurPackage.{u})
    (μ : YoungDiagram) :
    P.e μ ≠ 0 := by
  intro h
  have h2 := P.dim_sq_eq_coeff_one μ
  rw [h] at h2
  rw [show ((0 : SymGroupAlgebra μ.card)).coeff 1 = 0 from rfl,
    mul_zero] at h2
  have hdim : ((P.dim μ : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (P.dim_pos μ))
  exact pow_ne_zero 2 hdim h2

/-- Coefficients of an element commuting with the whole group
algebra are conjugation-invariant. -/
theorem coeff_conj_of_comm {G : Type*} [Group G]
    (x : MonoidAlgebra ℂ G)
    (hx : ∀ y, x * y = y * x) (g c : G) :
    x.coeff (c * g * c⁻¹) = x.coeff g := by
  have h := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff (c * g))
    (hx (MonoidAlgebra.single c 1))
  rw [show (x * MonoidAlgebra.single c (1 : ℂ)).coeff (c * g) =
      x.coeff ((c * g) * c⁻¹) * 1 from
    MonoidAlgebra.coeff_mul_single_apply x 1 c (c * g)] at h
  rw [show (MonoidAlgebra.single c (1 : ℂ) * x).coeff (c * g) =
      1 * x.coeff (c⁻¹ * (c * g)) from
    MonoidAlgebra.coeff_single_mul_apply x 1 c (c * g)] at h
  rw [mul_one, one_mul, inv_mul_cancel_left] at h
  exact h

/-- The package's characters are class functions: conjugation
invariance is forced by the centrality of the idempotents. -/
theorem SchurPackage.char_conj (P : SchurPackage.{u})
    (μ : YoungDiagram) (g c : Equiv.Perm (Fin μ.card)) :
    P.char μ (c * g * c⁻¹) = P.char μ g := by
  have h := coeff_conj_of_comm (P.e μ)
    (fun y => P.central μ y) g c
  rw [P.e_coeff, P.e_coeff] at h
  have hne : ((P.dim μ : ℂ) / (μ.card.factorial : ℂ)) ≠ 0 :=
    div_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (P.dim_pos μ)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  exact mul_left_cancel₀ hne h

end Coefficients

/-! ### The Frobenius field determines the characters

The completed cycle-type monomials attached to distinct cycle types
are distinct monomials, hence linearly independent as functions of
the prospective power sums; a class function with vanishing
cycle-weighted sums at every `t` is therefore zero.  Comparing the
package's Frobenius field with the Jacobi–Trudi one pins
`P.char = jtChar` and `P.dim = nDim ∘ jtSimple`, identifying the
package idempotents with the native projectors. -/

section Determination

open MvPolynomial

/-- The exponent record of the completed cycle-type monomial. -/
noncomputable def cycExp {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ℕ →₀ ℕ :=
  Multiset.toFinsupp π.cycleType +
    Finsupp.single 1 (n - π.cycleType.sum)

/-- Products of powers over a multiset's counting record. -/
theorem prod_pow_toFinsupp (t : ℕ → ℂ) (m : Multiset ℕ) :
    (Multiset.toFinsupp m).prod (fun c e => t c ^ e) =
      (m.map t).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [show a ::ₘ s = {a} + s from (Multiset.singleton_add a s).symm]
    rw [Multiset.toFinsupp_add, Finsupp.prod_add_index'
      (fun c => pow_zero (t c)) (fun c e e' => pow_add (t c) e e'),
      Multiset.toFinsupp_singleton]
    have hsingle : ((Finsupp.single a (1 : ℕ)).prod
        fun c e => t c ^ e) = t a ^ (1 : ℕ) :=
      Finsupp.prod_single_index (pow_zero (t a))
    rw [hsingle, pow_one, ih, Multiset.map_add, Multiset.prod_add,
      Multiset.map_singleton, Multiset.prod_singleton]

/-- The completed cycle-type monomial evaluates to the completed
cycle-type product. -/
theorem eval_cycExp (t : ℕ → ℂ) {n : ℕ} (π : Equiv.Perm (Fin n)) :
    eval t (monomial (cycExp π) (1 : ℂ)) = cycleProd t π := by
  rw [eval_monomial, one_mul, cycExp, Finsupp.prod_add_index'
    (fun c => pow_zero (t c)) (fun c e e' => pow_add (t c) e e')]
  have hsingle : (Finsupp.single 1 (n - π.cycleType.sum)).prod
      (fun c e => t c ^ e) = t 1 ^ (n - π.cycleType.sum) :=
    Finsupp.prod_single_index (pow_zero (t 1))
  rw [prod_pow_toFinsupp, hsingle]
  rfl

/-- The exponent record determines, and is determined by, the
cycle type. -/
theorem cycExp_eq_iff {n : ℕ} (π π' : Equiv.Perm (Fin n)) :
    cycExp π = cycExp π' ↔ π.cycleType = π'.cycleType := by
  constructor
  · intro h
    have hcount : ∀ c : ℕ, π.cycleType.count c = π'.cycleType.count c := by
      intro c
      rcases eq_or_ne c 1 with rfl | hc
      · rw [Multiset.count_eq_zero_of_notMem
          (fun hmem => by
            have := Equiv.Perm.two_le_of_mem_cycleType hmem
            omega),
          Multiset.count_eq_zero_of_notMem
          (fun hmem => by
            have := Equiv.Perm.two_le_of_mem_cycleType hmem
            omega)]
      · have happ := congrArg (fun f : ℕ →₀ ℕ => f c) h
        simp only [cycExp, Finsupp.add_apply,
          Multiset.toFinsupp_apply, Finsupp.single_apply] at happ
        simp only [ite_eq_right (fun h1 : (1 : ℕ) = c => hc h1.symm),
          add_zero] at happ
        exact happ
    exact Multiset.ext.mpr hcount
  · intro h
    rw [cycExp, cycExp, h]

/-- **A class function is determined by its Frobenius pairings**:
if all its completed cycle-weighted sums vanish, it vanishes. -/
theorem classFun_eq_zero_of_cycleProd {n : ℕ}
    (δ : Equiv.Perm (Fin n) → ℂ)
    (hconj : ∀ g c : Equiv.Perm (Fin n), δ (c * g * c⁻¹) = δ g)
    (hvan : ∀ t : ℕ → ℂ,
      ∑ π : Equiv.Perm (Fin n), δ π * cycleProd t π = 0) :
    ∀ π, δ π = 0 := by
  classical
  set p : MvPolynomial ℕ ℂ :=
    ∑ π : Equiv.Perm (Fin n), monomial (cycExp π) (δ π) with hp
  have hp0 : p = 0 := by
    refine mv_eval_zero_nat p fun t => ?_
    rw [hp, map_sum]
    rw [Finset.sum_congr rfl fun π _ => show
        eval t (monomial (cycExp π) (δ π)) = δ π * cycleProd t π
        from by
      rw [show monomial (cycExp π) (δ π) =
        δ π • monomial (cycExp π) (1 : ℂ) from by
          rw [smul_monomial, smul_eq_mul, mul_one]]
      rw [smul_eq_C_mul, map_mul, eval_C, eval_cycExp]]
    exact hvan t
  intro π₀
  have hcoeff := congrArg (fun q : MvPolynomial ℕ ℂ => q.coeff (cycExp π₀)) hp0
  rw [hp, coeff_sum, AddMonoidAlgebra.coeff_zero] at hcoeff
  rw [Finset.sum_congr rfl (fun π _ => coeff_monomial
    (cycExp π₀) (cycExp π) (δ π))] at hcoeff
  rw [Finset.sum_congr rfl (fun π _ => show
      (if cycExp π = cycExp π₀ then δ π else 0) =
      (if cycExp π = cycExp π₀ then δ π₀ else 0) from by
    by_cases hπ : cycExp π = cycExp π₀
    · rw [ite_eq_left hπ, ite_eq_left hπ]
      have hct := (cycExp_eq_iff π π₀).mp hπ
      obtain ⟨c, hc⟩ := isConj_iff.mp
        (Equiv.Perm.isConj_of_cycleType_eq hct.symm)
      rw [← hc, hconj]
    · rw [ite_eq_right hπ, ite_eq_right hπ])] at hcoeff
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hcoeff
  have hmem : π₀ ∈ Finset.univ.filter
      (fun π : Equiv.Perm (Fin n) => cycExp π = cycExp π₀) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hpos : (0 : ℕ) < (Finset.univ.filter
      (fun π : Equiv.Perm (Fin n) => cycExp π = cycExp π₀)).card :=
    Finset.card_pos.mpr ⟨π₀, hmem⟩
  rcases mul_eq_zero.mp hcoeff with hcard | hδ
  · exact absurd hcard (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      hpos))
  · exact hδ

/-- **The package's characters are the Jacobi–Trudi ones.** -/
theorem SchurPackage.char_eq_jtChar (P : SchurPackage.{u})
    (μ : YoungDiagram) (π : Equiv.Perm (Fin μ.card)) :
    P.char μ π = jtChar μ π := by
  have hzero := classFun_eq_zero_of_cycleProd
    (fun π => P.char μ π - jtChar μ π) ?conj ?van π
  · exact sub_eq_zero.mp hzero
  case conj =>
    intro g c
    rw [P.char_conj μ g c]
    congr 1
    rw [jtSimple_char μ, jtSimple_char μ]
    exact Representation.char_conj (ρ := rhoS (jtSimple μ)) g c
  case van =>
    intro t
    have h1 : ((μ.card.factorial : ℂ))⁻¹ *
        ∑ π : Equiv.Perm (Fin μ.card),
          P.char μ π * cycleProd t π = diagramSchur μ t :=
      P.frobenius μ t
    have h2 := jtChar_frobenius' μ t
    have hne : ((μ.card.factorial : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    have hsum := mul_left_cancel₀ hne (h1.trans h2.symm)
    rw [Finset.sum_congr rfl fun π _ => sub_mul (P.char μ π)
      (jtChar μ π) (cycleProd t π)]
    rw [Finset.sum_sub_distrib, hsum, sub_self]

/-- **The package's dimensions are the native ones.** -/
theorem SchurPackage.dim_eq (P : SchurPackage.{u})
    (μ : YoungDiagram) :
    P.dim μ = nDim (jtSimple μ) := by
  have h1 := P.char_one μ
  rw [P.char_eq_jtChar μ 1, jtSimple_char μ 1] at h1
  have h2 : nChar (jtSimple μ) 1 = (nDim (jtSimple μ) : ℂ) := by
    rw [nChar, Representation.char_one]
    rfl
  rw [h2] at h1
  exact_mod_cast h1.symm

/-- **The package idempotents are the native projectors.** -/
theorem SchurPackage.e_eq_nProjector (P : SchurPackage.{u})
    (μ : YoungDiagram) :
    P.e μ = nProjector (jtSimple μ) := by
  rw [SchurPackage.e_def,
    show P.char μ = jtChar μ from funext (P.char_eq_jtChar μ),
    P.dim_eq μ]
  exact charIdempotent_jtSimple μ

end Determination

/-! ### Orthogonality of the blocks

Distinct shapes of one size have orthogonal central idempotents:
through the native action table, a common simple module would force
the two Jacobi–Trudi characters to agree, hence the two Schur
specialisations, hence the shapes — by the separation theorem. -/

section Orthogonality

/-- Relabelling as a homomorphism of permutation groups. -/
def permCastHom {m n : ℕ} (h : m = n) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin n) where
  toFun := permCast h
  map_one' := permCast_one h
  map_mul' := permCast_mul h

/-- The inverse of a relabelling is the reverse relabelling. -/
theorem permCast_symm {m n : ℕ} (h : m = n) :
    (permCast h).symm = permCast h.symm :=
  rfl

/-- Pulling a representation back along a relabelling preserves
irreducibility. -/
theorem isIrreducible_comp_permCastHom {m n : ℕ} (h : m = n)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (hρ : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp (permCastHom h)) := by
  subst h
  have hid : permCastHom (rfl : m = m) =
      MonoidHom.id (Equiv.Perm (Fin m)) := by
    refine MonoidHom.ext fun g => ?_
    change permCast rfl g = g
    rw [permCast_rfl]
    rfl
  rw [hid, MonoidHom.comp_id]
  exact hρ

/-- **Orthogonality of the recast idempotents**, unbundled form:
distinct diagrams of one size have orthogonal idempotents. -/
theorem e_mul_e_eq_zero_of_ne (P : SchurPackage.{u}) {n : ℕ}
    (lam mu : YoungDiagram) (hl : lam.card = n) (hm : mu.card = n)
    (hne : lam ≠ mu) :
    symCast (le_of_eq hl) (P.e lam) *
      symCast (le_of_eq hm) (P.e mu) = 0 := by
  classical
  subst hl
  rw [symCast_le_refl]
  -- the second factor as a class element
  set c' : Equiv.Perm (Fin lam.card) → ℂ :=
    fun g => nCoeff (jtSimple mu) ((permCast hm).symm g) with hc'def
  have hB : symCast (le_of_eq hm) (P.e mu) = classElem c' := by
    rw [P.e_eq_nProjector mu]
    rw [show nProjector (jtSimple mu) =
      classElem (nCoeff (jtSimple mu)) from rfl]
    rw [symCast_classElem_of_eq]
  have hc' : ∀ g c : Equiv.Perm (Fin lam.card),
      c' (c * g * c⁻¹) = c' g := by
    intro g c
    rw [hc'def]
    change nCoeff (jtSimple mu)
      ((permCast hm).symm (c * g * c⁻¹)) = _
    rw [permCast_symm, permCast_mul, permCast_mul, permCast_inv]
    exact nCoeff_classFun (jtSimple mu) _ _
  rw [P.e_eq_nProjector lam, hB]
  -- kill every simple submodule
  apply eq_zero_of_kills_simples
  intro T hT s hs
  rw [mul_assoc,
    classElem_mul_mem_native (S := T) hT c' hc' s hs,
    mul_smul_comm,
    nProjector_mul_mem (jtSimple lam) T
      (jtSimple_simple lam) hT s hs]
  by_cases hiso :
      Nonempty ((rhoS (jtSimple lam)).Equiv (rhoS T))
  swap
  · rw [ite_eq_right hiso, zero_smul, smul_zero]
  rw [ite_eq_left hiso, one_smul]
  suffices hzero : (∑ g, c' g * nChar T g) = 0 by
    rw [hzero, zero_div, zero_smul]
  by_contra hne0
  -- reindex the pairing to the `mu`-side group
  have hre : (∑ g : Equiv.Perm (Fin lam.card), c' g * nChar T g) =
      ∑ g' : Equiv.Perm (Fin mu.card),
        nCoeff (jtSimple mu) g' * nChar T (permCast hm g') := by
    rw [← Equiv.sum_comp (permCast hm)
      (fun g => c' g * nChar T g)]
    refine Finset.sum_congr rfl fun g' _ => ?_
    congr 1
  -- the pulled-back representation of the common simple
  set ρ' : Representation ℂ (Equiv.Perm (Fin mu.card))
      (subCarrier T) := (rhoS T).comp (permCastHom hm) with hρ'
  have hirr' : ρ'.IsIrreducible :=
    isIrreducible_comp_permCastHom hm (rhoS T)
      (rhoS_isIrreducible T hT)
  have hirrS : (rhoS (jtSimple mu)).IsIrreducible :=
    rhoS_isIrreducible (jtSimple mu) (jtSimple_simple mu)
  have hcard0 : ((Nat.card (Equiv.Perm (Fin mu.card)) : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  have : Invertible ((Nat.card (Equiv.Perm (Fin mu.card)) : ℂ)) :=
    invertibleOfNonzero hcard0
  have horth := Representation.char_orthonormal ρ'
    (rhoS (jtSimple mu))
  -- evaluate the pairing
  have hval : (∑ g' : Equiv.Perm (Fin mu.card),
      nCoeff (jtSimple mu) g' * nChar T (permCast hm g')) =
      ((nDim (jtSimple mu) : ℂ) /
        (Fintype.card (Equiv.Perm (Fin mu.card)) : ℂ)) *
      ∑ g' : Equiv.Perm (Fin mu.card),
        ρ'.character g' * (rhoS (jtSimple mu)).character g'⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [nCoeff]
    rw [show nChar T (permCast hm g') = ρ'.character g' from rfl]
    rw [show nChar (jtSimple mu) g'⁻¹ =
      (rhoS (jtSimple mu)).character g'⁻¹ from rfl]
    ring
  have hval2 : (∑ g' : Equiv.Perm (Fin mu.card),
      ρ'.character g' * (rhoS (jtSimple mu)).character g'⁻¹) =
      (Nat.card (Equiv.Perm (Fin mu.card)) : ℂ) *
        (if Nonempty ((rhoS (jtSimple mu)).Equiv ρ')
          then 1 else 0) := by
    rw [← horth, ← mul_assoc, mul_inv_cancel₀ hcard0, one_mul]
  -- a common simple forces the characters to agree
  have hiso2 : Nonempty ((rhoS (jtSimple mu)).Equiv ρ') := by
    by_contra hempty
    rw [hre, hval, hval2, ite_eq_right hempty, mul_zero, mul_zero]
      at hne0
    exact hne0 rfl
  obtain ⟨φlam⟩ := hiso
  obtain ⟨φmu⟩ := hiso2
  have hcharlam : ∀ g, jtChar lam g = nChar T g := by
    intro g
    rw [jtSimple_char lam g]
    exact congrFun (Representation.char_iso φlam) g
  have hcharmu : ∀ g', jtChar mu g' =
      nChar T (permCast hm g') := by
    intro g'
    rw [jtSimple_char mu g']
    exact congrFun (Representation.char_iso φmu) g'
  -- hence the Schur specialisations agree, and the shapes
  have hds : ∀ t, diagramSchur mu t = diagramSchur lam t := by
    intro t
    rw [← jtChar_frobenius' mu t, ← jtChar_frobenius' lam t]
    have hfac : ((mu.card.factorial : ℂ))⁻¹ =
        ((lam.card.factorial : ℂ))⁻¹ := by rw [hm]
    have hsum : (∑ g' : Equiv.Perm (Fin mu.card),
        jtChar mu g' * cycleProd t g') =
        ∑ g : Equiv.Perm (Fin lam.card),
          jtChar lam g * cycleProd t g := by
      rw [← Equiv.sum_comp (permCast hm)
        (fun g => jtChar lam g * cycleProd t g)]
      refine Finset.sum_congr rfl fun g' _ => ?_
      rw [hcharmu g', ← hcharlam (permCast hm g')]
      congr 1
      rw [cycleProd, cycleProd, cycleType_permCast]
      have hexp : mu.card - g'.cycleType.sum =
          lam.card - g'.cycleType.sum := by omega
      rw [hexp]
    rw [hfac, hsum]
  exact hne (diagramSchur_injective hds).symm

/-- **Orthogonality of the blocks**: distinct shapes of one size
have orthogonal recast idempotents. -/
theorem SchurPackage.shape_e_orthogonal (P : SchurPackage.{u})
    {n : ℕ} (μ ν : Shape n) (hμν : μ ≠ ν) :
    Shape.e P μ * Shape.e P ν = 0 := by
  refine e_mul_e_eq_zero_of_ne P μ.val ν.val μ.prop ν.prop ?_
  intro h
  exact hμν (Shape.ext h)

end Orthogonality

/-! ### Completeness of the blocks

The recast idempotents are linearly independent — orthogonal
nonzero idempotents — and all lie in the span of the class sums,
which is at most `p(n)`-dimensional; as there are exactly `p(n)`
shapes, they must span, and expanding the identity over them forces
every coefficient to be `1`. -/

section Completeness

/-- The full cycle type of a permutation of `Fin n`, completed by
its fixed points: a partition of `n`. -/
noncomputable def fullPartition {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Nat.Partition n where
  parts := π.cycleType +
    Multiset.replicate (n - π.cycleType.sum) 1
  parts_pos := fun {p} hp => by
    rcases Multiset.mem_add.mp hp with hp | hp
    · have := Equiv.Perm.two_le_of_mem_cycleType hp
      omega
    · rw [Multiset.eq_of_mem_replicate hp]
      exact Nat.one_pos
  parts_sum := by
    rw [Multiset.sum_add, Equiv.Perm.sum_cycleType,
      Multiset.sum_replicate, smul_eq_mul, mul_one]
    have hle : π.support.card ≤ n := by
      have hcard := Finset.card_le_univ π.support
      rwa [Fintype.card_fin] at hcard
    omega

/-- The full cycle type determines the cycle type. -/
theorem cycleType_eq_of_fullPartition_eq {n : ℕ}
    {π π' : Equiv.Perm (Fin n)}
    (h : fullPartition π = fullPartition π') :
    π.cycleType = π'.cycleType := by
  classical
  have hfil : ∀ σ : Equiv.Perm (Fin n),
      (fullPartition σ).parts.filter (fun p => 2 ≤ p) =
        σ.cycleType := by
    intro σ
    rw [show (fullPartition σ).parts = σ.cycleType +
      Multiset.replicate (n - σ.cycleType.sum) 1 from rfl]
    rw [Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr
      (fun a ha => Equiv.Perm.two_le_of_mem_cycleType ha)]
    rw [Multiset.filter_eq_nil.mpr (fun a ha => by
      rw [Multiset.eq_of_mem_replicate ha]
      omega)]
    rw [add_zero]
  rw [← hfil π, ← hfil π', h]

open scoped Classical in
/-- The class sum of a full cycle type. -/
noncomputable def classSum (n : ℕ) (ρ : Nat.Partition n) :
    SymGroupAlgebra n :=
  ∑ π ∈ Finset.univ.filter
    (fun π : Equiv.Perm (Fin n) => fullPartition π = ρ),
    MonoidAlgebra.single π 1

open scoped Classical in
/-- **Class elements lie in the span of the class sums**: the
conjugation-invariant elements are spanned by `p(n)` vectors. -/
theorem classElem_mem_span_classSum {n : ℕ}
    (c : Equiv.Perm (Fin n) → ℂ)
    (hc : ∀ g k : Equiv.Perm (Fin n), c (k * g * k⁻¹) = c g) :
    classElem c ∈
      Submodule.span ℂ (Set.range (classSum n)) := by
  rw [classElem]
  rw [← Finset.sum_fiberwise Finset.univ
    (fun π : Equiv.Perm (Fin n) => fullPartition π)
    (fun π => c π • MonoidAlgebra.single π (1 : ℂ))]
  refine Submodule.sum_mem _ fun ρ _ => ?_
  by_cases hfib : (Finset.univ.filter
      (fun π : Equiv.Perm (Fin n) => fullPartition π = ρ)).Nonempty
  · obtain ⟨π₀, hπ₀⟩ := hfib
    have hconst : ∀ π ∈ Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) => fullPartition π = ρ),
        c π = c π₀ := by
      intro π hπ
      have hfp : fullPartition π = fullPartition π₀ := by
        rw [(Finset.mem_filter.mp hπ).2,
          (Finset.mem_filter.mp hπ₀).2]
      have hct := cycleType_eq_of_fullPartition_eq hfp
      obtain ⟨k, hk⟩ := isConj_iff.mp
        (Equiv.Perm.isConj_of_cycleType_eq hct.symm)
      rw [← hk, hc]
    rw [Finset.sum_congr rfl fun π hπ => by rw [hconst π hπ]]
    rw [← Finset.smul_sum]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨ρ, rfl⟩)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hfib,
      Finset.sum_empty]
    exact Submodule.zero_mem _

/-- The identity is a class element. -/
theorem one_eq_classElem_ite (n : ℕ) :
    (1 : SymGroupAlgebra n) =
      classElem (fun π : Equiv.Perm (Fin n) =>
        if π = 1 then (1 : ℂ) else 0) := by
  refine MonoidAlgebra.coeff_injective ?_
  ext k
  show (1 : SymGroupAlgebra n).coeff k =
    (classElem (fun π : Equiv.Perm (Fin n) =>
      if π = 1 then (1 : ℂ) else 0)).coeff k
  rw [classElem_coeff]
  rw [show (1 : SymGroupAlgebra n) =
    MonoidAlgebra.single 1 1 from MonoidAlgebra.one_def]
  rw [show (MonoidAlgebra.single (1 : Equiv.Perm (Fin n))
      (1 : ℂ)).coeff k =
    (if (1 : Equiv.Perm (Fin n)) = k then (1 : ℂ) else 0) from
      Finsupp.single_apply]
  by_cases hk : k = 1
  · subst hk
    rw [ite_eq_left rfl]
  · rw [ite_eq_right (fun h => hk h.symm), ite_eq_right hk]

/-- The recast idempotent of a shape is a class element. -/
theorem shape_e_eq_classElem (P : SchurPackage.{u}) {n : ℕ}
    (μ : Shape n) :
    Shape.e P μ = classElem (fun g : Equiv.Perm (Fin n) =>
      nCoeff (jtSimple μ.val) ((permCast μ.prop).symm g)) := by
  rw [Shape.e, P.e_eq_nProjector μ.val,
    show nProjector (jtSimple μ.val) =
      classElem (nCoeff (jtSimple μ.val)) from rfl,
    symCast_classElem_of_eq]

/-- The recast idempotents lie in the span of the class sums. -/
theorem shape_e_mem_span (P : SchurPackage.{u}) {n : ℕ}
    (μ : Shape n) :
    Shape.e P μ ∈
      Submodule.span ℂ (Set.range (classSum n)) := by
  rw [shape_e_eq_classElem]
  refine classElem_mem_span_classSum _ ?_
  intro g k
  show nCoeff (jtSimple μ.val)
    ((permCast μ.prop).symm (k * g * k⁻¹)) = _
  rw [permCast_symm, permCast_mul, permCast_mul, permCast_inv]
  exact nCoeff_classFun (jtSimple μ.val) _ _

/-- The recast idempotents are nonzero. -/
theorem shape_e_ne_zero (P : SchurPackage.{u}) {n : ℕ}
    (μ : Shape n) :
    Shape.e P μ ≠ 0 := by
  rw [Ne, Shape.e_eq_zero_iff]
  exact P.e_ne_zero μ.val

/-- Multiplying a weighted sum of the recast idempotents by one of
them extracts its term. -/
theorem sum_smul_mul_shape_e (P : SchurPackage.{u}) {n : ℕ}
    (c : Shape n → ℂ) (ν : Shape n) :
    (∑ μ : Shape n, c μ • Shape.e P μ) * Shape.e P ν =
      c ν • Shape.e P ν := by
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single ν
    (fun μ _ hμν => by
      rw [smul_mul_assoc, P.shape_e_orthogonal μ ν hμν, smul_zero])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [smul_mul_assoc, Shape.e_mul_self]

/-- The recast idempotents are linearly independent. -/
theorem shape_e_linearIndependent (P : SchurPackage.{u}) (n : ℕ) :
    LinearIndependent ℂ (fun μ : Shape n => Shape.e P μ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc ν
  have hL := sum_smul_mul_shape_e P c ν
  rw [hc, zero_mul] at hL
  rcases smul_eq_zero.mp hL.symm with h0 | h0
  · exact h0
  · exact absurd h0 (shape_e_ne_zero P ν)

/-- The identity of the group algebra lies in the span of the
class sums. -/
theorem one_mem_span_classSum (n : ℕ) :
    (1 : SymGroupAlgebra n) ∈
      Submodule.span ℂ (Set.range (classSum n)) := by
  rw [one_eq_classElem_ite]
  refine classElem_mem_span_classSum _ ?_
  intro g k
  show (if k * g * k⁻¹ = 1 then (1 : ℂ) else 0) =
    (if g = 1 then (1 : ℂ) else 0)
  by_cases hg : g = 1
  · subst hg
    rw [ite_eq_left rfl, ite_eq_left (by group)]
  · rw [ite_eq_right hg, ite_eq_right (fun h => hg (by
      calc g = k⁻¹ * (k * g * k⁻¹) * k := by group
        _ = 1 := by rw [h]; group))]

/-- Every element in the class-sum span has coordinates in the recast
central idempotents. -/
theorem eq_sum_shape_e_of_mem_span (P : SchurPackage.{u}) {n : ℕ}
    {x : SymGroupAlgebra n}
    (hx : x ∈ Submodule.span ℂ (Set.range (classSum n))) :
    ∃ c : Shape n → ℂ, ∑ μ, c μ • Shape.e P μ = x := by
  classical
  set W := Submodule.span ℂ (Set.range (classSum n)) with hWdef
  have : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hfr : Module.finrank ℂ W ≤ Fintype.card (Nat.Partition n) := by
    refine le_trans (finrank_span_le_card (Set.range (classSum n))) ?_
    rw [Set.toFinset_range]
    exact le_trans Finset.card_image_le (le_of_eq Finset.card_univ)
  have hmem : ∀ μ : Shape n, Shape.e P μ ∈ W := shape_e_mem_span P
  set E' : Shape n → W := fun μ => ⟨Shape.e P μ, hmem μ⟩ with hE'def
  have hli' : LinearIndependent ℂ E' :=
    LinearIndependent.of_comp W.subtype
      (shape_e_linearIndependent P n)
  have hcard : Fintype.card (Shape n) = Module.finrank ℂ W :=
    le_antisymm hli'.fintype_card_le_finrank
      (le_trans hfr
        (le_of_eq (Fintype.card_congr (shapeEquivPartition n)).symm))
  have hspan : Submodule.span ℂ (Set.range E') = ⊤ :=
    hli'.span_eq_top_of_card_eq_finrank' hcard
  have h1sp : (⟨x, hx⟩ : W) ∈ Submodule.span ℂ (Set.range E') := by
    rw [hspan]
    exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at h1sp
  obtain ⟨c, hc⟩ := h1sp
  refine ⟨c, ?_⟩
  have hval : W.subtype (∑ μ : Shape n, c μ • E' μ) =
      W.subtype ⟨x, hx⟩ := congrArg _ hc
  rw [map_sum] at hval
  rw [Finset.sum_congr rfl fun μ _ =>
    map_smul W.subtype (c μ) (E' μ)] at hval
  exact hval

/-- **Completeness of the blocks**: at every size the recast
central idempotents sum to the identity of the group algebra. -/
theorem SchurPackage.sum_shape_e_eq_one (P : SchurPackage.{u})
    (n : ℕ) :
    ∑ μ : Shape n, Shape.e P μ = 1 := by
  classical
  obtain ⟨c, hc'⟩ := eq_sum_shape_e_of_mem_span P
    (one_mem_span_classSum n)
  have hone : ∀ ν : Shape n, c ν = 1 := by
    intro ν
    have h := congrArg
      (fun z : SymGroupAlgebra n => z * Shape.e P ν) hc'
    rw [sum_smul_mul_shape_e P c ν, one_mul] at h
    have hz : (c ν - 1) • Shape.e P ν = 0 := by
      rw [sub_smul, one_smul, h, sub_self]
    rcases smul_eq_zero.mp hz with h0 | h0
    · rwa [sub_eq_zero] at h0
    · exact absurd h0 (shape_e_ne_zero P ν)
  rw [← hc']
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hone μ, one_smul]

end Completeness

/-! ### The regular-representation dimension bound

Reading the identity coefficient off the completeness identity
gives `∑ (dim μ)² = n!`; the elementary inequality
`∑ aᵢ² ≤ (∑ aᵢ)²` for naturals and a square root then give the
forms consumed by the Deligne development. -/

section RegularBound

/-- The identity coefficient of a recast idempotent. -/
theorem shape_e_coeff_one (P : SchurPackage.{u}) {n : ℕ}
    (μ : Shape n) :
    (Shape.e P μ).coeff 1 =
      ((P.dim μ.val : ℂ)) ^ 2 / (n.factorial : ℂ) := by
  have h1 : (Shape.e P μ).coeff 1 = (P.e μ.val).coeff 1 := by
    change (symCast (le_of_eq μ.prop) (P.e μ.val)).coeff 1 = (P.e μ.val).coeff 1
    rw [symCast_apply_of_eq μ.prop (P.e μ.val) 1,
      permCast_symm, permCast_one]
  have hfac : ((μ.val.card.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (P.e μ.val).coeff 1 =
      ((P.dim μ.val : ℂ)) ^ 2 / (μ.val.card.factorial : ℂ) := by
    rw [eq_div_iff hfac, mul_comm]
    exact (P.dim_sq_eq_coeff_one μ.val).symm
  rw [h1, h3, Shape.card_val]

/-- **Wedderburn completeness of the blocks**: the squares of the
dimensions of the shapes of size `n` sum to `n!`. -/
theorem SchurPackage.sum_dim_sq_eq (P : SchurPackage.{u}) (n : ℕ) :
    ∑ μ : Shape n, P.dim μ.val ^ 2 = n.factorial := by
  have hsum := congrArg (fun z : SymGroupAlgebra n => z.coeff 1)
    (P.sum_shape_e_eq_one n)
  rw [show (∑ μ : Shape n, Shape.e P μ).coeff 1 =
      ∑ μ : Shape n, (Shape.e P μ).coeff 1 from by
    rw [MonoidAlgebra.coeff_sum]
    exact Finsupp.finsetSum_apply _ _ _] at hsum
  rw [show ((1 : SymGroupAlgebra n)).coeff 1 = 1 from by
    rw [show (1 : SymGroupAlgebra n) =
      MonoidAlgebra.single 1 1 from MonoidAlgebra.one_def]
    exact Finsupp.single_eq_same] at hsum
  rw [Finset.sum_congr rfl fun μ _ => shape_e_coeff_one P μ]
    at hsum
  rw [← Finset.sum_div] at hsum
  have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [div_eq_one_iff_eq hfac] at hsum
  exact_mod_cast hsum

/-- The factorial is at most the square of the dimension sum. -/
theorem SchurPackage.factorial_le_sq_sum_dim (P : SchurPackage.{u})
    (n : ℕ) :
    (n.factorial : ℝ) ≤
      ((∑ μ : Shape n, P.dim μ.val : ℕ) : ℝ) ^ 2 := by
  have h1 := P.sum_dim_sq_eq n
  have h2 : (∑ μ : Shape n, P.dim μ.val ^ 2) ≤
      (∑ μ : Shape n, P.dim μ.val) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => Nat.zero_le _
  rw [h1] at h2
  exact_mod_cast h2

/-- **The regular-representation dimension bound**: the dimensions
of the shapes of size `n` sum to at least `√(n!)`. -/
theorem SchurPackage.sqrt_factorial_le_sum_dim (P : SchurPackage.{u})
    (n : ℕ) :
    Real.sqrt n.factorial ≤
      ((∑ μ : Shape n, P.dim μ.val : ℕ) : ℝ) := by
  have h2 := Real.sqrt_le_sqrt (P.factorial_le_sq_sum_dim n)
  rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at h2

end RegularBound

end RS
