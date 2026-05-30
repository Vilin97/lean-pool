/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.CertifyMaximality
import LeanPool.RingOfIntegersProject.TimesTableAsLists
import LeanPool.RingOfIntegersProject.TimesTable.Defs

/-!
## Certificates for p-maximality

With `K` a torsion-free ring and `O` and `Oₘ` subalgebras, finite and free as `ℤ`-modules,
and such that `O ≤ Oₘ`, we give some certificates for `p`-maximality of `O`.

# Certificates:

- `MaximalOrderCertificateLists`: a certificate for `p`-maximality which always exists for
  a ring of integers· Requires verification of `n` identities in `O / pO` and `n ^ 2` in `O`.
- `MaximalOrderCertificateOfUnramifiedLists` : a shorter certificate for `p`-maximality
  applicable when `p` is unramified in `K`.
- `MaximalOrderCertificateWLists` : a certificate for `p`-maximality using a witness
  evaluation· This requires verification of `n` identities in `O / pO` and `n` in `O`· -/

open Module BigOperators Pointwise

lemma nonempty_sum_of_pos {n m : ℕ} (h : 0 < m + n) : Nonempty ((Fin m) ⊕ (Fin n)) := by
  haveI : Nonempty (Fin (m + n)) := Fin.pos_iff_nonempty.mp h
  exact Equiv.nonempty (finSumFinEquiv)


section Proofs

variable {p t : ℕ} [Fact <| Nat.Prime p] {O : Type*} [CommRing O] (B : Basis (Fin (m + n)) ℤ O)

lemma v_linearIndependent {k : ℕ} (v : Fin k → (Fin (m + n) → (ZMod p)))
    (v_ind : Fin k → Fin (m + n))
  (hindv : ∀ i, v i (v_ind i) ≠ 0 ∧ (∀ j, j ≠ i → v j (v_ind i) = 0)) :
    LinearIndependent (ZMod p) (fun (i : Fin k) => ((basis_zmodp_algebra O p
      B).equivFun.symm).toFun (v i)) := by
  rw [LinearEquiv.toFun_eq_coe]
  simp_rw [Basis.equivFun_symm_eq_repr_symm']
  refine linearIndependent_of_repr_diag (basis_zmodp_algebra O p B) _ ?_
  intro i
  use (v_ind i)
  constructor
  · simp only [Basis.repr_symm_apply, Basis.repr_linearCombination,
    Finsupp.coe_equivFunOnFinite_symm,
      ne_eq]
    exact (hindv i).1
  · intro k hk
    simp only [Basis.repr_symm_apply, Basis.repr_linearCombination,
      Finsupp.coe_equivFunOnFinite_symm]
    exact (hindv i).2 k hk

local notation "Ip" =>  Ideal.radical ((p : O) • (⊤ : Submodule O O) : Ideal O)
local notation I "mod'" p =>  I ⧸ (p : ℤ) • (⊤ : Submodule ℤ Ip)
local notation x "mod" p => (@Submodule.Quotient.mk ℤ Ip _ _ _ ((p : ℤ) • (⊤ : Submodule ℤ Ip))) x
local notation "R" =>   O ⧸ (p : O) • (⊤ : Submodule O O)
local notation x "mod''" p => (Ideal.Quotient.mk ((p : O) • (⊤ : Submodule O O))) x
local notation I "mod'''" p => Submodule.map (quotientMkToSemilinear O O p)
  (Submodule.restrictScalars ℤ I)

lemma wFrob_linearIndependent [Nontrivial O] [Module.Free ℤ O]
    (w : Fin n → (Fin (m + n) → (ZMod p))) (w_ind : Fin n → Fin (m + n))
    (wFrob : Fin n → (Fin (m + n) → (ZMod p)))
    (hindw : ∀ i, wFrob i (w_ind i) ≠ 0 ∧ (∀ j, j ≠ i → wFrob j (w_ind i) = 0))
    (hwFrobComp : ∀ j, (((basis_zmodp_algebra O p B).equivFun.symm).toFun (w j)) ^ (p ^ t) =
      (((basis_zmodp_algebra O p B).equivFun.symm).toFun (wFrob j))) :
  LinearIndependent (ZMod p) (((Frob R p) ^ t : R →ₗ[ZMod p] R) ∘
    (fun j => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (w j))) := by
  have : (((Frob R p) ^ t : R →ₗ[ZMod p] R) ∘ (fun j => ((basis_zmodp_algebra O p
    B).equivFun.symm).toFun (w j))) =
    (fun j => (((basis_zmodp_algebra O p B).equivFun.symm).toFun (wFrob j))) := by
    ext j
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      Function.comp_apply]
    erw [iter_Frob, hwFrobComp j]
    rfl
  simp_rw [this]
  exact v_linearIndependent B wFrob w_ind hindw


lemma v_is_reduced_mod {k : ℕ} (b1 : Fin k → (Fin (m + n) → ℤ))
    (v : Fin k → (Fin (m + n) → (ZMod p)))
    (hmod1 : ∀ i, (algebraMap ℤ (ZMod p)) ∘ (b1 i) = v i) :
    ∀ i, ((fun j => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (v j)) i =
      (fun j => (((B.equivFun.symm).toFun) (b1 j))) i mod'' p) := by
  intro i
  apply LinearEquiv.injective (basis_zmodp_algebra O p B).repr
  ext s
  rw [← basis_zmodp_repr_eq_zmodp_basis_repr O p B (((B.equivFun.symm).toFun) (b1 i))]
  simp_rw [LinearEquiv.toFun_eq_coe, Basis.equivFun_symm_eq_repr_symm']
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination,
    Finsupp.coe_equivFunOnFinite_symm, Function.comp_apply]
  rw [ ← (hmod1 i)]
  rfl

variable [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O]

omit [NoZeroSMulDivisors ℤ O] in
lemma v_in_Frob_ker {k : ℕ} (v : Fin k → (Fin (m + n) → (ZMod p)))
  (hvFrobKer : ∀ i, (((basis_zmodp_algebra O p B).equivFun.symm).toFun (v i)) ^ (p ^ t) = 0) :
  ∀ (i : Fin k), (((Frob R p) ^ t) ((fun j =>
    ((basis_zmodp_algebra O p B).equivFun.symm).toFun (v j)) i) = 0) := by
  intro i
  rw [iter_Frob]
  exact hvFrobKer i

-- If p doesn't divide the discriminant of K, then p is unramified and Ip = pO, which implies
-- p-maximality.

omit [NoZeroSMulDivisors ℤ O] in
lemma rad_eq_smul_top_of_CertificateOfUnramified
  (n t : ℕ) (B : Basis (Fin (0 + n)) ℤ O)
  (hle : n ≤ p ^ t) (w : Fin n → (Fin (0 + n) → (ZMod p)))
  (wFrob : Fin n → (Fin (0 + n) → (ZMod p)))
  (w_ind : Fin n → Fin (0 + n))
  (hindw : ∀ i, wFrob i (w_ind i) ≠ 0 ∧ (∀ j, j ≠ i → wFrob j (w_ind i) = 0))
  (hwFrobComp : ∀ j, (((basis_zmodp_algebra O p B).equivFun.symm).toFun (w j)) ^ (p ^ t) =
    (((basis_zmodp_algebra O p B).equivFun.symm).toFun (wFrob j)))
 : Ip = (p : O) • (⊤ : Submodule O O) := by
  refine le_antisymm ?_ (Ideal.le_radical)
  intro x hx
  have Bc := B
  rw [zero_add] at Bc
  have aux := (radical_eq_kernel_iter_frob_aux O p n t Bc hle (Ideal.Quotient.mk _ x)).1 ⟨x, ⟨hx,
    rfl⟩⟩
  rw [← iter_Frob, ← LinearMap.mem_ker,
  kernel_eq_bot_of_linearIndependent_im (basis_zmodp_algebra O p Bc) _ _
    (wFrob_linearIndependent B w w_ind wFrob hindw hwFrobComp)] at aux
  simp only [Submodule.mem_bot] at aux
  exact Ideal.Quotient.eq_zero_iff_mem.1 aux


omit [Fact (Nat.Prime p)] [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O] in
lemma zsmul_p_aux {a : O} : (p : ℤ) • a = p * a := by
  rw [zsmul_eq_mul]
  norm_cast

variable
[Nonempty (Fin m ⊕ Fin n)]
(hle : m + n ≤ p ^ t)
(b1 : Fin m → (Fin (m + n) → ℤ))
(b2 : Fin n → (Fin (m + n) → ℤ))
(v : Fin m → (Fin (m + n) → (ZMod p)))
(w : Fin n → (Fin (m + n) → (ZMod p)))
(wFrob : Fin n → (Fin (m + n) → (ZMod p)))
(v_ind : Fin m → Fin (m + n))
(w_ind : Fin n → Fin (m + n))
(hmod1 : ∀ i, (algebraMap ℤ (ZMod p)) ∘ (b1 i) = v i)
(hmod2 : ∀ j, (algebraMap ℤ (ZMod p)) ∘ (b2 j) = w j)
(hindv : ∀ i, v i (v_ind i) ≠ 0 ∧ (∀ j, j ≠ i → v j (v_ind i) = 0))
(hindw : ∀ i, wFrob i (w_ind i) ≠ 0 ∧ (∀ j, j ≠ i → wFrob j (w_ind i) = 0))
(hvFrobKer : ∀ i, (((basis_zmodp_algebra O p B).equivFun.symm).toFun (v i)) ^ (p ^ t) = 0)
(hwFrobComp : ∀ j, (((basis_zmodp_algebra O p B).equivFun.symm).toFun (w j)) ^ (p ^ t) =
  (((basis_zmodp_algebra O p B).equivFun.symm).toFun (wFrob j)))
    -- Proof that wFrob is the image of w under the Frobenius map.


/-- Imported declaration. -/
noncomputable def BasisRadMod : Basis (Fin m ⊕ Fin n) (ZMod p) (Ip mod' p) := by
  let b1' := (fun j => (((B.equivFun.symm).toFun) (b1 j)))
  let b2' := (fun j => (((B.equivFun.symm).toFun) (b2 j)))
  let v' := (fun i => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (v i))
  let w' := (fun i => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (w i))
  refine basis_radical_of_linear_independent_ker_im O p b1' b2' v' w' ?_ ?_ ?_ ?_ ?_ hle B
  · exact v_is_reduced_mod B b1 v hmod1
  · exact v_is_reduced_mod B b2 w hmod2
  · exact v_linearIndependent B v v_ind hindv
  · exact wFrob_linearIndependent B w w_ind wFrob hindw hwFrobComp
  · exact v_in_Frob_ker B v hvFrobKer


include v w hle hmod1 hindv hindw hvFrobKer hwFrobComp in
lemma aux_in_Ip (k : Fin m ⊕ Fin n) :
   Sum.elim (fun i => ((B.equivFun.symm).toFun) (b1 i)) (↑(p : Fin n → O)  *
    (fun j => ((B.equivFun.symm).toFun) (b2 j))) k ∈ Ip := by
  let b1' := (fun j => (((B.equivFun.symm).toFun) (b1 j)))
  let b2' := (fun j => (((B.equivFun.symm).toFun) (b2 j)))
  let v' := (fun i => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (v i))
  let w' := (fun i => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (w i))
  refine basis_radical_of_linear_independent_ker_im_def_in_Ip O p b1' b2' v' w' ?_ ?_ ?_ ?_ hle B k
  · exact v_is_reduced_mod B b1 v hmod1
  · exact v_linearIndependent B v v_ind hindv
  · exact wFrob_linearIndependent B w w_ind wFrob hindw hwFrobComp
  · exact v_in_Frob_ker B v hvFrobKer


local notation "B'" => BasisRadMod B hle b1 b2 v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw
  hvFrobKer hwFrobComp
local notation "InAux" k => aux_in_Ip B hle b1 b2 v w wFrob v_ind w_ind hmod1 hindv hindw hvFrobKer
  hwFrobComp k

lemma BasisRadMod_apply (k : Fin m ⊕ Fin n) : B' k =
    (⟨Sum.elim (fun i => ((B.equivFun.symm).toFun) (b1 i))
  (↑(p : Fin n → O)  * (fun j => ((B.equivFun.symm).toFun) (b2 j))) k, InAux k⟩ : Ip) mod p := by
  let b1' := (fun j => (((B.equivFun.symm).toFun) (b1 j)))
  let b2' := (fun j => (((B.equivFun.symm).toFun) (b2 j)))
  let v' := (fun i => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (v i))
  let w' := (fun i => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (w i))
  refine basis_radical_of_linear_independent_ker_im_app O p b1' b2' v' w' ?_ ?_ _ _ ?_ hle B k
  · exact v_is_reduced_mod B b1 v hmod1
  · exact v_is_reduced_mod B b2 w hmod2

variable
-- Linear idependence by looking at the matrices of `n` endomorphisms
(g : Fin (m + n) → (Fin (m + n) → ℤ))
(a : Fin (m + n) → Fin m → (Fin m → ℤ))
(c : Fin (m + n) → Fin m → (Fin n → ℤ))
(d : Fin (m + n) → Fin n → (Fin m → ℤ))
(e : Fin (m + n) → Fin n → (Fin n → ℤ))
(ab_ind : Fin (m + n) → ((Fin m ⊕ Fin n) × (Fin m ⊕ Fin n)))
(hindab : ∀ (i : Fin (m + n)), (algebraMap ℤ (ZMod p)) ((fun k => Sum.elim ((fun j =>
  Sum.elim (a k j) (c k j))) ((fun j => Sum.elim (d k j) (e k j)))) i (ab_ind i).1 (ab_ind i).2) ≠
    0 ∧
    (∀ j, j ≠ i → (algebraMap ℤ (ZMod p)) ((fun k => Sum.elim ((fun j => Sum.elim (a k j) (c k j)))
      ((fun j => Sum.elim (d k j) (e k j)))) j (ab_ind i).1 (ab_ind i).2) = 0))
(hmul1 : ∀ i j, (B.equivFun.symm).toFun (g i) * ((B.equivFun.symm).toFun (b1 j)) =
  Finset.univ.sum (fun l => (a i j l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (c i j l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k))
      l))))
(hmul2 : ∀ i j, (B.equivFun.symm).toFun (g i) * ((p : ℤ) • ((B.equivFun.symm).toFun (b2 j))) =
  Finset.univ.sum (fun l => (d i j l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (e i j l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k))
      l))))

include B g b1 b2 hle v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw hvFrobKer hwFrobComp hindab
  hmul1 hmul2 in
/-- Given the certifying data, the map `map_to_end_lin` has trivial kernel· -/
lemma ker_map_eq_bot_of_data : LinearMap.ker (map_to_end_lin O p) = ⊥ := by
  let g' := (fun i => (B.equivFun.symm).toFun (g i))
  let q := Sum.elim (fun i => ((B.equivFun.symm).toFun) (b1 i)) (↑(p : Fin n →
    O)  * (fun j => ((B.equivFun.symm).toFun) (b2 j)))
  let BMod := BasisRadMod B hle b1 b2 v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw hvFrobKer
    hwFrobComp
  convert ker_map_to_end_lin_eq_bot_of_mul_ne_zero' O p g' q (basis_zmodp_algebra O p B) BMod ?_ ?_
    ?_
  · exact aux_in_Ip B hle b1 b2 v w wFrob v_ind w_ind hmod1 hindv hindw hvFrobKer hwFrobComp
  · exact
      BasisRadMod_apply B hle b1 b2 v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw hvFrobKer
        hwFrobComp
  · intro i
    specialize hindab i
    use (ab_ind i).1, (ab_ind i).2
    cases h : (ab_ind i).1
    · simp_rw [h] at hindab
      simp only [g', q]
      dsimp at hindab ⊢
      simp_rw [← LinearEquiv.toFun_eq_coe, hmul1, zsmul_p_aux]
      constructor
      · simp only [BMod, BasisRadMod]
        erw [← basis_radical_of_linear_independent_ker_im_in_repr]
        convert hindab.1
      · intro l hl
        simp only [BMod, BasisRadMod]
        erw [← basis_radical_of_linear_independent_ker_im_in_repr]
        convert hindab.2 l hl
    · simp_rw [h] at hindab
      simp only [g', q]
      dsimp at hindab ⊢
      simp_rw [← LinearEquiv.toFun_eq_coe, ← zsmul_p_aux, hmul2, zsmul_p_aux]
      constructor
      · simp only [BMod, BasisRadMod]
        erw [← basis_radical_of_linear_independent_ker_im_in_repr]
        convert hindab.1
      · intro l hl
        simp only [BMod, BasisRadMod]
        erw [← basis_radical_of_linear_independent_ker_im_in_repr]
        convert hindab.2 l hl


-- Linear independence by evaluating `n` endomorphisms at a single witness.

include B b1 b2 hle v w wFrob v_ind w_ind hmod1 hindv hindw hvFrobKer hwFrobComp in
lemma sum_in_Ip (wit1 : Fin m → ℤ) (wit2 : Fin n → ℤ) : Finset.univ.sum
    (fun l => (wit1 l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (wit2 l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k)) l)))
      ∈ Ip := by
  let b1' := (fun j => (((B.equivFun.symm).toFun) (b1 j)))
  let b2' := (fun j => (((B.equivFun.symm).toFun) (b2 j)))
  let v' := (fun i => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (v i))
  let w' := (fun i => ((basis_zmodp_algebra O p B).equivFun.symm).toFun (w i))
  simp_rw [zsmul_p_aux]
  refine basis_radical_of_linear_independent_ker_im_in_Ip O p b1' b2' v' w' ?_ ?_ ?_ ?_ hle B wit1
    wit2
  · exact v_is_reduced_mod B b1 v hmod1
  · exact v_linearIndependent B v v_ind hindv
  · exact wFrob_linearIndependent B w w_ind wFrob hindw hwFrobComp
  · exact v_in_Frob_ker B v hvFrobKer

variable
  (wit1 : Fin m → ℤ)
  (wit2 : Fin n → ℤ)
  (aw : Fin (m + n) → (Fin m → ℤ))
  (cw : Fin (m + n) → (Fin n → ℤ))
  (hmulw : ∀ i, (B.equivFun.symm).toFun (g i) * (Finset.univ.sum (fun l =>
  (wit1 l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
  Finset.univ.sum (fun l => (wit2 l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k)) l)))) =
  Finset.univ.sum (fun l => (aw i l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
  Finset.univ.sum (fun l => (cw i l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k)) l))))
  (ac_indw : Fin (m + n) → (Fin m ⊕ Fin n))
  (hacindw : ∀ i, ((algebraMap ℤ (ZMod p)) ((Sum.elim (fun j => aw i j) (fun j => cw i j)) (ac_indw
    i)) ≠ 0 ∧
      ∀ k, k ≠ i → (algebraMap ℤ (ZMod p)) ((Sum.elim (fun j => aw k j) (fun j => cw k j)) (ac_indw
        i)) = 0))


include B g b1 b2 hle v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw hvFrobKer hwFrobComp wit1 wit2
  hacindw hmulw in
/-- Given the certifying data, the map `map_to_end_lin` has trivial endomorphism· -/
lemma ker_map_eq_bot_of_data_witness : LinearMap.ker (map_to_end_lin O p) = ⊥ := by
  let g' := (fun i => (B.equivFun.symm).toFun (g i))
  let wit := Finset.univ.sum (fun l => (wit1 l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (wit2 l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k)) l)))
  let BMod := BasisRadMod B hle b1 b2 v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw hvFrobKer
    hwFrobComp
  convert ker_map_to_end_lin_eq_bot_of_mul_ne_zero_of_single_eval O p g' wit ?_
    (basis_zmodp_algebra O p B) BMod ?_
  swap
  · intro i
    specialize hacindw i
    use (ac_indw i)
    cases h : (ac_indw i)
    · simp_rw [h] at hacindw
      simp only [g']
      dsimp at hacindw ⊢
      unfold wit
      simp_rw [← LinearEquiv.toFun_eq_coe, hmulw, zsmul_p_aux]
      simp only [BMod, BasisRadMod]
      constructor
      · erw [← basis_radical_of_linear_independent_ker_im_in_repr]
        exact hacindw.1
      · intro k hk
        erw [← basis_radical_of_linear_independent_ker_im_in_repr]
        exact hacindw.2 k hk
    · simp_rw [h] at hacindw
      simp only [g']
      dsimp at hacindw ⊢
      unfold wit
      simp_rw [← LinearEquiv.toFun_eq_coe, hmulw, zsmul_p_aux]
      simp only [BMod, BasisRadMod]
      constructor
      · erw [← basis_radical_of_linear_independent_ker_im_in_repr]
        exact hacindw.1
      · intro k hk
        erw [← basis_radical_of_linear_independent_ker_im_in_repr]
        exact hacindw.2 k hk
  · exact sum_in_Ip B hle b1 b2 v w wFrob v_ind w_ind hmod1 hindv hindw
      hvFrobKer hwFrobComp wit1 wit2


end Proofs


section ProofLists

/- Here we translate the previous certifying data into our computations with lists using a
  times table· -/


variable {p t : ℕ} {O : Type*} [CommRing O]
  (B : Basis (Fin (m + n)) ℤ O)

variable
  (b1 : Fin m → (Fin (m + n) → ℤ))
  (b2 : Fin n → (Fin (m + n) → ℤ))

-- Pointwise addition has been implemented for Lists of integers (Lean.Omega.IntList.add).
-- We exclude this instance
attribute [-instance]  Lean.Omega.IntList.instAdd

lemma hmul_lists_aux (a1 : Fin m → ℤ) (a2 : Fin n → ℤ)
  (c : Fin (m + n) → ℤ)
  (h : List.ofFn c = List.sum (List.ofFn (fun l => List.mulPointwise (a1 l) (List.ofFn (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise ((a2 l) * ↑p) (List.ofFn (b2 l))))) :
  (B.equivFun.symm).toFun c = Finset.univ.sum (fun l => (a1 l) •
  ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +  Finset.univ.sum (fun l => (a2 l) • ((p : ℤ) •
    ((fun k => (B.equivFun.symm).toFun (b2 k)) l))) := by
  have zero_add': ∀ (l : List ℤ), 0 + l = l := by simp only [zero_add, implies_true]
  have add_zero': ∀ (l : List ℤ), l + 0 = l := by simp only [add_zero, implies_true]
  simp only [LinearEquiv.toFun_eq_coe, Basis.equivFun_symm_eq_repr_symm' B]
  apply_fun B.repr
  · simp only [Basis.repr_symm_apply, map_add, map_sum, map_smul, Basis.repr_linearCombination,
      smul_smul]
    simp_rw [List.mulPointwise_ofFn] at h
    cases m
    · cases n
      · simp only [Nat.add_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        dsimp at c
        exact Subsingleton.eq_zero (Finsupp.equivFunOnFinite.symm c)
      · rw [← (List.sum_ofFn' (Nat.succ_ne_zero _) (fun l => (a2 l * ↑p) • b2 l))] at h
        simp only [List.ofFn_zero, List.sum_nil, zero_add', List.ofFn_inj] at h
        ext k
        rw [h]
        simp only [zsmul_eq_mul, Int.cast_mul, Pi.intCast_def, Int.cast_id, Int.cast_natCast,
          Pi.natCast_def,
        Finset.sum_apply, Pi.mul_apply, Finset.univ_eq_empty, Finset.sum_empty,
          Finsupp.finset_sum_apply, Finsupp.coe_smul, Pi.smul_apply,
        Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul, zero_add]
    · cases n
      · rw [← (List.sum_ofFn' (Nat.succ_ne_zero _) (fun l => (a1 l) • b1 l))] at h
        simp only [List.ofFn_zero, List.sum_nil, add_zero', List.ofFn_inj] at h
        ext k
        rw [h]
        simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id,
          Finsupp.coe_equivFunOnFinite_symm, Finset.sum_apply, Pi.mul_apply,
          Finsupp.coe_finset_sum, Finsupp.coe_smul, Nat.succ_eq_add_one,
          Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      · rw [← (List.sum_ofFn' (Nat.succ_ne_zero _) (fun l => (a2 l * ↑p) • b2 l))] at h
        rw [← (List.sum_ofFn' (Nat.succ_ne_zero _) (fun l => (a1 l) • b1 l))] at h
        simp only [List.add_ofFn, List.ofFn_inj] at h
        ext k
        rw [h]
        simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Int.cast_mul, Int.cast_natCast,
          Pi.natCast_def,
        Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply, Finset.sum_apply, Pi.mul_apply,
        Finsupp.coe_add, Finsupp.coe_finset_sum, Finsupp.coe_smul]
  · exact LinearEquiv.injective B.repr

lemma hmul_lists_aux_length (a1 : Fin m → ℤ) (a2 : Fin n → ℤ)
 : (List.sum (List.ofFn (fun l => List.mulPointwise (a1 l) (List.ofFn (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise ((a2 l) * ↑p) (List.ofFn (b2 l))))).length =
      m + n := by
  rw [List.add_length]
  cases m
  · cases n
    · simp only [add_zero, List.ofFn_zero, List.sum_nil, max_self, List.length_eq_zero_iff]
      rfl
    · erw [List.ofFn_zero, List.sum_nil, List.length_nil, Nat.max_comm, Nat.max_zero]
      rw [list_sum_length (Nat.succ_ne_zero _)]
      intro i
      rw [List.mulPointwise_length, List.length_ofFn]
  · rcases n
    · erw [List.ofFn_zero, List.sum_nil, List.length_nil, Nat.max_zero]
      rw [list_sum_length (Nat.succ_ne_zero _)]
      intro i
      rw [List.mulPointwise_length, List.length_ofFn]
    · rw [Nat.max_eq_left ?_, list_sum_length (Nat.succ_ne_zero _)]
      · intro i
        rw [List.mulPointwise_length, List.length_ofFn]
      · rw [list_sum_length (Nat.succ_ne_zero _), list_sum_length (Nat.succ_ne_zero _)]
        · intro i
          rw [List.mulPointwise_length, List.length_ofFn]
        · intro i
          rw [List.mulPointwise_length, List.length_ofFn]


variable
  (g : Fin (m + n) → (Fin (m + n) → ℤ))
  (T' : Fin (m + n) → Fin (m + n) → Fin (m + n) → ℤ)
  (T : Fin (m + n) → Fin (m + n) → List ℤ)
  (heq : ∀ i j, T i j = List.ofFn (T' i j))
  (basisMulBasis : ∀ i j k, B.repr (B i * B j) k = T' i j k)

variable [hp : Fact <| Nat.Prime p] [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O]

include T' basisMulBasis heq in
omit hp [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O] in
lemma hmul1_lists (a : Fin (m + n) → Fin m → (Fin m → ℤ))
    (c : Fin (m + n) → Fin m → (Fin n → ℤ))
    (i : Fin (m + n)) (j : Fin m)
    (h : table_mul_list T (List.ofFn (g i)) (List.ofFn (b1 j)) =
    List.sum (List.ofFn (fun l => List.mulPointwise (a i j l) (List.ofFn (b1 l)))) +
      List.sum (List.ofFn (fun l => List.mulPointwise ((c i j l) * p) (List.ofFn (b2 l))))) :
  (B.equivFun.symm).toFun (g i) * ((B.equivFun.symm).toFun (b1 j)) =
  Finset.univ.sum (fun l => (a i j l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (c i j l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k))
      l))) := by
  let c' := FnOfList (m + n) (table_mul_list' T' (List.ofFn (g i)) (List.ofFn (b1 j)))
    (table_mul_list_length T' _ _)
  have hc' : List.ofFn c' = table_mul_list' T' (List.ofFn (g i)) (List.ofFn (b1 j)) := by rw
    [listOfFn_of_FnOfList]
  erw [table_mul_list_eq_mul T' B _ _ _ basisMulBasis hc' ]
  rw [← table_mul_eq_table_mul' T' T heq, h] at hc'
  exact hmul_lists_aux B b1 b2 _ _ c' hc'

include T' basisMulBasis heq in
omit hp [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O] in
lemma hmul2_lists (d : Fin (m + n) → Fin n → (Fin m → ℤ))
    (e : Fin (m + n) → Fin n → (Fin n → ℤ))
    (i : Fin (m + n)) (j : Fin n)
    (h : table_mul_list T (List.ofFn (g i)) (List.mulPointwise p (List.ofFn (b2 j))) =
    List.sum (List.ofFn (fun l => List.mulPointwise (d i j l) (List.ofFn (b1 l)))) +
      List.sum (List.ofFn (fun l => List.mulPointwise ((e i j l) * p) (List.ofFn (b2 l))))) :
  (B.equivFun.symm).toFun (g i) * ((p : ℤ) • ((B.equivFun.symm).toFun (b2 j))) =
  Finset.univ.sum (fun l => (d i j l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (e i j l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k))
      l))) := by
  let c' := FnOfList (m + n) (table_mul_list' T' (List.ofFn (g i)) (List.mulPointwise p (List.ofFn
    (b2 j)))) (table_mul_list_length T' _ _)
  have hc' : List.ofFn c' = table_mul_list' T' (List.ofFn (g i)) (List.mulPointwise p (List.ofFn
    (b2 j))) := by rw [listOfFn_of_FnOfList]
  have hcc := hc'
  rw [List.mulPointwise_ofFn] at hc'
  dsimp
  rw [← map_smul]
  erw [table_mul_list_eq_mul T' B _ _ _ basisMulBasis hc' ]
  rw [← table_mul_eq_table_mul' T' T heq, h] at hcc
  exact hmul_lists_aux B b1 b2 _ _ c' hcc

include T' basisMulBasis heq in
omit hp [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O] in
lemma hmul_lists_witness (wit1 : Fin m → ℤ) (wit2 : Fin n → ℤ)
  (aw : Fin (m + n) → (Fin m → ℤ)) (cw : Fin (m + n) → (Fin n → ℤ))
  (i : Fin (m + n))
  (h : table_mul_list T (List.ofFn (g i)) (List.sum (List.ofFn (fun l => List.mulPointwise (wit1 l)
    (List.ofFn (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise ((wit2 l) * p) (List.ofFn (b2 l))))) =
    List.sum (List.ofFn (fun l => List.mulPointwise ((aw i) l) (List.ofFn (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise (((cw i) l) * p) (List.ofFn (b2 l))))) :
    (B.equivFun.symm).toFun (g i) * (Finset.univ.sum (fun l => (wit1 l) • ((fun k =>
      (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (wit2 l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k))
      l)))) =
    Finset.univ.sum (fun l => (aw i l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (cw i l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k)) l)))
      := by
  let c' := FnOfList (m + n) (table_mul_list' T' (List.ofFn (g i)) ((List.sum (List.ofFn (fun l =>
    List.mulPointwise (wit1 l) (List.ofFn (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise ((wit2 l) *
      p) (List.ofFn (b2 l))))))) (table_mul_list_length T' _ _)
  have hc' : List.ofFn c' = table_mul_list' T' (List.ofFn (g i)) ((List.sum (List.ofFn (fun l =>
    List.mulPointwise (wit1 l) (List.ofFn (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise ((wit2 l) *
      p) (List.ofFn (b2 l)))))) := by rw [listOfFn_of_FnOfList]
  let c'' := FnOfList (m + n) (List.sum (List.ofFn (fun l => List.mulPointwise (wit1 l) (List.ofFn
    (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise ((wit2 l) * p) (List.ofFn (b2 l)))))
    (by apply hmul_lists_aux_length)
  have hc'' : List.ofFn c'' = (List.sum (List.ofFn (fun l => List.mulPointwise (wit1 l) (List.ofFn
    (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise ((wit2 l) *
      p) (List.ofFn (b2 l))))) := by rw [listOfFn_of_FnOfList]
  have hcc' := hc'
  rw [← hc''] at hc'
  rw [← table_mul_eq_table_mul' T' T heq, h] at hcc'
  erw [← hmul_lists_aux B b1 b2 _ _ _  hc'', table_mul_list_eq_mul T' B _ _ _ basisMulBasis hc']
  exact hmul_lists_aux B b1 b2 _ _ c' hcc'

variable
  (TMod : Fin (m + n) → Fin (m + n) → List (ZMod p))
  (hTMod : ∀ i j, List.map (algebraMap ℤ (ZMod p)) (T i j) = TMod i j)

include basisMulBasis in
omit [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O] in
lemma basisModMulbasisMod : ∀ i j k,
  (basis_zmodp_algebra O p B).repr (((basis_zmodp_algebra O p B) i) *
    ((basis_zmodp_algebra O p B) j)) k =
  (fun i j k => (algebraMap ℤ (ZMod p) ((T' i j k)))) i j k:= by
  intro i j k
  erw [basis_zmodp_repr_mul_eq_zmodp_basis_repr_mul O p B i j k,
  Function.comp_apply, basisMulBasis i j k]

include hTMod heq in
omit [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O] in
lemma THeqMod : ∀ i j, TMod i j = List.ofFn
    ((fun i j k => (algebraMap ℤ (ZMod p) ((T' i j k)))) i j) := by
  intro i j
  rw [← hTMod, heq, List.map_ofFn, List.ofFn_inj]
  rfl

variable
  (v : Fin m → (Fin (m + n) → (ZMod p)))
  (w : Fin n → (Fin (m + n) → (ZMod p)))
  (wFrob : Fin n → (Fin (m + n) → (ZMod p)))

include hTMod heq basisMulBasis in
omit [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O] in
lemma hvFrobKer_lists (i : Fin m)
  (h : nPow_sq_table TMod (List.ofFn (v i)) (p ^ t) = List.replicate (m + n) 0) :
   (((basis_zmodp_algebra O p B).equivFun.symm) (v i)) ^ (p ^ t) = 0 := by
   set l := fun (_ : Fin (m + n)) => (0 : ZMod p) with hld
   have hl : List.ofFn l = List.replicate (m + n) 0 := List.ofFn_const _ _
   rw [← h] at hl
   rw [table_nPow_sq_table_eq_pow _ TMod ((basis_zmodp_algebra O p B)) (v i) (basisModMulbasisMod B
     T' basisMulBasis)
    (THeqMod T' T heq TMod hTMod) _ (Nat.pow_pos (n := t) (Nat.Prime.pos (hp.out))) l hl]
   rw [hld]
   simp only [     Basis.equivFun_symm_apply, zero_smul, Finset.sum_const_zero]

include hTMod heq basisMulBasis in
omit [Nontrivial O] [NoZeroSMulDivisors ℤ O] [Module.Free ℤ O] in
lemma hwFrobComp_lists (j : Fin n)
  (h : nPow_sq_table TMod (List.ofFn (w j)) (p ^ t) = List.ofFn (wFrob j)) :
  (((basis_zmodp_algebra O p B).equivFun.symm) (w j)) ^ (p ^ t) =
  (((basis_zmodp_algebra O p B).equivFun.symm) (wFrob j)) := by
  rw [table_nPow_sq_table_eq_pow _ TMod ((basis_zmodp_algebra O p B)) (w j) (basisModMulbasisMod B
    T' basisMulBasis)
    (THeqMod T' T heq TMod hTMod) _ (Nat.pow_pos (n := t) (Nat.Prime.pos (hp.out))) (wFrob j)
      h.symm]

end ProofLists


section Data

instance subalgebraNoZeroSMulDivisorsInt {K : Type*} [CommRing K] [NoZeroSMulDivisors ℤ K]
    (O : Subalgebra ℤ K) : NoZeroSMulDivisors ℤ O :=
  Function.Injective.noZeroSMulDivisors (fun x : O => (x : K)) Subtype.val_injective rfl
    (by intro c x; rfl)

/- This collection of data proves that `O` is `p`-maximal· -/

variable
{K : Type*} [CommRing K] [NoZeroSMulDivisors ℤ K]
(O : Subalgebra ℤ K) (p : ℕ) [hpI : Fact <| Nat.Prime p]
{Om : Subalgebra ℤ K} (hm : O ≤ Om) {n m : ℕ}
(B : Basis (Fin (m + n)) ℤ O)
(B' : Basis (Fin (m + n)) ℤ Om)
(hpos : 0 < m + n)
(hle : m + n ≤ p ^ t)
(b1 : Fin m → (Fin (m + n) → ℤ))
(b2 : Fin n → (Fin (m + n) → ℤ))
(v : Fin m → (Fin (m + n) → (ZMod p)))
(w : Fin n → (Fin (m + n) → (ZMod p)))
(wFrob : Fin n → (Fin (m + n) → (ZMod p)))
(v_ind : Fin m → Fin (m + n))
(w_ind : Fin n → Fin (m + n))
(hmod1 : ∀ i, (algebraMap ℤ (ZMod p)) ∘ (b1 i) = v i)
(hmod2 : ∀ j, (algebraMap ℤ (ZMod p)) ∘ (b2 j) = w j)
(hindv : ∀ i, v i (v_ind i) ≠ 0 ∧ (∀ j, j ≠ i → v j (v_ind i) = 0))
(hindw : ∀ i, wFrob i (w_ind i) ≠ 0 ∧ (∀ j, j ≠ i → wFrob j (w_ind i) = 0))
(hvFrobKer : ∀ i, (((basis_zmodp_algebra O p B).equivFun.symm).toFun (v i)) ^ (p ^ t) = 0)
(hwFrobComp : ∀ j, (((basis_zmodp_algebra O p B).equivFun.symm).toFun (w j)) ^ (p ^ t) =
  (((basis_zmodp_algebra O p B).equivFun.symm).toFun (wFrob j)))
(g : Fin (m + n) → (Fin (m + n) → ℤ))
(a : Fin (m + n) → Fin m → (Fin m → ℤ))
(c : Fin (m + n) → Fin m → (Fin n → ℤ))
(d : Fin (m + n) → Fin n → (Fin m → ℤ))
(e : Fin (m + n) → Fin n → (Fin n → ℤ))
(ab_ind : Fin (m + n) → ((Fin m ⊕ Fin n) × (Fin m ⊕ Fin n)))
(hindab : ∀ (i : Fin (m + n)), (algebraMap ℤ (ZMod p)) ((fun k => Sum.elim
  ((fun j => Sum.elim (a k j) (c k j))) ((fun j => Sum.elim (d k j) (e k j)))) i
  (ab_ind i).1 (ab_ind i).2) ≠ 0 ∧ (∀ j, j ≠ i → (algebraMap ℤ (ZMod p))
  ((fun k => Sum.elim ((fun j => Sum.elim (a k j) (c k j)))
  ((fun j => Sum.elim (d k j) (e k j)))) j (ab_ind i).1 (ab_ind i).2) = 0))
(hmul1 : ∀ i j, (B.equivFun.symm).toFun (g i) * ((B.equivFun.symm).toFun (b1 j)) =
  Finset.univ.sum (fun l => (a i j l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
  Finset.univ.sum (fun l => (c i j l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k)) l))))
(hmul2 : ∀ i j, (B.equivFun.symm).toFun (g i) * ((p : ℤ) • ((B.equivFun.symm).toFun (b2 j))) =
  Finset.univ.sum (fun l => (d i j l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
  Finset.univ.sum (fun l => (e i j l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k)) l))))

local notation "O*" => Subalgebra.toSubmodule (AlgHom.range (Subalgebra.inclusion hm))

include hpos B hpI B' hle b1 b2 v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw hvFrobKer hwFrobComp
  g a c d e ab_ind hindab hmul1 hmul2
lemma pMaximal_of_data [Module.Free ℤ Om] [Module.Finite ℤ Om] : piMaximal (p : ℤ)  O* := by
  haveI := nonempty_sum_of_pos hpos
  haveI := Module.Free.of_basis B
  haveI : Nontrivial O := by
    rw [nontrivial_iff]
    use (B (⟨0, hpos⟩ : Fin (m + n))), 0
    apply Basis.ne_zero
  have : (algebraMap ℤ O p) = (p : O) := by norm_num
  refine order_piMaximal_of_order_eq_multiplierRing hm (Nat.prime_iff_prime_int.mp hpI.out) ?_ ?_
  · rw [rank_eq_card_basis B, rank_eq_card_basis B']
  · rw [this]
    refine mult_ring_eq_ring_of_trivial_ker_map_to_end_lin O p ?_
    exact
      ker_map_eq_bot_of_data B hle b1 b2 v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw hvFrobKer
        hwFrobComp g a c d e ab_ind hindab hmul1 hmul2


variable
(wit1 : Fin m → ℤ)
(wit2 : Fin n → ℤ)
(aw : Fin (m + n) → (Fin m → ℤ))
(cw : Fin (m + n) → (Fin n → ℤ))
(hmulw : ∀ i, (B.equivFun.symm).toFun (g i) * (Finset.univ.sum (fun l => (wit1 l) • ((fun k =>
  (B.equivFun.symm).toFun (b1 k)) l)) +
    Finset.univ.sum (fun l => (wit2 l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k))
      l)))) =
  Finset.univ.sum (fun l => (aw i l) • ((fun k => (B.equivFun.symm).toFun (b1 k)) l)) +
  Finset.univ.sum (fun l => (cw i l) • ((p : ℤ) • ((fun k => (B.equivFun.symm).toFun (b2 k)) l))))
(ac_indw : Fin (m + n) → (Fin m ⊕ Fin n))
(hacindw : ∀ i, ((algebraMap ℤ (ZMod p)) ((Sum.elim (fun j => aw i j) (fun j => cw i j)) (ac_indw
  i)) ≠ 0 ∧
      ∀ k, k ≠ i → (algebraMap ℤ (ZMod p)) ((Sum.elim (fun j => aw k j) (fun j => cw k j)) (ac_indw
        i)) = 0))

include wit1 wit2 aw cw hmulw ac_indw hacindw in
omit hindab hmul1 hmul2 a c d e ab_ind in
lemma pMaximal_of_data_witness [Module.Free ℤ Om] [Module.Finite ℤ Om] : piMaximal (p : ℤ)  O* := by
  haveI := nonempty_sum_of_pos hpos
  haveI := Module.Free.of_basis B
  haveI : Nontrivial O := by
    rw [nontrivial_iff]
    use (B (⟨0, hpos⟩ : Fin (m + n))), 0
    apply Basis.ne_zero
  have : (algebraMap ℤ O p) = (p : O) := by norm_num
  refine order_piMaximal_of_order_eq_multiplierRing hm (Nat.prime_iff_prime_int.mp hpI.out) ?_ ?_
  · rw [rank_eq_card_basis B, rank_eq_card_basis B']
  · rw [this]
    refine mult_ring_eq_ring_of_trivial_ker_map_to_end_lin O p ?_
    exact ker_map_eq_bot_of_data_witness B hle b1 b2 v w wFrob v_ind w_ind hmod1 hmod2 hindv hindw
      hvFrobKer hwFrobComp g wit1 wit2 aw cw hmulw ac_indw hacindw

end Data

--------------------------------------------------------------------------------------------

section Certificate

variable {K : Type*} (p : ℕ) [CommRing K] [NoZeroSMulDivisors ℤ K]
  [hpI : Fact <| Nat.Prime p] (O : Subalgebra ℤ K) (Om : Subalgebra ℤ K)
  (hm : O ≤ Om)

local notation "O*" => Subalgebra.toSubmodule (AlgHom.range (Subalgebra.inclusion hm))

attribute [-instance]  Lean.Omega.IntList.instAdd



/-- A certificate for `p`-maximality which requires verifying `n` identities in `O / pO`
and `n ^ 2` identities in `O` :
- `m` : the nullity of the iterated Frobenius map `Frob ^ t`.
- `n` : The rank of the iterated Frobenius map.
- `t` : The number of iterations of the Frobenius map.
- `TT` : A times table for `O`.
- `B'` : An integral basis for `Om` (not explicitly known).
- `b1` : Lifts of the vectors in `v`.
- `b2` : Lifts of the vectors in `w`.
- `v` : Coordinates for the basis of the kernel of the iterated Frobenius map.
- `w` : Coordinates for elements that are mapped by the iterated Frobenius map to a basis for the
  image.
- `wFrob` : Coordinates of the image of `w` under the iterated Frobenius map.
- `v_ind` : Indices of `v` to check for linear independence.
- `w_ind` : Indices of `wFrob` to check for linear independence.
- `g` : A list of coordinates of elements in `O`.
- `a` : The coefficients of the `b1ᵢ's` in the expansion of `gᵢ * b1ⱼ`
- `c` : The coefficients of the `(p * b2ᵢ)'s` in the expansion of `gᵢ * b1`ⱼ
- `d` : The coefficients of the `b1ᵢ's` in the expansion of `gᵢ * (p * b2ⱼ)`
- `e` : The coefficients of the `(p * b2ᵢ)'s` in the expansion of `gᵢ * (p * b2ⱼ)`
- `ab_ind` : indices to check for linear independence of
  the matrices representing endomorphisms of `Iₚ/pIₚ` -/
structure MaximalOrderCertificateLists {K : Type*} [CommRing K] [NoZeroSMulDivisors ℤ K]
  (p : ℕ) [hpI : Fact <| Nat.Prime p] (O : Subalgebra ℤ K) (Om : Subalgebra ℤ K) (hm : O ≤ Om) where
  /-- Imported declaration. -/
  m : ℕ
  /-- Imported declaration. -/
  n : ℕ
  /-- Imported declaration. -/
  t : ℕ
  hpos : 0 < m + n
  /-- Imported declaration. -/
  TT : TimesTable (Fin (m + n)) ℤ  O
  /-- Imported declaration. -/
  B' : Basis (Fin (m + n)) ℤ  Om
  /-- Imported declaration. -/
  T : Fin (m + n) → Fin (m + n) → List ℤ
  heq : ∀ i j, T i j = List.ofFn (TT.table i j)
  /-- Imported declaration. -/
  TMod : Fin (m + n) → Fin (m + n) → List (ZMod p)
  hTMod : ∀ i j, List.map (algebraMap ℤ (ZMod p)) (T i j) = TMod i j
  hle : m + n ≤ p ^ t
  /-- Imported declaration. -/
  b1 : Fin m → (Fin (m + n) → ℤ)
  /-- Imported declaration. -/
  b2 : Fin n → (Fin (m + n) → ℤ)
  /-- Imported declaration. -/
  v : Fin m → (Fin (m + n) → (ZMod p))
  /-- Imported declaration. -/
  w : Fin n → (Fin (m + n) → (ZMod p))
  /-- Imported declaration. -/
  wFrob : Fin n → (Fin (m + n) → (ZMod p))
  /-- Imported declaration. -/
  v_ind : Fin m → Fin (m + n)
  /-- Imported declaration. -/
  w_ind : Fin n → Fin (m + n)
  hmod1 : ∀ i, (algebraMap ℤ (ZMod p)) ∘ (b1 i) = v i
  hmod2 : ∀ j, (algebraMap ℤ (ZMod p)) ∘ (b2 j) = w j
  hindv : ∀ i, v i (v_ind i) ≠ 0 ∧ (∀ j, j ≠ i → v j (v_ind i) = 0)
  hindw : ∀ i, wFrob i (w_ind i) ≠ 0 ∧ (∀ j, j ≠ i → wFrob j (w_ind i) = 0)
  hvFrobKer : ∀ i, nPow_sq_table TMod (List.ofFn (v i)) (p ^ t) = List.replicate (m + n) 0
  hwFrobComp : ∀ j, nPow_sq_table TMod (List.ofFn (w j)) (p ^ t) = List.ofFn (wFrob j)
  /-- Imported declaration. -/
  g : Fin (m + n) → (Fin (m + n) → ℤ)
  /-- Imported declaration. -/
  a : Fin (m + n) → Fin m → (Fin m → ℤ)
  /-- Imported declaration. -/
  c : Fin (m + n) → Fin m → (Fin n → ℤ)
  /-- Imported declaration. -/
  d : Fin (m + n) → Fin n → (Fin m → ℤ)
  /-- Imported declaration. -/
  e : Fin (m + n) → Fin n → (Fin n → ℤ)
  /-- Imported declaration. -/
  ab_ind : Fin (m + n) → ((Fin m ⊕ Fin n) × (Fin m ⊕ Fin n))
  hindab : ∀ (i : Fin (m + n)), (algebraMap ℤ (ZMod p)) ((fun k => Sum.elim ((fun j => Sum.elim (a
    k j) (c k j))) ((fun j => Sum.elim (d k j) (e k j)))) i (ab_ind i).1 (ab_ind i).2)≠ 0
    ∧ (∀ j, j ≠ i → (algebraMap ℤ (ZMod p)) ((fun k => Sum.elim ((fun j => Sum.elim (a k j) (c k
      j))) ((fun j => Sum.elim (d k j) (e k j)))) j (ab_ind i).1 (ab_ind i).2) = 0)
  hmul1 : ∀ i j, table_mul_list T (List.ofFn (g i)) (List.ofFn (b1 j)) =
    List.sum (List.ofFn (fun l => List.mulPointwise (a i j l) (List.ofFn (b1 l)))) +
      List.sum (List.ofFn (fun l => List.mulPointwise ((c i j l) * p) (List.ofFn (b2 l))))
  hmul2 : ∀ i j,
    table_mul_list T (List.ofFn (g i)) (List.mulPointwise p (List.ofFn (b2 j))) =
    List.sum (List.ofFn (fun l => List.mulPointwise (d i j l) (List.ofFn (b1 l)))) +
      List.sum (List.ofFn (fun l => List.mulPointwise ((e i j l) * p) (List.ofFn (b2 l))))

/-- A shorter certificate for `p`-maximality, which exists if `Iₚ = pO` (i.e· `p` is unramified).
See `MaximalOrderCertificateLists` for details· -/
structure MaximalOrderCertificateOfUnramifiedLists {K : Type*} [CommRing K] [NoZeroSMulDivisors ℤ K]
  (p : ℕ) [hpI : Fact <| Nat.Prime p] (O : Subalgebra ℤ K) (Om : Subalgebra ℤ K) (hm : O ≤ Om) where
  /-- Imported declaration. -/
  n : ℕ
  /-- Imported declaration. -/
  t : ℕ
  hpos : 0 < 0 + n
  /-- Imported declaration. -/
  TT : TimesTable (Fin (0 + n)) ℤ  O
  /-- Imported declaration. -/
  B' : Basis (Fin n) ℤ Om
  /-- Imported declaration. -/
  T : Fin (0 + n) → Fin (0 + n) → List ℤ
  heq : ∀ i j, T i j = List.ofFn (TT.table i j)
  /-- Imported declaration. -/
  TMod : Fin (0 + n) → Fin (0 + n) → List (ZMod p)
  hTMod : ∀ i j, List.map (algebraMap ℤ (ZMod p)) (T i j) = TMod i j
  hle : n ≤ p ^ t
  /-- Imported declaration. -/
  w : Fin n → (Fin (0 + n) → (ZMod p))
  /-- Imported declaration. -/
  wFrob : Fin n → (Fin (0 + n) → (ZMod p))
  /-- Imported declaration. -/
  w_ind : Fin n → Fin (0 + n)
  hindw : ∀ i, wFrob i (w_ind i) ≠ 0 ∧ (∀ j, j ≠ i → wFrob j (w_ind i) = 0)
  hwFrobComp : ∀ j, nPow_sq_table TMod (List.ofFn (w j)) (p ^ t) = List.ofFn (wFrob j)

/-- We get a proof of the `p`-maximality of `O` from a term of type
   `MaximalOrderCertificateOfUnramifiedLists` -/
theorem pMaximal_of_MaximalOrderCertificateOfUnramifiedLists [Module.Free ℤ Om] [Module.Finite ℤ Om]
  (C : MaximalOrderCertificateOfUnramifiedLists p O Om hm) :
  piMaximal (p : ℤ) O* := by
  haveI := Module.Free.of_basis C.TT.basis
  haveI : Nontrivial O := by
    rw [nontrivial_iff]
    use (C.TT.basis (⟨0, C.hpos⟩ : Fin (0 + C.n))), 0
    apply Basis.ne_zero
  refine order_piMaximal_of_order_eq_multiplierRing hm (Nat.prime_iff_prime_int.mp hpI.out) ?_ ?_
  · rw [rank_eq_card_basis C.TT.basis, rank_eq_card_basis C.B']
    simp only [zero_add, Fintype.card_fin]
  · have : (algebraMap ℤ O p) = (p : O) := by norm_num
    rw [this]
    refine mult_ring_eq_ring_of_trivial_ker_map_to_end_lin O p ?_
    refine ker_map_to_end_lin_eq_bot_of_rad_eq_smul O p ?_
    refine rad_eq_smul_top_of_CertificateOfUnramified C.n C.t C.TT.basis C.hle C.w C.wFrob C.w_ind
      C.hindw ?_
    intro j
    exact
      hwFrobComp_lists C.TT.basis C.TT.table C.T C.heq C.TT.basis_mul_basis C.TMod C.hTMod C.w
        C.wFrob _ (C.hwFrobComp j)

/-- We get a proof of the `p`-maximality of `O` from a term of type
   `MaximalOrderCertificateLists` -/
theorem pMaximal_of_MaximalOrderCertificateLists [Module.Free ℤ Om] [Module.Finite ℤ Om]
  (C : MaximalOrderCertificateLists p O Om hm) :
  piMaximal (p : ℤ) O* := by
  refine pMaximal_of_data O p hm C.TT.basis C.B' C.hpos C.hle C.b1 C.b2 C.v C.w C.wFrob C.v_ind
    C.w_ind C.hmod1 C.hmod2 C.hindv C.hindw ?_ ?_ C.g C.a C.c C.d
    C.e C.ab_ind C.hindab ?_ ?_
  · exact fun i =>
      hvFrobKer_lists C.TT.basis C.TT.table C.T C.heq C.TT.basis_mul_basis C.TMod
        C.hTMod C.v _ (C.hvFrobKer i)
  · exact fun j =>
      hwFrobComp_lists C.TT.basis C.TT.table C.T C.heq C.TT.basis_mul_basis C.TMod
        C.hTMod C.w C.wFrob _ (C.hwFrobComp j)
  · exact fun i j =>
      hmul1_lists C.TT.basis C.b1 C.b2 C.g C.TT.table C.T C.heq C.TT.basis_mul_basis
        C.a C.c i j (C.hmul1 i j)
  · exact fun i j =>
      hmul2_lists C.TT.basis C.b1 C.b2 C.g C.TT.table C.T C.heq C.TT.basis_mul_basis
        C.d C.e i j (C.hmul2 i j)


/-- A certificate for `p`-maximality which requires verifying `n` identities in `O / pO`
  and only `n` identities in `O`.
  This is similar to `MaximalOrderCertificateLists` (see for details) but we prove
  the linear independence of endomorphisms of `Iₚ/pIₚ` by providing a 'witness'
  for evaluation· The new components are:
  - `w1` : the coefficients of the `b1ᵢ's` in the expansion of the witness
  - `w2` : the coefficients of the `(p * b2ᵢ)'s` in the expansion of the witness
  - `ac_indw` : the coefficients to check for linear independence -/
structure MaximalOrderCertificateWLists {K : Type*} [CommRing K] [CommRing K]
    [NoZeroSMulDivisors ℤ K]
  (p : ℕ) [hpI : Fact <| Nat.Prime p] (O : Subalgebra ℤ K) (Om : Subalgebra ℤ K) (hm : O ≤ Om) where
  /-- Imported declaration. -/
  m : ℕ
  /-- Imported declaration. -/
  n : ℕ
  /-- Imported declaration. -/
  t : ℕ
  hpos : 0 < m + n
  /-- Imported declaration. -/
  TT : TimesTable (Fin (m + n)) ℤ  O
  /-- Imported declaration. -/
  B' : Basis (Fin (m + n)) ℤ  Om
  /-- Imported declaration. -/
  T : Fin (m + n) → Fin (m + n) → List ℤ
  heq : ∀ i j, T i j = List.ofFn (TT.table i j)
  /-- Imported declaration. -/
  TMod : Fin (m + n) → Fin (m + n) → List (ZMod p)
  hTMod : ∀ i j, List.map (algebraMap ℤ (ZMod p)) (T i j) = TMod i j
  hle : m + n ≤ p ^ t
  /-- Imported declaration. -/
  b1 : Fin m → (Fin (m + n) → ℤ)
  /-- Imported declaration. -/
  b2 : Fin n → (Fin (m + n) → ℤ)
  /-- Imported declaration. -/
  v : Fin m → (Fin (m + n) → (ZMod p))
  /-- Imported declaration. -/
  w : Fin n → (Fin (m + n) → (ZMod p))
  /-- Imported declaration. -/
  wFrob : Fin n → (Fin (m + n) → (ZMod p))
  /-- Imported declaration. -/
  v_ind : Fin m → Fin (m + n)
  /-- Imported declaration. -/
  w_ind : Fin n → Fin (m + n)
  hmod1 : ∀ i, (algebraMap ℤ (ZMod p)) ∘ (b1 i) = v i
  hmod2 : ∀ j, (algebraMap ℤ (ZMod p)) ∘ (b2 j) = w j
  hindv : ∀ i, v i (v_ind i) ≠ 0 ∧ (∀ j, j ≠ i → v j (v_ind i) = 0)
  hindw : ∀ i, wFrob i (w_ind i) ≠ 0 ∧ (∀ j, j ≠ i → wFrob j (w_ind i) = 0)
  hvFrobKer : ∀ i, nPow_sq_table TMod (List.ofFn (v i)) (p ^ t) = List.replicate (m + n) 0
  hwFrobComp : ∀ j, nPow_sq_table TMod (List.ofFn (w j)) (p ^ t) = List.ofFn (wFrob j)
  /-- Imported declaration. -/
  g : Fin (m + n) → (Fin (m + n) → ℤ)
  /-- Imported declaration. -/
  w1 : Fin m → ℤ
  /-- Imported declaration. -/
  w2 : Fin n → ℤ
  /-- Imported declaration. -/
  a : Fin (m + n) → (Fin m → ℤ)
  /-- Imported declaration. -/
  c : Fin (m + n) → (Fin n → ℤ)
  hmulw : ∀ i,  table_mul_list T (List.ofFn (g i)) (List.sum (List.ofFn (fun l => List.mulPointwise
    (w1 l) (List.ofFn (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise ((w2 l) * p) (List.ofFn (b2 l))))) =
    List.sum (List.ofFn (fun l => List.mulPointwise ((a i) l) (List.ofFn (b1 l)))) +
    List.sum (List.ofFn (fun l => List.mulPointwise (((c i) l) * p) (List.ofFn (b2 l))))
  /-- Imported declaration. -/
  ac_indw : Fin (m + n) → (Fin m ⊕ Fin n)
  hacindw : ∀ i, ((algebraMap ℤ (ZMod p)) ((Sum.elim (fun j => a i j) (fun j => c i j)) (ac_indw
    i)) ≠ 0 ∧
        ∀ k, k ≠ i → (algebraMap ℤ (ZMod p)) ((Sum.elim (fun j => a k j) (fun j => c k j)) (ac_indw
          i)) = 0)


/-- We get a proof of the `p`-maximality of `O` from a term of type
   `MaximalOrderCertificateWLists` -/
theorem pMaximal_of_MaximalOrderCertificateWLists [Module.Free ℤ Om] [Module.Finite ℤ Om]
  (C : MaximalOrderCertificateWLists p O Om hm) :
  piMaximal (p : ℤ) O* := by
  refine pMaximal_of_data_witness O p hm C.TT.basis C.B' C.hpos C.hle C.b1 C.b2 C.v C.w C.wFrob
    C.v_ind C.w_ind
    C.hmod1 C.hmod2 C.hindv C.hindw ?_ ?_ C.g C.w1 C.w2 C.a C.c ?_ C.ac_indw C.hacindw
  · exact fun i =>
      hvFrobKer_lists C.TT.basis C.TT.table C.T C.heq C.TT.basis_mul_basis C.TMod
        C.hTMod C.v _ (C.hvFrobKer i)
  · exact fun j =>
      hwFrobComp_lists C.TT.basis C.TT.table C.T C.heq C.TT.basis_mul_basis C.TMod
        C.hTMod C.w C.wFrob _ (C.hwFrobComp j)
  · intro i
    refine hmul_lists_witness C.TT.basis C.b1 C.b2 C.g C.TT.table C.T C.heq
      C.TT.basis_mul_basis C.w1 C.w2 C.a C.c i (C.hmulw i)



end Certificate
