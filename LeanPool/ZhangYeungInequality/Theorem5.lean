/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.CopyLemma
import LeanPool.ZhangYeungInequality.Delta
import LeanPool.ZhangYeungInequality.EntropyRegion
import LeanPool.ZhangYeungInequality.Prelude
import LeanPool.ZhangYeungInequality.Theorem3

/-!
# Theorem 5, the `n + 2`-variable Zhang-Yeung generalization

Theorem 5 of [@zhangyeung1998, §III, eqs. 27-28] extends the four-variable Zhang-Yeung
inequality
to a family `X : ∀ i : Fin n, Ω → S i` of `n` side variables. The asymmetric point form
fixes one
distinguished index `i : Fin n`; the averaged symmetric form follows by summing over `i`
and
dividing by `n`.

## Main statements

- `ZhangYeung.theorem5`: paper eq. (27), the asymmetric `Fin n`-indexed form.
- `ZhangYeung.theorem5_averaged`: paper eq. (28), the averaged symmetric form.

## Implementation notes

The proof follows the same copy-lemma chase as `ZhangYeung.theorem3`, but applies
`condIndep_copies` once at the tuple codomain `∀ j : Fin n, S j`. The tuple-level
conditional
independence is projected down to each pair `(X' i, XstarCoord k)`, those pairwise delta
bounds are
summed over `k`, and the resulting `n`-ary mutual-information sum is controlled by a
local
chain-rule lemma `mutualInfo_add_n_way_inequality`.

Internally the chase runs in `(Z, U)` order to match `delta`; the public statement is
rewritten to
the paper's `I[U : Z]` order at the end via `mutualInfo_comm` and `condMutualInfo_comm`.

## References

* [@zhangyeung1998, §III, Theorem 5, eqs. 27-28] -- see
  `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of the
  theorem
  statement, verified 2026-04-16.

## Tags

Shannon entropy, mutual information, non-Shannon information inequality, Zhang-Yeung,
conditional
independence
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR

universe u

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Invariance of mutual information under an injective measurable transformation of the
right-hand
variable.
-/
private lemma mutualInfo_comp_right_of_injective
    {α β γ : Type*}
    [Finite α] [Finite β] [Finite γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β}
    (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : β → γ} (hf : Function.Injective f) :
    I[X : f ∘ Y; μ] = I[X : Y; μ] := by
  have h_joint : H[⟨X, f ∘ Y⟩; μ] = H[⟨X, Y⟩; μ] := by
    let g : α × β → α × γ := fun p => (p.1, f p.2)
    have hg : Function.Injective g := by
      intro p q hpq
      rcases p with ⟨xp, yp⟩
      rcases q with ⟨xq, yq⟩
      simp only [g, Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (hf hpq.2)
    change H[g ∘ ⟨X, Y⟩; μ] = H[⟨X, Y⟩; μ]
    exact entropy_comp_of_injective μ (hX.prodMk hY) g hg
  rw [mutualInfo_def, mutualInfo_def, entropy_comp_of_injective μ hY f hf, h_joint]

/--
Swapping the two coordinates of the right-hand pair does not change the mutual
information.
-/
private lemma mutualInfo_pair_swap_right
    {α β γ : Type*}
    [Finite α] [Finite β] [Finite γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : ⟨Y, Z⟩; μ] = I[X : ⟨Z, Y⟩; μ] := by
  change I[X : fun a => (Y a, Z a); μ] =
    I[X : Prod.swap ∘ (fun a => (Y a, Z a)); μ]
  exact (mutualInfo_comp_right_of_injective hX (hY.prodMk hZ) μ
    (f := Prod.swap) Prod.swap_injective).symm

/-- Measurability of the `(tuple, (z, u)) ↦ (z, u)` projection. -/
private lemma measurable_pairZU
    {n : ℕ} {S : Fin n → Type*} {S_Z S_U : Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace S_Z] [MeasurableSpace S_U] :
    Measurable (fun p : (∀ i : Fin n, S i) × (S_Z × S_U) => p.2) := by
  fun_prop

/-- Measurability of the `(tuple, (z, u)) ↦ (x_i, (z, u))` projection. -/
private lemma measurable_pairXZU
    {n : ℕ} {S : Fin n → Type*} {S_Z S_U : Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace S_Z] [MeasurableSpace S_U]
    (i : Fin n) :
    Measurable (fun p : (∀ j : Fin n, S j) × (S_Z × S_U) => (p.1 i, p.2)) := by
  fun_prop

/-- Measurability of the `(tuple, (z, u)) ↦ (z, u, x_i)` projection. -/
private lemma measurable_projZUX
    {n : ℕ} {S : Fin n → Type*} {S_Z S_U : Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace S_Z] [MeasurableSpace S_U]
    (i : Fin n) :
    Measurable (fun p : (∀ j : Fin n, S j) × (S_Z × S_U) => (p.2.1, p.2.2, p.1 i)) := by
  fun_prop

/--
Project tuple-level conditional independence down to a single pair of coordinates.
-/
private lemma tuple_condIndepFun_pairProj
    {n : ℕ} {S : Fin n → Type*} {T : Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace T]
    {μ : Measure Ω} {Xprime Xstar : Ω → ∀ i : Fin n, S i} {V : Ω → T}
    (i k : Fin n) (h : CondIndepFun Xprime Xstar V μ) :
    CondIndepFun (fun ω => Xprime ω i) (fun ω => Xstar ω k) V μ := by
  exact ZhangYeung.condIndepFun_comp (φ := fun x => x i) (ψ := fun x => x k)
    (measurable_pi_apply i) (measurable_pi_apply k) h

/--
Chain-rule domination of the sum of the coordinate-wise mutual informations by the
mutual
information with the full tuple plus total correlation.
-/
private lemma mutualInfo_add_n_way_inequality
    {n : ℕ} {α : Type*} {β : Fin n → Type*}
    [Finite α] [∀ k, Finite (β k)]
    [MeasurableSpace α] [∀ k, MeasurableSpace (β k)]
    [MeasurableSingletonClass α] [∀ k, MeasurableSingletonClass (β k)]
    {A : Ω → α} {B : ∀ k : Fin n, Ω → β k}
    (hA : Measurable A) (hB : ∀ k, Measurable (B k))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∑ k, I[A : B k; μ]
      ≤ I[A : (fun ω => fun k : Fin n => B k ω); μ]
        + ∑ k, H[B k; μ]
        - H[(fun ω => fun k : Fin n => B k ω); μ] := by
  induction n with
  | zero =>
      let c : ∀ k : Fin 0, β k := fun k => nomatch k
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      have htuple : (fun ω => fun k : Fin 0 => B k ω) = fun _ : Ω => c := by
        funext ω k
        exact Fin.elim0 k
      rw [htuple]
      have hconstMI : I[A : (fun _ : Ω => c); μ] = 0 := mutualInfo_const hA c
      have hconstH : H[(fun _ : Ω => c); μ] = 0 := by
        simp
      linarith
  | succ n ih =>
      let Binit : ∀ k : Fin n, Ω → β k.castSucc := fun k => B k.castSucc
      let Blast : Ω → β (Fin.last n) := B (Fin.last n)
      let BinitTuple : Ω → (∀ k : Fin n, β k.castSucc) := fun ω k => B k.castSucc ω
      let Btuple : Ω → (∀ k : Fin (n + 1), β k) := fun ω k => B k ω
      have hBinit : ∀ k : Fin n, Measurable (Binit k) := fun k => hB k.castSucc
      have hBlast : Measurable Blast := hB (Fin.last n)
      have hBinitTuple : Measurable BinitTuple := measurable_pi_lambda _ hBinit
      have hBtuple : Measurable Btuple := measurable_pi_lambda _ hB
      have h_tail := ih (β := fun k => β k.castSucc) (B := Binit) hBinit
      let pack : (∀ k : Fin (n + 1), β k) → (∀ k : Fin n,
        β k.castSucc) × β (Fin.last n) :=
        fun x => (fun k => x k.castSucc, x (Fin.last n))
      have hpack : Function.Injective pack := by
        intro x y hxy
        have hxyInit : (fun k : Fin n => x (Fin.castSucc k)) =
          fun k : Fin n => y (Fin.castSucc k) :=
          (Prod.mk.inj hxy).1
        have hxyLast : x (Fin.last n) = y (Fin.last n) := (Prod.mk.inj hxy).2
        ext i
        rcases Fin.eq_castSucc_or_eq_last i with hi | rfl
        · obtain ⟨j, rfl⟩ := hi
          exact congrFun hxyInit j
        · exact hxyLast
      have h_tuple_ent : H[⟨BinitTuple, Blast⟩; μ] = H[Btuple; μ] := by
        change H[pack ∘ Btuple; μ] = H[Btuple; μ]
        exact entropy_comp_of_injective μ hBtuple pack hpack
      have h_tuple_mi : I[A : ⟨BinitTuple, Blast⟩; μ] = I[A : Btuple; μ] := by
        have h_joint : H[⟨A, ⟨BinitTuple, Blast⟩⟩; μ] = H[⟨A, Btuple⟩; μ] := by
          let packA : α × (∀ k : Fin (n + 1), β k) → α × ((∀ k : Fin n,
            β k.castSucc) × β (Fin.last n)) :=
            fun p => (p.1, pack p.2)
          have hpackA : Function.Injective packA := by
            intro p q hpq
            rcases p with ⟨a₁, x⟩
            rcases q with ⟨a₂, y⟩
            have hpq' : (a₁, pack x) = (a₂, pack y) := by simpa [packA] using hpq
            exact Prod.ext (Prod.mk.inj hpq').1 (hpack (Prod.mk.inj hpq').2)
          change H[packA ∘ ⟨A, Btuple⟩; μ] = H[⟨A, Btuple⟩; μ]
          exact entropy_comp_of_injective μ (hA.prodMk hBtuple) packA hpackA
        rw [mutualInfo_def, mutualInfo_def, h_tuple_ent, h_joint]
      have h_three :
          I[A : BinitTuple; μ] + I[A : Blast; μ]
            = I[A : ⟨BinitTuple, Blast⟩; μ] + I[BinitTuple : Blast; μ]
              - I[BinitTuple : Blast | A; μ] := by
        simpa using (mutualInfo_add_three_way_identity (X := A) (Y := BinitTuple) (Z :=
          Blast) hA hBinitTuple hBlast μ)
      have h_nonneg : 0 ≤ I[BinitTuple : Blast | A; μ] :=
        condMutualInfo_nonneg hBinitTuple hBlast
      have h_pairInfo : I[BinitTuple : Blast; μ] =
        H[BinitTuple; μ] + H[Blast; μ] - H[Btuple; μ] := by
        rw [mutualInfo_def, h_tuple_ent]
      have h_split :
          I[A : BinitTuple; μ] + I[A : Blast; μ]
            ≤ I[A : Btuple; μ] + H[BinitTuple; μ] + H[Blast; μ] - H[Btuple; μ] := by
        rw [h_tuple_mi, h_pairInfo] at h_three
        linarith
      have h_sum_tail :
          ∑ k : Fin (n + 1), I[A : B k; μ]
            = (∑ k : Fin n, I[A : B k.castSucc; μ]) + I[A : Blast; μ] := by
        simpa [Blast] using (Fin.sum_univ_castSucc (f := fun k : Fin (n + 1) => I[A : B k; μ]))
      have h_sum_entropy :
          ∑ k : Fin (n + 1), H[B k; μ]
            = (∑ k : Fin n, H[B k.castSucc; μ]) + H[Blast; μ] := by
        simpa [Blast] using (Fin.sum_univ_castSucc (f := fun k : Fin (n + 1) => H[B k; μ]))
      rw [h_sum_tail, h_sum_entropy]
      linarith

end Helpers

section MainTheorems

variable {Ω : Type*} [MeasurableSpace Ω]
  {n : ℕ}
  {S_U S_Z : Type u} {S : Fin n → Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [∀ i, MeasurableSpace (S i)]
  [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [∀ i, MeasurableSingletonClass (S i)]

/--
**Theorem 5 of [@zhangyeung1998, §III, eq. 27]** -- the `n + 2`-variable Zhang-Yeung
inequality,
indexed by a distinguished coordinate `i : Fin n`.
-/
theorem _root_.ZhangYeung.theorem5
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Fin n) :
    2 ≤ n →
    n * I[U : Z; μ] - ∑ j, I[U : Z | X j; μ] - n * I[U : Z | X i; μ]
      ≤ I[X i : ⟨U, Z⟩; μ]
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by
  intro _hn
  let Xtuple : Ω → (∀ j : Fin n, S j) := fun ω j => X j ω
  let ZU : Ω → S_Z × S_U := fun ω => (Z ω, U ω)
  have hXtuple : Measurable Xtuple := measurable_pi_lambda _ hX
  have hZU : Measurable ZU := hZ.prodMk hU
  obtain ⟨Ω', mΩ', Xprime, Xstar, V, ν, hν, hXprime, hXstar, hV, hCond, hFirst, hSecond⟩ :=
    condIndep_copies Xtuple ZU hXtuple hZU μ
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure ν := hν
  let Z' : Ω' → S_Z := fun ω => (V ω).1
  let U' : Ω' → S_U := fun ω => (V ω).2
  let X' : ∀ j : Fin n, Ω' → S j := fun j ω => Xprime ω j
  let XstarCoord : ∀ j : Fin n, Ω' → S j := fun j ω => Xstar ω j
  have hZ' : Measurable Z' := measurable_fst.comp hV
  have hU' : Measurable U' := measurable_snd.comp hV
  have hX' : ∀ j, Measurable (X' j) := fun j => (measurable_pi_apply j).comp hXprime
  have hXstarCoord : ∀ j,
    Measurable (XstarCoord j) := fun j => (measurable_pi_apply j).comp hXstar
  have hPair : ∀ k : Fin n,
    delta Z' U' (X' i) (XstarCoord k) ν ≤ I[X' i : XstarCoord k; ν] := by
    intro k
    have hVanish : I[X' i : XstarCoord k | (fun ω' => (Z' ω', U' ω')); ν] = 0 := by
      simpa [Z', U'] using (condMutualInfo_eq_zero (hX' i) (hXstarCoord k)).mpr
        (tuple_condIndepFun_pairProj i k hCond)
    rw [delta_of_condMI_vanishes_eq (hX' i) hZ' hU' (hXstarCoord k) ν hVanish]
    have h1 : 0 ≤ I[X' i : XstarCoord k | Z'; ν] := condMutualInfo_nonneg (hX' i) (hXstarCoord k)
    have h2 : 0 ≤ I[X' i : XstarCoord k | U'; ν] := condMutualInfo_nonneg (hX' i) (hXstarCoord k)
    have h3 : 0 ≤ I[Z' : U' | ⟨X' i, XstarCoord k⟩; ν] := condMutualInfo_nonneg hZ' hU'
    linarith
  have hTransport : ∀ k : Fin n,
    delta Z U (X i) (X k) μ = delta Z' U' (X' i) (XstarCoord k) ν := by
    intro k
    have hPairZU : IdentDistrib (fun ω => (Z ω, U ω)) (fun ω' => (Z' ω', U' ω')) μ ν :=
      hFirst.symm.comp measurable_pairZU
    have hTripleFirst :
        IdentDistrib (fun ω => (Z ω, U ω, X i ω)) (fun ω' => (Z' ω', U' ω',
          X' i ω')) μ ν :=
      hFirst.symm.comp (measurable_projZUX i)
    have hTripleSecond :
        IdentDistrib (fun ω => (Z ω, U ω, X k ω)) (fun ω' => (Z' ω', U' ω',
          XstarCoord k ω')) μ ν :=
      hSecond.symm.comp (measurable_projZUX k)
    rw [delta_def, delta_def, hPairZU.mutualInfo_eq,
      IdentDistrib.condMutualInfo_eq hZ hU (hX i) hZ' hU' (hX' i) hTripleFirst,
      IdentDistrib.condMutualInfo_eq hZ hU (hX k) hZ' hU' (hXstarCoord k) hTripleSecond]
  have hDeltaSum :
      ∑ k : Fin n, delta Z U (X i) (X k) μ
        = n * I[Z : U; μ] - n * I[Z : U | X i; μ] - ∑ k : Fin n, I[Z : U | X k; μ] := by
    simp_rw [delta_def]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const]
    simp [nsmul_eq_mul, Fintype.card_fin]
  have hSum :
      n * I[Z : U; μ] - n * I[Z : U | X i; μ] - ∑ k : Fin n, I[Z : U | X k; μ]
        ≤ ∑ k : Fin n, I[X' i : XstarCoord k; ν] := by
    calc
      n * I[Z : U; μ] - n * I[Z : U | X i; μ] - ∑ k : Fin n, I[Z : U | X k; μ]
        = ∑ k : Fin n, delta Z U (X i) (X k) μ := hDeltaSum.symm
      _ = ∑ k : Fin n, delta Z' U' (X' i) (XstarCoord k) ν := by
        refine Finset.sum_congr rfl ?_
        intro k _
        exact hTransport k
      _ ≤ ∑ k : Fin n, I[X' i : XstarCoord k; ν] := Finset.sum_le_sum fun k _ => hPair k
  have hChain := mutualInfo_add_n_way_inequality (A := X' i) (B :=
    XstarCoord) (hX' i) hXstarCoord ν
  have hCondProj :
      CondIndepFun (X' i) (fun ω' => fun k : Fin n => XstarCoord k ω') (fun ω' => (Z' ω',
        U' ω')) ν := by
    change CondIndepFun ((fun x => x i) ∘ Xprime) Xstar V ν
    exact (ZhangYeung.condIndepFun_comp (φ := fun x => x i) (ψ := id)
      (measurable_pi_apply i) measurable_id hCond)
  have hDP :
      I[X' i : (fun ω' => fun k : Fin n => XstarCoord k ω'); ν]
        ≤ I[X' i : (fun ω' => (Z' ω', U' ω')); ν] :=
    mutualInfo_le_of_condIndepFun (hX' i) hXstar (hZ'.prodMk hU') ν hCondProj
  have hMargXZU :
      I[X' i : (fun ω' => (Z' ω', U' ω')); ν]
        = I[X i : (fun ω => (Z ω, U ω)); μ] := by
    have hPairXZU :
        IdentDistrib (fun ω => (X i ω, (Z ω, U ω)))
          (fun ω' => (X' i ω', (Z' ω', U' ω'))) μ ν :=
      hFirst.symm.comp (measurable_pairXZU i)
    exact hPairXZU.mutualInfo_eq.symm
  have hTupleSecond :
      IdentDistrib (fun ω' => fun k : Fin n => XstarCoord k ω') (fun ω => fun k :
        Fin n => X k ω) ν μ := by
    exact hSecond.comp measurable_fst
  have hMargJoint :
      H[(fun ω' => fun k : Fin n => XstarCoord k ω'); ν] =
        H[(fun ω : Ω => fun k : Fin n => X k ω); μ] :=
    hTupleSecond.entropy_congr
  have hMargSingle : ∀ k : Fin n, H[XstarCoord k; ν] = H[X k; μ] := by
    intro k
    have hCoord : IdentDistrib (XstarCoord k) (X k) ν μ := by
      exact hTupleSecond.comp (measurable_pi_apply k)
    exact hCoord.entropy_congr
  have hMargSingles : ∑ k : Fin n, H[XstarCoord k; ν] = ∑ k : Fin n, H[X k; μ] := by
    refine Finset.sum_congr rfl ?_
    intro k _
    exact hMargSingle k
  have hInternal :
      n * I[Z : U; μ] - ∑ j, I[Z : U | X j; μ] - n * I[Z : U | X i; μ]
        ≤ I[X i : (fun ω => (Z ω, U ω)); μ]
          + ∑ j, H[X j; μ]
          - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by
    linarith [hSum, hChain, hDP, hMargXZU, hMargJoint, hMargSingles]
  have hCondComm : (fun j : Fin n => I[Z : U | X j; μ]) = fun j : Fin n => I[U : Z | X j; μ] := by
    funext j
    exact condMutualInfo_comm hZ hU (X j) μ
  have hSwapRhs :
      I[X i : (fun ω => (Z ω, U ω)); μ] = I[X i : ⟨U, Z⟩; μ] := by
    simpa using mutualInfo_pair_swap_right (hX i) hZ hU μ
  have hPaperOrder :
      n * I[U : Z; μ] - ∑ j, I[U : Z | X j; μ] - n * I[U : Z | X i; μ]
        ≤ I[X i : (fun ω => (Z ω, U ω)); μ]
          + ∑ j, H[X j; μ]
          - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by
    have hCondI : I[Z : U | X i; μ] = I[U : Z | X i; μ] := condMutualInfo_comm hZ hU (X i) μ
    simpa [hCondComm, hCondI, mutualInfo_comm hZ hU μ] using hInternal
  simpa [hSwapRhs] using hPaperOrder

/--
**Theorem 5 of [@zhangyeung1998, §III, eq. 28]** -- the averaged symmetric form of the
`n +
2`-variable Zhang-Yeung inequality.
-/
theorem _root_.ZhangYeung.theorem5_averaged
    (hn : 2 ≤ n)
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    n * I[U : Z; μ] - 2 * (∑ j, I[U : Z | X j; μ])
      ≤ (1 / n : ℝ) * (∑ i, I[X i : ⟨U, Z⟩; μ])
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by
  let lhs : ℝ := n * I[U : Z; μ] - 2 * (∑ j : Fin n, I[U : Z | X j; μ])
  let tail : ℝ := ∑ j : Fin n, H[X j; μ] - H[(fun ω : Ω => fun j : Fin n => X j ω); μ]
  let rhs : Fin n → ℝ := fun i => I[X i : ⟨U, Z⟩; μ]
  have hsum : ∑ i : Fin n, (n * I[U : Z; μ] - ∑ j : Fin n,
    I[U : Z | X j; μ] - n * I[U : Z | X i; μ])
      ≤ ∑ i : Fin n, (rhs i + tail) := by
    refine Finset.sum_le_sum ?_
    intro i _
    simpa [rhs, tail, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (theorem5 hU hZ hX μ i hn)
  have hleft :
      ∑ i : Fin n, (n * I[U : Z; μ] - ∑ j : Fin n, I[U : Z | X j; μ] - n * I[U : Z | X i; μ])
        = n * lhs := by
    have hsumCond : ∑ x : Fin n, n * I[U : Z | X x; μ] = n * ∑ x : Fin n,
      I[U : Z | X x; μ] := by
      rw [Finset.mul_sum]
    calc
      ∑ i : Fin n, (n * I[U : Z; μ] - ∑ j : Fin n, I[U : Z | X j; μ] - n * I[U : Z | X i; μ])
          = n ^ 2 * I[U : Z; μ] - ∑ x : Fin n, n * I[U : Z | X x; μ] - n * ∑ j : Fin n,
            I[U : Z | X j; μ] := by
            simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            ring
      _ = n ^ 2 * I[U : Z; μ] - n * ∑ x : Fin n, I[U : Z | X x; μ] - n * ∑ j : Fin n,
        I[U : Z | X j; μ] := by
            rw [hsumCond]
      _ = n * lhs := by
            change n ^ 2 * I[U : Z; μ] - n * ∑ x : Fin n,
              I[U : Z | X x; μ] - n * ∑ j : Fin n, I[U : Z | X j; μ]
              = n * (n * I[U : Z; μ] - 2 * ∑ j : Fin n, I[U : Z | X j; μ])
            ring
  have hright : ∑ i : Fin n, (rhs i + tail) = (∑ i : Fin n, rhs i) + n * tail := by
    simp only [rhs, tail, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin,
      nsmul_eq_mul]
  have hscaled : n * lhs ≤ (∑ i : Fin n, rhs i) + n * tail := by
    simpa [hleft, hright] using hsum
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos_nat)
  have hdiv : lhs ≤ ((∑ i : Fin n, rhs i) + n * tail) / n := by
    exact (le_div_iff₀ hn_pos).2 (by simpa [mul_comm] using hscaled)
  have hsplit : ((∑ i : Fin n, rhs i) + n * tail) / n = (1 / n : ℝ) * (∑ i : Fin n,
    rhs i) + tail := by
    field_simp [hn_ne]
  have hfinal := hdiv
  rw [hsplit] at hfinal
  simpa [lhs, rhs, tail, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hfinal

end MainTheorems

end ZhangYeung
