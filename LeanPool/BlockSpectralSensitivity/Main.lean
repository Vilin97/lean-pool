/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Spectral.CertUnion
public import LeanPool.BlockSpectralSensitivity.Paley.Tournament
public import LeanPool.BlockSpectralSensitivity.Construction.Conflict
public import LeanPool.BlockSpectralSensitivity.Construction.BlockSens
public import LeanPool.BlockSpectralSensitivity.LLL.GateExists
public import LeanPool.BlockSpectralSensitivity.Spectral.Multiplicative

/-!
# The counterexample

Fix the Paley tournament on `k = 14011` vertices and a gate labelling
`γ : Idx → Idx → Fin 144` satisfying the local certificate-list conditions (L1) and (L2)
of Section 6.  The function `ind Arc γ` is the indicator of the union of the certificate
subcubes of Section 3.

The two headline estimates are

* `bs_ge` — `bs(f) ≥ 14011` (Section 5), and
* `lam_sq_le` — `lambda(f)^2 ≤ 7149 + 2 √150108` (Sections 11–12),

with `U := 7149 + 2 √150108 < 7924 < 14011`.  Setting

  `α := 2 log 14011 / log U > 2`,

we obtain `lambda(f)^α ≤ 14011 ≤ bs(f)`, and, for the `m`-fold self-composition `F_m`
of Section 14 (using `BSLambda.lam_iterFun_eq`, the multiplicativity of `lambda` under
composition, which is proved in `BSLambda/Spectral/Multiplicative.lean`),

* `lam_iter_rpow_le_bs` — `lambda(F_m)^α ≤ bs(F_m)`, and
* `bs_div_lam_sq_ge` — `bs(F_m) / lambda(F_m)^2 ≥ (14011/U)^m` with `14011/U > 1.768`,

which tends to infinity and so refutes `bs(f) = O(lambda(f)^2)`.

Everything in this file is stated for an arbitrary gate labelling satisfying (L1) and
(L2); `BSLambda/LLL/GateExists.lean` is where such a labelling is produced.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace BSLambda

namespace Final

open Construction

/-- The vertex set of the Paley tournament: `Z/14011`. -/
abbrev Idx : Type := ZMod 14011

/-- The arc relation of the Paley tournament on `14011` vertices (Section 2). -/
def Arc : Idx → Idx → Bool := paleyArc 14011

/-- The Paley orientation is a doubly regular tournament with `d = 7005` and `t = 3502`
(Section 2). -/
theorem isDR_arc : IsDRTournamentWith Arc 7005 3502 := paley_isDR

/-- The Paley orientation is in particular a tournament (Section 2). -/
theorem isTournament_arc : IsTournament Arc := isDR_arc.toIsTournament

/-- The number of coordinates in each block, `r = 144` (Section 3). -/
abbrev r : ℕ := 144

/-- The certificate codimension `c = r + d = 144 + 7005 = 7149` (Section 3.2). -/
abbrev certCodim : ℕ := 7149

/-- The spectral bound `U = 7149 + 2 √150108` of Section 12. -/
noncomputable def U : ℝ := 7149 + 2 * Real.sqrt 150108

/-- The separation exponent `α = 2 log 14011 / log U` of Section 14. -/
noncomputable def alpha : ℝ := 2 * Real.log 14011 / Real.log U

/-- The tournament has `14011` vertices (Section 2). -/
theorem card_idx : Fintype.card Idx = 14011 := by simp [Idx]

/-- Every certificate has codimension `c = 7149` (Section 3.2). -/
theorem codim_cert_eq (γ : Idx → Idx → Fin r) (i : Idx) :
    (cert Arc γ i).codim = certCodim := by
  rw [codim_cert isTournament_arc, isDR_arc.card_outNbrs]

/-- Distinct certificates have exactly one conflicting fixed literal (Section 4). -/
theorem uniqueConflict_cert (γ : Idx → Idx → Fin r) (i j : Idx) (hij : i ≠ j) :
    ∃! v, (cert Arc γ i).Conflict (cert Arc γ j) v := by
  obtain ⟨v, hv⟩ := exists_conflict_of_ne isTournament_arc hij
  refine ⟨v, hv, fun w hw ↦ ?_⟩
  rcases isTournament_arc.arc_or_arc hij with h | h
  · rw [eq_gateCoord_of_conflict isTournament_arc hij.symm h hw,
      eq_gateCoord_of_conflict isTournament_arc hij.symm h hv]
  · rw [eq_gateCoord_of_conflict isTournament_arc hij h hw.symm,
      eq_gateCoord_of_conflict isTournament_arc hij h hv.symm]

/-- Property (L1) of Section 6: every positive point has at most three other
certificates at distance one. -/
@[expose] def ListOne (γ : Idx → Idx → Fin r) : Prop :=
  ∀ i x, (cert Arc γ i).Sat x →
    (Finset.univ.filter fun j => j ≠ i ∧ (cert Arc γ j).dist x = 1).card ≤ 3

/-- Property (L2) of Section 6: every positive point has at most seven other
certificates at distance at most two. -/
@[expose] def ListTwo (γ : Idx → Idx → Fin r) : Prop :=
  ∀ i x, (cert Arc γ i).Sat x →
    (Finset.univ.filter fun j => j ≠ i ∧ (cert Arc γ j).dist x ≤ 2).card ≤ 7

/-- The certificate family attached to a gate labelling satisfying (L1) and (L2)
(Sections 3, 4 and 6). -/
@[expose, simps]
def family (γ : Idx → Idx → Fin r) (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    CertFamily (Coord Idx r) Idx where
  P := cert Arc γ
  c := certCodim
  A := 3
  B := 7
  codim_eq := codim_cert_eq γ
  uniqueConflict := uniqueConflict_cert γ
  listOne := h₁
  listTwo := h₂

variable {γ : Idx → Idx → Fin r}

/-- The indicator of the certificate family is definitionally the indicator
`Construction.ind` of the union of the certificate subcubes (Section 3.3). -/
theorem family_ind (h₁ : ListOne γ) (h₂ : ListTwo γ) : (family γ h₁ h₂).ind = ind Arc γ := rfl

/-! ### Block sensitivity -/

/-- **Block sensitivity** (Section 5): `bs(f) ≥ 14011`. -/
theorem bs_ge : 14011 ≤ bs (ind Arc γ) := by
  simpa using card_le_bs (Arc := Arc) (γ := γ)

/-- `bs_ge` cast into `ℝ`, the form in which the numeric comparisons below use it. -/
theorem bs_ge_real : (14011 : ℝ) ≤ (bs (ind Arc γ) : ℝ) := by exact_mod_cast bs_ge

/-! ### The spectral bound -/

/-- Substituting `c = 7149`, `A = 3`, `B = 7` into the Spectral Lemma's right-hand side
`c + 2 √(A (c-1) B)` gives exactly `U = 7149 + 2 √150108` (Section 12). -/
theorem family_bound_eq_U (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    ((family γ h₁ h₂).c : ℝ) + 2 * (family γ h₁ h₂).offBound = U := by
  rw [CertFamily.offBound, U, family_c, family_A, family_B]
  norm_num

/-- **The spectral bound** (Sections 11–12): `lambda(f)^2 ≤ 7149 + 2 √150108`. -/
theorem lam_sq_le (h₁ : ListOne γ) (h₂ : ListTwo γ) : lam (ind Arc γ) ^ 2 ≤ U := by
  rw [← family_ind h₁ h₂, ← family_bound_eq_U h₁ h₂]
  exact (family γ h₁ h₂).lam_sq_le

/-- `√150108 < 387.5`, the only numerical estimate needed in Section 12. -/
theorem sqrt_150108_lt : Real.sqrt 150108 < 387.5 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 387.5)]
  norm_num

/-- `U < 7924` (Section 12). -/
theorem U_lt : U < 7924 := by
  rw [U]
  linarith [sqrt_150108_lt]

/-- `7149 ≤ U`; in particular `1 < U` and `0 < log U` (Section 12). -/
theorem U_ge : (7149 : ℝ) ≤ U := by simp [U]

/-- `U` is positive, since `7149 ≤ U`. -/
theorem U_pos : (0 : ℝ) < U := by linarith [U_ge]

/-- `log U` is positive. -/
theorem log_U_pos : 0 < Real.log U := Real.log_pos (by linarith [U_ge])

/-! ### The exponent -/

/-- **The exponent exceeds two** (Section 14): `α > 2`, because `U < 14011`. -/
theorem two_lt_alpha : 2 < alpha := by
  have hlog : Real.log U < Real.log 14011 := Real.log_lt_log U_pos (U_lt.trans (by norm_num))
  rw [alpha, lt_div_iff₀ log_U_pos]
  linarith

/-- `U ^ (α/2) = 14011` (Section 14). -/
theorem U_rpow_alpha : U ^ (alpha / 2) = 14011 := by
  have h1 : alpha / 2 = Real.log 14011 / Real.log U := by
    rw [alpha]
    ring
  have h2 : Real.log U * (Real.log 14011 / Real.log U) = Real.log 14011 := by
    field_simp [log_U_pos.ne']
  rw [h1, Real.rpow_def_of_pos U_pos, h2]
  exact Real.exp_log (by norm_num)

/-- Split an `rpow` exponent through a square: `x ^ t = (x ^ 2) ^ s` whenever `t = 2 * s`.
This is the step that turns the bound on `lambda ^ 2` into a bound on `lambda ^ t`. -/
private theorem rpow_eq_sq_rpow {x t s : ℝ} (hx : 0 ≤ x) (hts : t = 2 * s) :
    x ^ t = (x ^ (2 : ℕ)) ^ s := by
  subst hts
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

/-- **The separation for the seed** (Sections 12 and 14):
`lambda(f)^α ≤ 14011 ≤ bs(f)`. -/
theorem lam_rpow_le (h₁ : ListOne γ) (h₂ : ListTwo γ) : lam (ind Arc γ) ^ alpha ≤ 14011 := by
  calc lam (ind Arc γ) ^ alpha
      = (lam (ind Arc γ) ^ (2 : ℕ)) ^ (alpha / 2) := rpow_eq_sq_rpow (lam_nonneg _) (by ring)
    _ ≤ U ^ (alpha / 2) :=
        Real.rpow_le_rpow (sq_nonneg _) (lam_sq_le h₁ h₂) (by linarith [two_lt_alpha])
    _ = 14011 := U_rpow_alpha

/-! ### Self-composition -/

/-- **Block sensitivity of the iterates** (Section 14): `bs(F_m) ≥ 14011 ^ m`. -/
theorem bs_iter_ge (m : ℕ) : 14011 ^ m ≤ bs (iterFun (ind Arc γ) m) := by
  have hr : NeZero r := NeZero.of_pos (by norm_num : (0 : ℕ) < r)
  have h := card_pow_le_bs_iterFun (ind_zeroInput Arc γ) (ind_flipSet_block (Arc := Arc) (γ := γ))
    (block_nonempty (ι := Idx) (r := r)) (fun _ _ hij ↦ block_disjoint hij) m
  rwa [card_idx] at h

/-- **The separation for the iterates** (Section 14): `lambda(F_m)^α ≤ bs(F_m)`. -/
theorem lam_iter_rpow_le_bs (h₁ : ListOne γ) (h₂ : ListTwo γ) (m : ℕ) :
    lam (iterFun (ind Arc γ) m) ^ alpha ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by
  calc lam (iterFun (ind Arc γ) m) ^ alpha
      = (lam (ind Arc γ) ^ m) ^ alpha := by rw [lam_iterFun_eq (ind Arc γ) m]
    _ = (lam (ind Arc γ) ^ alpha) ^ m := by
        rw [← Real.rpow_natCast (lam (ind Arc γ)) m, ← Real.rpow_mul (lam_nonneg _), mul_comm,
          Real.rpow_mul (lam_nonneg _), Real.rpow_natCast]
    _ ≤ (14011 : ℝ) ^ m := by
        gcongr
        · exact Real.rpow_nonneg (lam_nonneg _) _
        · exact lam_rpow_le h₁ h₂
    _ ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by exact_mod_cast bs_iter_ge m

/-- **The ratio blows up** (Section 14): `bs(F_m) / lambda(F_m)^2 ≥ (14011/U)^m`, and
`14011/U > 1.768`.  This refutes `bs(f) = O(lambda(f)^2)`. -/
theorem bs_div_lam_sq_ge (h₁ : ListOne γ) (h₂ : ListTwo γ) (m : ℕ) :
    (14011 / U) ^ m * lam (iterFun (ind Arc γ) m) ^ 2
      ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by
  have hlam_sq : lam (iterFun (ind Arc γ) m) ^ 2 ≤ U ^ m := by
    rw [lam_iterFun_eq (ind Arc γ) m]
    calc (lam (ind Arc γ) ^ m) ^ 2 = (lam (ind Arc γ) ^ 2) ^ m := by ring
      _ ≤ U ^ m := pow_le_pow_left₀ (sq_nonneg _) (lam_sq_le h₁ h₂) m
  have hU : (0 : ℝ) < U := U_pos
  calc (14011 / U) ^ m * lam (iterFun (ind Arc γ) m) ^ 2
      ≤ (14011 / U) ^ m * U ^ m := mul_le_mul_of_nonneg_left hlam_sq (by positivity)
    _ = 14011 ^ m := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero m U_pos.ne')]
    _ ≤ bs (iterFun (ind Arc γ) m) := by exact_mod_cast bs_iter_ge m

/-- The growth ratio exceeds `1.768` (Section 12). -/
theorem ratio_gt : (1.768 : ℝ) < 14011 / U := by
  have h : (14011 : ℝ) / 7924 < 14011 / U := div_lt_div_of_pos_left (by norm_num) U_pos U_lt
  linarith

/-! ### The separation with an explicit exponent -/

/-- **`bs(f) > lambda(f)^2`** (Sections 5 and 12): the seed has a gap by a factor
`14011/7924 > 1.768`. Self-composition amplifies this gap without bound, as proved
in `exists_ratio_blowup`. -/
theorem lam_sq_lt_bs (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    lam (ind Arc γ) ^ 2 < (bs (ind Arc γ) : ℝ) := by
  linarith [lam_sq_le h₁ h₂, U_lt, bs_ge_real (γ := γ)]

/-- `7924 ^ 1.06 < 14011` (Section 14).  Raising to the fiftieth power turns this into the integer
inequality `7924 ^ 53 < 14011 ^ 50`, which avoids estimating any logarithm.  It is the
quantitative form of `2.12 < alpha` (the true value being `2.1269738...`). -/
theorem rpow_1_06_lt : (7924 : ℝ) ^ (1.06 : ℝ) < 14011 := by
  refine lt_of_pow_lt_pow_left₀ 50 (by norm_num) ?_
  rw [← Real.rpow_natCast ((7924 : ℝ) ^ (1.06 : ℝ)) 50, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **`bs(f) > lambda(f)^2.12`** (Sections 5, 12 and 14).  This is `lam_rpow_le` with the
irrational exponent `alpha = 2.1269738...` replaced by the explicit rational `2.12`, and
with a strict inequality. -/
theorem lam_rpow_212_lt_bs (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    lam (ind Arc γ) ^ (2.12 : ℝ) < (bs (ind Arc γ) : ℝ) := by
  calc lam (ind Arc γ) ^ (2.12 : ℝ)
      = (lam (ind Arc γ) ^ (2 : ℕ)) ^ (1.06 : ℝ) := rpow_eq_sq_rpow (lam_nonneg _) (by norm_num)
    _ ≤ U ^ (1.06 : ℝ) := Real.rpow_le_rpow (by positivity) (lam_sq_le h₁ h₂) (by norm_num)
    _ ≤ (7924 : ℝ) ^ (1.06 : ℝ) := Real.rpow_le_rpow U_pos.le U_lt.le (by norm_num)
    _ < 14011 := rpow_1_06_lt
    _ ≤ (bs (ind Arc γ) : ℝ) := bs_ge_real

/-! ### Existence of the gate labelling -/

/-- **Existence of a good gate labelling** (Sections 6-10): the asymmetric Lovász Local
Lemma produces a labelling `γ : Idx → Idx → Fin 144` satisfying both (L1) and (L2). -/
theorem exists_listOne_listTwo : ∃ γ : Idx → Idx → Fin r, ListOne γ ∧ ListTwo γ :=
  LLL.exists_gate_labelling (Arc := Arc) (r := r) card_idx isDR_arc rfl

/-! ### The unconditional statements -/

/-- **The headline separation** (Sections 5-12).  There is a total Boolean function `f`
with

  `bs(f) > lambda(f) ^ 2.12`.

Self-composition amplifies the seed separation; `exists_ratio_blowup` below supplies
the family of inequalities used to refute `bs(f) = O(lambda(f)^2)`. -/
theorem exists_bs_gt_lam_rpow :
    ∃ f : Input (Coord Idx r) → Bool, lam f ^ (2.12 : ℝ) < (bs f : ℝ) := by
  obtain ⟨γ, h₁, h₂⟩ := exists_listOne_listTwo
  exact ⟨ind Arc γ, lam_rpow_212_lt_bs h₁ h₂⟩

/-- **The counterexample** (Sections 5 and 12).  There is a total Boolean function `f`
with `bs(f) ≥ 14011` and `lambda(f)^2 ≤ U = 7149 + 2 √150108 < 7924`; since
`α = 2 log 14011 / log U > 2`, it also satisfies `lambda(f)^α ≤ bs(f)`. -/
theorem exists_counterexample :
    ∃ γ : Idx → Idx → Fin r,
      14011 ≤ bs (ind Arc γ) ∧ lam (ind Arc γ) ^ 2 ≤ U ∧
        lam (ind Arc γ) ^ alpha ≤ (bs (ind Arc γ) : ℝ) := by
  obtain ⟨γ, h₁, h₂⟩ := exists_listOne_listTwo
  exact ⟨γ, bs_ge, lam_sq_le h₁ h₂, (lam_rpow_le h₁ h₂).trans bs_ge_real⟩

/-- **`bs` is not `O(lambda²)`** (Section 14).  There is a function `f` whose `m`-fold
self-compositions satisfy `bs(F_m) / lambda(F_m)^2 ≥ (14011/U)^m` with `14011/U > 1.768`,
so the ratio tends to infinity.  Unlike in Section 14, the multiplicativity of `lambda`
under composition is not imported but proved (`BSLambda.lam_iterFun_eq`). -/
theorem exists_ratio_blowup :
    ∃ γ : Idx → Idx → Fin r, ∀ m : ℕ,
      (14011 / U) ^ m * lam (iterFun (ind Arc γ) m) ^ 2
        ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by
  obtain ⟨γ, h₁, h₂⟩ := exists_listOne_listTwo
  exact ⟨γ, bs_div_lam_sq_ge h₁ h₂⟩

end Final

end BSLambda
