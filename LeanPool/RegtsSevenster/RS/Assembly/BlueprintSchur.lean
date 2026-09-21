/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Assembly.Blueprint
import LeanPool.RegtsSevenster.RS.Novel.Envelope.ObjectTower
import LeanPool.RegtsSevenster.RS.TheoremTotal

/-!
# Blueprint: the Schur package, the dimension bound, the open sector

The second part of the axiom audit.  It pins the symmetric-group
input the forward direction rests on, the auxiliary `⌊2eR⌋` dimension
bound, the total bound `k + 2ℓ ≤ R`, and the open-sector Proposition 3.
Read `Blueprint.lean`
first: it audits the forward proof itself.
-/

/-! ### The Schur package

Jacobi–Trudi characters: the Frobenius identity, orthonormality,
the branching containment, the block faithfulness and the square
growth bound — the fields of `SchurPackage`, and the package.
-/

/- Upstream audit output: 'RS.jtChar_frobenius'' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.jtChar_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.jtChar_eq_nChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.nProjector_block_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.square_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.branching_of_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.jtChar_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.schurPackageOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.restrPairing_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.schurPackage' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### The forward theorem on Deligne alone -/

/- Upstream audit output: 'RS.regts_sevenster_deligne_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### The trace zeta function

The zeta function of a Frobenius tower is the Newton generating
series of its super power sums, and rational when the characters
are hook-confined.
-/

/- Upstream audit output: 'RS.FrobeniusTower.traceZeta_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.FrobeniusTower.traceZeta_superSpectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.traceZeta_eq_newtonH_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### Corollary A.2 with the sharp threshold

The appendix's own statement: a real dimension bound `A`, every side
`s > 2e√A`, and degrees at most `s − 1`.
-/

/- Upstream audit output: 'RS.FrobeniusTower.traceZeta_rational_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.FrobeniusTower.traceZeta_superSpectrum_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.PermTower.hook_confinement_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.newtonH_series_rational_of_hook_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### Hook-confined sequences

Lemma A.9 for arbitrary hook dimensions, with numerator degree at
most `b` and denominator degree at most `a`.
-/

/-
info: RS.newtonH_series_rational_of_hook_vanishing {t : ℕ → ℂ} {a b : ℕ}
  (hvan : ∀ (μ : YoungDiagram), ¬RS.IsInHook a b μ → RS.diagramSchur μ t = 0) :
  ∃ P Q,
    P.coeff 0 = 1 ∧ Q.coeff 0 = 1 ∧ P.natDegree ≤ b ∧ Q.natDegree ≤ a ∧ IsCoprime P Q ∧ RS.newtonHSeries t * ↑Q = ↑P
-/

/-
info: RS.superPowerSums_of_hook_vanishing {t : ℕ → ℂ} {a b : ℕ}
  (hvan : ∀ (μ : YoungDiagram), ¬RS.IsInHook a b μ → RS.diagramSchur μ t = 0) :
  ∃ α β,
    α.card ≤ a ∧
      β.card ≤ b ∧
        (∀ x ∈ α, x ≠ 0) ∧
          (∀ x ∈ β, x ≠ 0) ∧
            (∀ x ∈ α, x ∉ β) ∧
              ∀ (m : ℕ), 1 ≤ m → t m = (Multiset.map (fun x => x ^ m) α).sum - (Multiset.map (fun x => x ^ m) β).sum
-/

/-! ### The separate-sector dimension bound

The `⌊2eR⌋` bound: a square diagram past it is dead, its
idempotent acts as zero, and the surviving sector is bounded.
-/

/- Upstream audit output: 'RS.square_growth_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.PermTower.not_alive_square_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.skeinRep_square_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.functional_charIdempotent_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.charIdempotent_image_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.RelTransitionSystem.pathMatch_invol' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.superPermAction_square_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.mixedPartition_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.squareSectorBound_of_detPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.diagramSchur_square_const_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_quant_of_detPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.squareBinomialDetPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.det_binomial_upper_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_quant_deligne_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### The total dimension bound

Native blocks bound constituent dimensions; simultaneous word orbits
bound the commutant by a polynomial. The transported colour action
then forces `k + 2 * ℓ ≤ R` by comparison of exponential bases.
-/

/- Upstream audit output: 'RS.nDim_sq_le_finrank_of_projector_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.finrank_le_mul_commutant' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.finrank_commutant_le_word_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.le_of_pow_le_pow_mul_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.colourTotalEquiv_modelPermMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.stdModel_total_dimension_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_total_deligne_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### The open sector: Proposition 3

Repair connectivity of a pairing fibre, the canonical frame and
its re-canonicalization, the per-move ledgers and the paired step
— together, the signed value depends on the boundary pairing and
nothing else.  Independence *across* pairings is false.
-/

/- Upstream audit output: 'RS.EdgeSubset.repair_connectivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.eulerian_iff_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.openCircuitCount_glueOpen_participating' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.pathCanonical_agree_nonperiodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.exists_pathCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.third_chord_reparity' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.pairingConnectivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.stepLedger_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.throughSummand_independence_of_allInternal' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.twoPath_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.pathMatch_repair_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.crossesCut_iff_chordPairCross' depends on axioms: [propext] -/

/- Upstream audit output: 'RS.EdgeSubset.pathSign_of_samePairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.signedValueAt_samePairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.pairedLedger_iff_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.signedValueAt_samePairing_of_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.TransposeVerify.not_throughIndependenceC' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.cutPartner_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.eulerianIndependence' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.throughSummand_portFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.twoPathNonSep_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.throughValueC_eq_signedValueAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.chainDir_pathMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.pathCanonical_iff_chainDir' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.exists_recanonicalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.swap_dirs_opposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.mem_antiLowSet_transport_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.chainDir_true_iff_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.mem_antiLowSet_transport_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.pairedLedger_iff_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.stateOddFlipSet_flipSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.mem_highSet_repair_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.chordCrossingCount_repair_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.fourLabel_parity_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.fourLabel_parity_nonsep' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.flipSignProd_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.flipSignProd_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.antiLowSet_transport_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.symmU_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.statusDiff_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.statusDiff_of_samePairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.mem_pairFold_antiLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.antiLow_labels_eq_statusChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.antiLowSet_transport_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.antiLowSet_transport_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.nonsep_labels_eq_statusChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.diagCrossCount_glue_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.pairedLedgerUnsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.pairedLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.stepStatusLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.chainStatusLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### The appendix, for an object

Corollary A.2 as the appendix states it: for an arbitrary object of a
rigid symmetric ℂ-linear category whose tensor powers have
exponentially bounded endomorphism dimensions, the trace zeta
function of every endomorphism is rational of the stated degree.
-/

/-
info: 'RS.frobenius_powHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/-
info: 'RS.objectFrobeniusTower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/-
info: 'RS.traceZeta_rational_of_object' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/-
info: 'RS.scalarTrace_eq_zero_of_isNilpotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/-
info: 'RS.traceZeta_superSpectrum_of_object' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/-! ### The appendix's theorems, by type

The axiom audits above fix what these rest on; the pins below fix
what they say — the hypothesis on the object, the threshold, and the
degree bound.
-/

/-
info: @RS.traceZeta_rational_of_object : ∀ {A : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] [inst_2 : CategoryTheory.SymmetricCategory A]
  [inst_3 : CategoryTheory.Preadditive A] [inst_4 : CategoryTheory.Linear ℂ A]
  [inst_5 : CategoryTheory.MonoidalPreadditive A] [inst_6 : CategoryTheory.MonoidalLinear ℂ A]
  [inst_7 : CategoryTheory.RigidCategory A] (hu : RS.HasScalarUnit A) (X : A)
  [∀ (n : ℕ), Module.Finite ℂ (CategoryTheory.End (RS.tensorPow A X n))] (A₀ : ℝ),
  (∀ (n : ℕ), ↑(Module.finrank ℂ (CategoryTheory.End (RS.tensorPow A X n))) ≤ A₀ ^ n) →
    ∀ (g : CategoryTheory.End X) {s : ℕ},
      2 * Real.exp 1 * √A₀ < ↑s →
        ∃ (Pp : Polynomial ℂ) (Qp : Polynomial ℂ),
          Pp.coeff 0 = 1 ∧
            Qp.coeff 0 = 1 ∧
              Pp.natDegree ≤ s - 1 ∧
                Qp.natDegree ≤ s - 1 ∧
                  IsCoprime Pp Qp ∧ (RS.traceZeta fun (m : ℕ) => (RS.scalarTrace hu X) (g ^ m)) * ↑Qp = ↑Pp
-/

/-
info: @RS.traceZeta_superSpectrum_of_object : ∀ {A : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] [inst_2 : CategoryTheory.SymmetricCategory A]
  [inst_3 : CategoryTheory.Preadditive A] [inst_4 : CategoryTheory.Linear ℂ A]
  [inst_5 : CategoryTheory.MonoidalPreadditive A] [inst_6 : CategoryTheory.MonoidalLinear ℂ A]
  [inst_7 : CategoryTheory.RigidCategory A] (hu : RS.HasScalarUnit A) (X : A)
  [∀ (n : ℕ), Module.Finite ℂ (CategoryTheory.End (RS.tensorPow A X n))] (A₀ : ℝ),
  (∀ (n : ℕ), ↑(Module.finrank ℂ (CategoryTheory.End (RS.tensorPow A X n))) ≤ A₀ ^ n) →
    ∀ (g : CategoryTheory.End X) {s : ℕ},
      2 * Real.exp 1 * √A₀ < ↑s →
        ∃ (alpha : Multiset ℂ) (beta : Multiset ℂ),
          alpha.card ≤ s - 1 ∧
            beta.card ≤ s - 1 ∧
              (∀ x ∈ alpha, x ≠ 0) ∧
                (∀ x ∈ beta, x ≠ 0) ∧
                  (∀ x ∈ alpha, x ∉ beta) ∧
                    ∀ (m : ℕ),
                      1 ≤ m →
                        (RS.scalarTrace hu X) (g ^ m) =
                          (Multiset.map (fun (x : ℂ) => x ^ m) alpha).sum -
                            (Multiset.map (fun (x : ℂ) => x ^ m) beta).sum
-/

/-
info: @RS.objectFrobeniusTower : {A : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} A] →
    [inst_1 : CategoryTheory.MonoidalCategory A] →
      [CategoryTheory.SymmetricCategory A] →
        [inst_3 : CategoryTheory.Preadditive A] →
          [inst_4 : CategoryTheory.Linear ℂ A] →
            [inst_5 : CategoryTheory.MonoidalPreadditive A] →
              [CategoryTheory.MonoidalLinear ℂ A] →
                [CategoryTheory.RigidCategory A] →
                  RS.HasScalarUnit A →
                    (X : A) →
                      (P : RS.SchurPackage) →
                        (A₀ : ℝ) →
                          (∀ (n : ℕ), ↑(Module.finrank ℂ (CategoryTheory.End (RS.tensorPow A X n))) ≤ A₀ ^ n) →
                            RS.FrobeniusTower P (fun (n : ℕ) => CategoryTheory.End (RS.tensorPow A X n)) A₀
                              (CategoryTheory.End X)
-/
