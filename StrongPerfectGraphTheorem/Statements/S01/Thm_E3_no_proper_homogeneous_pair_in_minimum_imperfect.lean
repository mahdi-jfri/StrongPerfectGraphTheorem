/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 1.  This module holds `thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect`;
    `thm_1_2` is in `StrongPerfectGraphTheorem.MainTheorem`, and the others are in the sibling
    modules of `StrongPerfectGraphTheorem/Statements/S01`. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Replication
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.ProofLemmas.ProperHomogeneousPairColouringAssembly

/-!
# The Strong Perfect Graph Theorem — Section 1

The numbered results of Section 1 of Chudnovsky, Robertson, Seymour and Thomas,
*The Strong Perfect Graph Theorem* (June 20 2002 / revised July 19 2005,
printed pages 1–4), together with the external results that the paper's deduction of
**1.2** from **1.3** relies on, and the two external results used inside its proof of
**1.5**.

The centrepiece is `thm_1_2`: *a graph is perfect if and only if it is Berge.*

Contents, in the order printed in the paper:

* `thm_1_1` — Lovász [16]: the complement of every perfect graph is perfect;
* `thm_1_2` — **the Strong Perfect Graph Theorem**;
* `thm_1_3` — the structure theorem for Berge graphs (the contents of sections 2–24);
* `thm_1_5` — no minimum imperfect graph admits a balanced skew partition;

and the external ingredients of the proof of 1.2, printed page 4:

* `thm_E2_no_proper_2_join_in_minimum_imperfect` — Cornuéjols and Cunningham [13];
* `thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect` — Chvátal and Sbihi [7];
* `thm_E4_basic_implies_perfect` — König [15], Lovász [16], and "the reader";
* `thm_E5_perfect_implies_berge`;

and the two external ingredients of the proof of 1.5, printed pages 3–4:

* `thm_E6_no_star_cutset_in_minimum_imperfect` — Chvátal [6];
* `thm_E7_lovasz_replication` — Lovász [16].

Every definition used below is imported: `Berge`, `IsPerfect`, `MinimumImperfect` from
`StrongPerfectGraphTheorem.Types.Core`; `AdmitsProper2Join`, `AdmitsProperHomogeneousPair`,
`AdmitsBalancedSkewPartition`, `AdmitsStarCutset` from `StrongPerfectGraphTheorem.Types.Decompositions`;
`IsBasic` from `StrongPerfectGraphTheorem.Types.BasicClasses`; `replicateVertex` from
`StrongPerfectGraphTheorem.Types.Replication`.  Nothing is restated here.

Ambient conventions: all graphs of the paper are finite and simple, so the vertex type
carries `[Fintype V]` (and `[DecidableEq V]`); the paper's `Ḡ` is Mathlib's `Gᶜ`.
-/

@[expose] public section

namespace StrongPerfectGraphTheorem.MainTheorem

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Decompositions
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.Replication
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **E3**, due to Chvátal and Sbihi [7]; used in the proof of 1.2 from 1.3.

PAPER (printed p. 4): *"It is shown in [7] that `G` does not admit a proper homogeneous
pair."*

(The paper's *proper homogeneous pair* is *"a slight variation of the 'homogeneous pair' of
Chvátal and Sbihi [7]"*.) -/
theorem thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect
    (G : SimpleGraph V) (hG : SPGT.MinimumImperfect G) :
    ¬ SPGT.AdmitsProperHomogeneousPair G := by
  rintro ⟨A, B, hAB⟩
  exact StrongPerfectGraphTheorem.ProofLemmas.ProperHomogeneousPairColouringAssembly G hG A B hAB


end SPGT

end StrongPerfectGraphTheorem.MainTheorem
