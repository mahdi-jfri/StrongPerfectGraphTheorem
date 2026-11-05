/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 1.  This module holds `thm_1_1`; `thm_1_2` is in
    `StrongPerfectGraphTheorem.MainTheorem`, and the others are in the sibling modules of
    `StrongPerfectGraphTheorem/Statements/S01`. -/

module

public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.ProofLemmas.PerfectInducedSubgraph
public import StrongPerfectGraphTheorem.ProofLemmas.PerfectGraphComplementCliqueNumColorable
public import StrongPerfectGraphTheorem.ProofLemmas.HoleBasics

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

open StrongPerfectGraphTheorem.Types.Core

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-! ## The paper's own numbered theorems (Section 1, printed pages 1–4) -/

/-- **1.1** (printed p. 1), due to Lovász [16]; used, but not proved, in this paper.

PAPER: *"The complement of every perfect graph is perfect."*

*"in 1961 Berge [1] proposed two celebrated conjectures about perfect graphs.  The first
was proved by Lovász [16] in 1972, and is the following."*  The paper's `Ḡ` is `Gᶜ`.
**PRIOR WORK, PROVED HERE.**  Lovász [16] (1972).  The paper states and uses 1.1 but does not
prove it.  The proof below applies
`StrongPerfectGraphTheorem.ProofLemmas.PerfectGraphComplementCliqueNumColorable` to each
induced subgraph of `G`. -/
theorem thm_1_1 (G : SimpleGraph V)
    (hG : SPGT.IsPerfect G) :
    SPGT.IsPerfect Gᶜ := by
  intro X
  letI : Fintype X := Fintype.ofFinite X
  have hperfect : SPGT.IsPerfect (G.induce X) :=
    StrongPerfectGraphTheorem.ProofLemmas.PerfectInducedSubgraph G X hG
  have hcolor : (G.induce X)ᶜ.Colorable (G.induce X)ᶜ.cliqueNum :=
    StrongPerfectGraphTheorem.ProofLemmas.PerfectGraphComplementCliqueNumColorable
      (G.induce X) hperfect
  rw [StrongPerfectGraphTheorem.ProofLemmas.HoleBasics.induce_compl] at hcolor
  exact le_antisymm
    (SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcolor)
    SimpleGraph.cliqueNum_le_chromaticNumber


end SPGT

end StrongPerfectGraphTheorem.MainTheorem
