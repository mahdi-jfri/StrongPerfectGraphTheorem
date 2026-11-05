/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 1.  This module holds `thm_E5_perfect_implies_berge`; `thm_1_2` is in
    `StrongPerfectGraphTheorem.MainTheorem`, and the others are in the sibling modules of
    `StrongPerfectGraphTheorem/Statements/S01`. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Replication
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.ProofLemmas.HoleSupportCycleIso
public import StrongPerfectGraphTheorem.ProofLemmas.OddCycleCliqueAndTwoColoringObstruction
public import StrongPerfectGraphTheorem.ProofLemmas.OddCycleComplementCliqueAndColoringObstruction
public import StrongPerfectGraphTheorem.ProofLemmas.IsoTransport
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

Ambient conventions: all graphs of the paper are finite
and simple, so the vertex type carries `[Fintype V]` (and `[DecidableEq V]`); the paper's
`Ḡ` is Mathlib's `Gᶜ`.
-/

@[expose] public section

namespace StrongPerfectGraphTheorem.MainTheorem

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Decompositions
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.Replication
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **E5**; the direction of 1.2 that the paper regards as immediate, and the reason a
minimum imperfect graph *"is Berge and not perfect"*.

PAPER (printed p. 1): *"It is easy to see that every perfect graph is Berge."*

No proof is printed, so it is proved here directly.  An odd hole of length at least 5 has
clique number 2 but is not 2-colourable.  An odd antihole of length `2m + 1` with `m ≥ 2` has
clique number `m` but is not `m`-colourable.  Either one contradicts perfection. -/
theorem thm_E5_perfect_implies_berge (G : SimpleGraph V) (hG : SPGT.IsPerfect G) :
    SPGT.Berge G := by
  classical
  constructor
  · intro c hc
    by_contra heven
    have hodd : Odd c.length := (Nat.not_even_iff_odd).mp
      (by simpa [StrongPerfectGraphTheorem.Types.Core.SPGT.holeLength] using heven)
    have hfive : 5 ≤ c.length := by
      have hfour : 4 ≤ c.length := hc.1
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨e, _⟩ := StrongPerfectGraphTheorem.ProofLemmas.HoleSupportCycleIso G c hc
    have hobs := StrongPerfectGraphTheorem.ProofLemmas.OddCycleCliqueAndTwoColoringObstruction
      c.length hfive hodd
    have hclique : (G.induce (c.toFinset : Set V)).cliqueNum = 2 := by
      rw [← StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.cliqueNum_iso e]
      exact hobs.1
    have hcol : (G.induce (c.toFinset : Set V)).Colorable 2 := by
      rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
      rw [hG (c.toFinset : Set V), hclique]
    exact hobs.2 (SimpleGraph.Colorable.of_hom e.toHom hcol)
  · intro c hc
    by_contra heven
    have hodd : Odd c.length := (Nat.not_even_iff_odd).mp
      (by simpa [StrongPerfectGraphTheorem.Types.Core.SPGT.holeLength] using heven)
    obtain ⟨m, hm⟩ := hodd
    have hlen : c.length = 2 * m + 1 := by omega
    have hm2 : 2 ≤ m := by
      have hfour : 4 ≤ c.length := hc.1
      omega
    obtain ⟨e, _⟩ := StrongPerfectGraphTheorem.ProofLemmas.HoleSupportCycleIso Gᶜ c hc
    have ecomp := StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.Iso.compl e
    have hgraph : ((Gᶜ).induce (c.toFinset : Set V))ᶜ =
        G.induce (c.toFinset : Set V) := by
      rw [StrongPerfectGraphTheorem.ProofLemmas.HoleBasics.induce_compl]
      simp
    rw [hgraph] at ecomp
    have e' : (SimpleGraph.cycleGraph c.length)ᶜ ≃g
        G.induce (c.toFinset : Set V) := ecomp
    have hobs := StrongPerfectGraphTheorem.ProofLemmas.OddCycleComplementCliqueAndColoringObstruction m hm2
    have hclique : (G.induce (c.toFinset : Set V)).cliqueNum = m := by
      rw [← StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.cliqueNum_iso e']
      rw [hlen]
      exact hobs.1
    have hcol : (G.induce (c.toFinset : Set V)).Colorable m := by
      rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
      rw [hG (c.toFinset : Set V), hclique]
    apply hobs.2
    rw [← hlen]
    exact SimpleGraph.Colorable.of_hom e'.toHom hcol


end SPGT

end StrongPerfectGraphTheorem.MainTheorem
