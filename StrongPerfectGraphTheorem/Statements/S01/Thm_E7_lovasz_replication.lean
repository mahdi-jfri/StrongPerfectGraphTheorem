/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 1.  This module holds `thm_E7_lovasz_replication`;
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
public import StrongPerfectGraphTheorem.ProofLemmas.ColorClassHitsAllMaximumCliques
public import StrongPerfectGraphTheorem.ProofLemmas.StableMaximumCliqueTransversalsImplyPerfect
public import StrongPerfectGraphTheorem.ProofLemmas.ReplicateInduceWithoutNewIso
public import StrongPerfectGraphTheorem.ProofLemmas.ReplicateInduceOnlyNewIso
public import StrongPerfectGraphTheorem.ProofLemmas.ReplicateBothTwinsCliqueBounds
public import StrongPerfectGraphTheorem.ProofLemmas.ReplicateBothTwinsUnchangedTransversal
public import StrongPerfectGraphTheorem.ProofLemmas.IsoTransport

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


/-- **E7**, the replication lemma of Lovász [16]; used inside the proof of 1.5.

PAPER (printed p. 4, in the proof of claim (2) of 1.5): *"a theorem of Lovász [16] shows
that replicating a vertex of a perfect graph makes another perfect graph; so if we replace
`z` by a set `Z` of `t − s` vertices all complete to `B₁` and to each other, and with no
other neighbours in `Aᵢ ∪ B`, then the graph we make is perfect."*

`replicateVertex G v` is the graph obtained from `G` by adding one new vertex adjacent to
`v` and to all the neighbours of `v`. -/
theorem thm_E7_lovasz_replication (G : SimpleGraph V) (v : V) (hG : SPGT.IsPerfect G) :
    SPGT.IsPerfect (SPGT.replicateVertex G v) := by
  classical
  apply StrongPerfectGraphTheorem.ProofLemmas.StableMaximumCliqueTransversalsImplyPerfect
  intro X hX
  obtain ⟨x⟩ := hX
  by_cases hw : Sum.inr () ∈ X
  · by_cases hv : Sum.inl v ∈ X
    · let A : Set V := {a : V | Sum.inl a ∈ X}
      let H0 : SimpleGraph A := G.induce A
      let H : SimpleGraph X := (SPGT.replicateVertex G v).induce X
      have hchi0 : H0.chromaticNumber = (H0.cliqueNum : ℕ∞) := hG A
      have hbounds : H0.cliqueNum ≤ H.cliqueNum ∧
          H.cliqueNum ≤ H0.cliqueNum + 1 ∧
            (H.cliqueNum = H0.cliqueNum + 1 →
              ∀ Q : Finset X, H.IsClique (↑Q : Set X) →
                Q.card = H.cliqueNum →
                  (⟨Sum.inl v, hv⟩ : X) ∈ Q ∧ (⟨Sum.inr (), hw⟩ : X) ∈ Q) := by
        simpa [A, H0, H] using
          (StrongPerfectGraphTheorem.ProofLemmas.ReplicateBothTwinsCliqueBounds G v X hv hw)
      have hcases : H.cliqueNum = H0.cliqueNum ∨ H.cliqueNum = H0.cliqueNum + 1 := by
        omega
      rcases hcases with hsame | hmore
      · simpa [A, H0, H] using
          (StrongPerfectGraphTheorem.ProofLemmas.ReplicateBothTwinsUnchangedTransversal
            G v X hv hw hchi0 hsame)
      · refine ⟨{⟨Sum.inr (), hw⟩}, ?_, ?_⟩
        · simp [H]
        · intro Q hQ hcard
          have htwins := hbounds.2.2 hmore Q (by simpa [H] using hQ)
            (by simpa [H] using hcard)
          exact ⟨⟨Sum.inr (), hw⟩, htwins.2, by simp⟩
    · obtain ⟨e, -, -⟩ :=
        StrongPerfectGraphTheorem.ProofLemmas.ReplicateInduceOnlyNewIso G v X hw hv
      have hchi : ((SPGT.replicateVertex G v).induce X).chromaticNumber =
          (((SPGT.replicateVertex G v).induce X).cliqueNum : ℕ∞) := by
        rw [StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.chromaticNumber_iso e,
          StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.cliqueNum_iso e]
        exact hG (insert v {a : V | Sum.inl a ∈ X})
      obtain ⟨S, -, hS, hmeet⟩ :=
        StrongPerfectGraphTheorem.ProofLemmas.ColorClassHitsAllMaximumCliques
          ((SPGT.replicateVertex G v).induce X) x hchi
      exact ⟨S, hS, hmeet⟩
  · obtain ⟨e, -⟩ :=
      StrongPerfectGraphTheorem.ProofLemmas.ReplicateInduceWithoutNewIso G v X hw
    have hchi : ((SPGT.replicateVertex G v).induce X).chromaticNumber =
        (((SPGT.replicateVertex G v).induce X).cliqueNum : ℕ∞) := by
      rw [StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.chromaticNumber_iso e,
        StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.cliqueNum_iso e]
      exact hG {a : V | Sum.inl a ∈ X}
    obtain ⟨S, -, hS, hmeet⟩ :=
      StrongPerfectGraphTheorem.ProofLemmas.ColorClassHitsAllMaximumCliques
        ((SPGT.replicateVertex G v).induce X) x hchi
    exact ⟨S, hS, hmeet⟩


end SPGT

end StrongPerfectGraphTheorem.MainTheorem
