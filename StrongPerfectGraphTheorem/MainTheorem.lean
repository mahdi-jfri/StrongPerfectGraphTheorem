module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Replication
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Statements.S01.Thm_1_1
public import StrongPerfectGraphTheorem.Statements.S01.Thm_1_3
public import StrongPerfectGraphTheorem.Statements.S01.Thm_1_5
public import StrongPerfectGraphTheorem.Statements.S01.Thm_E2_no_proper_2_join_in_minimum_imperfect
public import StrongPerfectGraphTheorem.Statements.S01.Thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect
public import StrongPerfectGraphTheorem.Statements.S01.Thm_E4_basic_implies_perfect
public import StrongPerfectGraphTheorem.Statements.S01.Thm_E5_perfect_implies_berge
public import StrongPerfectGraphTheorem.ProofLemmas.IsoTransport

/-!
# The Strong Perfect Graph Theorem

This file proves **1.2**, the main theorem of Chudnovsky, Robertson, Seymour and Thomas,
*The strong perfect graph theorem*: a graph is perfect if and only if it is Berge
(`thm_1_2`). The proof is the paper's deduction of 1.2 from 1.3 (printed p. 4).

It uses the following results, all proved in this library:

* `thm_1_1`, Lovász [16]: the complement of every perfect graph is perfect;
* `thm_1_3`, the structure theorem for Berge graphs, which takes up Sections 2–24 of the paper:
  every Berge graph is basic, or one of `G`, `Ḡ` admits a proper 2-join, or `G` admits a
  proper homogeneous pair, or `G` admits a balanced skew partition;
* `thm_1_5`: no minimum imperfect graph admits a balanced skew partition;
* `thm_E2_no_proper_2_join_in_minimum_imperfect`, Cornuéjols and Cunningham [13];
* `thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect`, Chvátal and Sbihi [7];
* `thm_E4_basic_implies_perfect`: every basic graph is perfect (König [15], Lovász [16]);
* `thm_E5_perfect_implies_berge`: every perfect graph is Berge.

The proof of 1.5 also uses Chvátal's star cutset lemma
(`thm_E6_no_star_cutset_in_minimum_imperfect`) and Lovász's replication lemma
(`thm_E7_lovasz_replication`).

The definitions `Berge`, `IsPerfect` and `MinimumImperfect` are in `Types.Core`, the
decompositions are in `Types.Decompositions`, and `IsBasic` is in `Types.BasicClasses`.

As in the paper, all graphs are finite and simple. The vertex type carries `[Fintype V]` and
`[DecidableEq V]`, and the paper's `Ḡ` is Mathlib's `Gᶜ`. The file `MathlibForm` restates
`thm_1_2` using only Mathlib's notions.
-/

@[expose] public section

namespace StrongPerfectGraphTheorem.MainTheorem

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Decompositions
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.Replication
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

-- `thm_1_2` is stated for a vertex type with both `[Fintype V]` and `[DecidableEq V]`, as
-- everywhere in the library. Its proof uses only `[Fintype V]`, because the argument runs at a
-- minimum counterexample on `Fin n₀`, where decidable equality is automatic. The section
-- variable stays for uniformity, so the linter is silenced.
set_option linter.unusedSectionVars false


/-- **The four printed sentences of the proof of 1.2** (printed p. 4, *"Proof of 1.2,
assuming 1.3"*), packaged as a standalone statement: *no graph on a finite vertex type
with decidable equality is a minimum imperfect graph.*

PAPER: *"Suppose that there is a minimum imperfect graph `G`.  Thus `G` is Berge and not
perfect.  Every basic graph is perfect, and so `G` is not basic.  It is shown in [13] that
`G` does not admit a proper 2-join.  From Lovász's theorem 1.1, it follows that `Ḡ` is also
a minimum imperfect graph, and therefore `Ḡ` also does not admit a proper 2-join.  It is
shown in [7] that `G` does not admit a proper homogeneous pair, and `G` does not admit a
balanced skew partition by 1.5.  It follows that `G` violates 1.3, and therefore there is
no such graph `G`."*

`[DecidableEq W]` is required, not decorative: the final step applies `thm_1_3` and
`thm_1_5`, both stated under `[Fintype V] [DecidableEq V]`.  It costs nothing, because this
  lemma is only ever applied at `W = Fin n₀`, where both instances are automatic. -/
theorem no_minimumImperfect {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (hG : SPGT.MinimumImperfect G) : False := by
  -- *"Thus `G` is Berge and not perfect."*  (Page 1: *"in particular, any such graph is
  -- Berge and not perfect"*.)  Both follow from the first conjunct of `MinimumImperfect`
  -- together with E5, *"every perfect graph is Berge"*.
  have hnp : ¬ SPGT.IsPerfect G :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.minimumImperfect_not_perfect hG
      (thm_E5_perfect_implies_berge G)
  have hb : SPGT.Berge G :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.minimumImperfect_berge hG
      (thm_E5_perfect_implies_berge G)
  -- *"Every basic graph is perfect, and so `G` is not basic."*
  have hnotbasic : ¬ SPGT.IsBasic G := fun hbasic =>
    hnp (thm_E4_basic_implies_perfect G hbasic)
  -- *"It is shown in [13] that `G` does not admit a proper 2-join."*
  have hno2join : ¬ SPGT.AdmitsProper2Join G :=
    thm_E2_no_proper_2_join_in_minimum_imperfect G hG
  -- *"From Lovász's theorem 1.1, it follows that `Ḡ` is also a minimum imperfect graph …"*
  have hGc : SPGT.MinimumImperfect Gᶜ :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.minimumImperfect_compl' hG
      (fun K hK => thm_1_1 K hK)
  -- *"… and therefore `Ḡ` also does not admit a proper 2-join."*
  have hno2joinc : ¬ SPGT.AdmitsProper2Join Gᶜ :=
    thm_E2_no_proper_2_join_in_minimum_imperfect Gᶜ hGc
  -- *"It is shown in [7] that `G` does not admit a proper homogeneous pair …"*
  have hnohp : ¬ SPGT.AdmitsProperHomogeneousPair G :=
    thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect G hG
  -- *"… and `G` does not admit a balanced skew partition by 1.5."*
  have hnoskew : ¬ SPGT.AdmitsBalancedSkewPartition G := thm_1_5 G hG
  -- *"It follows that `G` violates 1.3, and therefore there is no such graph `G`."*
  rcases thm_1_3 G hb with h | (h | h) | h | h
  · exact hnotbasic h
  · exact hno2join h
  · exact hno2joinc h
  · exact hnohp h
  · exact hnoskew h


/-- **1.2** (printed p. 1) — **the Strong Perfect Graph Theorem**, the main theorem of the
paper and of this development.

PAPER: *"A graph is perfect if and only if it is Berge."*

*"The second conjecture has remained open until now; it was known as the strong perfect
graph conjecture, and the following is the main result of this paper."*

There is no hypothesis beyond the ambient one that the vertex type is finite: the assertion
is about *every* graph. -/
theorem thm_1_2 (G : SimpleGraph V) :
    SPGT.IsPerfect G ↔ SPGT.Berge G := by
  constructor
  · -- *"It is easy to see that every perfect graph is Berge, and so to prove 1.2 it
    -- remains to prove the converse."*  (printed p. 1)
    exact fun hp => thm_E5_perfect_implies_berge G hp
  · -- The converse.  Suppose it fails at `G`; then `G` is a counterexample to 1.2 …
    intro hB
    by_contra hnP
    have hcex : ¬ (SPGT.IsPerfect G ↔ SPGT.Berge G) := fun hiff => hnP (hiff.mpr hB)
    -- … and so, taking a counterexample *"with as few vertices as possible"*, there is a
    -- minimum imperfect graph.  This is the paper's *"Suppose that there is a minimum
    -- imperfect graph `G`."*
    obtain ⟨n₀, H₀, hH₀⟩ :=
      _root_.StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.exists_minimumImperfect G hcex
    -- *"… and therefore there is no such graph `G`.  This proves 1.2."*
    exact no_minimumImperfect H₀ hH₀


end SPGT

end StrongPerfectGraphTheorem.MainTheorem
