/-  Proof of statement 1.3 (`StrongPerfectGraphTheorem.MainTheorem.SPGT.thm_1_3`).

    The paper's argument, printed p. 86 immediately after 13.5:

      "Clearly any counterexample to 1.3 is recalcitrant, so 13.5 will imply 1.3."

    So: suppose 1.3 fails for `G`.  The failure of the four printed alternatives is
    literally the four bullets of *recalcitrant* (`G` Berge; `G`, `Ḡ` not line graphs of
    bipartite graphs and `G` not a double split graph; neither `G` nor `Ḡ` admits a proper
    2-join; `G` admits neither a proper homogeneous pair nor a balanced skew partition) —
    the middle bullet coming from the failure of the first alternative, `G` basic.  Apply
    13.5: `G` or `Ḡ` is bipartite.  But that is also one of the disjuncts of `IsBasic G`,
    which we assumed to fail.  Contradiction.  -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Replication
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Statements.S13.Thm_13_5

@[expose] public section

namespace StrongPerfectGraphTheorem.MainTheorem

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Decompositions
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.Replication
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **1.3** (printed p. 4) — the structure theorem for Berge graphs; the whole of
sections 2–24 of the paper is devoted to its proof.

PAPER: *"For every Berge graph `G`, either `G` is basic, or one of `G, Ḡ` admits a proper
2-join, or `G` admits a proper homogeneous pair, or `G` admits a balanced skew
partition."*

The four printed alternatives are kept in the printed order; *"one of `G, Ḡ` admits a
proper 2-join"* is the two-way disjunction `AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ`. -/
theorem thm_1_3 (G : SimpleGraph V) (hG : SPGT.Berge G) :
    SPGT.IsBasic G ∨
      (SPGT.AdmitsProper2Join G ∨ SPGT.AdmitsProper2Join Gᶜ) ∨
      SPGT.AdmitsProperHomogeneousPair G ∨
      SPGT.AdmitsBalancedSkewPartition G := by
  -- "Clearly any counterexample to 1.3 is recalcitrant": suppose `G` is a counterexample.
  by_contra hcon
  push Not at hcon
  obtain ⟨hbasic, ⟨h2j, h2jc⟩, hhp, hskew⟩ := hcon
  -- The failure of the first alternative unpacks into the six negations of `IsBasic`.
  rw [StrongPerfectGraphTheorem.Types.BasicClasses.SPGT.IsBasic] at hbasic
  push Not at hbasic
  obtain ⟨⟨hbip, hlg, hds⟩, ⟨hbipc, hlgc, _hdsc⟩⟩ := hbasic
  -- `G` is therefore recalcitrant, in the sense defined on printed page 86.
  have hrec : StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT.Recalcitrant G :=
    ⟨hG, ⟨hlg, hlgc, hds⟩, ⟨h2j, h2jc⟩, ⟨hhp, hskew⟩⟩
  -- 13.5: if `G` is recalcitrant then `G` or `Ḡ` is bipartite.
  rcases StrongPerfectGraphTheorem.Statements.S13.SPGT.thm_13_5 G hrec with h | h
  · exact hbip h
  · exact hbipc h


end SPGT

end StrongPerfectGraphTheorem.MainTheorem
