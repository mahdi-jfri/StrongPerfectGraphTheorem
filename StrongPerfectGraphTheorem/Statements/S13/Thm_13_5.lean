/-  Proof of statement 13.5 (`StrongPerfectGraphTheorem.Statements.S13.SPGT.thm_13_5`).

    The paper's proof of 13.5 is printed at the head of §24 (printed p. 145):

      "We recall that we are trying to prove 13.5.  In view of 23.5, it suffices to show
       the following, which is 1.8.12, and the objective of the remainder of the paper:
       24.1  Let G ∈ F₁₁; then either G is complete, or G is bipartite, or G admits a
       balanced skew partition."

    So the argument is exactly: 23.5 (in its "in particular" form, `thm_23_5_recalcitrant`:
    for every recalcitrant `G`, one of `G, Ḡ` lies in `F₁₁`), followed by 24.1 applied to
    whichever of `G, Ḡ` lies in `F₁₁`.  In each case 24.1's third alternative is killed by
    the last bullet of *recalcitrant* (`G` admits no balanced skew partition) — for `Ḡ`
    via `admitsBalancedSkewPartition_compl` — its second alternative is one of the two
    disjuncts of the goal, and its first alternative ("complete") forces the complement to
    have no edges at all, hence to be 2-colourable, which is the other disjunct.  -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Staircases
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Statements.S23.Thm_23_5_recalcitrant
public import StrongPerfectGraphTheorem.Statements.S24.Thm_24_1
public import StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S13

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Staircases StrongPerfectGraphTheorem.Types.Staircases.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT

namespace SPGT

/-- A graph with no edges at all is 2-colourable, hence bipartite.  (Used twice below:
`G` complete makes `Ḡ` edgeless, and `Ḡ` complete makes `G` edgeless.) -/
private theorem bipartite_of_no_adj {W : Type*} {H : SimpleGraph W}
    (h : ∀ u v : W, ¬ H.Adj u v) : H.IsBipartite :=
  ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 2)) fun {u v} hadj => absurd hadj (h u v)⟩

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **13.5** (printed p. 86), introduced by *"The remainder of the paper is basically a proof
of the following."*

PAPER: *"If `G` is recalcitrant then either `G` or `Ḡ` is bipartite."*

Followed by *"Clearly any counterexample to 1.3 is recalcitrant, so 13.5 will imply 1.3."*
*Recalcitrant* is the four-bullet notion defined immediately before the statement and
transcribed in `StrongPerfectGraphTheorem.Types.LongOddPrism`; *bipartite* is Mathlib's
`SimpleGraph.IsBipartite`, and the paper's `Ḡ` is `Gᶜ`. -/
theorem thm_13_5 (G : SimpleGraph V) (hG : Recalcitrant G) :
    G.IsBipartite ∨ Gᶜ.IsBipartite := by
  -- The last bullet of *recalcitrant*: `G` admits no balanced skew partition.
  have hbsp : ¬ AdmitsBalancedSkewPartition G := hG.2.2.2.2
  -- "In view of 23.5": one of `G, Ḡ` belongs to `F₁₁`.
  rcases _root_.StrongPerfectGraphTheorem.Statements.S23.SPGT.thm_23_5_recalcitrant G hG with h11 | h11
  · -- `G ∈ F₁₁`; apply 24.1 to `G`.
    rcases _root_.StrongPerfectGraphTheorem.Statements.S24.SPGT.thm_24_1 G h11 with hcomp | hbip | hskew
    · -- `G` complete, so `Ḡ` has no edges and is therefore bipartite.
      refine Or.inr (bipartite_of_no_adj ?_)
      intro u v huv
      rw [SimpleGraph.compl_adj] at huv
      exact huv.2 (hcomp u v huv.1)
    · exact Or.inl hbip
    · exact absurd hskew hbsp
  · -- `Ḡ ∈ F₁₁`; apply 24.1 to `Ḡ`.
    rcases _root_.StrongPerfectGraphTheorem.Statements.S24.SPGT.thm_24_1 Gᶜ h11 with hcomp | hbip | hskew
    · -- `Ḡ` complete, so `G` has no edges and is therefore bipartite.
      refine Or.inl (bipartite_of_no_adj ?_)
      intro u v huv
      have hcv : Gᶜ.Adj u v := hcomp u v (G.ne_of_adj huv)
      rw [SimpleGraph.compl_adj] at hcv
      exact hcv.2 huv
    · exact Or.inr hbip
    · exact absurd
        (_root_.StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp hskew)
        hbsp


end SPGT

end StrongPerfectGraphTheorem.Statements.S13
