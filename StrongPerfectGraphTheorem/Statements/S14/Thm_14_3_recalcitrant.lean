module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.DoubleDiamond
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Statements.S14.Thm_14_3
public import StrongPerfectGraphTheorem.ProofLemmas.RecalcitrantInF5

/-!
# Section 14 — The double diamond

The three numbered statements 14.1–14.3 of Chudnovsky–Robertson–Seymour–Thomas, *The Strong
Perfect Graph Theorem* (published/Annals version, printed pages 87–91).

Every defined term used here is imported and never restated:

* *double diamond*, *cube*, *maximal cube*, *the graph formed by a cube*, *minor* and *major*
  (with respect to a maximal cube) come from `StrongPerfectGraphTheorem.Types.DoubleDiamond`;
* *attachment* from `StrongPerfectGraphTheorem.Types.Appearances`;
* the classes `F₅`, `F₆` from `StrongPerfectGraphTheorem.Types.Classes`;
* *recalcitrant* from `StrongPerfectGraphTheorem.Types.LongOddPrism` (it is defined in §13);
* *proper 2-join* and *balanced skew partition* from `StrongPerfectGraphTheorem.Types.Decompositions`;
* *connected*, *complete to*, *anticomplete to* from `StrongPerfectGraphTheorem.Types.Core`.

Encoding conventions:

* a cube is the quadruple of vertex sets `(A, B, C, D)`, and the vertex set `V(K)` of the
  graph `K = G|(A ∪ B ∪ C ∪ D)` that it forms is `A ∪ B ∪ C ∪ D`;
* *"the set of neighbours of `v` in `V(K)`"* is `G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)`, and
  *"the set of attachments of `F` in `V(K)`"* is `attachments G F (A ∪ B ∪ C ∪ D)`;
* *"`X` includes `S`"* is `S ⊆ X`;
* quantification over all finite graphs is `∀ (n : ℕ) (H : SimpleGraph (Fin n))`.

Published-vs-draft note: **14.3** is the published form, *"either one of `G, Ḡ` admits a
**proper** 2-join"* (the arXiv draft says *"a 2-join"*).

The closing sentence of 14.3, *"In particular, every recalcitrant graph belongs to `F₆`"*, has
no free `G` and is asserted by the paper outright, so it is a **separate, hypothesis-free**
  theorem `thm_14_3_recalcitrant` rather than a conjunct sitting under 14.3's hypotheses.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S14

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.DoubleDiamond StrongPerfectGraphTheorem.Types.DoubleDiamond.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **14.3**, final sentence (printed p. 91) — the closing corollary of 14.3, stated on its own
because the paper asserts it of *every* recalcitrant graph, under no hypothesis.

PAPER: *"In particular, every recalcitrant graph belongs to `F₆`."*

`G` here is an arbitrary finite graph (it is unrelated to the `G ∈ F₅` of `thm_14_3`);
*recalcitrant* is the four-bullet notion of §13. -/
theorem thm_14_3_recalcitrant (G : SimpleGraph V) (hG : SPGT.Recalcitrant G) : SPGT.InF6 G := by
  -- Printed p. 86: *"Certainly every recalcitrant graph belongs to `F₅`, by 10.6 and 9.7."*
  have hF5 : SPGT.InF5 G :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.RecalcitrantInF5.recalcitrant_inF5 G hG
  refine ⟨hF5, ?_⟩
  -- The remaining conjunct of `F₆`: `G` contains no double diamond.
  intro hdd
  -- 14.3 itself, applied to `G ∈ F₅`.
  rcases thm_14_3 G hF5 hdd with (h | h) | h
  · exact hG.2.2.1.1 h            -- `G` admits no proper 2-join
  · exact hG.2.2.1.2 h            -- nor does `Ḡ`
  · exact hG.2.2.2.2 h            -- `G` admits no balanced skew partition


end SPGT

end StrongPerfectGraphTheorem.Statements.S14
