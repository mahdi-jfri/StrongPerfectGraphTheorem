/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 7. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Overshadowed
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.Thm74Proof

/-!
# Section 7 — Rung replacement

The five numbered statements 7.1–7.5 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 34–39).

All defined terms are imported and never restated: *track*, *`k`-connected* from
`StrongPerfectGraphTheorem.Types.Tracks`; *prism* / *form a prism* / *long* and the §10 notions
*saturates* and *major with respect to a prism* from `StrongPerfectGraphTheorem.Types.Prisms`;
*Berge*, *anticonnected*, *path*, *length*, *`Y`-complete* from `StrongPerfectGraphTheorem.Types.Core`;
*appearance*, *(non)degenerate appearance*, *`J`-enlargement* from
`StrongPerfectGraphTheorem.Types.Appearances`; *overshadowed appearance* from
`StrongPerfectGraphTheorem.Types.Overshadowed`; *balanced skew partition* from
`StrongPerfectGraphTheorem.Types.Decompositions`.

Encoding conventions:

* the paper's indices `1,2,3` are `0,1,2 : Fin 3`, so the triangles of a prism are
  `{a 0, a 1, a 2}` and `{b 0, b 1, b 2}` (this matches `Prisms.FormPrism`);
* a path (of the paper: an *induced* path) is the list of its vertices in order, and a
  track (a not-necessarily-induced path of a host graph) likewise;
* "a path in `G \ Y`" is a path of `G` none of whose vertices lies in `Y`.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S07

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Overshadowed StrongPerfectGraphTheorem.Types.Overshadowed.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **7.4** (printed p. 35)

PAPER: *"Let `G` be Berge, and for `1 ≤ i ≤ 3` let `Pᵢ` be a path of even length `≥ 2`, from
`aᵢ` to `bᵢ`, such that these three paths form a prism with triangles `A = {a₁, a₂, a₃}` and
`B = {b₁, b₂, b₃}`.  Let `P₁'` be a path from `a₁'` to `b₁`, such that `P₁', P₂, P₃` also
form a prism.  Let `y ∈ V(G)` have at least two neighbours in `A` and in `B`.  Then it also
has at least two neighbours in `{a₁', a₂, a₃}`."*

Notes on the transcription.

* *"`P₁', P₂, P₃` also form a prism"*: since `P₁'` has ends `a₁'` and `b₁` and `P₂, P₃` keep
  their ends, the triangles of that prism are `{a₁', a₂, a₃}` and `{b₁, b₂, b₃}`; the first
  is the family `![a₁', a 1, a 2] : Fin 3 → V`.
* *"`y` has at least two neighbours in `A` and in `B`"* is verbatim the §10 notion *major
  with respect to the prism* (`MajorForPrism`), so it is written that way; the conclusion
  concerns only the new triangle, and says that at least two of `a₁', a₂, a₃` are neighbours
  of `y`. -/
theorem thm_7_4 (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V) (P₁ P₂ P₃ : List V)
    (hprism : FormPrism G a b P₁ P₂ P₃)
    (heven₁ : Even (pathLength P₁)) (heven₂ : Even (pathLength P₂))
    (heven₃ : Even (pathLength P₃))
    (hlen₁ : 2 ≤ pathLength P₁) (hlen₂ : 2 ≤ pathLength P₂) (hlen₃ : 2 ≤ pathLength P₃)
    (a₁' : V) (P₁' : List V) (hP₁' : IsPathFrom G P₁' a₁' (b 0))
    (hprism' : FormPrism G ![a₁', a 1, a 2] b P₁' P₂ P₃)
    (y : V) (hy : MajorForPrism G a b y) :
    2 ≤ (({a₁', a 1, a 2} : Set V) ∩ G.neighborSet y).ncard := by
  exact StrongPerfectGraphTheorem.ProofLemmas.Thm74Proof.replacement_neighbors
    (R := ![P₁, P₂, P₃]) hG hprism heven₂ heven₃ hlen₂ hlen₃ hprism' hy


end SPGT

end StrongPerfectGraphTheorem.Statements.S07
