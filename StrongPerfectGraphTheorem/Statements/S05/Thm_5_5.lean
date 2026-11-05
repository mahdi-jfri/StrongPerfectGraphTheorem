/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 5. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.ProofLemmas.Thm55Reduction
public import StrongPerfectGraphTheorem.ProofLemmas.Thm55Structure
public import StrongPerfectGraphTheorem.ProofLemmas.Thm55BranchReach

/-!
# Section 5 — Small attachments to a line graph

The eight numbered statements 5.1 – 5.8 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published / *Annals* version; printed pages 18–28).
Every definition used here is imported, never restated:

* `StrongPerfectGraphTheorem.Types.Core` — `Berge`, `IsPathFrom`, `pathLength`, `ConnectedSet`, …
* `StrongPerfectGraphTheorem.Types.Tracks` — `IsTrackList`, `trackLength`, `trackEdges`, `IsTrackFrom`,
  `branchVertices`, `IsBranch`, `incidentEdges` (`= δ_H(v)`), `IsSubdivision`,
  `IsBipartiteSubdivision`, `IsKConnected`, `CyclicallyThreeConnected`, `DifferentBiparity`
* `StrongPerfectGraphTheorem.Types.Appearances` — `IsAppearance`, `Appears`, `DegenerateK4Appearance`,
  `DegenerateAppearance`, `NondegenerateAppearance`, `IsJEnlargement`, `SaturatesLineGraph`,
  `LocalForLineGraph`, `MajorForLineGraph`, `attachments`
* `StrongPerfectGraphTheorem.Types.Decompositions` — `AdmitsProper2Join`, `AdmitsBalancedSkewPartition`
* `StrongPerfectGraphTheorem.Types.BasicClasses` — `IsLineGraphOfBipartite`

## Encoding conventions specific to this section

* `K₄` is `(⊤ : SimpleGraph (Fin 4))` and `K₃,₃` is `completeBipartiteGraph (Fin 3) (Fin 3)`;
  "`A = B`" for two graphs on different vertex types is `Nonempty (A ≃g B)`.
* A track is the list `q` of its vertices in order, so `E(track) = trackEdges q`, its length
  is `trackLength q = q.length - 1`, and its ends are named by `IsTrackFrom`.  Consequently
  the paper's *"track of length ≥ k"* is the guard `k + 1 ≤ q.length`; this guard is written
  as an existential binder `(_hq : k + 1 ≤ q.length)` so that the `getElem` side conditions
  for the first edge `s(q[0], q[1])` and the last edge `s(q[q.length-2], q[q.length-1])` are
  discharged automatically.
* *"`V(J)` is the set of branch-vertices of `H`"* and *"the branches of `H` are in 1-1
  correspondence with the edges of `J`"* (printed p. 20) are used to render *"vertex of `J`"*
  as `branchVertices H` and *"edge `b₁b₂` of `J`"* as *"branch of `H` with ends `b₁, b₂`"*,
  exactly as in `Appearances.LocalForLineGraph`.  This avoids exposing the embedding
  `V(J) ⊆ V(H)` hidden inside `IsSubdivision`.
* For an appearance, `V(L(H))` is the vertex set `K ⊆ V(G)` of the induced subgraph, and the
  vertex of `G` corresponding to an edge `e` of `H` is `↑(φ ⟨e, he⟩)`, where
  `φ : H.lineGraph ≃g G.induce K` is the isomorphism carried by the appearance.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S05

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.BasicClasses.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **5.5** (printed p. 21)

PAPER: *"Let `H` be cyclically 3-connected, and let `C, D` be subgraphs with `C ∪ D = H`,
`|V(C ∩ D)| ≤ 2`, and `V(C), V(D) ≠ V(H)`.  Then one of `C, D` is contained in a branch of
`H`."*

(The paper adds immediately after: *"The proof is clear."*)

Transcription notes.

* `C, D` are `SimpleGraph.Subgraph`s of `H`; `C ∪ D` is `C ⊔ D` and *"`= H`"* is `= ⊤`;
  `C ∩ D` is `C ⊓ D`, whose vertex set is `C.verts ∩ D.verts`; and `V(H) = Set.univ`.
* *"`C` is contained in a branch of `H`"*: a branch is a track, given by the list `q` of its
  vertices, so containment is `C.verts ⊆ V(q)` together with `C.edgeSet ⊆ trackEdges q`. -/
theorem thm_5_5 {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    (hc3 : CyclicallyThreeConnected H) (C D : H.Subgraph)
    (hunion : C ⊔ D = ⊤) (hcap : (C ⊓ D).verts.ncard ≤ 2)
    (hCne : C.verts ≠ Set.univ) (hDne : D.verts ≠ Set.univ) :
    (∃ q : List W, IsBranch H q ∧ C.verts ⊆ {v : W | v ∈ q} ∧ C.edgeSet ⊆ trackEdges q) ∨
    (∃ q : List W, IsBranch H q ∧ D.verts ⊆ {v : W | v ∈ q} ∧ D.edgeSet ⊆ trackEdges q) := by
  apply StrongPerfectGraphTheorem.ProofLemmas.Thm55Reduction.reduce H hc3 C D hunion hcap hCne hDne
  · intro x y hxb hyb hx hy
    exact StrongPerfectGraphTheorem.ProofLemmas.Thm55BranchReach.branch_rchIn_compl_of_ncard_le_two
      hc3 (C.verts ∩ D.verts) hcap hxb hyb hx hy
  · intro E hEne hES hEcl hEnb
    exact StrongPerfectGraphTheorem.ProofLemmas.Thm55Structure.branchless_side_contained
      H hc3 (C.verts ∩ D.verts) E hcap hEne hES hEcl hEnb


end SPGT

end StrongPerfectGraphTheorem.Statements.S05
