module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.ProofLemmas.Thm56Core

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


/-- **5.6** (printed p. 21)

PAPER: *"Let `c₁, c₂` be nonadjacent vertices of a graph `H`, such that `H \ {c₁, c₂}` is
connected.  For `i = 1, 2`, let the edges incident with `cᵢ` be partitioned into two sets
`Aᵢ, Bᵢ`, where `A₁, A₂` are both nonempty and at least one of `B₁, B₂` is nonempty.  Assume
that for every edge `uv ∈ A₁ ∪ A₂`, `H \ {u, v}` is connected, and that no vertex of `V(H)`
is incident with all edges in `A₁ ∪ A₂`.  Then one of the following holds:*

*1. there is a track in `H` with first edge in `A₁`, second edge in `B₁` (and hence second
vertex `c₁`), last vertex `c₂` and last edge in `A₂`, or*

*2. there is a track in `H` with first edge in `A₂`, second edge in `B₂` (and hence second
vertex `c₂`), last vertex `c₁` and last edge in `A₁`."*

Transcription notes.

* *"the edges incident with `cᵢ` are partitioned into two sets `Aᵢ, Bᵢ`"*: `Aᵢ ∪ Bᵢ = δ_H(cᵢ)`
  and `Aᵢ, Bᵢ` are disjoint.  Empty parts are allowed — the paper separately demands that
  `A₁, A₂` be nonempty and that at least one of `B₁, B₂` be nonempty.
* *"`H \ S` is connected"* is `ConnectedSet H Sᶜ`, following the paper's own convention that
  a set `X` is connected when `H|X` is connected (so `∅` counts as connected).
* A track is the list `q` of its vertices in order; the guard `3 ≤ q.length` (equivalently
  `2 ≤ trackLength q`) is exactly what it means for the track to *have* a second edge, and is
  needed for `s(q[1], q[2])` to be well-formed.  The first edge is `s(q[0], q[1])`, the second
  is `s(q[1], q[2])`, the last vertex is `q.getLast?` and the last edge is
  `s(q[q.length-2], q[q.length-1])`.
* The parenthetical *"(and hence second vertex `c₁`)"* is flagged by the paper as a
  consequence of the first two conditions, not as an extra requirement, so it is not a
  conjunct. -/
theorem thm_5_6 {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (c₁ c₂ : W)
    (hnadj : ¬ H.Adj c₁ c₂)
    (hconn : ConnectedSet H (({c₁, c₂} : Set W)ᶜ))
    (A₁ B₁ A₂ B₂ : Set (Sym2 W))
    (hpart₁ : A₁ ∪ B₁ = incidentEdges H c₁) (hdisj₁ : Disjoint A₁ B₁)
    (hpart₂ : A₂ ∪ B₂ = incidentEdges H c₂) (hdisj₂ : Disjoint A₂ B₂)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB : B₁.Nonempty ∨ B₂.Nonempty)
    (hAconn : ∀ e ∈ A₁ ∪ A₂, ∀ u v : W, e = s(u, v) → ConnectedSet H (({u, v} : Set W)ᶜ))
    (hnocover : ¬ ∃ w : W, ∀ e ∈ A₁ ∪ A₂, w ∈ e) :
    (∃ (q : List W) (_hq : 3 ≤ q.length),
      IsTrackList H q ∧
      s(q[0], q[1]) ∈ A₁ ∧ s(q[1], q[2]) ∈ B₁ ∧
      q.getLast? = some c₂ ∧ s(q[q.length - 2], q[q.length - 1]) ∈ A₂) ∨
    (∃ (q : List W) (_hq : 3 ≤ q.length),
      IsTrackList H q ∧
      s(q[0], q[1]) ∈ A₂ ∧ s(q[1], q[2]) ∈ B₂ ∧
      q.getLast? = some c₁ ∧ s(q[q.length - 2], q[q.length - 1]) ∈ A₁) := by
  simpa only [StrongPerfectGraphTheorem.ProofLemmas.Thm56Basics.Outcome] using
    StrongPerfectGraphTheorem.ProofLemmas.Thm56Core.conclusion H c₁ c₂ hnadj hconn A₁ B₁ A₂ B₂
      hpart₁ hdisj₁ hpart₂ hdisj₂ hA₁ hA₂ hB hAconn hnocover


end SPGT

end StrongPerfectGraphTheorem.Statements.S05
