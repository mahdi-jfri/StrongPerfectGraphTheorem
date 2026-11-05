/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 5. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.ProofLemmas.Thm57Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm57Claim1
public import StrongPerfectGraphTheorem.ProofLemmas.Thm57Claim2
public import StrongPerfectGraphTheorem.ProofLemmas.Thm57Endgame
public import StrongPerfectGraphTheorem.ProofLemmas.Thm57FinalSentence

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


/-- **5.7** (printed p. 22)

PAPER: *"Let `H` be bipartite and cyclically 3-connected.  Let `X ⊆ E(H)`, such that there is
no track in `H` of even length `≥ 4`, with its end-edges in `X` and with no other edge in `X`.
Then either:*

*1. `X` saturates `L(H)`, or*

*2. there is a branch-vertex `b` of `H` with `X ⊆ δ(b)`, or*

*3. there is a branch `B` of `H` with `X ⊆ E(B)`, or*

*4. there is a branch `B` of `H` with ends `b₁, b₂` say, such that `X \ E(B) = δ(b₁) \ E(B)`,
or*

*5. there is a branch `B` of `H` of odd length with ends `b₁, b₂` say, such that*
*`X \ E(B) = (δ(b₁) ∪ δ(b₂)) \ E(B)`,*
*or*

*6. there are two vertices `c₁, c₂` of `H`, of different biparity and not in the same branch
of `H`, such that `X = δ(c₁) ∪ δ(c₂)`.*

*In particular, either statements 1 or 6 hold, or there are at most two branch-vertices of `H`
incident with more than one edge in `X`; and exactly two only if statement 5 holds."*

Transcription notes.

* This is the **published** one-hypothesis / six-alternative form (the arXiv v1 draft split it
  into two statements with different hypotheses and alternatives).
* The hypothesis: a track of even length `≥ 4` is a list `q` with `5 ≤ q.length` (equivalently
  `4 ≤ trackLength q`) and `Even (trackLength q)`; its end-edges are `s(q[0], q[1])` and
  `s(q[q.length-2], q[q.length-1])`; *"no other edge in `X`"* says every edge of the track
  other than those two is outside `X`.
* The final *"In particular …"* sentence is part of the statement (it is what the rest of the
  paper cites as 5.7.1–5.7.6), so the conclusion is the conjunction of the six-fold
  disjunction with that sentence.  *"branch-vertices of `H` incident with more than one edge
  in `X`"* is `{b ∈ branchVertices H | (δ_H(b) ∩ X).Nontrivial}`, and *"at most two"* /
  *"exactly two"* are stated with `Set.ncard`. -/
theorem thm_5_7 {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    (hbip : H.IsBipartite) (hc3 : CyclicallyThreeConnected H)
    (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotrack : ¬ ∃ (q : List W) (_hq : 5 ≤ q.length),
      IsTrackList H q ∧ Even (trackLength q) ∧
      s(q[0], q[1]) ∈ X ∧ s(q[q.length - 2], q[q.length - 1]) ∈ X ∧
      ∀ e ∈ trackEdges q, e ≠ s(q[0], q[1]) →
        e ≠ s(q[q.length - 2], q[q.length - 1]) → e ∉ X) :
    (SaturatesLineGraph H X ∨
     (∃ b ∈ branchVertices H, X ⊆ incidentEdges H b) ∨
     (∃ q : List W, IsBranch H q ∧ X ⊆ trackEdges q) ∨
     (∃ (q : List W) (b₁ b₂ : W), IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
       X \ trackEdges q = incidentEdges H b₁ \ trackEdges q) ∨
     (∃ (q : List W) (b₁ b₂ : W), IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
       Odd (trackLength q) ∧
       X \ trackEdges q = (incidentEdges H b₁ ∪ incidentEdges H b₂) \ trackEdges q) ∨
     (∃ c₁ c₂ : W, DifferentBiparity H c₁ c₂ ∧
       (¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
       X = incidentEdges H c₁ ∪ incidentEdges H c₂)) ∧
    ((SaturatesLineGraph H X ∨
      (∃ c₁ c₂ : W, DifferentBiparity H c₁ c₂ ∧
        (¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
        X = incidentEdges H c₁ ∪ incidentEdges H c₂)) ∨
     ({b ∈ branchVertices H | (incidentEdges H b ∩ X).Nontrivial}.ncard ≤ 2 ∧
      ({b ∈ branchVertices H | (incidentEdges H b ∩ X).Nontrivial}.ncard = 2 →
        ∃ (q : List W) (b₁ b₂ : W), IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
          Odd (trackLength q) ∧
          X \ trackEdges q =
            (incidentEdges H b₁ ∪ incidentEdges H b₂) \ trackEdges q))) := by
  have hnotrack' : StrongPerfectGraphTheorem.ProofLemmas.Thm57Setup.NoEvenTrack57 H X := hnotrack
  have hfirst : StrongPerfectGraphTheorem.ProofLemmas.Thm57Setup.Concl57 H X := by
    by_cases hsat : SaturatesLineGraph H X
    · exact Or.inl hsat
    by_cases htwo : StrongPerfectGraphTheorem.ProofLemmas.Thm57Setup.TwoDisjointEdges H X
    · by_cases hbranch : StrongPerfectGraphTheorem.ProofLemmas.Thm57Setup.SomeBranchMeetsAll H X
      · exact StrongPerfectGraphTheorem.ProofLemmas.Thm57Claim2.thm57Claim2
          H hbip hc3 X hXE hnotrack' htwo hbranch
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (StrongPerfectGraphTheorem.ProofLemmas.Thm57Endgame.thm57Endgame
            H hbip hc3 X hXE hnotrack' htwo hbranch hsat)))))
    · rcases StrongPerfectGraphTheorem.ProofLemmas.Thm57Claim1.thm57Claim1
        H hbip hc3 X hXE htwo with h2 | h3
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
  exact ⟨hfirst,
    StrongPerfectGraphTheorem.ProofLemmas.Thm57FinalSentence.thm57FinalSentence H hbip hc3 X hXE hfirst⟩


end SPGT

end StrongPerfectGraphTheorem.Statements.S05
