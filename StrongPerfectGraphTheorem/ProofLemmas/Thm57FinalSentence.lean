module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.ProofLemmas.Thm57Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm57FinalHelpers

/-!
# 5.7 — the final *"In particular …"* sentence

PAPER (printed p. 22, statement; p. 22, first paragraph of the proof):

> In particular, either statements 1 or 6 hold, or there are at most two branch-vertices of `H`
> incident with more than one edge in `X`; and exactly two only if statement 5 holds.
>
> *Proof.*  The second assertion (the final sentence) follows from the first, because if
> statements 2,3 or 4 hold then there is at most one branch-vertex incident with more than one
> edge in `X`; while if `B, b₁, b₂` are as in statement 5, then since `B` is odd, it follows
> that `b₁, b₂` have no common neighbour, and so no branch-vertex different from `b₁, b₂` is
> incident with more than one edge in `X`.

So this lemma is exactly *"the second assertion follows from the first"*.

Proof sketch per alternative, with the load-bearing details the printed sentence compresses.

* **2** (`X ⊆ δ(b)`): a second branch-vertex `b' ≠ b` incident with two edges of `X` would give
  two distinct edges each containing both `b` and `b'`, but `s(b,b')` is the only such edge.
  So `BigBranchVertices H X ⊆ {b}`.
* **3** (`X ⊆ E(B)`): a vertex incident with two edges of a track is an *internal* vertex of
  it, and internal vertices of a branch are not branch-vertices.  So `BigBranchVertices H X`
  is empty.
* **4** (`X \ E(B) = δ(b₁) \ E(B)`, `B` a branch with ends `b₁, b₂`): a branch-vertex `b ≠ b₁`
  incident with two edges of `X` has at most one of them in `E(B)` (it must be an *end* of `B`,
  since internal vertices are not branch-vertices, and an end carries one track-edge) and at
  most one in `δ(b₁)` (namely `s(b₁,b)`), so it has exactly one of each; hence `b = b₂`,
  `b₁b₂ ∈ E(H)`, and `s(b₁,b₂) ∉ E(B)`, i.e. `H` has *two* distinct branches with ends
  `b₁, b₂` — the single edge `b₁b₂` and `B`.  That contradicts the simplicity of the `J` of
  which `H` is a subdivision (the same *"since `J` is simple"* step the paper uses inside
  claim (2)).  So again `BigBranchVertices H X ⊆ {b₁}`.
* **5**: `B` odd and `H` bipartite make `b₁, b₂` of different biparity, so they have no common
  neighbour; a branch-vertex `b ∉ {b₁,b₂}` with two edges of `X` would need two edges among
  `E(B) ∪ δ(b₁) ∪ δ(b₂)` at `b`, and the same end/internal analysis leaves only
  `{s(b₁,b), s(b₂,b)}`, i.e. a common neighbour.  So `BigBranchVertices H X ⊆ {b₁,b₂}`,
  giving `ncard ≤ 2`, and `ncard = 2 → Stmt57_5` holds because `Stmt57_5` is the case
  hypothesis.
* **1** and **6** go into the left disjunct of `Concl57Final` unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm57FinalSentence

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **5.7, second assertion** — the *"In particular …"* sentence follows from the six-fold
disjunction. -/
theorem thm57FinalSentence (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (h : Concl57 H X) :
    Concl57Final H X := by
  exact Thm57FinalHelpers.final_from_alternatives H hbip hc3 X hXE h

end StrongPerfectGraphTheorem.ProofLemmas.Thm57FinalSentence
