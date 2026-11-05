/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 16. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.Wheels
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.ProofLemmas.OddWheelAttachmentMain
public import StrongPerfectGraphTheorem.ProofLemmas.OddWheelAttachmentSetup
public import StrongPerfectGraphTheorem.ProofLemmas.OddWheelAttachmentAssembly
public import StrongPerfectGraphTheorem.ProofLemmas.OddWheelAttachmentClaim2
public import StrongPerfectGraphTheorem.ProofLemmas.OddWheelAttachmentEndgameSetup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm162ClaimThree
public import StrongPerfectGraphTheorem.ProofLemmas.Thm162ClaimFour
public import StrongPerfectGraphTheorem.ProofLemmas.Thm162Endgame

/-!
# Section 16 — Odd wheels

The three numbered statements 16.1 – 16.3 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published / *Annals* version; printed pages 96–102).
Every definition used here is imported, never restated:

* `StrongPerfectGraphTheorem.Types.Core` — `IsPathList`, `IsPathFrom`, `SPGT.interior`, `VertexComplete`,
  `EdgeComplete`, `ConnectedSet`
* `StrongPerfectGraphTheorem.Types.Wheels` — `IsWheel` (*rim* `C`, *hub* `Y`), `IsSegment`, `IsOddWheel`,
  `SameWheelParity`, `OppositeWheelParity` — the whole wheel vocabulary of the section
  preamble (printed p. 96)
* `StrongPerfectGraphTheorem.Types.Appearances` — `attachments` (printed p. 20: *"a vertex in `V(K)` is said
  to be an attachment of `F` … if it has a neighbour in `V(F)`"*)
* `StrongPerfectGraphTheorem.Types.Decompositions` — `AdmitsBalancedSkewPartition`
* `StrongPerfectGraphTheorem.Types.Classes` — `InF6`, `InF7`
* `StrongPerfectGraphTheorem.Types.LongOddPrism` — `Recalcitrant`

The section's own vocabulary is exactly *rim*, *hub*, *segment* / *`Y`-segment*, *odd wheel*
and *wheel-parity* (same / opposite); all of it lives in `StrongPerfectGraphTheorem.Types.Wheels`.  The two
further terms of the section — *"line"* and the *"optimality"* of `(C,Y)` — are introduced
inside the proof of 16.3 and are used nowhere else, so they are not part of any statement.

## Encoding conventions specific to this section

* The rim `C` is the list of the vertices of the hole in cyclic order; the paper's numbering
  *"`C` has vertices `p₁, …, pₙ` in order"* is that list, so `p_k` is `C[k-1]` and `V(C)` is
  `{w | w ∈ C}`.
* *"a path of `C`"* / *"a 3-vertex path `p₁-p₂-p₃` in `C`"* is a path of `G` whose vertices
  form a cyclically consecutive block of `C`, in either orientation, i.e.
  `∃ k, S <+: C.rotate k ∨ S.reverse <+: C.rotate k`; this is the convention of
  `StrongPerfectGraphTheorem.Types.Wheels.SPGT.IsSegment` for *"a path in a path or hole `H`"*.
* Because a hole is induced, an *edge* of a path or hole listed as `P` is exactly a pair of
  adjacent vertices of `P`; so *"there is a `Z`-complete edge in `P`"* is
  `∃ x ∈ P, ∃ y ∈ P, EdgeComplete G Z x y` (`EdgeComplete` already contains `G.Adj x y`).
* *"the neighbours of `v` in `C`"* is `{u | u ∈ C ∧ G.Adj v u}`, equivalently
  `G.neighborSet v ∩ {u | u ∈ C}`.
* `SPGT.interior` is always written with its `SPGT.` prefix (Mathlib's topological `interior`
  otherwise captures the bare name).

## Published vs. arXiv v1

* **16.2, third bullet** — the arXiv draft's bullet is ill-formed: it speaks of
  `{p₄, …, pₙ}` although no numbering of `C` has been fixed anywhere in the statement.  The
  published version repairs this by opening the bullet with *"we can number the vertices of `C`
  as `p₁, …, pₙ` in order, such that `p₁, p₂, p₃` are all `Y`-complete, and …"*.  **The
  published form is what is transcribed here**: naming a cyclically consecutive triple
  `p₁, p₂, p₃` of `C` *is* the numbering, and `{p₄, …, pₙ}` is then exactly the set of vertices
  of `C` other than `p₁, p₂, p₃`.  (A numbering "in order" may run either way round the cycle;
  both orientations are allowed, as they must be.  The two readings are in fact equivalent,
  since reversing a numbering reverses the path `p₁-f₁-⋯-f_k-p₃` as well.)
* **16.1** and **16.3** are word-for-word identical in the two versions (up to
  *"so that"* → *"such that"*).
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S16

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.Wheels StrongPerfectGraphTheorem.Types.Wheels.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **16.2** (printed p. 98)

PAPER: *"Let `G ∈ F₆`, and let `(C,Y)` be a wheel in `G`.  Let `F ⊆ V(G) \ (V(C) ∪ Y)` be
connected, such that no vertex in `F` is `Y`-complete.  Let `X ⊆ V(C)` be the set of
attachments of `F` in `C`.  Suppose that there exist vertices in `X` with opposite
wheel-parity, and there are two vertices in `X` that are nonadjacent.  Then either:*

*• there is a vertex `v ∈ F` such that `(C, Y ∪ {v})` is a wheel, or*

*• there is a vertex `v ∈ F` with at least four neighbours in `C`, and a 3-vertex path
`p₁-p₂-p₃` in `C`, such that `p₁, p₂, p₃` are all `Y ∪ {v}`-complete, and every other
neighbour of `v` in `C` has the same wheel-parity as `p₁`, or*

*• we can number the vertices of `C` as `p₁, …, pₙ` in order, such that `p₁, p₂, p₃` are all
`Y`-complete, and there is a path `p₁-f₁-⋯-f_k-p₃` with interior in `F`, such that there are
no edges between `{f₁, …, f_k}` and `{p₄, …, pₙ}`."*

This is the **published** third bullet (the arXiv draft's version of it is ill-formed; see the
module docstring).

Transcription notes.

* *"`X ⊆ V(C)` is the set of attachments of `F` in `C`"* is `X = attachments G F {u | u ∈ C}`,
  the printed-p.-20 notion: the vertices of `C` with a neighbour in `F`.
* *"there exist vertices in `X` with opposite wheel-parity"* and *"there are two vertices in
  `X` that are nonadjacent"* are two separate hypotheses, as printed (the second pair need not
  be the first pair).
* In the third bullet the numbering of `C` is captured by naming a cyclically consecutive
  triple `p₁, p₂, p₃` of the rim; `{p₄, …, pₙ}` is then the set of vertices of `C` other than
  `p₁, p₂, p₃`, and `{f₁, …, f_k}` is `SPGT.interior P` for the path `P = p₁-f₁-⋯-f_k-p₃`.
* The three alternatives appear in the order printed. -/
theorem thm_16_2 (G : SimpleGraph V) (hG : InF6 G)
    (C : List V) (Y : Set V) (hwheel : IsWheel G C Y)
    (F : Set V) (hFC : ∀ f ∈ F, f ∉ C) (hFY : ∀ f ∈ F, f ∉ Y)
    (hFconn : ConnectedSet G F) (hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y)
    (X : Set V) (hX : X = attachments G F {u : V | u ∈ C})
    (hopp : ∃ a ∈ X, ∃ b ∈ X, OppositeWheelParity G C Y a b)
    (hnonadj : ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ ¬ G.Adj a b) :
    (∃ v ∈ F, IsWheel G C (Y ∪ {v})) ∨
    (∃ v ∈ F, 4 ≤ (G.neighborSet v ∩ {u : V | u ∈ C}).ncard ∧
      ∃ p₁ p₂ p₃ : V, IsPathList G [p₁, p₂, p₃] ∧
        (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
        VertexComplete G p₁ (Y ∪ {v}) ∧ VertexComplete G p₂ (Y ∪ {v}) ∧
        VertexComplete G p₃ (Y ∪ {v}) ∧
        ∀ u ∈ C, G.Adj v u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁) ∨
    (∃ p₁ p₂ p₃ : V,
      (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
      VertexComplete G p₁ Y ∧ VertexComplete G p₂ Y ∧ VertexComplete G p₃ Y ∧
      ∃ P : List V, IsPathFrom G P p₁ p₃ ∧ (∀ x ∈ SPGT.interior P, x ∈ F) ∧
        ∀ x ∈ SPGT.interior P, ∀ u ∈ C, u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → ¬ G.Adj x u) := by
  subst hX
  exact StrongPerfectGraphTheorem.ProofLemmas.OddWheelAttachmentAssembly.concl_of_claims hG hwheel
    (StrongPerfectGraphTheorem.ProofLemmas.OddWheelAttachmentClaim2.claim_two G)
    (StrongPerfectGraphTheorem.ProofLemmas.Thm162ClaimThree.claim_three G)
    (StrongPerfectGraphTheorem.ProofLemmas.Thm162ClaimFour.claim_four G)
    (StrongPerfectGraphTheorem.ProofLemmas.OddWheelAttachmentEndgameSetup.endgame_of_contradiction
      (StrongPerfectGraphTheorem.ProofLemmas.Thm162Endgame.endgame_contradiction G))
    ⟨hFconn, hFC, hFY, hFnc, hopp, hnonadj⟩


end SPGT

end StrongPerfectGraphTheorem.Statements.S16
