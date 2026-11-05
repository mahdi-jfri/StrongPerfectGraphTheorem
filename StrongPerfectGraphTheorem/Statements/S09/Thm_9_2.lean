/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 9. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Overshadowed
public import StrongPerfectGraphTheorem.Types.Knots
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic
public import StrongPerfectGraphTheorem.ProofLemmas.Thm92LineGraph
public import StrongPerfectGraphTheorem.ProofLemmas.Thm92KnotDictionary

/-!
# Section 9 — Double split graphs

The seven numbered statements 9.1–9.7 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 47–56).

All defined terms are imported and never restated: *knot*, *the knot induces `K`*, *local* and
*resolves* with respect to a knot, *strip*, *rung*, *antistrip*, *parallel*, *co-parallel*,
*twist*, *striation*, *`V(L)`*, *local* and *resolves* with respect to a striation, *maximal
striation* from `StrongPerfectGraphTheorem.Types.Knots`; *Berge*, *path*, *antipath*, *length*, *interior*,
*anticomplete*, *connected set* from `StrongPerfectGraphTheorem.Types.Core`; *appearance*, *(non)degenerate
appearance*, *`J`-enlargement*, *`J` appears in `G`*, *saturates `L(H)`*, *local with respect
to `L(H)`*, *attachments* from `StrongPerfectGraphTheorem.Types.Appearances`; *overshadowed appearance* from
`StrongPerfectGraphTheorem.Types.Overshadowed`; *double split graph* from `StrongPerfectGraphTheorem.Types.BasicClasses`;
*proper 2-join* and *balanced skew partition* from `StrongPerfectGraphTheorem.Types.Decompositions`.

Encoding conventions:

* paths and antipaths are the lists of their vertices in order, so `V(P)` is `{v | v ∈ P}`,
  and `P \ a` is `{v | v ∈ P} \ {a}`;
* `K₄` is `(⊤ : SimpleGraph (Fin 4))`, `K₃,₃` is `completeBipartiteGraph (Fin 3) (Fin 3)`, and
  the paper's `Ḡ` is `Gᶜ`;
* an *appearance* `L(H)` of `J` in `G` is the pair `(H, K)` of a bipartite subdivision `H` of
  `J` and the induced subgraph `G|K` that `L(H)` is isomorphic to, together (where a notion
  has to cross between the two sides) with the identification `φ : H.lineGraph ≃g G.induce K`;
* "there is a graph `X` such that …" is `∃ (n : ℕ) (X : SimpleGraph (Fin n)), …`.

**Naming the ends of a knot.**  `Knots.IsKnot` existentially quantifies the eight end labels
`a₁,b₁,a₂,b₂,x₁,y₁,x₂,y₂`, as the paper does (*"we can label the ends … such that"*).  Those
labels are nevertheless *uniquely determined* by the four lists, since `IsKnot` fixes them by
`IsPathFrom G P₁ a₁ b₁`, …, i.e. as the heads and last entries of the lists.  Statements 9.2
and 9.3, whose text refers to the labels, therefore name them by the extra hypotheses
`IsPathFrom G P₁ a₁ b₁` etc.; this is the paper's own *"Define `aᵢ, bᵢ, xᵢ, yᵢ` `(i = 1,2)` as
usual"* (the opening sentence of the proofs of 9.1 and 9.3) and adds no content.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S09

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Overshadowed StrongPerfectGraphTheorem.Types.Overshadowed.SPGT
open StrongPerfectGraphTheorem.Types.Knots StrongPerfectGraphTheorem.Types.Knots.SPGT
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.BasicClasses.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **9.2** (printed p. 48)

PAPER: *"Let `(P₁,P₂,Q₁,Q₂)` be a knot in a graph `G`, inducing `K`, where `Q₁,Q₂` both have
length 1, and so `K = L(H)` is an appearance of `K₄`.  Let `X ⊆ V(K)`.  Then:*

*• `X` is local with respect to the knot if and only if it is local with respect to `L(H)`*

*• `X` resolves the knot if and only if `X` saturates `L(H)` and `X` meets both `V(P₁)` and
`V(P₂)`."*

(The paper adds: *"The proof is obvious and we omit it."*)

Notes on the transcription.

* *"and so `K = L(H)` is an appearance of `K₄`"* is flagged by the paper as a **consequence**
  of the preceding hypotheses; but the statement needs a name for `H`, so `H` and the
  identification `φ : H.lineGraph ≃g G.induce K` are given as data together with the
  hypothesis `IsAppearance G K₄ H K` that they do form an appearance.  Since that hypothesis
  is implied by the others, this is an equivalent statement.
* The two §5 notions on the right-hand sides — *local with respect to `L(H)`*
  (`Appearances.LocalForLineGraph`) and *saturates `L(H)`*
  (`Appearances.SaturatesLineGraph`) — are conditions on a set of **edges of `H`**, those
  being the vertices of `L(H)`.  Under `φ`, the set `X` of vertices of `G` corresponds to the
  set of edges `e` of `H` with `φ e ∈ X`, which is what they are applied to.
* *"`X` meets both `V(P₁)` and `V(P₂)`"* is nonemptiness of the two intersections. -/
theorem thm_9_2 (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hQ₁ : pathLength Q₁ = 1) (hQ₂ : pathLength Q₂ = 1)
    (n : ℕ) (H : SimpleGraph (Fin n)) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (X : Set V) (hX : X ⊆ K) :
    (LocalForKnot G P₁ P₂ Q₁ Q₂ X ↔
      LocalForLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X}) ∧
    (ResolvesKnot G P₁ P₂ Q₁ Q₂ X ↔
      (SaturatesLineGraph H
          {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} ∧
        (X ∩ {v : V | v ∈ P₁}).Nonempty ∧ (X ∩ {v : V | v ∈ P₂}).Nonempty)) := by
  classical
  let E : Set (Sym2 (Fin n)) :=
    {e | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X}
  let X' : Set (↥K) := {v | (v : V) ∈ X}
  have hE : E ⊆ H.edgeSet := by
    intro e he
    exact he.choose
  have himage : φ '' StrongPerfectGraphTheorem.ProofLemmas.Thm92LineGraph.edgeSubtypeSet H E = X' := by
    ext v
    constructor
    · rintro ⟨e, he, rfl⟩
      change (e : Sym2 (Fin n)) ∈ E at he
      obtain ⟨he', hx⟩ := he
      have heq : (⟨(e : Sym2 (Fin n)), he'⟩ : H.edgeSet) = e := Subtype.ext rfl
      change (↑(φ e) : V) ∈ X
      simpa [heq] using hx
    · intro hv
      refine ⟨φ.symm v, ?_, φ.apply_symm_apply v⟩
      change ((φ.symm v : H.edgeSet) : Sym2 (Fin n)) ∈ E
      refine ⟨(φ.symm v).property, ?_⟩
      change (v : V) ∈ X at hv
      simpa using hv
  have hsub := happ.1.1
  have hbip := happ.1.2
  have hlocalIso :
      StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.IntrinsicLocal (G.induce K) X' ↔
        StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.IntrinsicLocal H.lineGraph
          (StrongPerfectGraphTheorem.ProofLemmas.Thm92LineGraph.edgeSubtypeSet H E) := by
    rw [← himage]
    exact StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.intrinsicLocal_image_iff φ _
  have hsatIso :
      StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.IntrinsicSaturates (G.induce K) X' ↔
        StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.IntrinsicSaturates H.lineGraph
          (StrongPerfectGraphTheorem.ProofLemmas.Thm92LineGraph.edgeSubtypeSet H E) := by
    rw [← himage]
    exact StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.intrinsicSaturates_image_iff φ _
  change (LocalForKnot G P₁ P₂ Q₁ Q₂ X ↔ LocalForLineGraph H E) ∧
    (ResolvesKnot G P₁ P₂ Q₁ Q₂ X ↔
      SaturatesLineGraph H E ∧ (X ∩ {v : V | v ∈ P₁}).Nonempty ∧
        (X ∩ {v : V | v ∈ P₂}).Nonempty)
  constructor
  · calc
      LocalForKnot G P₁ P₂ Q₁ Q₂ X ↔
          StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.IntrinsicLocal (G.induce K) X' :=
        StrongPerfectGraphTheorem.ProofLemmas.Thm92KnotDictionary.localForKnot_iff_intrinsic
          G P₁ P₂ Q₁ Q₂ hknot K hK hQ₁ hQ₂ X hX
      _ ↔ StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.IntrinsicLocal H.lineGraph
          (StrongPerfectGraphTheorem.ProofLemmas.Thm92LineGraph.edgeSubtypeSet H E) := hlocalIso
      _ ↔ LocalForLineGraph H E :=
        (StrongPerfectGraphTheorem.ProofLemmas.Thm92LineGraph.localForLineGraph_iff_intrinsic
          hsub hbip E hE).symm
  · calc
      ResolvesKnot G P₁ P₂ Q₁ Q₂ X ↔
          StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.IntrinsicSaturates (G.induce K) X' ∧
            (X ∩ {v : V | v ∈ P₁}).Nonempty ∧
            (X ∩ {v : V | v ∈ P₂}).Nonempty :=
        StrongPerfectGraphTheorem.ProofLemmas.Thm92KnotDictionary.resolvesKnot_iff_intrinsic
          G P₁ P₂ Q₁ Q₂ hknot K hK hQ₁ hQ₂ X hX
      _ ↔ StrongPerfectGraphTheorem.ProofLemmas.Thm92Intrinsic.IntrinsicSaturates H.lineGraph
            (StrongPerfectGraphTheorem.ProofLemmas.Thm92LineGraph.edgeSubtypeSet H E) ∧
          (X ∩ {v : V | v ∈ P₁}).Nonempty ∧
          (X ∩ {v : V | v ∈ P₂}).Nonempty := and_congr hsatIso Iff.rfl
      _ ↔ SaturatesLineGraph H E ∧
          (X ∩ {v : V | v ∈ P₁}).Nonempty ∧
          (X ∩ {v : V | v ∈ P₂}).Nonempty := and_congr
        (StrongPerfectGraphTheorem.ProofLemmas.Thm92LineGraph.saturatesLineGraph_iff_intrinsic
          hsub hbip E).symm Iff.rfl


end SPGT

end StrongPerfectGraphTheorem.Statements.S09
