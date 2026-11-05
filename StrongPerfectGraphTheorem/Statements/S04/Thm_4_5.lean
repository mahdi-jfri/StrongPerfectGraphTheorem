/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 4. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.SkewTools
public import StrongPerfectGraphTheorem.Statements.S04.Thm_4_2
public import StrongPerfectGraphTheorem.Statements.S04.Thm_4_4
public import StrongPerfectGraphTheorem.ProofLemmas.AnticompleteUnionComponents
public import StrongPerfectGraphTheorem.ProofLemmas.BalancedNestedSetsExcludePairTypes

/-!
# Section 4 — Skew partitions

The six numbered statements 4.1 – 4.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published / *Annals* version; printed pages 14–18).
Every definition used here is imported, never restated:

* `StrongPerfectGraphTheorem.Types.Core` — `Berge`, `IsPathFrom`, `IsAntipathFrom`, `pathLength`,
  `SPGT.interior`, `IsComponent`, `IsAnticomponent`, `VertexComplete`,
  `VertexAnticomplete`, `Complete`, `Anticomplete`, `SPGT.Balanced`
* `StrongPerfectGraphTheorem.Types.Decompositions` — `IsSkewPartition`, `IsBalancedSkewPartition`,
  `AdmitsBalancedSkewPartition`
* `StrongPerfectGraphTheorem.Types.SkewTools` — `IsLooseSkewPartition`, `AdmitsLooseSkewPartition`,
  `IsPathPair`, `IsAntipathPair`, `IsKernel`

## Encoding conventions specific to this section

* A path / antipath is the list `p` of its vertices in order, with named ends via
  `IsPathFrom` / `IsAntipathFrom`; "with interior in `S`" is
  `∀ x ∈ SPGT.interior p, x ∈ S`; "odd" / "even" refer to `SPGT.pathLength p`, the number of
  edges.  (`SPGT.interior` and `SPGT.Balanced` are always written with their `SPGT.`
  prefix, since the bare names are captured by Mathlib's topological `interior` and by
  Mathlib's `Balanced` set-in-a-module predicate.)
* The paper's *"let `A₁,…,A_m` be the components of `A`, and `B₁,…,B_n` the anticomponents of
  `B`"* fixes an enumeration only in order to index the alternatives of 4.4 by `(i,j)`; since
  the published 4.4 quantifies over *all* `i,j`, the enumeration is rendered by universally
  quantifying over all components `A'` of `A` and all anticomponents `B'` of `B`.  (The
  published paper itself made this change: it indexes path/antipath pairs by the *sets*
  `(A_i,B_j)` rather than by the index pair `(i,j)`.)
* *"has only one vertex"* is `∃ a, S = {a}`.

## Published vs. arXiv v1

**4.6 is strictly stronger in the published version and it is the published form that is
transcribed here.**  The arXiv draft's hypotheses read *"joined by an even path with interior
in `A₁`"* and *"joined by an even antipath with interior in `W`"*; the published 4.6 reads
*"with interior in `A`"* and *"with interior in `B`"*.  Since `A₁ ⊆ A` and `W ⊆ B`, the
published hypotheses are weaker, hence the published theorem is stronger.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S04

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.SkewTools StrongPerfectGraphTheorem.Types.SkewTools.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **4.5** (printed p. 17)

PAPER: *"Let `G` be Berge.  Suppose that there is a partition of `V(G)` into four nonempty
sets `X,Y,L,R`, such that there are no edges between `L` and `R`, and `X` is complete to `Y`.
If either:*

*• some vertex in `X ∪ Y` has no neighbours in `L` or no neighbours in `R`, or*

*• some vertex in `L ∪ R` is complete to `X` or complete to `Y`, or*

*• `(L,Y)` is balanced*

*then `G` admits a balanced skew partition."*

Transcription notes.

* *"a partition of `V(G)` into four nonempty sets"* is: the four sets cover `V(G)`, are
  pairwise disjoint, and each is nonempty.
* *"there are no edges between `L` and `R`"* is `Anticomplete G L R`, and *"`X` is complete to
  `Y`"* is `Complete G X Y`.
* *"has no neighbours in `L`"* is `VertexAnticomplete G v L`; *"is complete to `X`"* is
  `VertexComplete G v X`.
* *"`(L,Y)` is balanced"* is the pair-balancedness of `Core`, with the sets in the printed
  order: no odd path between nonadjacent vertices of `Y` with interior in `L`, and no odd
  antipath between adjacent vertices of `L` with interior in `Y`.
* The three alternatives appear in the order printed. -/
theorem thm_4_5 (G : SimpleGraph V) (hG : Berge G) (X Y L R : Set V)
    (hcover : X ∪ Y ∪ L ∪ R = Set.univ)
    (hXY : Disjoint X Y) (hXL : Disjoint X L) (hXR : Disjoint X R)
    (hYL : Disjoint Y L) (hYR : Disjoint Y R) (hLR : Disjoint L R)
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hLne : L.Nonempty) (hRne : R.Nonempty)
    (hnoedge : Anticomplete G L R) (hcomplete : Complete G X Y)
    (h : (∃ v ∈ X ∪ Y, VertexAnticomplete G v L ∨ VertexAnticomplete G v R) ∨
         (∃ v ∈ L ∪ R, VertexComplete G v X ∨ VertexComplete G v Y) ∨
         SPGT.Balanced G L Y) :
    AdmitsBalancedSkewPartition G := by
  have hantiCompl : Anticomplete Gᶜ X Y := by
    intro x hx y hy hxy
    exact hxy.2 (hcomplete x hx y hy)
  obtain ⟨hAnconn, A_L, A_R, hALcomp, hALsub, hARcomp, hARsub⟩ :=
    StrongPerfectGraphTheorem.Types.AnticompleteUnionComponents.anticompleteUnionComponents
      G L R hLR hLne hRne hnoedge
  obtain ⟨hBnconn, B_X, B_Y, hBXcomp, hBXsub, hBYcomp, hBYsub⟩ :=
    StrongPerfectGraphTheorem.Types.AnticompleteUnionComponents.anticompleteUnionComponents
      Gᶜ X Y hXY hXne hYne hantiCompl
  have hcoverAB : (L ∪ R) ∪ (X ∪ Y) = Set.univ := by
    simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hcover
  have hdisjAB : Disjoint (L ∪ R) (X ∪ Y) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    rcases hzA with hzL | hzR <;> rcases hzB with hzX | hzY
    · exact Set.disjoint_left.1 hXL hzX hzL
    · exact Set.disjoint_left.1 hYL hzY hzL
    · exact Set.disjoint_left.1 hXR hzX hzR
    · exact Set.disjoint_left.1 hYR hzY hzR
  have hAB : IsSkewPartition G (L ∪ R) (X ∪ Y) := by
    refine ⟨hcoverAB, hdisjAB, hAnconn, ?_⟩
    simpa only [AnticonnectedSet] using hBnconn
  by_cases hloose : IsLooseSkewPartition G (L ∪ R) (X ∪ Y)
  · exact thm_4_2 G hG ⟨L ∪ R, X ∪ Y, hloose⟩
  · have hLY : Balanced G L Y := by
      rcases h with hfirst | hsecond | hbalanced
      · rcases hfirst with ⟨v, hvB, hvL | hvR⟩
        · exact (hloose ⟨hAB, Or.inl ⟨v, hvB, A_L, hALcomp,
            fun a ha => hvL a (hALsub ha)⟩⟩).elim
        · exact (hloose ⟨hAB, Or.inl ⟨v, hvB, A_R, hARcomp,
            fun a ha => hvR a (hARsub ha)⟩⟩).elim
      · rcases hsecond with ⟨v, hvA, hvX | hvY⟩
        · exact (hloose ⟨hAB, Or.inr ⟨v, hvA, B_X, hBXcomp,
            fun b hb => hvX b (hBXsub hb)⟩⟩).elim
        · exact (hloose ⟨hAB, Or.inr ⟨v, hvA, B_Y, hBYcomp,
            fun b hb => hvY b (hBYsub hb)⟩⟩).elim
      · exact hbalanced
    have hexclude :=
      StrongPerfectGraphTheorem.Types.BalancedNestedSetsExcludePairTypes.balancedNestedSetsExcludePairTypes
        G (L ∪ R) (X ∪ Y) L Y A_L B_Y hLY hALsub hBYsub
    rcases thm_4_4 G hG (L ∪ R) (X ∪ Y) hAB with
      (hloose' | hbalanced) | hallpath | hallantipath
    · exact (hloose hloose').elim
    · exact ⟨L ∪ R, X ∪ Y, hbalanced⟩
    · exact (hexclude.1 (hallpath A_L B_Y hALcomp hBYcomp)).elim
    · exact (hexclude.2 (hallantipath A_L B_Y hALcomp hBYcomp)).elim


end SPGT

end StrongPerfectGraphTheorem.Statements.S04
