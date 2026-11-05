/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 4. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.SkewTools
public import StrongPerfectGraphTheorem.ProofLemmas.AnticomponentOfSkewSideBasics
public import StrongPerfectGraphTheorem.ProofLemmas.ComponentsOfSetBasics
public import StrongPerfectGraphTheorem.ProofLemmas.ConnectedSetUnionAttach
public import StrongPerfectGraphTheorem.ProofLemmas.Thm46AntipathPairCase
public import StrongPerfectGraphTheorem.ProofLemmas.Thm46PathPairCase
public import StrongPerfectGraphTheorem.ProofLemmas.Thm46Step1First
public import StrongPerfectGraphTheorem.ProofLemmas.Thm46Step1Other
public import StrongPerfectGraphTheorem.Statements.S04.Thm_4_2
public import StrongPerfectGraphTheorem.Statements.S04.Thm_4_4

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


/-- **4.6** (printed p. 17)

PAPER: *"Let `(A,B)` be a skew partition of a Berge graph `G`, and let `W` be a kernel for it.
Let `A₁` be a component of `A`, and suppose that*

*• every pair of nonadjacent vertices of `W` with neighbours in `A₁` are joined by an even
path with interior in `A`*

*• every pair of adjacent vertices of `A₁` with nonneighbours in `W` are joined by an even
antipath with interior in `B`.*

*Then `G` admits a balanced skew partition."*

Transcription notes.

* This is the **published** form.  The arXiv v1 draft asked for the even path to have
  interior in `A₁` and the even antipath to have interior in `W`; the published paper asks
  only for interior in `A`, resp. in `B`.  As `A₁ ⊆ A` and `W ⊆ B`, the published hypotheses
  are weaker and the published theorem is therefore strictly stronger; it is the published
  form that is transcribed.  (Consistently, the arXiv proof is one line and the published
  proof runs to a page.)
* *Kernel* is the printed-p.-17 notion (`SkewTools.IsKernel`): an anticonnected subset `W` of
  `B` such that some component of `A` contains no `W`-complete vertex.  It carries the
  standing context "`(A,B)` is a skew partition of `G`", which is also stated separately here
  as the paper does.
* *"a pair of nonadjacent vertices of `W` **with neighbours in `A₁`**"* means that each of the
  two vertices has a neighbour in `A₁`; *"a pair of adjacent vertices of `A₁` **with
  nonneighbours in `W`**"* means that each of the two has a nonneighbour in `W`. -/
theorem thm_4_6 (G : SimpleGraph V) (hG : Berge G) (A B W A₁ : Set V)
    (hAB : IsSkewPartition G A B)
    (hW : IsKernel G A B W)
    (hA₁ : IsComponent G A A₁)
    (hpath : ∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v →
      (∃ x ∈ A₁, G.Adj u x) → (∃ x ∈ A₁, G.Adj v x) →
      ∃ p : List V, IsPathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ A) ∧
        Even (pathLength p))
    (hantipath : ∀ u ∈ A₁, ∀ v ∈ A₁, G.Adj u v →
      (∃ w ∈ W, ¬ G.Adj u w) → (∃ w ∈ W, ¬ G.Adj v w) →
      ∃ p : List V, IsAntipathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ B) ∧
        Even (pathLength p)) :
    AdmitsBalancedSkewPartition G := by
  classical
  by_contra hcon
  obtain ⟨-, hWanti, hWB, A₀, hA₀, hnoWcomp⟩ := hW
  have hnl : ¬ IsLooseSkewPartition G A B := by
    intro hloose
    exact hcon (StrongPerfectGraphTheorem.Statements.S04.SPGT.thm_4_2 G hG ⟨A, B, hloose⟩)
  have hbal₁ : SPGT.Balanced G A₁ W :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm46Step1First.balanced_first hG hAB hWB hA₁
      hpath hantipath hcon
  have hbal : ∀ A' : Set V, IsComponent G A A' → SPGT.Balanced G A' W := by
    intro A' hA'
    exact StrongPerfectGraphTheorem.ProofLemmas.Thm46Step1Other.balanced_other hG hAB hWB hWanti hnl
      hA₁ hA' hbal₁ hpath hcon
  have hAne : A.Nonempty :=
    StrongPerfectGraphTheorem.Statements.S04.SPGT.Helpers42.nonempty_of_not_connected hAB.2.2.1
  have hA₀ne : A₀.Nonempty :=
    StrongPerfectGraphTheorem.ProofLemmas.ComponentsOfSetBasics.nonempty_of_isComponent G hAne hA₀
  obtain ⟨a₀, ha₀⟩ := hA₀ne
  have hWne : W.Nonempty := by
    have hn := hnoWcomp a₀ ha₀
    simp only [VertexComplete, not_forall] at hn
    obtain ⟨w, hw, -⟩ := hn
    exact ⟨w, hw⟩
  obtain ⟨w₀, hw₀⟩ := hWne
  obtain ⟨B₁, hB₁, hw₀B₁⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B (hWB hw₀)
  have hWB₁ : W ⊆ B₁ := by
    have hconn : ConnectedSet Gᶜ (W ∪ B₁) :=
      StrongPerfectGraphTheorem.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union
        hWanti hB₁.2.1 (Or.inl ⟨w₀, hw₀, hw₀B₁⟩)
    have heq : W ∪ B₁ = B₁ :=
      hB₁.2.2 (W ∪ B₁) Set.subset_union_right
        (Set.union_subset hWB hB₁.1) hconn
    intro w hw
    exact heq ▸ Or.inl hw
  obtain ⟨b₂, hb₂B, hb₂B₁⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.AnticomponentOfSkewSideBasics.sdiff_nonempty
      G hB₁ hAB.2.2.2
  obtain ⟨B₂, hB₂, hb₂B₂⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hb₂B
  have hB₂ne : B₂ ≠ B₁ := fun heq => hb₂B₁ (heq ▸ hb₂B₂)
  rcases StrongPerfectGraphTheorem.Statements.S04.SPGT.thm_4_4 G hG A B hAB with
    (hloose | hbalanced) | hallpath | hallantipath
  · exact hcon (StrongPerfectGraphTheorem.Statements.S04.SPGT.thm_4_2 G hG ⟨A, B, hloose⟩)
  · exact hcon ⟨A, B, hbalanced⟩
  · exact StrongPerfectGraphTheorem.ProofLemmas.Thm46PathPairCase.path_pair_case hG hAB hWanti hWB₁
      hB₁ hB₂ hB₂ne hA₀ hnoWcomp (hbal A₀ hA₀)
      (hallpath A₀ B₂ hA₀ hB₂)
  · exact StrongPerfectGraphTheorem.ProofLemmas.Thm46AntipathPairCase.antipath_pair_case hG hAB hWB
      hWanti hA₀ hnoWcomp (hbal A₀ hA₀) (hallantipath A₀ B₂ hA₀ hB₂) hcon


end SPGT

end StrongPerfectGraphTheorem.Statements.S04
