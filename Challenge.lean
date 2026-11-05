module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# The Strong Perfect Graph Theorem

A graph is *perfect* if every induced subgraph can be colored with as many colors as the size of
its largest clique. A *hole* is an induced cycle of length at least four, and an *antihole* is an
induced subgraph whose complement is a hole. A graph is *Berge* if it has no hole of odd length
and no antihole of odd length.

Berge conjectured in 1961 that a graph is perfect exactly when it is Berge. Chudnovsky,
Robertson, Seymour and Thomas proved this in *The strong perfect graph theorem*, Annals of
Mathematics 164 (2006), 51–229. This file states the theorem for finite graphs, with `sorry`.
`Solution.lean` proves it.

The definitions below use Mathlib's notions only:

* `SimpleGraph.induce X G` is the subgraph of `G` induced on the vertex set `X`;
* `SimpleGraph.chromaticNumber` is the chromatic number, a value in `ℕ∞`;
* `SimpleGraph.cliqueNum` is the largest size of a clique;
* `SimpleGraph.cycleGraph n` is the cycle on the vertex set `Fin n`;
* `SimpleGraph.IsIndContained H G` says that `G` has an induced subgraph isomorphic to `H`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- A graph `G` is *perfect* if for every set `X` of vertices, the subgraph of `G` induced on `X`
has chromatic number equal to its clique number. -/
def IsPerfect (G : SimpleGraph V) : Prop :=
  ∀ X : Set V, (G.induce X).chromaticNumber = (G.induce X).cliqueNum

/-- `G` has an *odd hole*: for some odd `n ≥ 5`, the cycle on `n` vertices is isomorphic to an
induced subgraph of `G`. (An odd hole has odd length at least four, so at least five.) -/
def HasOddHole (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ Odd n ∧ (cycleGraph n).IsIndContained G

/-- A graph `G` is *Berge* if it has no odd hole and no odd antihole. An odd antihole of `G` is
an odd hole of the complement `Gᶜ`. -/
def IsBerge (G : SimpleGraph V) : Prop :=
  ¬ G.HasOddHole ∧ ¬ Gᶜ.HasOddHole

/-- **The Strong Perfect Graph Theorem** (Chudnovsky, Robertson, Seymour and Thomas). A finite
graph is perfect if and only if it is Berge. -/
theorem strong_perfect_graph_theorem [Finite V] (G : SimpleGraph V) :
    G.IsPerfect ↔ G.IsBerge := by
  sorry

end SimpleGraph
