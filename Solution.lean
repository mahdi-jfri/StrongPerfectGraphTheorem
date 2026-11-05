module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import StrongPerfectGraphTheorem.MathlibForm

/-!
# The Strong Perfect Graph Theorem, proved

This file repeats the definitions of `Challenge.lean` word for word and proves its theorem. The
proof is `StrongPerfectGraphTheorem.MathlibForm.strong_perfect_graph_theorem`, which is the
library's main theorem `StrongPerfectGraphTheorem.MainTheorem.SPGT.thm_1_2` restated with
Mathlib's notions.
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
    G.IsPerfect ↔ G.IsBerge :=
  StrongPerfectGraphTheorem.MathlibForm.strong_perfect_graph_theorem G

end SimpleGraph
