/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 18. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Pseudowheels
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.ProofLemmas.Thm185Singleton

/-!
# Section 18 — Pseudowheels

The seven numbered statements 18.1 … 18.7 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages
109–116).

Every defined term used here already lives in an imported module; nothing is
restated:

* `StrongPerfectGraphTheorem.Types.Core` — `IsPathList`, `IsPathFrom`, `IsAntipathFrom`,
  `pathLength`, `SPGT.interior`, `VertexComplete`, `EdgeComplete`, `Complete`,
  `ConnectedSet`, `AnticonnectedSet`;
* `StrongPerfectGraphTheorem.Types.Tracks` — `IsTrackList` (§5's *track*: a **subgraph**, not
  necessarily induced), used in 18.1;
* `StrongPerfectGraphTheorem.Types.Appearances` — `attachments` (§5's *attachment*), used in 18.6;
* `StrongPerfectGraphTheorem.Types.Pseudowheels` — `IsPseudowheel`, `OptimalPseudowheel`;
* `StrongPerfectGraphTheorem.Types.Decompositions` — `AdmitsBalancedSkewPartition`;
* `StrongPerfectGraphTheorem.Types.LongOddPrism` — `Recalcitrant` (§13);
* `StrongPerfectGraphTheorem.Types.Classes` — `InF7`, `InF8` (the classes `F₇`, `F₈` of §1).

Encoding conventions:

* a *path* of the paper is the list `p : List V` of its vertices in order,
  together with `IsPathList G p`; its length is `pathLength p`, its interior is
  `SPGT.interior p` (always qualified — a bare `interior` is Mathlib's topological
  one), and `V(P)` is `{w : V | w ∈ p}`.  The paper's `n` is `p.length`;
* "`P` is a path of `G \ (X ∪ Y)`" is `IsPathList G p ∧ ∀ w ∈ p, w ∉ X ∪ Y`;
* **a subpath** of a path `P` is a contiguous block of the list, `q <:+: p`
  (`List.IsInfix`), which is automatically a path of `G` when it is non-null,
  since `P` is induced;
* **the number of `X`-complete edges of `P`.**  Paths of the paper are induced, so
  the edges of `P` are exactly the adjacent pairs of vertices of `P`, and their
  number is
  `{e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p, e = s(u, v) ∧ EdgeComplete G X u v}.ncard` —
  a set of *unordered* pairs, so each edge is counted exactly once (the
  convention already used in `StrongPerfectGraphTheorem.Statements.S02`);
* the paper's `pₙ₋₁`, `pₙ₋₂` are written `pn1`, `pn2` (the subscript minus `₋` is
  not a Lean identifier character), pinned down by `p.dropLast.getLast?` and
  `p.dropLast.dropLast.getLast?`;
* "have the same parity" is `a % 2 = b % 2`.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S18

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Pseudowheels StrongPerfectGraphTheorem.Types.Pseudowheels.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **18.5** (printed p. 111).

PAPER: *"Let `G ∈ F₇`, and let `(X,Y,P)` be an optimal pseudowheel in `G`, where
`P` is `p₁`-`⋯`-`pₙ`.  Let `v ∈ V(G) \ (X ∪ Y ∪ V(P))`, not `Y`-complete.  Then
there is a subpath `P'` of `P` such that*

* *`V(P')` contains all the neighbours of `v` in `P`,*

* *there is no `Y`-complete vertex in the interior of `P'`, and*

* *if `v` is `X`-complete, then either `V(P') = {p₁}`, or `pₙ ∈ V(P')`."*

Encoding notes.

* `p₁` and `pₙ` are the first and last vertices of `P`, named by `hhead`/`hlast`.
* *"a subpath `P'` of `P`"* is a contiguous block `q <:+: P` which is a path
  (`IsPathList G q`, so in particular non-null — the empty list is not a path of
  the paper). -/
theorem thm_18_5 (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V) (P : List V)
    (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (v : V) (hvXY : v ∉ X ∪ Y) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y) :
    ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
      (∀ w ∈ P, G.Adj v w → w ∈ q) ∧
      (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
      (VertexComplete G v X → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q)) := by
  exact Scratch186Singleton.singleton_good G hG X Y P p₁ pₙ v hopt hhead hlast
    hvXY hvP hvY


end SPGT

end StrongPerfectGraphTheorem.Statements.S18
