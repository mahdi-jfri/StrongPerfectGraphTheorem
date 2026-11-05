module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Pseudowheels
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Statements.S16.Thm_16_3_recalcitrant
public import StrongPerfectGraphTheorem.Statements.S18.Thm_18_7
public import StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas

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


/-- **18.7**, final sentence (printed p. 115) — the closing corollary of 18.7,
stated on its own because the paper asserts it of *every* recalcitrant graph,
under no hypothesis.

PAPER: *"In particular, every recalcitrant graph belongs to `F₈`."*

Encoding notes.

* `G` is an arbitrary finite graph, unrelated to the `G ∈ F₇` of `thm_18_7`;
  *recalcitrant* is the four-bullet notion of §13.
* This sentence is genuinely stronger than the first, and is the form the rest of
  the paper uses.  `F₈` requires that **neither** `G` **nor** `Ḡ` contain a
  pseudowheel, whereas the first sentence produces a balanced skew partition only
  from a pseudowheel *in `G`*; the bridge is that recalcitrance is closed under
  complementation and excludes balanced skew partitions. -/
theorem thm_18_7_recalcitrant (G : SimpleGraph V) (hG : SPGT.Recalcitrant G) :
    SPGT.InF8 G := by
  -- Printed p. 114 (the closing sentence of 16.3): every recalcitrant graph is in `F₇`.
  have hF7 : SPGT.InF7 G :=
    _root_.StrongPerfectGraphTheorem.Statements.S16.SPGT.thm_16_3_recalcitrant G hG
  -- `F₇` is complement-closed; 18.7 is stated for `G` only, and `F₈` asks for the
  -- absence of pseudowheels in `G` *and* in `Ḡ`.
  have hF7c : SPGT.InF7 Gᶜ :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.inF7_compl.mpr hF7
  -- The last bullet of *recalcitrant*, and its complement form.
  have hbsp : ¬ SPGT.AdmitsBalancedSkewPartition G := hG.2.2.2.2
  have hbspc : ¬ SPGT.AdmitsBalancedSkewPartition Gᶜ := fun h =>
    hbsp (_root_.StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp h)
  -- 18.7: *"Let `G ∈ F₇`.  If it contains a pseudowheel then it admits a balanced
  -- skew partition."*
  exact ⟨hF7, fun h => hbsp (thm_18_7 G hF7 h), fun h => hbspc (thm_18_7 Gᶜ hF7c h)⟩


end SPGT

end StrongPerfectGraphTheorem.Statements.S18
