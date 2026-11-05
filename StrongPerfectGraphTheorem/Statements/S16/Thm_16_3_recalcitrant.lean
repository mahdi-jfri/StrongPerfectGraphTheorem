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
public import StrongPerfectGraphTheorem.Statements.S14.Thm_14_3_recalcitrant
public import StrongPerfectGraphTheorem.Statements.S16.Thm_16_3
public import StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas

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


/-- **16.3**, final sentence (printed p. 101) — the closing corollary of 16.3, stated on its own
because the paper asserts it of *every* recalcitrant graph, under no hypothesis.

PAPER: *"In particular, every recalcitrant graph belongs to `F₇`."*

`G` here is an arbitrary finite graph (unrelated to the `G ∈ F₆` of `thm_16_3`); *recalcitrant*
is the four-bullet notion of §13. -/
theorem thm_16_3_recalcitrant (G : SimpleGraph V) (hG : SPGT.Recalcitrant G) : SPGT.InF7 G := by
  -- Printed p. 91 (the closing sentence of 14.3): every recalcitrant graph is in `F₆`.
  have hF6 : SPGT.InF6 G :=
    _root_.StrongPerfectGraphTheorem.Statements.S14.SPGT.thm_14_3_recalcitrant G hG
  -- `F₆` is complement-closed, so `Ḡ ∈ F₆` as well; 16.3 is stated for `G` only, and
  -- `F₇` asks for the absence of odd wheels in `G` *and* in `Ḡ`.
  have hF6c : SPGT.InF6 Gᶜ :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.inF6_compl.mpr hF6
  -- The last bullet of *recalcitrant*: `G` admits no balanced skew partition — and
  -- neither does `Ḡ`, since balanced skew partitions are complement-invariant.
  have hbsp : ¬ SPGT.AdmitsBalancedSkewPartition G := hG.2.2.2.2
  have hbspc : ¬ SPGT.AdmitsBalancedSkewPartition Gᶜ := fun h =>
    hbsp (_root_.StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp h)
  -- 16.3: *"If there is an odd wheel in `G` then `G` admits a balanced skew partition."*
  exact ⟨hF6, fun h => hbsp (thm_16_3 G hF6 h), fun h => hbspc (thm_16_3 Gᶜ hF6c h)⟩


end SPGT

end StrongPerfectGraphTheorem.Statements.S16
