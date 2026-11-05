/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 7. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Overshadowed
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.UnsaturatedMajorPrismYieldsGlobalMinimalAntipath
public import StrongPerfectGraphTheorem.ProofLemmas.GlobalMinimalPrismAntipathThirdTriangleVertexComplete
public import StrongPerfectGraphTheorem.ProofLemmas.GlobalMinimalPrismAntipathOppositeTriangleCompleteAndEven
public import StrongPerfectGraphTheorem.ProofLemmas.GlobalMinimalPrismAntipathContradictsThm33

/-!
# Section 7 — Rung replacement

The five numbered statements 7.1–7.5 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 34–39).

All defined terms are imported and never restated: *track*, *`k`-connected* from
`StrongPerfectGraphTheorem.Types.Tracks`; *prism* / *form a prism* / *long* and the §10 notions
*saturates* and *major with respect to a prism* from `StrongPerfectGraphTheorem.Types.Prisms`;
*Berge*, *anticonnected*, *path*, *length*, *`Y`-complete* from `StrongPerfectGraphTheorem.Types.Core`;
*appearance*, *(non)degenerate appearance*, *`J`-enlargement* from
`StrongPerfectGraphTheorem.Types.Appearances`; *overshadowed appearance* from
`StrongPerfectGraphTheorem.Types.Overshadowed`; *balanced skew partition* from
`StrongPerfectGraphTheorem.Types.Decompositions`.

Encoding conventions:

* the paper's indices `1,2,3` are `0,1,2 : Fin 3`, so the triangles of a prism are
  `{a 0, a 1, a 2}` and `{b 0, b 1, b 2}` (this matches `Prisms.FormPrism`);
* a path (of the paper: an *induced* path) is the list of its vertices in order, and a
  track (a not-necessarily-induced path of a host graph) likewise;
* "a path in `G \ Y`" is a path of `G` none of whose vertices lies in `Y`.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S07

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Overshadowed StrongPerfectGraphTheorem.Types.Overshadowed.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **7.3** (printed p. 35)

PAPER: *"Let `G` be Berge, let `Y ⊆ V(G)` be anticonnected, and for `i = 1, 2, 3` let
`aᵢ-Pᵢ-bᵢ` be a path in `G \ Y`, forming a prism with triangles `{a₁, a₂, a₃}`,
`{b₁, b₂, b₃}`.  Assume `P₁, P₂, P₃` all have length `> 1`, and that every vertex in `Y` is
adjacent to at least two of `a₁, a₂, a₃` and to at least two of `b₁, b₂, b₃`.  Then at least
two of `a₁, a₂, a₃` and at least two of `b₁, b₂, b₃` are `Y`-complete."*

Notes on the transcription.

* *"`aᵢ-Pᵢ-bᵢ` is a path in `G \ Y`"*: `Pᵢ` is a path of `G` with ends `aᵢ, bᵢ` (which is
  part of `FormPrism`) none of whose vertices lies in `Y`.
* *"every vertex in `Y` is adjacent to at least two of `a₁, a₂, a₃` and to at least two of
  `b₁, b₂, b₃`"* is verbatim the §10 notion *major with respect to the prism*
  (`MajorForPrism`, i.e. the neighbour set *saturates* the prism), so it is written that way.
* Likewise the conclusion *"at least two of `a₁, a₂, a₃` and at least two of `b₁, b₂, b₃`
  are `Y`-complete"* says that the set of `Y`-complete vertices *saturates* the prism. -/
theorem thm_7_3 (G : SimpleGraph V) (hG : Berge G) (Y : Set V) (hY : AnticonnectedSet G Y)
    (a b : Fin 3 → V) (P₁ P₂ P₃ : List V)
    (hprism : FormPrism G a b P₁ P₂ P₃)
    (hP₁ : ∀ v ∈ P₁, v ∉ Y) (hP₂ : ∀ v ∈ P₂, v ∉ Y) (hP₃ : ∀ v ∈ P₃, v ∉ Y)
    (hlen₁ : 1 < pathLength P₁) (hlen₂ : 1 < pathLength P₂) (hlen₃ : 1 < pathLength P₃)
    (hYmajor : ∀ y ∈ Y, MajorForPrism G a b y) :
    SaturatesPrism a b {v : V | VertexComplete G v Y} := by
  classical
  by_contra hunsaturated
  let P : Fin 3 → List V := ![P₁, P₂, P₃]
  have hprismP : FormPrism G a b (P 0) (P 1) (P 2) := by
    simpa [P] using hprism
  have hPoutside : ∀ i v, v ∈ P i → v ∉ Y := by
    intro i v hv
    fin_cases i
    · exact hP₁ v (by simpa [P] using hv)
    · exact hP₂ v (by simpa [P] using hv)
    · exact hP₃ v (by simpa [P] using hv)
  have hPlength : ∀ i, 1 < pathLength (P i) := by
    intro i
    fin_cases i
    · simpa [P] using hlen₁
    · simpa [P] using hlen₂
    · simpa [P] using hlen₃
  rcases StrongPerfectGraphTheorem.ProofLemmas.UnsaturatedMajorPrismYieldsGlobalMinimalAntipath
      G Y a b P hY hprismP hPoutside hPlength hYmajor hunsaturated with
    ⟨σ, swapped, α, β, R, q, Q, hforward, hreverse, hprismR, hRoutside,
      hRlength, hYmajorR, hQshape, hQantipath, hqY, hα0, hα1, hminimal⟩
  exact StrongPerfectGraphTheorem.ProofLemmas.GlobalMinimalPrismAntipathContradictsThm33
    G hG Y α β R q Q hprismR hRoutside hRlength hYmajorR hQshape hQantipath
      hqY hα0 hα1 hminimal


end SPGT

end StrongPerfectGraphTheorem.Statements.S07
