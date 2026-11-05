/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 12. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Staircases
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.PathBasics
public import StrongPerfectGraphTheorem.ProofLemmas.Thm124Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm124Claim5
public import StrongPerfectGraphTheorem.ProofLemmas.Thm124Endgame

/-!
# Section 12 — Attachments in a staircase

The five numbered statements 12.1–12.5 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 69–77).

All the defined terms used here are imported and never restated: *step-connected strip*,
*left-star*, *right-star*, *banister*, *1-breaker*, *staircase*, `V(K)`, *maximal*, *local*,
*minor*, *major*, *left-diagonal*, *right-diagonal*, *central*, *strongly maximal* and
*2-breaker* come
from `StrongPerfectGraphTheorem.Types.Staircases`; *even prism* from `StrongPerfectGraphTheorem.Types.Prisms`; *attachment*,
*appearance* from `StrongPerfectGraphTheorem.Types.Appearances`; *Berge*, *connected set*, *antipath*,
*interior*, *complete*/*anticomplete* from `StrongPerfectGraphTheorem.Types.Core`; *balanced skew partition*
from `StrongPerfectGraphTheorem.Types.Decompositions`.

Encoding conventions:

* a staircase `K = (S = (A, C, B), a₀-R₀-b₀)` is carried by the six pieces of data
  `A C B : Set V`, `a₀ : V`, `R₀ : List V`, `b₀ : V`, in the paper's order; `V(S)` is
  `A ∪ B ∪ C` and `V(K)` is `staircaseVertices A C B R₀`;
* a path/antipath is the list of its vertices in order, `V(R)` for such a list `R` is
  `{v | v ∈ R}`, and `R₀ \ a₀` is `{x | x ∈ R₀ ∧ x ≠ a₀}`;
* *"`F` contains a path `u`-`R`-`v`"* is: `R` is a path of `G` from `u` to `v` all of whose
  vertices lie in `F`;
* *"there are no edges between `X` and `Y`"* is `SPGT.Anticomplete G X Y`;
* *"there is no appearance of `K₄` in `G`"* is `¬ Appears G (⊤ : SimpleGraph (Fin 4))`;
  *"no even prism in `G`"* is: no three paths of `G` form an even prism; *"no 1-breaker
  (2-breaker) in `G`"* is the negated existential over the data of a 1-breaker (2-breaker).

Published-vs-draft note: case 1 of **12.1** is the published one, *"`v` is minor; and in that
case, either `v` is a left-star or `v` is not `A`-complete, and either `v` is a right-star or
`v` is not `B`-complete"*; the arXiv v1 draft has only *"`v` is minor"*.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S12

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Staircases StrongPerfectGraphTheorem.Types.Staircases.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **12.4** (printed p. 74)

PAPER: *"Let `G` be a Berge graph, containing no appearance of `K₄`, no even prism, and no
1-breaker.  If there is a 2-breaker in `G` then `G` admits a balanced skew partition."*

A 2-breaker is a pair `(K, Q)` with `K = (S = (A, C, B), a₀`-`R₀`-`b₀)`, so *"there is a
2-breaker in `G`"* is the existence of the staircase data together with the set `Q`. -/
theorem thm_12_4 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (h2breaker : ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) (Q : Set V),
      IsTwoBreaker G A C B a₀ R₀ b₀ Q) :
    AdmitsBalancedSkewPartition G := by
  classical
  obtain ⟨A, C, B, a₀, R₀, b₀, Q, h⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm124Setup.exists_setup
      G hG hK4 hprism hbreaker h2breaker
  obtain ⟨b, hbB, hbQ⟩ := h.existsBComplete
  have hQne : Q.Nonempty := by
    by_contra hQempty
    apply h.a₀NotComplete
    intro q hq
    exact (hQempty ⟨q, hq⟩).elim
  have ha₀Q : a₀ ∉ Q :=
    h.notMemQ_of_mem a₀ (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.head_mem h.pathFrom.2.1)
  have hb₀Q : b₀ ∉ Q :=
    h.notMemQ_of_mem b₀ (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.getLast_mem h.pathFrom.2.2)
  have hb₀att : ∃ z ∈ B ∪ C, G.Adj b₀ z :=
    ⟨b, Or.inl hbB, h.rightStar.2.1 b hbB⟩
  exact StrongPerfectGraphTheorem.ProofLemmas.Thm124Endgame.thm124Endgame
    G hG A B C Q a₀ b₀ hQne ha₀Q h.a₀NotComplete hb₀Q h.b₀NotComplete
      h.leftStar.2.1 hb₀att b hbB hbQ
      (StrongPerfectGraphTheorem.ProofLemmas.Thm124Claim5.claim5 h)


end SPGT

end StrongPerfectGraphTheorem.Statements.S12
