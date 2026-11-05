/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 12. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Staircases
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.Thm125Case1
public import StrongPerfectGraphTheorem.ProofLemmas.Thm125Case2Finish
public import StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish
public import StrongPerfectGraphTheorem.ProofLemmas.Thm125Case4

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


/-- **12.5** (printed p. 77)

PAPER: *"Let `G` be a Berge graph, containing no appearance of `K₄`, no even prism, no
1-breaker and no 2-breaker.  Let `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` be a strongly maximal
staircase in `G`.  Let `q₁`-`⋯`-`q_k` be an antipath such that `q₂, …, q_{k-1}` are both left-
and right-diagonal, and `q₁` is left- and not right-diagonal, and `q_k` is right- and not
left-diagonal.  Then `q₁` is a left-star and `q_k` is a right-star."*

The antipath `q₁-⋯-q_k` is the list `q` of its vertices in order, with ends `q₁` and `q_k`;
`q₂, …, q_{k-1}` is its interior `SPGT.interior q`. -/
theorem thm_12_5 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (h2breaker : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' : V) (Q' : Set V),
      IsTwoBreaker G A' C' B' a₀' R₀' b₀' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ SPGT.interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧ ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧ ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk) :
    IsLeftStar G A C B q₁ ∧ IsRightStar G A C B qk := by
  by_cases hqa₀ : G.Adj q₁ a₀
  · by_cases hqkb₀ : G.Adj qk b₀
    · exact StrongPerfectGraphTheorem.ProofLemmas.Thm125Case1.case1 G hG hprism hbreaker
        A C B a₀ b₀ R₀ hK q q₁ qk hq hqint hq₁ hqk hqa₀ hqkb₀
    · exact StrongPerfectGraphTheorem.ProofLemmas.Thm125Case2Finish.case2 G hG hK4 hprism hbreaker
        A C B a₀ b₀ R₀ hK q q₁ qk hq hqint hq₁ hqk hqa₀ hqkb₀
  · by_cases hqkb₀ : G.Adj qk b₀
    · exact StrongPerfectGraphTheorem.ProofLemmas.Thm125Case4.case4 G hG hK4 hprism hbreaker
        A C B a₀ b₀ R₀ hK q q₁ qk hq hqint hq₁ hqk hqa₀ hqkb₀
    · exact StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish.case3 G hG hK4 hprism hbreaker
        h2breaker A C B a₀ b₀ R₀ hK q q₁ qk hq hqint hq₁ hqk hqa₀ hqkb₀


end SPGT

end StrongPerfectGraphTheorem.Statements.S12
