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
public import StrongPerfectGraphTheorem.ProofLemmas.Thm121Cases
public import StrongPerfectGraphTheorem.ProofLemmas.Thm121Symmetry
public import StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry
public import StrongPerfectGraphTheorem.ProofLemmas.MinimalNonlocalStaircaseAttachmentPath
public import StrongPerfectGraphTheorem.ProofLemmas.ACompleteStaircaseAttachmentPathForcesOutcome
public import StrongPerfectGraphTheorem.ProofLemmas.NonlocalStaircaseAttachmentPrismJumpForcesOutcome

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
set_option linter.unusedSectionVars false

namespace StrongPerfectGraphTheorem.Statements.S12

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Staircases StrongPerfectGraphTheorem.Types.Staircases.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem localForStaircase_swap (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (X : Set V) :
    LocalForStaircase A C B a₀ R₀ b₀ X ↔
      LocalForStaircase B C A b₀ R₀.reverse a₀ X := by
  simp only [LocalForStaircase, List.mem_reverse]
  constructor
  · rintro (h | h | h | h)
    · refine Or.inl (fun x hx => ?_)
      rcases h hx with (hxA | hxB) | hxC
      · exact Or.inl (Or.inr hxA)
      · exact Or.inl (Or.inl hxB)
      · exact Or.inr hxC
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  · rintro (h | h | h | h)
    · refine Or.inl (fun x hx => ?_)
      rcases h hx with (hxB | hxA) | hxC
      · exact Or.inl (Or.inr hxB)
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr hxC
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))

private theorem thm122Outcome_swap
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V) (F : Set V)
    (h :
      (∃ w ∈ F, MajorForStaircase G B C A b₀ R₀.reverse a₀ w) ∨
      (∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsBanister G B C A u R v ∧
        Anticomplete G {w : V | w ∈ R} {w : V | w ∈ R₀.reverse}) ∨
      (∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsPathFrom G R u v ∧
        ((IsLeftStar G B C A u ∧ (∃ x ∈ R₀.reverse, x ≠ b₀ ∧ G.Adj v x) ∧
            Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (B ∪ A ∪ C)) ∨
          (IsRightStar G B C A u ∧ (∃ x ∈ R₀.reverse, x ≠ a₀ ∧ G.Adj v x) ∧
            Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (B ∪ A ∪ C))))) :
    (∃ w ∈ F, MajorForStaircase G A C B a₀ R₀ b₀ w) ∨
    (∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsBanister G A C B u R v ∧
      Anticomplete G {w : V | w ∈ R} {w : V | w ∈ R₀}) ∨
    (∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsPathFrom G R u v ∧
      ((IsLeftStar G A C B u ∧ (∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∧
          Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (A ∪ B ∪ C)) ∨
        (IsRightStar G A C B u ∧ (∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x) ∧
          Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (A ∪ B ∪ C)))) := by
  rcases h with hmajor | hbanister | hpath
  · obtain ⟨w, hwF, hw⟩ := hmajor
    exact Or.inl ⟨w, hwF,
      StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.majorForStaircase_swap.mpr hw⟩
  · obtain ⟨u, v, R, hRF, hban, hanti⟩ := hbanister
    refine Or.inr (Or.inl ⟨v, u, R.reverse, ?_, ?_, ?_⟩)
    · intro w hw
      exact hRF w (List.mem_reverse.mp hw)
    · obtain ⟨hR, hout, hleft, hright, hinterior⟩ := hban
      refine ⟨StrongPerfectGraphTheorem.ProofLemmas.PathBasics.isPathFrom_reverse hR, ?_,
        StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.isLeftStar_swap.mpr hright,
        StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mpr hleft, ?_⟩
      · intro w hw
        have hw' := hout w (List.mem_reverse.mp hw)
        intro hwABC
        apply hw'
        rcases hwABC with (hwA | hwB) | hwC
        · exact Or.inl (Or.inr hwA)
        · exact Or.inl (Or.inl hwB)
        · exact Or.inr hwC
      · intro w hw
        have hw' := hinterior w
          (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.mem_interior_reverse.mp hw)
        intro x hx
        apply hw' x
        rcases hx with (hxA | hxB) | hxC
        · exact Or.inl (Or.inr hxA)
        · exact Or.inl (Or.inl hxB)
        · exact Or.inr hxC
    · intro x hx y hy
      exact hanti x (List.mem_reverse.mp hx) y (List.mem_reverse.mpr hy)
  · obtain ⟨u, v, R, hRF, hR, hstars⟩ := hpath
    refine Or.inr (Or.inr ⟨u, v, R, hRF, hR, ?_⟩)
    rcases hstars with ⟨hleft, ⟨x, hxR, hxb₀, hvx⟩, hanti⟩ |
      ⟨hright, ⟨x, hxR, hxa₀, hvx⟩, hanti⟩
    · refine Or.inr ⟨
        StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mpr hleft,
        ⟨x, List.mem_reverse.mp hxR, hxb₀, hvx⟩, ?_⟩
      intro w hw y hy
      apply hanti w hw y
      rcases hy with (hyA | hyB) | hyC
      · exact Or.inl (Or.inr hyA)
      · exact Or.inl (Or.inl hyB)
      · exact Or.inr hyC
    · refine Or.inl ⟨
        StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.isLeftStar_swap.mpr hright,
        ⟨x, List.mem_reverse.mp hxR, hxa₀, hvx⟩, ?_⟩
      intro w hw y hy
      apply hanti w hw y
      rcases hy with (hyA | hyB) | hyC
      · exact Or.inl (Or.inr hyA)
      · exact Or.inl (Or.inl hyB)
      · exact Or.inr hyC


/-- **12.2** (printed p. 71)

PAPER: *"Let `G` be a Berge graph, such that there is no appearance of `K₄` in `G`, no even
prism in `G`, and no 1-breaker in `G`.  Let `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` be a maximal
staircase in `G`, and let `F ⊆ V(G) \ V(K)` be connected, such that its set of attachments in
`V(K)` is not local with respect to `K`.  Then `F` contains either:*

*1. a major vertex, or*

*2. a banister `u`-`R`-`v`, such that there are no edges between `V(R)` and `V(R₀)`, or*

*3. (up to symmetry) a path `u`-`R`-`v`, where `u` is a left-star, `v` has a neighbour in
`R₀ \ a₀`, and there are no edges between `V(R \ u)` and `V(S)`."*

Notes on the transcription.

* *"`F` contains …"* means that all the vertices of the object lie in `F`.
* *"up to symmetry"*: the only symmetry of the hypotheses is the reversal of the strip, which
  interchanges `A` with `B`, `a₀` with `b₀`, and left-stars with right-stars (`V(S)`, `V(K)`
  and `V(R₀)` are unchanged).  So alternative 3 is stated as the two-way disjunction of the
  printed alternative and its mirror image, exactly as for 10.3.
* `V(R \ u)` is the set of vertices of `R` other than `u` (`u` being an end of `R`). -/
theorem thm_12_2 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (hFK : F ⊆ (staircaseVertices A C B R₀)ᶜ) (hFconn : ConnectedSet G F)
    (hFloc : ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G F (staircaseVertices A C B R₀))) :
    -- 12.2.1
    (∃ w ∈ F, MajorForStaircase G A C B a₀ R₀ b₀ w) ∨
    -- 12.2.2
    (∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsBanister G A C B u R v ∧
      SPGT.Anticomplete G {w : V | w ∈ R} {w : V | w ∈ R₀}) ∨
    -- 12.2.3, up to the symmetry that reverses the strip
    (∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsPathFrom G R u v ∧
      ((IsLeftStar G A C B u ∧ (∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∧
          SPGT.Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (A ∪ B ∪ C)) ∨
        (IsRightStar G A C B u ∧ (∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x) ∧
          SPGT.Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (A ∪ B ∪ C)))) := by
  obtain ⟨F', f, f₁, fk, hFsub, hFoutside, hF'conn, hF'nonlocal, hminimal,
      hFvertices, hpath, hpackage⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.MinimalNonlocalStaircaseAttachmentPath.minimalNonlocalStaircaseAttachmentPath
      G A C B a₀ b₀ R₀ F hK.1 hFK hFconn hFloc
  by_cases hlength : 2 ≤ f.length
  · rcases hpackage with hleft | hright
    · rcases hleft with ⟨hleftAttach, hleftUnique, hrungAttach, hrungUnique⟩
      by_cases hcomplete : VertexComplete G f₁ A
      · exact StrongPerfectGraphTheorem.ProofLemmas.ACompleteStaircaseAttachmentPathForcesOutcome.aCompleteStaircaseAttachmentPathForcesOutcome
          G A C B a₀ b₀ R₀ F F' f f₁ fk
            hG hK4 hprism hK hFsub hFoutside hF'conn hF'nonlocal hminimal hFvertices
            hpath hlength hleftAttach hleftUnique hrungAttach hrungUnique hcomplete
      · exact StrongPerfectGraphTheorem.ProofLemmas.NonlocalStaircaseAttachmentPrismJumpForcesOutcome.nonlocalStaircaseAttachmentPrismJumpForcesOutcome
          G A C B a₀ b₀ R₀ F F' f f₁ fk
            hG hK4 hprism hK hFsub hFoutside hF'conn hF'nonlocal hminimal hFvertices
            hpath hlength hleftAttach hleftUnique hrungAttach hrungUnique hcomplete
    · rcases hright with ⟨hrightAttach, hrightUnique, hrungAttach, hrungUnique⟩
      have hvertices : staircaseVertices B C A R₀.reverse = staircaseVertices A C B R₀ :=
        StrongPerfectGraphTheorem.ProofLemmas.Thm121Symmetry.thm121SwapVertices A C B R₀
      have houtsideSwap : F' ⊆ (staircaseVertices B C A R₀.reverse)ᶜ := by
        rw [hvertices]
        exact hFoutside
      have hnonlocalSwap : ¬ LocalForStaircase B C A b₀ R₀.reverse a₀
          (attachments G F' (staircaseVertices B C A R₀.reverse)) := by
        intro hlocal
        rw [hvertices] at hlocal
        exact hF'nonlocal ((localForStaircase_swap A C B a₀ b₀ R₀ _).mpr hlocal)
      have hminimalSwap : ∀ D : Set V, D ⊂ F' → ConnectedSet G D →
          LocalForStaircase B C A b₀ R₀.reverse a₀
            (attachments G D (staircaseVertices B C A R₀.reverse)) := by
        intro D hDF hDconn
        rw [hvertices]
        exact (localForStaircase_swap A C B a₀ b₀ R₀ _).mp (hminimal D hDF hDconn)
      have hrightAttach' : ∃ u ∈ B ∪ C, G.Adj f₁ u := hrightAttach
      have hrightUnique' : ∀ x ∈ F', (∃ u ∈ B ∪ C, G.Adj x u) → x = f₁ := hrightUnique
      have hrungAttach' : ∃ r ∈ R₀.reverse, r ≠ b₀ ∧ G.Adj fk r := by
        simpa only [List.mem_reverse] using hrungAttach
      have hrungUnique' : ∀ x ∈ F', (∃ r ∈ R₀.reverse, r ≠ b₀ ∧ G.Adj x r) → x = fk := by
        simpa only [List.mem_reverse] using hrungUnique
      by_cases hcomplete : VertexComplete G f₁ B
      · apply thm122Outcome_swap G A C B a₀ b₀ R₀ F
        exact StrongPerfectGraphTheorem.ProofLemmas.ACompleteStaircaseAttachmentPathForcesOutcome.aCompleteStaircaseAttachmentPathForcesOutcome
          G B C A b₀ a₀ R₀.reverse F F' f f₁ fk
            hG hK4 hprism
            (StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.maximalStaircase_swap.mp hK)
            hFsub houtsideSwap hF'conn hnonlocalSwap hminimalSwap hFvertices hpath hlength
            hrightAttach' hrightUnique' hrungAttach' hrungUnique' hcomplete
      · apply thm122Outcome_swap G A C B a₀ b₀ R₀ F
        exact StrongPerfectGraphTheorem.ProofLemmas.NonlocalStaircaseAttachmentPrismJumpForcesOutcome.nonlocalStaircaseAttachmentPrismJumpForcesOutcome
          G B C A b₀ a₀ R₀.reverse F F' f f₁ fk
            hG hK4 hprism
            (StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.maximalStaircase_swap.mp hK)
            hFsub houtsideSwap hF'conn hnonlocalSwap hminimalSwap hFvertices hpath hlength
            hrightAttach' hrightUnique' hrungAttach' hrungUnique' hcomplete
  · have hlenPos : 0 < f.length := List.length_pos_of_ne_nil hpath.1.1
    have hlenOne : f.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlenOne
    have hxf₁ : x = f₁ := by simpa using hpath.2.1
    subst f₁
    have hxk : x = fk := by simpa using hpath.2.2
    subst fk
    have hFsingle : F' = ({x} : Set V) := by simpa using hFvertices
    have hxF' : x ∈ F' := by rw [hFsingle]; simp
    have hxF : x ∈ F := hFsub hxF'
    have hxoutside : x ∉ staircaseVertices A C B R₀ := hFoutside hxF'
    rcases StrongPerfectGraphTheorem.ProofLemmas.Thm121Cases.thm121Cases G hG hK4 hprism hbreaker
        A C B a₀ b₀ R₀ hK x hxoutside with hminor | hmajor | hstars
    · exfalso
      apply hF'nonlocal
      have hatt : attachments G F' (staircaseVertices A C B R₀) =
          G.neighborSet x ∩ staircaseVertices A C B R₀ := by
        ext z
        constructor
        · rintro ⟨hzK, y, hyF, hzy⟩
          have hyx : y = x := by
            rw [hFsingle] at hyF
            simpa using hyF
          subst y
          exact ⟨hzy.symm, hzK⟩
        · rintro ⟨hxz, hzK⟩
          exact ⟨hzK, x, hxF', hxz.symm⟩
      rw [hatt]
      exact hminor.1.2
    · exact Or.inl ⟨x, hxF, hmajor.1⟩
    · refine Or.inr (Or.inr ⟨x, x, [x], ?_,
          ⟨StrongPerfectGraphTheorem.ProofLemmas.PathBasics.isPathList_singleton G x, rfl, rfl⟩, ?_⟩)
      · intro w hw
        have hwx : w = x := by simpa using hw
        simpa [hwx] using hxF
      · rcases hstars with ⟨hleft, hr⟩ | ⟨hright, hr⟩
        · exact Or.inl ⟨hleft, hr, by simp [Anticomplete]⟩
        · exact Or.inr ⟨hright, hr, by simp [Anticomplete]⟩


end SPGT

end StrongPerfectGraphTheorem.Statements.S12
