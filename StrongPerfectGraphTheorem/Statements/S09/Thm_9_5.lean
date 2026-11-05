/-  Proof of statement 9.5 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.  Reproduces the printed proof
    (printed pp. 52–53) step for step, through
    `StrongPerfectGraphTheorem.ProofLemmas.Thm95Body`. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Overshadowed
public import StrongPerfectGraphTheorem.Types.Knots
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.Thm95Body

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace StrongPerfectGraphTheorem.Statements.S09

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Overshadowed StrongPerfectGraphTheorem.Types.Overshadowed.SPGT
open StrongPerfectGraphTheorem.Types.Knots StrongPerfectGraphTheorem.Types.Knots.SPGT
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.BasicClasses.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **9.5** (printed p. 52)

PAPER: *"Let `G` be Berge, such that there is no appearance in `G` or in `Ḡ` of any
`K₄`-enlargement, and there is no overshadowed appearance of `K₄` in `G` or in `Ḡ`.  Let `L`
be a maximal striation in `G`.  Let `F ⊆ V(G) \ V(L)` be connected, such that for each
`f ∈ F`, the set of its neighbours in `V(L)` is local with respect to `L`.  Then the set of
attachments of `F` in `V(L)` is local with respect to `L`."*

Notes on the transcription.

* *"`F ⊆ V(G) \ V(L)` be connected"* is `F ⊆ (V(L))ᶜ` together with `Core.ConnectedSet`,
  which follows the paper in counting `∅` as connected.
* *"The set of attachments of `F` in `V(L)`"* is `Appearances.attachments G F (V(L))`, i.e.
  `{k ∈ V(L) | k has a neighbour in F}`. -/
theorem thm_9_5 (G : SimpleGraph V) (hG : Berge G)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance G H K' φ)
    (hnoovercompl : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gᶜ H K' φ)
    (m n : ℕ) (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (hL : MaximalStriation G S T)
    (F : Set V) (hFsub : F ⊆ (striationVertices S T)ᶜ) (hFconn : ConnectedSet G F)
    (hFlocal : ∀ f ∈ F,
      LocalForStriation G S T (G.neighborSet f ∩ striationVertices S T)) :
    LocalForStriation G S T (attachments G F (striationVertices S T)) := by
  -- PAPER: *"Let `L` have strips `Sᵢ = (Aᵢ, Cᵢ, Bᵢ)` and antistrips `Tⱼ = (Xⱼ, Zⱼ, Yⱼ)`."*
  have hs : Thm95Body.Setup G S T := ⟨hG, hnoenl, hnoover, hnoovercompl, hL⟩
  -- PAPER: *"Suppose not, and choose a counterexample `F` with `F` minimal."*  Choosing a
  -- minimal counterexample is induction on `|F|`: every strictly smaller admissible
  -- configuration inside `F` is already known to have local attachments.
  suffices H : ∀ k : ℕ, ∀ F' : Set V, F'.ncard ≤ k → Thm95Body.Cand G S T F' →
      LocalForStriation G S T (attachments G F' (striationVertices S T)) by
    exact H F.ncard F le_rfl ⟨hFsub, hFconn, hFlocal⟩
  intro k
  induction k with
  | zero =>
    intro F' hk hF'
    refine Thm95Body.local_of_minimal hs hF' ?_
    intro F'' _ hlt _
    exfalso
    omega
  | succ k ih =>
    intro F' hk hF'
    refine Thm95Body.local_of_minimal hs hF' ?_
    intro F'' _ hlt hF''
    exact ih F'' (by omega) hF''


end SPGT

end StrongPerfectGraphTheorem.Statements.S09
