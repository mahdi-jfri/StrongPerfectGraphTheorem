module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.StripSystems
public import StrongPerfectGraphTheorem.Types.Overshadowed
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.Thm85MinimalNonlocal
public import StrongPerfectGraphTheorem.ProofLemmas.Thm85Claim1
public import StrongPerfectGraphTheorem.ProofLemmas.Thm85Claim2
public import StrongPerfectGraphTheorem.ProofLemmas.Thm85Claim3
public import StrongPerfectGraphTheorem.ProofLemmas.Thm85PathStructure
public import StrongPerfectGraphTheorem.ProofLemmas.Thm85Endgame

/-!
# Section 8 — Generalized line graphs

The six numbered statements 8.1–8.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 39–47).

All defined terms are imported and never restated: *`J`-strip system*, *`uv`-rung*,
*a choice of rungs forms `L(H)`*, *nondegenerate strip system*, *`V(S,N)`*, *saturates the
strip system*, *major* and *local* with respect to the strip system, *maximal strip system*
from `StrongPerfectGraphTheorem.Types.StripSystems`; *Berge*, *path*, *length*, *connected set* from
`StrongPerfectGraphTheorem.Types.Core`; *`k`-connected* from `StrongPerfectGraphTheorem.Types.Tracks`; *appearance*,
*(non)degenerate appearance*, *`J`-enlargement*, *saturates `L(H)`*, *attachments* from
`StrongPerfectGraphTheorem.Types.Appearances`; *overshadowed appearance* from `StrongPerfectGraphTheorem.Types.Overshadowed`;
*proper 2-join* and *balanced skew partition* from `StrongPerfectGraphTheorem.Types.Decompositions`.

Encoding conventions:

* an *appearance* `L(H)` of `J` in `G` is the pair `(H, K)` of a bipartite subdivision `H` of
  `J` and the induced subgraph `G|K` that `L(H)` is isomorphic to; the notions that have to
  cross between the two sides (`saturates L(H)`, *overshadowed*) additionally take the
  identification `φ : H.lineGraph ≃g G.induce K`, which is the paper's silent "equality
  convention" of printed p. 20 made explicit;
* "there is a graph `X` such that …" is `∃ (n : ℕ) (X : SimpleGraph (Fin n)), …`;
* `K₄` is `(⊤ : SimpleGraph (Fin 4))`, `K₃,₃` is `completeBipartiteGraph (Fin 3) (Fin 3)`, and
  "`J = K₄`" is `Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4)))`;
* the paper's `Ḡ` is `Gᶜ`.

Statement 8.6 is the restatement of 5.4 (*"We are now ready to prove 5.4, which we restate:"*),
and is transcribed here in exactly the same form as `StrongPerfectGraphTheorem.Statements.S05.SPGT.thm_5_4`.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S08

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.StripSystems StrongPerfectGraphTheorem.Types.StripSystems.SPGT
open StrongPerfectGraphTheorem.Types.Overshadowed StrongPerfectGraphTheorem.Types.Overshadowed.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **8.5** (printed p. 42)

PAPER: *"Let `G` be Berge, let `J` be a 3-connected graph, and let `(S,N)` be a maximal
`J`-strip system in `G`.  Assume that there is no `J`-enlargement with a nondegenerate
appearance in `G`.  Assume moreover that if `J = K₄` then `(S,N)` is nondegenerate and there
is no overshadowed appearance of `J` in `G`.  Let `F ⊆ V(G) \ V(S,N)` be connected, so that no
member of `F` is major with respect to `(S,N)`.  Then the set of attachments of `F` in
`V(S,N)` is local."*

Notes on the transcription.

* This is the **published** form of the statement.  (The arXiv v1 draft `stripnbrs1` had a
  two-bullet *disjunctive* hypothesis — *"either `(S,N)` is nondegenerate and there is no
  `J`-enlargement with a nondegenerate appearance in `G`, or `J = K₃,₃` and there is no
  `J`-enlargement that appears in either `G` or `Ḡ`"* — and a *disjunctive* conclusion
  — *"either `J = K₄` and there is an overshadowed appearance of `J` in `G`, or the set of
  attachments of `F` in `V(S,N)` is local"*.  Both were replaced in the published version by
  the flat hypotheses and the single conclusion transcribed here.)
* *"A maximal `J`-strip system in `G`"* is both conjuncts `IsJStripSystem G J S N` and
  `MaximalStripSystem G J S N` (the latter is *only* the "no larger system" condition; see
  its doc-comment).
* *"`F ⊆ V(G) \ V(S,N)` be connected"* is `F ⊆ (V(S,N))ᶜ` together with `Core.ConnectedSet`,
  which follows the paper in counting `∅` as connected.
* *"The set of attachments of `F` in `V(S,N)`"* is `Appearances.attachments G F (V(S,N))`,
  i.e. `{k ∈ V(S,N) | k has a neighbour in F}`; *"is local"* is
  `StripSystems.LocalForStripSystem`. -/
theorem thm_8_5 {U : Type*} [Fintype U] (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hmax : MaximalStripSystem G J S N)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (hK₄ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateStripSystem G J S N ∧
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V) (φ : H.lineGraph ≃g G.induce K'),
          IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' φ)
    (F : Set V) (hF : F ⊆ (stripSystemVertices J S)ᶜ) (hFconn : ConnectedSet G F)
    (hFmajor : ∀ f ∈ F, ¬ MajorForStripSystem G J S N f) :
    LocalForStripSystem J S N (attachments G F (stripSystemVertices J S)) := by
  classical
  -- PAPER: *"Let `X` be the set of attachments of `F` in `V(S,N)`, and suppose for a
  -- contradiction that `X` is not local."*
  by_contra hXnotlocal
  -- PAPER: *"We may assume that `F` is minimal (connected) with this property."*
  obtain ⟨F₀, hF₀sub, hF₀ne, hF₀conn, hF₀notlocal, hF₀min⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm85MinimalNonlocal.thm85MinimalNonlocal G J hJ S N F hFconn
      hXnotlocal
  have hF₀compl : F₀ ⊆ (stripSystemVertices J S)ᶜ := hF₀sub.trans hF
  have hF₀major : ∀ f ∈ F₀, ¬ MajorForStripSystem G J S N f :=
    fun f hf => hFmajor f (hF₀sub hf)
  -- (1) PAPER: *"For every choice of rungs, forming `L(H)` say: for each `y ∈ F`, the set of
  -- neighbours of `y` does not saturate `L(H)`, and if `J = K₄` then `L(H)` is not
  -- degenerate."*
  have hclaim1 := fun (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
      (φ : H.lineGraph ≃g G.induce K)
      (hK : K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v})
      (hforms : FormsLineGraph G J S N R H) =>
    StrongPerfectGraphTheorem.ProofLemmas.Thm85Claim1.thm85Claim1 G hG J hJ S N hSN hnoenl hK₄ F₀ hF₀compl
      hF₀major n H R K φ hK hforms
  -- (2) PAPER: *"There is no `v ∈ V(J)` such that `X ⊆ ⋃(S_uv : uv ∈ E(J))`."*
  have hclaim2 :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm85Claim2.thm85Claim2 G hG J hJ S N hSN hmax hnoenl hK₄ F₀
      hF₀compl hF₀ne hF₀conn hF₀major hF₀notlocal hF₀min hclaim1
  -- (3) PAPER: *"There are two disjoint edges in `K`."*
  have hclaim3 :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm85Claim3.thm85Claim3 G hG J hJ S N hSN hmax hnoenl hK₄ F₀
      hF₀compl hF₀ne hF₀conn hF₀major hF₀notlocal hF₀min hclaim1 hclaim2
  -- PAPER: *"… from the minimality of `F` it follows that `F` is the vertex set of a path, say
  -- `f₁, …, f_n`."*
  obtain ⟨P, f₁, fn, hP, hPF⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm85PathStructure.thm85PathStructure G J hJ S N hSN F₀ hF₀compl
      hF₀ne hF₀conn hF₀min hclaim3
  -- (4), (5), (6) and the closing paragraph, ending in a contradiction.
  exact StrongPerfectGraphTheorem.ProofLemmas.Thm85Endgame.thm85Endgame G hG J hJ S N hSN hmax hnoenl hK₄ F₀
    hF₀compl hF₀ne hF₀conn hF₀major hF₀notlocal hF₀min hclaim1 hclaim2 hclaim3 P f₁ fn hP hPF


end SPGT

end StrongPerfectGraphTheorem.Statements.S08
