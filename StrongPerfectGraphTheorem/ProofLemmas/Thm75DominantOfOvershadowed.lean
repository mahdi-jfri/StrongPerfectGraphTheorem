module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Overshadowed
public import StrongPerfectGraphTheorem.ProofLemmas.Thm75Setup

/-!
# 7.5: reading the overshadowing witness as a dominant vertex

PAPER (proof of 7.5, printed p. 35): *"There is an edge `c₁c₂` of `J` such that `Bc₁c₂` has odd
length `≥ 3`, and some vertex of `G` is nonadjacent in `G` to at most one vertex of `Nc₁` and to
at most one vertex of `Nc₂`.  We say such a vertex `v` is `Bc₁c₂`-dominant with respect to
`L(H)`."*

`Overshadowed.IsOvershadowedAppearance` states the same condition on the *edge* side of the
appearance — as a subsingleton subset of `δ_H(bᵢ)` — because that is how §6 phrases it.  This
module transports it across `φ` to the *vertex* side, i.e. to `Thm75Setup.IsDominantFor` on
`NSet`, which is the form in which 5.8 and 7.3 want it.  Only the fact that the difference set on
the `G` side is the image of the difference set on the `H` side is used, so no injectivity of `φ`
is needed.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm75DominantOfOvershadowed

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Overshadowed StrongPerfectGraphTheorem.Types.Overshadowed.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.Thm75Setup

/-- "`v` is nonadjacent to at most one vertex of `δ_H(c)`" (edge side) gives "`v` is nonadjacent
to at most one vertex of `N_c`" (vertex side). -/
theorem thm75DominantOfOvershadowed {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (K : Set V) (φ : H.lineGraph ≃g G.induce K) (c : W) (v : V)
    (h : (incidentEdges H c \
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, G.Adj v (↑(φ ⟨e, he⟩) : V)}).Subsingleton) :
    (NSet G H K φ c \ G.neighborSet v).Subsingleton := by
  rintro x ⟨⟨e, he, hec, rfl⟩, hxn⟩ y ⟨⟨f, hf, hfc, rfl⟩, hyn⟩
  have hekey : e ∈ incidentEdges H c \
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, G.Adj v (↑(φ ⟨e, he⟩) : V)} := by
    refine ⟨hec, ?_⟩
    rintro ⟨he', hadj⟩
    exact hxn hadj
  have hfkey : f ∈ incidentEdges H c \
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, G.Adj v (↑(φ ⟨e, he⟩) : V)} := by
    refine ⟨hfc, ?_⟩
    rintro ⟨hf', hadj⟩
    exact hyn hadj
  have : e = f := h hekey hfkey
  subst this
  rfl

end StrongPerfectGraphTheorem.ProofLemmas.Thm75DominantOfOvershadowed
