module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalAddTrack
public import StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalStructure
public import StrongPerfectGraphTheorem.ProofLemmas.SubdivisionCounting

/-!
# Building a `J`-enlargement out of a non-local attachment path

## What this is

The hypotheses below are *literally* outcome 1 of 5.8: a path `P` of `G` with ends `p₁, p₂`,
disjoint from the appearance `K = V(L(H))`, having no attachments in `K` other than
`N_H(c₁) ⊆ N(p₁)` and `N_H(c₂) ⊆ N(p₂)` for two vertices `c₁, c₂` of `H` that do **not** lie on
a common branch.  (`Nc c` is the set of vertices of `G` carried by the edges of `H` at `c`, i.e.
the clique of `L(H)` attached to `c`; `hN` pins that down through the isomorphism `φ`.)

The conclusion is the printed sentence that follows:

> *"Then there is an appearance `L(H')` in `G` of some `J`-enlargement `J'`, with `L(H)` an
> induced subgraph of `L(H')`.  Moreover, if `J' = K₃,₃` then `J = K₄`, and so `L(H)` is
> nondegenerate and therefore so is `L(H')`."*

The degeneracy tail of that sentence is carried by the hypothesis `hnd` (*if `J` is `K₄` then
the appearance is nondegenerate*) and by the `NondegenerateAppearance J' H'` conjunct of the
conclusion.

## No printed proof exists

**The paper prints no proof of this construction anywhere.**  It makes exactly the same
unjustified move three times:

* in the proof of 7.5, one step of the proof of 5.4 (printed p. 37);
* in the proof of 8.5 (printed p. 42);
* and in the proof of 9.3 (printed p. 48).

Each time the enlargement `J'` and the subdivision `H'` are simply asserted to exist.

Since there is no printed argument to follow, the Lean proof below is our own.  It extends `H`
by the path `P` (`EnlargementFromNonlocalAddTrack.addTrack`) and then reads the enlargement `J'`
off the extended subdivision (`EnlargementFromNonlocalStructure.promotedChordEnlargement`).

## Why it matters

Many later steps rely on this construction: claims (2), (3) and (4) of the printed proof of 8.5
all need it, as do `Thm75Claim2`, the `Thm84*` modules, claim (1) of 8.6 and `Thm83MixedRungs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalAttachmentPath

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT

private theorem nondegenerateAppearance_map {A B X : Type*} {J : SimpleGraph X}
    {H : SimpleGraph A} {H' : SimpleGraph B} (ψ : H ≃g H')
    (h : NondegenerateAppearance J H) : NondegenerateAppearance J H' := by
  intro hdeg
  apply h
  rcases hdeg with ⟨hk4, hd⟩ | ⟨hnk4, hk33, ⟨iso⟩⟩
  · exact Or.inl ⟨hk4,
      StrongPerfectGraphTheorem.ProofLemmas.SubdivisionCounting.degenerateK4Appearance_of_iso ψ.symm hd⟩
  · exact Or.inr ⟨hnk4, hk33, ⟨ψ.trans iso⟩⟩

/-- **Outcome 1 of 5.8 produces a `J`-enlargement with a nondegenerate appearance.**

`P` is a path of `G` off the appearance `K`, whose only attachments in `K` are the cliques
`Nc c₁` (complete to the end `p₁`) and `Nc c₂` (complete to the end `p₂`), for two vertices
`c₁, c₂` of `H` lying on no common branch.  Then `G` contains an appearance of some
`J`-enlargement `J'`, and that appearance is nondegenerate. -/
theorem enlargementFromNonlocalAttachmentPath {V : Type*} [Fintype V] [DecidableEq V]
    {U : Type*} [Fintype U] (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (happ : IsAppearance G J H K) (φ : H.lineGraph ≃g G.induce K)
    (Nc : Fin n → Set V)
    (hN : ∀ c : Fin n, Nc c = {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hPK : ∀ x ∈ P, x ∉ K)
    (c₁ c₂ : Fin n) (hnb : ¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (h₁ : ∀ x ∈ Nc c₁, G.Adj p₁ x) (h₂ : ∀ x ∈ Nc c₂, G.Adj p₂ x)
    (hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ Nc c₁) ∨ (x = p₂ ∧ y ∈ Nc c₂))
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H) :
    ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H' := by
  classical
  have hc :=
    StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalStructure.ne_and_not_adj_of_no_common_branch
      J hJ H happ.1.1 c₁ c₂ hnb
  have h₁' : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c₁ ∈ e →
      G.Adj p₁ (↑(φ ⟨e, he⟩) : V) := by
    intro e he hce
    apply h₁
    rw [hN c₁]
    exact ⟨e, he, ⟨he, hce⟩, rfl⟩
  have h₂' : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c₂ ∈ e →
      G.Adj p₂ (↑(φ ⟨e, he⟩) : V) := by
    intro e he hce
    apply h₂
    rw [hN c₂]
    exact ⟨e, he, ⟨he, hce⟩, rfl⟩
  have hno' : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c₁ ∈ e ∧
        y = (↑(φ ⟨e, he⟩) : V)) ∨
      (x = p₂ ∧ ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c₂ ∈ e ∧
        y = (↑(φ ⟨e, he⟩) : V)) := by
    intro x hx y hy hxy
    rcases hno x hx y hy hxy with h | h
    · left
      refine ⟨h.1, ?_⟩
      rw [hN c₁] at h
      obtain ⟨e, he, hinc, hval⟩ := h.2
      exact ⟨e, he, hinc.2, hval⟩
    · right
      refine ⟨h.1, ?_⟩
      rw [hN c₂] at h
      obtain ⟨e, he, hinc, hval⟩ := h.2
      exact ⟨e, he, hinc.2, hval⟩
  obtain ⟨D, q, ψ, hext, hqlen⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalAddTrack.addTrack
      G H K φ P p₁ p₂ hP hPK c₁ c₂ hc.1 hc.2 h₁' h₂' hno'
  obtain ⟨m, J', henl, hDsub, hclass⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalStructure.promotedChordEnlargement
      J hJ H happ.1.1 c₁ c₂ hnb D Sum.inl q hext
  have hbip : D.IsBipartite :=
    StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalStructure.branchExtensionBipartite
      G hG J hJ H happ.1 c₁ c₂ hnb D Sum.inl q hext
        (K ∪ {x : V | x ∈ P}) ψ
  have hnondeg : NondegenerateAppearance J' D :=
    StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalStructure.branchExtensionNondegenerate
      J hJ H happ.1.1 c₁ c₂ hnb D Sum.inl q hext J' henl hDsub hclass hnd
  let e := Fintype.equivFin (Fin n ⊕ Fin (P.length - 1))
  let H' : SimpleGraph (Fin (Fintype.card (Fin n ⊕ Fin (P.length - 1)))) :=
    D.map e.toEmbedding
  let θ : D ≃g H' := SimpleGraph.Iso.map e D
  refine ⟨m, J', henl, Fintype.card (Fin n ⊕ Fin (P.length - 1)), H',
    K ∪ {x : V | x ∈ P}, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact StrongPerfectGraphTheorem.ProofLemmas.SubdivisionCounting.isSubdivision_of_iso θ hDsub
    · exact SimpleGraph.Colorable.of_hom θ.symm.toHom hbip
    · exact ⟨θ.lineGraph.symm.trans ψ⟩
  · exact nondegenerateAppearance_map θ hnondeg

end StrongPerfectGraphTheorem.ProofLemmas.EnlargementFromNonlocalAttachmentPath
