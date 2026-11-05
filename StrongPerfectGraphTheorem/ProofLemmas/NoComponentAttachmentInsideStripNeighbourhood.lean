module

public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.StripSystems
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.Thm86ClaimTwo

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.NoComponentAttachmentInsideStripNeighbourhood

open StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.StripSystems.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions.SPGT

/-- **8.6, claim (2)** (printed p. 46).

Under the no-balanced-skew-partition assumption, a nonempty component outside a
`J`-strip system cannot have all of its attachments in a single branch-neighbourhood. -/
theorem noComponentAttachmentInsideStripNeighbourhood
    {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (hstrip : IsJStripSystem G J S N)
    (Z : Set V) (hZdisj : Disjoint Z (stripSystemVertices J S))
    (hnoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (F : Set V) (hF : IsComponent G Z F) (hFne : F.Nonempty)
    (hOutside : ∀ f ∈ F, ∀ x : V, x ∉ F → G.Adj f x → x ∈ stripSystemVertices J S)
    (v : U) (hFattach : attachments G F (stripSystemVertices J S) ⊆ N v) :
    AdmitsBalancedSkewPartition G := by
  classical
  -- `F ⊆ Z`, and `Z` is disjoint from `V(S,N)`.
  have hFdisj : Disjoint F (stripSystemVertices J S) :=
    Set.disjoint_of_subset_left hF.1 hZdisj
  -- **"every path in `G` from `F` to `F'` meets `N_v`"**, in the form claim (2) uses it: `F` is
  -- anticomplete to `F' = V(G) \ (F ∪ N_v)`.  A neighbour of `F` outside `F` lies in `V(S,N)`
  -- (because `F` is a component of `Z`), hence is an attachment of `F`, hence lies in `N_v`.
  have hFsep : Anticomplete G F ((F ∪ N v)ᶜ) := by
    intro f hf y hy hadj
    have hyF : y ∉ F := fun hc => hy (Or.inl hc)
    have hyV : y ∈ stripSystemVertices J S := hOutside f hf y hyF hadj
    exact hy (Or.inr (hFattach ⟨hyV, f, hf, hadj.symm⟩))
  exact Thm86ClaimTwo.admitsBalancedSkewPartition_of_attachments_in_N hG hJ hstrip hFne hFdisj
    hF.2.1 hFattach hFsep

end StrongPerfectGraphTheorem.ProofLemmas.NoComponentAttachmentInsideStripNeighbourhood
