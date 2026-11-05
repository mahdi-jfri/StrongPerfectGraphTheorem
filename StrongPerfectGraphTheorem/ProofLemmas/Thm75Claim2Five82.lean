module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.Thm75Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Five82ExactCard

/-!
# 7.5 claim (2): the 5.8.2 branch

PAPER (proof of 7.5, claim (2), printed pp. 36–38).  This module is everything from

*"So we may assume that 5.8.2 holds, and there is an edge `b₁b₂` of `J` … such that one of the
following holds: 1. … 2. … 3. … 4. …"*

down to

*"Hence we can apply induction on `F`, and the result follows.  This proves (2)."*

That is: the rung replacement, and then the two branches the paper runs in turn —

* ***`b₁b₂` and `c₁c₂` are different edges of `J`*** (p. 37).  `Bc₁c₂` survives in `H′`; 7.1
  produces two prisms related as in 7.4, and 7.4 transfers `Bc₁c₂`-dominance and maximality of
  `Y` from `L(H)` to `L(H′)`
  (`StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Five82Dominance.dominant_iff_of_one_clique_replacement`); then
  *"Since there is a proper subset `F′` of `F` with attachments in `S` and in the new set `T′` in
  `V(H′)` corresponding to `T` … it follows that we may apply the inductive hypothesis."*
* ***`bᵢ = cᵢ` for `i = 1, 2`*** (pp. 37–38).  Cases 3, 1 and 4 are each shown impossible, case 2
  applies, and dominance-and-maximality transfer to `L(H′)` through
  `StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Five82DoubleSwap.dominance_and_maximality_of_double_swap`;
  then the inductive hypothesis again.

## What plugs in where

* `StrongPerfectGraphTheorem.ProofLemmas.RungReplacementLabelled.rungReplacement` builds `L(H′)`.
  **Its `hpar` binder is discharged, in 5.8.2's case 1, by a Berge argument**
  (`StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Five82CaseGaps.case_one_parity`): since `J` is
  3-connected, there is a second track from `b₁` to `b₂` avoiding the old branch, and `R′`
  together with the rung of that track forms a hole of `G`.  That hole is even because `G` is
  Berge, and so `R′` has the parity of the old rung.  Cases 2, 3 and 4 supply the parity outright.
* `StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Five82DoubleSwap.dominance_and_maximality_of_double_swap`
  is the `bᵢ = cᵢ` transfer.
* `ih` is the induction hypothesis of the outer induction on `|F|` in
  `StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Generalised.thm75Claim2Generalised`: the whole of claim (2)
  for sets of size `≤ n`, quantified over **every** appearance — the paper's *"we assume it holds
  for all smaller choices of `F` (even for different choices of `L(H)`)"*.  Both branches consume
  it with `F′ ⊊ F`, and the `b₁b₂ ≠ c₁c₂` branch consumes it with the appearance changed as well,
  which is exactly why the outer statement had to quantify the appearance inside the induction.
* `hmin` is the same minimality that `Thm75Claim2FAvoidsLineGraph` uses; the `bᵢ = cᵢ` branch
  needs it a second time, to know that one end of `R′` has no neighbour in `T` (the field
  `hno_T` of `Thm75Claim2Five82AppearanceData.SameBranchReplacementData`).

The block from `b₁` to `hcases` is 5.8.2's output, copied verbatim from the second disjunct of
`Thm75Claim2Transport.five8W` with `N := NSet G H K φ`.

The proof splits on `|F|`.  If `|F| ≤ n`, then `ih` applies at once.  Otherwise `|F| = n + 1`,
and the rung-replacement argument is carried out in
`Thm75Claim2Five82ExactCard.exactCardRungReplacementStep`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Five82

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.Thm75Setup

/-- **7.5 claim (2), the 5.8.2 branch** (printed pp. 36–38): given 5.8.2's output for the minimal
`F`, together with the induction hypothesis `ih` on `|F|`, the theorem holds. -/
theorem thm75Claim2Five82 {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3) (n : ℕ)
    (ih : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V) (φ : H.lineGraph ≃g G.induce K),
      IsAppearance G J H K →
      ∀ (B : List (Fin m)) (c₁ c₂ : Fin m), IsBranch H B → IsTrackFrom H B c₁ c₂ →
        Odd (trackLength B) → 3 ≤ trackLength B →
      ∀ (Y : Set V), Y.Nonempty → AnticonnectedSet G Y →
        (∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) →
        (∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
          (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y) →
      ∀ (X X₀ X₁ Rset S T F : Set V),
        X = {x : V | VertexComplete G x Y} →
        Rset = {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
          e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)} →
        X₀ = X \ K →
        X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂) →
        S = Rset \ X₁ →
        T = (K \ Rset) \ X₁ →
        F.ncard ≤ n → ConnectedSet G F → (∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y) →
        (∃ s ∈ S, ∃ f ∈ F, G.Adj s f) → (∃ t ∈ T, ∃ f ∈ F, G.Adj t f) →
        ((∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
            ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
              IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H') ∨
          AdmitsBalancedSkewPartition G))
    (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List (Fin m)) (c₁ c₂ : Fin m)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y)
    (hYmax : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
      (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y)
    (X X₀ X₁ Rset S T : Set V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₀ : X₀ = X \ K)
    (hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂))
    (hS : S = Rset \ X₁) (hT : T = (K \ Rset) \ X₁)
    (F : Set V) (hFcard : F.ncard ≤ n + 1) (hFconn : ConnectedSet G F)
    (hFdisj : ∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y) (hFK : ∀ x ∈ F, x ∉ K)
    (hSF : ∃ s ∈ S, ∃ f ∈ F, G.Adj s f) (hTF : ∃ t ∈ T, ∃ f ∈ F, G.Adj t f)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ConnectedSet G F' →
      (∀ x ∈ F', x ∉ X₀ ∪ X₁ ∪ Y) → (∃ s ∈ S, ∃ f ∈ F', G.Adj s f) →
      (∃ t ∈ T, ∃ f ∈ F', G.Adj t f) → False)
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hPF : ∀ x ∈ P, x ∈ F)
    (b₁ b₂ : Fin m) (q : List (Fin m)) (R : List V) (r₁ r₂ : V)
    (hb₁ : b₁ ∈ branchVertices H) (hb₂ : b₂ ∈ branchVertices H)
    (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hR : IsPathList G R)
    (hRs : {x : V | x ∈ R} =
      {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hr₁ : NSet G H K φ b₁ ∩ {x : V | x ∈ R} = {r₁})
    (hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ R} = {r₂})
    (hcases :
      ((∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
          (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
      ((∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂}) ∨
          (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
        (Even (pathLength P) ↔ Even (pathLength R))) ∨
      (p₁ = p₂ ∧
        (∀ x ∈ (NSet G H K φ b₁ ∪ NSet G H K φ b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
        (∀ y ∈ K, G.Adj p₁ y → y ∈ NSet G H K φ b₁ ∪ NSet G H K φ b₂ ∪ {z : V | z ∈ R}) ∧
        Even (pathLength R)) ∨
      (r₁ = r₂ ∧ (∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂})) ∧
        Even (pathLength P))) :
    ((∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
        ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
          IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H') ∨
      AdmitsBalancedSkewPartition G) := by
  classical
  by_cases hsmall : F.ncard ≤ n
  · exact ih m H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom hYmax
      X X₀ X₁ Rset S T F hX hRset hX₀ hX₁ hS hT hsmall hFconn hFdisj hSF hTF
  · have hcard : F.ncard = n + 1 := by omega
    exact StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Five82ExactCard.exactCardRungReplacementStep
      G hG J hJ n ih m H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti
        hYdom hYmax X X₀ X₁ Rset S T hX hRset hX₀ hX₁ hS hT F hcard hFconn hFdisj
        hFK hSF hTF hmin P p₁ p₂ hP hPF b₁ b₂ q R r₁ r₂ hb₁ hb₂ hq hqf hR hRs
        hr₁ hr₂ hcases

end StrongPerfectGraphTheorem.ProofLemmas.Thm75Claim2Five82
