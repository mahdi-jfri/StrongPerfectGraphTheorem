module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.ProofLemmas.AddPendantVertexTransport
public import StrongPerfectGraphTheorem.ProofLemmas.NoOddHoleThroughAddedVertex
public import StrongPerfectGraphTheorem.ProofLemmas.NoOddAntiholeThroughAddedVertex

/-!
# Claim (1) of the proof of 1.5: `G'` is Berge

> *"(1) `G'` is Berge.  For suppose not.  Then in `G'` there is an odd hole or
> antihole using `z`."*

An odd hole or antihole `F` of `G' = G +ᵥ B₁` either avoids `z` — in which case
`AddPendantVertexTransport.exists_eq_map_inl` writes `F = ℓ.map Sum.inl` and the
transport clauses turn it into an odd hole (resp. odd antihole) of `G`, contradicting
`Berge G` — or it contains `z`, and then one of the two case lemmas
(`NoOddHoleThroughAddedVertex`, `NoOddAntiholeThroughAddedVertex`) applies.

`Berge G` is needed only for the `z ∉ F` branch, which is why the two case lemmas do
not take it.

It is a separate lemma so that §5 can cite one clean fact: §5.1 uses it to get
`Berge H`.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.AddPendantVertexBerge

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.ProofLemmas
open StrongPerfectGraphTheorem.ProofLemmas.AddPendantVertexTransport

/-- **Claim (1)**: adding to a Berge graph `G` a new vertex whose neighbour set is an
anticomponent `B₁` of the `B`-side of a balanced pair `(A, B)` gives a Berge graph. -/
theorem berge_addPendantVertex {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : Berge G) {A B B₁ : Set V}
    (hAB : A ∪ B = Set.univ) (hbal : SPGT.Balanced G A B)
    (hB₁ : IsAnticomponent G B B₁) :
    Berge (addPendantVertex G B₁) := by
  classical
  constructor
  · -- an odd hole of `G'`
    intro c hc
    by_cases hz : (Sum.inr () : V ⊕ Unit) ∈ c
    · -- "there is an odd hole ... using `z`" — case 1
      exact NoOddHoleThroughAddedVertex.even_holeLength_of_mem hAB hbal hB₁ hc hz
    · -- the hole avoids `z`, so it *is* a hole of `G`, and `G` is Berge
      obtain ⟨ℓ, hℓ, hℓlen⟩ := exists_eq_map_inl (fun x hx heq => hz (heq ▸ hx))
      have hGℓ : IsHoleList G ℓ := (isHoleList_map_inl G B₁ ℓ).mpr (hℓ ▸ hc)
      have e : holeLength c = holeLength ℓ := by
        show c.length = ℓ.length
        omega
      rw [e]
      exact hG.1 ℓ hGℓ
  · -- an odd antihole of `G'`
    intro c hc
    by_cases hz : (Sum.inr () : V ⊕ Unit) ∈ c
    · -- "now assume there is an odd antihole `D` in `G'`, again using `z`" — case 2
      exact NoOddAntiholeThroughAddedVertex.even_holeLength_of_mem hAB hbal hB₁ hc hz
    · obtain ⟨ℓ, hℓ, hℓlen⟩ := exists_eq_map_inl (fun x hx heq => hz (heq ▸ hx))
      have hGℓ : IsHoleList Gᶜ ℓ := (isHoleList_compl_map_inl G B₁ ℓ).mpr (hℓ ▸ hc)
      have e : holeLength c = holeLength ℓ := by
        show c.length = ℓ.length
        omega
      rw [e]
      exact hG.2 ℓ hGℓ

end StrongPerfectGraphTheorem.ProofLemmas.AddPendantVertexBerge
