module

public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs
public import StrongPerfectGraphTheorem.ProofLemmas.IntegralFlowDecomposesIntoSimpleSourceSinkPaths
public import StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork
public import StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitRoute

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.TwoVertexMengerForNonadjacentVertices

open StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs

/-- The nonadjacent-endpoint form of the two-vertex Menger interface used in result 7.1. -/
theorem twoVertexMengerForNonadjacentVertices
    {U : Type*} [Fintype U] (G : SimpleGraph U) (u v : U)
    (huv : u ≠ v) (hnadj : ¬ G.Adj u v) (hG : IsKConnected G 2) :
    ∃ p q : G.Walk u v,
      p.IsPath ∧
      q.IsPath ∧
      p.support ≠ q.support ∧
      ∀ w ∈ p.support, w ∈ q.support → w = u ∨ w = v := by
  classical
  letI : DecidableEq U := Classical.decEq U
  let arcDec : DecidableEq (StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.Arc U) :=
    Classical.decEq _
  letI : DecidableEq (StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.Arc U) := arcDec
  letI : BEq (StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.Arc U) :=
    instBEqOfDecidableEq
  letI : LawfulBEq (StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.Arc U) :=
    inferInstance
  let source : StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.Node U := (u, true)
  let sink : StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.Node U := (v, false)
  have hst : source ≠ sink := by simp [source, sink]
  obtain ⟨k, f, R, hflow, hsR, htR, hcut, -, -⟩ :=
    finiteIntegralMaxFlowMinCutForLabelledArcs
      StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.tail
      StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.head
      (StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.capacity G u v)
      source sink hst
  have hcutEq :
      StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.cutCapacity G u v R =
        FiniteIntegralMaxFlowMinCutForLabelledArcs.cutCapacity
          StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.tail
          StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.head
          (StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.capacity G u v) R := rfl
  have hk : 2 ≤ k := by
    have htwo := StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.two_le_cutCapacity
      G u v huv hG R (by simpa [source] using hsR) (by simpa [sink] using htR)
    rw [hcutEq, hcut] at htwo
    exact htwo
  obtain ⟨ρ₁, ρ₂, hρ₁ne, hρ₂ne, hroutes, hload⟩ :=
    IntegralFlowDecomposesIntoSimpleSourceSinkPaths
      StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.tail
      StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.head
      (StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.capacity G u v) f
      source sink k hst hflow hk
  have hroute₁ := hroutes ρ₁ (by simp)
  have hroute₂ := hroutes ρ₂ (by simp)
  have hcap₁ : ∀ a ∈ ρ₁,
      0 < StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.capacity G u v a := by
    intro a ha
    have hc : 0 < ρ₁.count a := List.count_pos_iff.mpr ha
    have hl := hload a
    have hf := hflow.1 a
    omega
  have hcap₂ : ∀ a ∈ ρ₂,
      0 < StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.capacity G u v a := by
    intro a ha
    have hc : 0 < ρ₂.count a := List.count_pos_iff.mpr ha
    have hl := hload a
    have hf := hflow.1 a
    omega
  obtain ⟨w₁, hw₁support, hw₁internal⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitRoute.route_to_walk
      G u v ρ₁ hρ₁ne
      (by simpa [source] using hroute₁.1)
      (by simpa [sink] using hroute₁.2.1)
      hroute₁.2.2.1 hcap₁
  obtain ⟨w₂, hw₂support, hw₂internal⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitRoute.route_to_walk
      G u v ρ₂ hρ₂ne
      (by simpa [source] using hroute₂.1)
      (by simpa [sink] using hroute₂.2.1)
      hroute₂.2.2.1 hcap₂
  let p : G.Walk u v := w₁.bypass
  let q : G.Walk u v := w₂.bypass
  have hp : p.IsPath := by simpa [p] using w₁.bypass_isPath
  have hq : q.IsPath := by simpa [q] using w₂.bypass_isPath
  have hpSub : ∀ x ∈ p.support, x ∈ w₁.support := by
    intro x hx
    exact w₁.support_bypass_subset (by simpa [p] using hx)
  have hqSub : ∀ x ∈ q.support, x ∈ w₂.support := by
    intro x hx
    exact w₂.support_bypass_subset (by simpa [q] using hx)
  have hinter : ∀ x ∈ p.support, x ∈ q.support → x = u ∨ x = v := by
    intro x hxp hxq
    by_contra hxends
    push_neg at hxends
    have hx₁ : Sum.inl x ∈ ρ₁ :=
      hw₁internal x (hpSub x hxp) hxends.1 hxends.2
    have hx₂ : Sum.inl x ∈ ρ₂ :=
      hw₂internal x (hqSub x hxq) hxends.1 hxends.2
    have hc₁ : 0 < ρ₁.count (Sum.inl x) := List.count_pos_iff.mpr hx₁
    have hc₂ : 0 < ρ₂.count (Sum.inl x) := List.count_pos_iff.mpr hx₂
    have hl := hload (Sum.inl x)
    have hf := hflow.1 (Sum.inl x)
    have hcapx : StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.capacity G u v
        (Sum.inl x) = 1 := by
      simp [StrongPerfectGraphTheorem.ProofLemmas.TwoVertexSplitNetwork.capacity, hxends.1, hxends.2]
    omega
  have hpq : p.support ≠ q.support := by
    intro heq
    obtain ⟨x, hux, p', hpcons⟩ := p.exists_eq_cons_of_ne huv
    have hxp : x ∈ p.support := by
      rw [hpcons]
      exact SimpleGraph.Walk.support_subset_support_cons p' hux p'.start_mem_support
    have hxu : x ≠ u := hux.ne.symm
    have hxv : x ≠ v := by
      intro hx
      subst x
      exact hnadj hux
    have hxq : x ∈ q.support := by simpa [heq] using hxp
    exact (hinter x hxp hxq).elim hxu hxv
  exact ⟨p, q, hp, hq, hpq, hinter⟩

end StrongPerfectGraphTheorem.ProofLemmas.TwoVertexMengerForNonadjacentVertices
