module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.SkewTools
public import StrongPerfectGraphTheorem.Types.Wheels
public import StrongPerfectGraphTheorem.Types.WheelSystems
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Statements.S16.Thm_16_2
public import StrongPerfectGraphTheorem.Statements.S22.Thm_22_3
public import StrongPerfectGraphTheorem.ProofLemmas.PathBasics
public import StrongPerfectGraphTheorem.ProofLemmas.HoleBasics
public import StrongPerfectGraphTheorem.ProofLemmas.Thm231AttachmentSet

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S23

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.BasicClasses.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.SkewTools StrongPerfectGraphTheorem.Types.SkewTools.SPGT
open StrongPerfectGraphTheorem.Types.Wheels StrongPerfectGraphTheorem.Types.Wheels.SPGT
open StrongPerfectGraphTheorem.Types.WheelSystems StrongPerfectGraphTheorem.Types.WheelSystems.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two vertices of a hole of length `≥ 6` at cyclic distance `2` are distinct and
nonadjacent.  (Used for the paper's `c₁, c₃`.) -/
private theorem consec_ends {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {C : List V} (hC : IsHoleList G C) (hlen : 6 ≤ C.length)
    {p₁ p₂ p₃ : V} (h : ∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k) :
    p₁ ≠ p₃ ∧ ¬ G.Adj p₁ p₃ := by
  obtain ⟨k, t, ht⟩ := h
  have hDhole : IsHoleList G (C.rotate k) := StrongPerfectGraphTheorem.ProofLemmas.HoleBasics.isHoleList_rotate hC k
  have hDlen : (C.rotate k).length = C.length := List.length_rotate _ _
  have hD : C.rotate k = p₁ :: p₂ :: p₃ :: t := by rw [← ht]; rfl
  have h0 : (0 : ℕ) < (C.rotate k).length := by omega
  have h2 : (2 : ℕ) < (C.rotate k).length := by omega
  have e0 : (C.rotate k)[0]'h0 = p₁ := by simp [hD]
  have e2 : (C.rotate k)[2]'h2 = p₃ := by simp [hD]
  constructor
  · rw [← e0, ← e2]
    exact StrongPerfectGraphTheorem.ProofLemmas.HoleBasics.hole_ne_of_ne_index hDhole h0 h2 (by omega)
  · rw [← e0, ← e2]
    refine StrongPerfectGraphTheorem.ProofLemmas.HoleBasics.hole_not_adj_of_gap' hDhole h0 h2 ?_ ?_
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem thm_23_1 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y) :
    ∃ (c₁ c₂ c₃ : V) (P : List V),
      (∃ k : ℕ, [c₁, c₂, c₃] <+: C.rotate k) ∧
      VertexComplete G c₁ Y ∧ VertexComplete G c₂ Y ∧ VertexComplete G c₃ Y ∧
      IsPathFrom G P c₁ c₃ ∧
      SPGT.interior P ≠ [] ∧
      (∀ w ∈ SPGT.interior P, w ∉ C ∧ w ∉ Y) ∧
      (∀ w ∈ SPGT.interior P, ¬ VertexComplete G w Y) ∧
      (∀ w ∈ SPGT.interior P, ∀ c ∈ C, c ≠ c₁ → c ≠ c₂ → c ≠ c₃ → ¬ G.Adj w c) := by
  classical
  have hF6 : InF6 G := hG.1.1
  have hwheel : IsWheel G C Y := hopt.1
  have hCh : IsHoleList G C := hwheel.1.1
  have hClen : 6 ≤ C.length := hwheel.1.2
  -- The first paragraph of the printed proof: 15.2 and the minimal subpath `P'`.
  obtain ⟨F, hFC, hFY, hFconn, hFnc, a, ha, b, hb, hopp, hnadjab⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm231AttachmentSet.exists_interior_set G hG hbsp C Y hopt
  -- Packaging of the third alternative of 16.2 into the conclusion of 23.1.
  have key : ∀ (q₁ q₂ q₃ : V) (Q : List V),
      (∃ k : ℕ, [q₁, q₂, q₃] <+: C.rotate k) →
      VertexComplete G q₁ Y → VertexComplete G q₂ Y → VertexComplete G q₃ Y →
      IsPathFrom G Q q₁ q₃ →
      (∀ x ∈ SPGT.interior Q, x ∈ F) →
      (∀ x ∈ SPGT.interior Q, ∀ u ∈ C, u ≠ q₁ → u ≠ q₂ → u ≠ q₃ → ¬ G.Adj x u) →
      ∃ (c₁ c₂ c₃ : V) (P : List V),
        (∃ k : ℕ, [c₁, c₂, c₃] <+: C.rotate k) ∧
        VertexComplete G c₁ Y ∧ VertexComplete G c₂ Y ∧ VertexComplete G c₃ Y ∧
        IsPathFrom G P c₁ c₃ ∧
        SPGT.interior P ≠ [] ∧
        (∀ w ∈ SPGT.interior P, w ∉ C ∧ w ∉ Y) ∧
        (∀ w ∈ SPGT.interior P, ¬ VertexComplete G w Y) ∧
        (∀ w ∈ SPGT.interior P, ∀ c ∈ C, c ≠ c₁ → c ≠ c₂ → c ≠ c₃ → ¬ G.Adj w c) := by
    intro q₁ q₂ q₃ Q hcons hc1 hc2 hc3 hQ hQF hQnb
    obtain ⟨hne13, hnadj13⟩ := consec_ends hCh hClen hcons
    have hQlen : 0 < Q.length := StrongPerfectGraphTheorem.ProofLemmas.PathBasics.path_length_pos hQ.1
    have hlen3 : 3 ≤ Q.length := by
      by_contra hcon
      push_neg at hcon
      have h12 : Q.length = 1 ∨ Q.length = 2 := by omega
      rcases h12 with h1 | h1
      · apply hne13
        obtain ⟨hq1, hq3⟩ := StrongPerfectGraphTheorem.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ
        match Q, h1, hq1, hq3 with
        | [x], _, hq1, hq3 => simp only [List.mem_singleton] at hq1 hq3; rw [hq1, hq3]
      · refine hnadj13 (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hQ ?_)
        rw [StrongPerfectGraphTheorem.ProofLemmas.PathBasics.pathLength_eq, h1]
    exact ⟨q₁, q₂, q₃, Q, hcons, hc1, hc2, hc3, hQ,
      StrongPerfectGraphTheorem.ProofLemmas.PathBasics.interior_ne_nil hQ.1 hlen3,
      fun w hw => ⟨hFC w (hQF w hw), hFY w (hQF w hw)⟩,
      fun w hw => hFnc w (hQF w hw),
      fun w hw c hc hb1 hb2 hb3 => hQnb w hw c hc hb1 hb2 hb3⟩
  -- 16.2 applied to `F`.
  rcases StrongPerfectGraphTheorem.Statements.S16.SPGT.thm_16_2 G hF6 C Y hwheel F hFC hFY hFconn hFnc
      (attachments G F {u : V | u ∈ C}) rfl ⟨a, ha, b, hb, hopp⟩
      ⟨a, ha, b, hb, hopp.1, hnadjab⟩ with halt | halt | halt
  · -- First alternative: a wheel with strictly larger hub, contrary to optimality.
    exfalso
    obtain ⟨v, hvF, hw⟩ := halt
    refine hopt.2 ⟨C, Y ∪ {v}, hw, Set.subset_union_left, ?_⟩
    intro hsub
    exact hFY v hvF (hsub (Set.mem_union_right _ rfl))
  · -- Second alternative: a kite for `(C,Y)`, contrary to 22.3.
    exfalso
    obtain ⟨v, hvF, hv4, p₁, p₂, p₃, -, hcons, hp1, hp2, hp3, -⟩ := halt
    have hadjv : ∀ w : V, VertexComplete G w (Y ∪ {v}) → G.Adj v w :=
      fun w hw => (hw v (Set.mem_union_right _ rfl)).symm
    have hYc : ∀ w : V, VertexComplete G w (Y ∪ {v}) → VertexComplete G w Y :=
      fun w hw x hx => hw x (Set.mem_union_left _ hx)
    have hset : {c : V | c ∈ C ∧ G.Adj v c} = G.neighborSet v ∩ {u : V | u ∈ C} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
      exact and_comm
    refine StrongPerfectGraphTheorem.Statements.S22.SPGT.thm_22_3 G hG hbsp C Y hopt ⟨v, hwheel, hFY v hvF, hFC v hvF, hFnc v hvF, ?_, ?_⟩
    · rw [hset]; exact hv4
    · obtain ⟨k, hk⟩ := hcons
      rcases hk with hk | hk
      · exact ⟨p₁, p₂, p₃, ⟨k, hk⟩, hadjv _ hp1, hadjv _ hp2, hadjv _ hp3,
          hYc _ hp1, hYc _ hp2, hYc _ hp3⟩
      · exact ⟨p₃, p₂, p₁, ⟨k, hk⟩, hadjv _ hp3, hadjv _ hp2, hadjv _ hp1,
          hYc _ hp3, hYc _ hp2, hYc _ hp1⟩
  · -- Third alternative: exactly the conclusion of 23.1.
    obtain ⟨p₁, p₂, p₃, ⟨k, hk⟩, hc1, hc2, hc3, P, hP, hPF, hPnb⟩ := halt
    rcases hk with hk | hk
    · exact key p₁ p₂ p₃ P ⟨k, hk⟩ hc1 hc2 hc3 hP hPF hPnb
    · refine key p₃ p₂ p₁ P.reverse ⟨k, hk⟩ hc3 hc2 hc1
        (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.isPathFrom_reverse hP) ?_ ?_
      · intro x hx
        exact hPF x (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.mem_interior_reverse.mp hx)
      · intro x hx u hu hb1 hb2 hb3
        exact hPnb x (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.mem_interior_reverse.mp hx) u hu hb3 hb2 hb1


end SPGT

end StrongPerfectGraphTheorem.Statements.S23
