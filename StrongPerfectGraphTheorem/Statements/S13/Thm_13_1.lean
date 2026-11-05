module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Staircases
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.ProofLemmas.Thm131Claim2
public import StrongPerfectGraphTheorem.ProofLemmas.Thm131Claim4
public import StrongPerfectGraphTheorem.ProofLemmas.Thm131Claim7
public import StrongPerfectGraphTheorem.ProofLemmas.Thm131Closing

/-!
# Section 13 — The long odd prism

The seven numbered statements 13.1–13.7 of Chudnovsky–Robertson–Seymour–Thomas, *The Strong
Perfect Graph Theorem* (published/Annals version, printed pages 78–86).

Every defined term used here is imported and never restated:

* *right-sequence*, *earlier*, *predecessor*, *trajectory*, *birth*, *`b`-optimal banister*,
  *3-breaker* and *recalcitrant* come from `StrongPerfectGraphTheorem.Types.LongOddPrism`;
* *strongly maximal staircase*, *right-star*, *banister*, *1-breaker* and *2-breaker* from
  `StrongPerfectGraphTheorem.Types.Staircases`;
* *even prism*, *long prism*, *odd prism* from `StrongPerfectGraphTheorem.Types.Prisms`;
* *appearance* from `StrongPerfectGraphTheorem.Types.Appearances`;
* the class `F₅` from `StrongPerfectGraphTheorem.Types.Classes`;
* *proper 2-join*, *proper homogeneous pair*, *balanced skew partition* from
  `StrongPerfectGraphTheorem.Types.Decompositions`;
* *Berge*, *path*, *antipath*, *length*, *interior*, *`X`-complete*, *`X`-complete edge*,
  *complete to*, *anticonnected* from `StrongPerfectGraphTheorem.Types.Core`.

Encoding conventions:

* a path/antipath is the list of its vertices in order; `V(P)` for such a list `P` is
  `{v | v ∈ P}`, `P*` is `SPGT.interior P` and the length of `P` is `pathLength P`;
* a staircase `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` is carried by the seven pieces of data
  `A C B : Set V`, `a₀ : V`, `R₀ : List V`, `b₀ : V`, and `V(K)` is `staircaseVertices`;
* the paper's right-sequence `x₁, …, x_t` is the list `x : List V`, and the set
  `X = {x₁, …, x_t}` is `{v | v ∈ x}`;
* *"there is no appearance of `K₄` in `G`"* is `¬ Appears G (⊤ : SimpleGraph (Fin 4))`;
* *"there is no even prism in `G`"* is: no three paths of `G` form an even prism;
* *"there is no 1-breaker in `G`"*, *"no 2-breaker"*, *"there is a 3-breaker"* existentially
  quantify the data carried by `IsOneBreaker`, `IsTwoBreaker`, `IsThreeBreaker`.

Published-vs-draft notes (see the transcription file for the full list):

* **13.4** is the *published* form: its 2-joins are **proper** 2-joins and its third outcome is
  *"`G` admits a **proper homogeneous pair**"* (the arXiv draft said *"an M-join"*).  Its
  hypothesis is transcribed literally — *"`G` is Berge, there is no appearance of `K₄` in
  either `G` or `Ḡ`, and `G` contains a long odd prism as an induced subgraph"* — and **not**
  as *"`G, Ḡ ∈ F₄`"*, which is how the statement 1.8.5 that 13.4 restates is phrased; the two
  agree only modulo the elsewhere-proved disposal of long *even* prisms.
* **13.6** carries the published hypothesis `X ⊆ V(G) \ V(P)` (the draft had `X ⊆ V(G)`).
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S13

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Staircases StrongPerfectGraphTheorem.Types.Staircases.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.Thm131Trajectory
open StrongPerfectGraphTheorem.ProofLemmas.Thm131EdgeCases
open StrongPerfectGraphTheorem.ProofLemmas.Thm131Claim2
open StrongPerfectGraphTheorem.ProofLemmas.Thm131Claim4
open StrongPerfectGraphTheorem.ProofLemmas.Thm131Claim7
open StrongPerfectGraphTheorem.ProofLemmas.Thm131Closing
open StrongPerfectGraphTheorem.ProofLemmas.Thm132Infrastructure

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **13.1** (printed pp. 79–80)

PAPER: *"Let `G` be Berge, containing no appearance of `K₄`, no even prism, no 1-breaker and
no 2-breaker.  Let `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` be a strongly maximal staircase in `G`,
and let `x₁, …, x_t` be a right-sequence.  Let `b` be a right-star, and let `a`-`R`-`b` be a
`b`-optimal banister.  Let `a`-`w₁`-`⋯`-`w_n` be the trajectory of `a`.  Then `n` is odd, and
either:*

*• `b` is the unique vertex of `R` which is `{w₁, …, w_n}`-complete, or*

*• `R` has length 1, and there exists some even `m` with `1 ≤ m < n` such that
`a`-`w₁`-`⋯`-`w_m`-`b` is an antipath."*

Notes on the transcription.

* *"the trajectory of `a`"* is the second of the section's two `trajectory` notions (the one
  for a general vertex, printed p. 79), which produces the antipath `a`-`w₁`-`⋯`-`w_n`
  **including** its first vertex `a`; so the trajectory is the list `a :: w` with
  `w = [w₁, …, w_n]`, and the paper's `n` is `w.length`.
* `{w₁, …, w_n}` is `{u | u ∈ w}`, and *"`b` is the unique vertex of `R` which is
  `{w₁, …, w_n}`-complete"* is: a vertex of `R` is `{w₁, …, w_n}`-complete exactly when it is
  `b` (`b` is a vertex of `R`, being one of its ends).
* `a`-`w₁`-`⋯`-`w_m`-`b` is the list `a :: (w.take m ++ [b])`, since `w.take m` is
  `[w₁, …, w_m]`. -/
theorem thm_13_1 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (x : List V) (hx : IsRightSequence G A C B x)
    (b : V) (hb : IsRightStar G A C B b)
    (a : V) (R : List V) (hopt : BOptimalBanister G A C B x a R b)
    (w : List V) (htraj : trajectoryOfVertex G A x a (a :: w)) :
    Odd w.length ∧
      ((∀ r ∈ R, (VertexComplete G r {u : V | u ∈ w} ↔ r = b)) ∨
        (pathLength R = 1 ∧
          ∃ m : ℕ, Even m ∧ 1 ≤ m ∧ m < w.length ∧
            IsAntipathList G (a :: (w.take m ++ [b])))) := by
  classical
  -- The printed proof is an induction on `t`, the length of the right-sequence:
  -- *"We proceed by induction on `t`, and assume the result holds for all smaller
  -- values of `t`."*
  have claim : ∀ n : ℕ, ∀ (y : List V), y.length = n →
      IsRightSequence G A C B y →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (P : List V), BOptimalBanister G A C B y c P d →
      ∀ (z : List V), trajectoryOfVertex G A y c (c :: z) →
        TrajectoryConclusion G c P d z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hylen hy d hd c P hP z hz
      have hS : StepConnected G A C B := hK.1.1.1
      have hIH : ∀ (q : List V), q.length < y.length →
          IsRightSequence G A C B q →
          ∀ (d' : V), IsRightStar G A C B d' →
          ∀ (c' : V) (Q : List V), BOptimalBanister G A C B q c' Q d' →
          ∀ (z' : List V), trajectoryOfVertex G A q c' (c' :: z') →
            TrajectoryConclusion G c' Q d' z' := by
        intro q hq hqseq d' hd' c' Q hQ z' hz'
        exact ih q.length (by omega) q rfl hqseq d' hd' c' Q hQ z' hz'
      -- PAPER (1): *"`n` is odd."*
      have hodd : Odd z.length := trajectory_tail_odd hG hS hy hP.1.2.2.1 hz
      obtain ⟨i, hi, j, hj, hcbirth, hantiData, hidx⟩ :=
        trajectoryOfVertex_data hS hy hP.1.2.2.1 hz
      let last : V := y[j]
      have hanti : IsAntipathFrom G (c :: z) c last := by
        simpa [last] using hantiData
      have hbeforeA : ∀ u ∈ z, u ≠ last → VertexComplete G u A :=
        trajectory_before_last_left_complete hz hanti
      have hzB : ∀ u ∈ z, VertexComplete G u B :=
        trajectory_tail_right_complete hS hy hP.1.2.2.1 hz hanti
      have hdnotz : d ∉ z := optimal_right_end_not_mem_trajectory hS hy hd hP hz
      have hzpos : 0 < z.length := by obtain ⟨k, hk⟩ := hodd; omega
      have hz_ne : z ≠ [] := List.ne_nil_of_length_pos hzpos
      have hlastZ : z.getLast? = some last := by
        simpa [List.getLast?_cons_of_ne_nil hz_ne] using hanti.2.2
      obtain ⟨aMiss, haMissA, hlastMiss⟩ := trajectory_last_misses_left hz hanti
      -- PAPER (2): *"If `wₙ` has a neighbour in `A` then the theorem holds."*
      by_cases hAnb : ∃ u ∈ A, G.Adj last u
      · exact claim_two hG heven hK hP.1 hanti hodd hbeforeA hzB hdnotz hAnb
          ⟨aMiss, haMissA, hlastMiss⟩
      · -- PAPER: *"From (2) we may assume that `wₙ` has no neighbour in `A`."*
        push Not at hAnb
        have hlastAntiA : VertexAnticomplete G last A := fun u hu => hAnb u hu
        have hlastB : VertexComplete G last B :=
          hzB last (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.getLast_mem hlastZ)
        have hlastStar : IsRightStar G A C B last := by
          by_cases heq : last = b₀
          · simpa [heq] using hK.1.1.2.1.2.2.2.1
          · have hout : last ∉ staircaseVertices A C B R₀ :=
              bComplete_not_mem_staircase hK.1.1 hlastB heq
            rcases bComplete_rightStar_or_major hG hK4 heven h1br hK.1 hout hlastB with
              hs | hm
            · exact hs
            · obtain ⟨u, huA, hlu⟩ := hm.2.1
              exact absurd hlu (hlastAntiA u huA)
        -- PAPER (4): *"If `n = 1` then the theorem holds."*
        by_cases hzone : z.length = 1
        · exact claim_four hG hK4 heven h1br h2br hK hy hd hlastStar hP hz hIH
            hanti hzone
        · -- PAPER: *"We may therefore assume that `n ≥ 3` (since it is odd.)"*
          have hzlong : 1 < z.length := by
            obtain ⟨ko, hko⟩ := hodd
            omega
          by_cases hother : ∃ r ∈ P, r ≠ d ∧ VertexComplete G r {u : V | u ∈ z}
          · -- PAPER (closing paragraph): *"We may therefore assume that some
            -- vertex of `R \ b` is `W`-complete, for otherwise the theorem holds
            -- by (7). … a contradiction."*
            exact absurd (closing_absurd hG heven hK hP.1 hanti hodd hzlong
              hbeforeA hzB hdnotz hlastStar hother) (fun h => h.elim)
          · push Not at hother
            by_cases hdW : VertexComplete G d {u : V | u ∈ z}
            · refine ⟨hodd, Or.inl ?_⟩
              intro r hr
              constructor
              · intro hc
                by_contra hne
                exact hother r hr hne hc
              · rintro rfl
                exact hdW
            · -- PAPER (7): *"If no vertex in `R` is `W`-complete then the
              -- theorem holds."*
              refine claim_seven hG hK4 heven h1br h2br hK hy hd hP hz hIH hanti
                hodd hzlong hbeforeA hzB hdnotz hlastStar ?_
              intro r hr hc
              by_cases hrd : r = d
              · exact hdW (hrd ▸ hc)
              · exact hother r hr hrd hc
  exact claim x.length x rfl hx b hb a R hopt w htraj


end SPGT

end StrongPerfectGraphTheorem.Statements.S13
