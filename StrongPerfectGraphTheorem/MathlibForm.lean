module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import StrongPerfectGraphTheorem.MainTheorem

/-!
# The main theorem in Mathlib's language

`Challenge.lean` states the Strong Perfect Graph Theorem with Mathlib's notions. There, an odd
hole of `G` is an induced copy of `SimpleGraph.cycleGraph n` in `G` for some odd `n ≥ 5`.

The library works with holes as lists of vertices instead: `Types.Core.SPGT.IsHoleList G c` says
that the list `c` has at least four vertices, no repeated vertex, and that two vertices of `c`
are adjacent exactly when their positions are cyclically consecutive. Its main theorem,
`MainTheorem.SPGT.thm_1_2`, says that `G` is perfect if and only if every hole of `G` and of `Gᶜ`
has even length.

This file shows that the two notions of hole agree
(`exists_isHoleList_iff_isIndContained`) and restates `thm_1_2` with Mathlib's notions
(`strong_perfect_graph_theorem`). `Solution.lean` uses only the last result.
-/

@[expose] public section

namespace StrongPerfectGraphTheorem.MathlibForm

open SimpleGraph StrongPerfectGraphTheorem.Types.Core.SPGT

/-- Two vertices of the cycle on `Fin (m + 2)` are adjacent exactly when their positions are
cyclically consecutive. -/
theorem cycleGraph_adj_iff_val (m : ℕ) (a b : Fin (m + 2)) :
    (cycleGraph (m + 2)).Adj a b ↔
      (b.val = (a.val + 1) % (m + 2) ∨ a.val = (b.val + 1) % (m + 2)) := by
  rw [cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add', Fin.ext_iff, Fin.ext_iff,
    Fin.val_add, Fin.val_add, Fin.val_one]
  exact Or.comm

/-- For `n ≥ 4`, `G` has a hole with `n` vertices, in the list sense of `IsHoleList`, if and only
if the cycle on `n` vertices is isomorphic to an induced subgraph of `G`.

The list `c` gives the embedding `i ↦ c[i]`, and an embedding `f` gives the list
`[f 0, …, f (n - 1)]`. -/
theorem exists_isHoleList_iff_isIndContained {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (hn : 4 ≤ n) :
    (∃ c : List V, IsHoleList G c ∧ c.length = n) ↔ (cycleGraph n).IsIndContained G := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  constructor
  · rintro ⟨c, ⟨-, hnd, hadj⟩, hlen⟩
    refine ⟨{ toFun := fun i => c.get (i.cast hlen.symm), inj' := ?_, map_rel_iff' := ?_ }⟩
    · intro i j hij
      simpa [Fin.ext_iff] using (List.Nodup.get_inj_iff hnd).1 hij
    · intro i j
      simp only [Function.Embedding.coeFn_mk, List.get_eq_getElem, Fin.val_cast]
      rw [hadj i.val j.val (by omega) (by omega), cycleGraph_adj_iff_val, hlen]
  · rintro ⟨f⟩
    refine ⟨List.ofFn f, ⟨by simpa using hn, List.nodup_ofFn.2 f.injective, ?_⟩, by simp⟩
    intro i j hi hj
    simp only [List.length_ofFn] at hi hj ⊢
    simp only [List.getElem_ofFn]
    rw [f.map_adj_iff, cycleGraph_adj_iff_val]

/-- Every hole of `G` has even length if and only if, for every odd `n ≥ 5`, the cycle on `n`
vertices is not an induced subgraph of `G`. A hole has length at least four, so a hole of odd
length has length at least five. -/
theorem forall_isHoleList_even_iff {V : Type*} (G : SimpleGraph V) :
    (∀ c : List V, IsHoleList G c → Even (holeLength c)) ↔
      ¬ ∃ n : ℕ, 5 ≤ n ∧ Odd n ∧ (cycleGraph n).IsIndContained G := by
  constructor
  · rintro h ⟨n, hn5, hodd, hind⟩
    obtain ⟨c, hc, rfl⟩ := (exists_isHoleList_iff_isIndContained G (by omega)).2 hind
    exact Nat.not_even_iff_odd.2 hodd (h c hc)
  · intro h c hc
    by_contra heven
    have hodd : Odd c.length := Nat.not_even_iff_odd.1 heven
    have h5 : 5 ≤ c.length := by
      have h4 : 4 ≤ c.length := hc.1
      obtain ⟨k, hk⟩ := hodd
      omega
    exact h ⟨c.length, h5, hodd, (exists_isHoleList_iff_isIndContained G hc.1).1 ⟨c, hc, rfl⟩⟩

/-- **The Strong Perfect Graph Theorem**, in Mathlib's language. A finite graph `G` is perfect
(every induced subgraph has chromatic number equal to its clique number) if and only if, for
every odd `n ≥ 5`, the cycle on `n` vertices is an induced subgraph of neither `G` nor `Gᶜ`.

This is `MainTheorem.SPGT.thm_1_2`, with holes translated by `forall_isHoleList_even_iff`. -/
theorem strong_perfect_graph_theorem {V : Type*} [Finite V] (G : SimpleGraph V) :
    (∀ X : Set V, (G.induce X).chromaticNumber = (G.induce X).cliqueNum) ↔
      (¬ ∃ n : ℕ, 5 ≤ n ∧ Odd n ∧ (cycleGraph n).IsIndContained G) ∧
        ¬ ∃ n : ℕ, 5 ≤ n ∧ Odd n ∧ (cycleGraph n).IsIndContained Gᶜ := by
  have := Fintype.ofFinite V
  classical
  rw [← forall_isHoleList_even_iff G, ← forall_isHoleList_even_iff Gᶜ]
  exact StrongPerfectGraphTheorem.MainTheorem.SPGT.thm_1_2 G

end StrongPerfectGraphTheorem.MathlibForm
