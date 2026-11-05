# The Strong Perfect Graph Theorem in Lean

This repository contains a complete Lean 4 proof of the Strong Perfect Graph Theorem:

> A finite graph is perfect if and only if it is Berge.

A graph is *perfect* if every induced subgraph can be colored with as many colors as the size
of its largest clique. A *hole* is an induced cycle of length at least four, and an *antihole*
is an induced subgraph whose complement is a hole. A graph is *Berge* if it has no hole of odd
length and no antihole of odd length.

Berge conjectured the theorem in 1961. Chudnovsky, Robertson, Seymour and Thomas proved it in

> M. Chudnovsky, N. Robertson, P. Seymour and R. Thomas, *The strong perfect graph theorem*,
> Annals of Mathematics 164 (2006), 51–229. [doi:10.4007/annals.2006.164.51](https://doi.org/10.4007/annals.2006.164.51)

The Lean proof follows this paper, result by result. It has no `sorry`, and it uses only the
three standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## The statement

The statement is in [`Challenge.lean`](Challenge.lean). It imports only Mathlib, and it uses
only Mathlib's notions of induced subgraph, chromatic number, clique number, cycle graph and
induced copy.

```lean
namespace SimpleGraph

variable {V : Type*}

def IsPerfect (G : SimpleGraph V) : Prop :=
  ∀ X : Set V, (G.induce X).chromaticNumber = (G.induce X).cliqueNum

def HasOddHole (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ Odd n ∧ (cycleGraph n).IsIndContained G

def IsBerge (G : SimpleGraph V) : Prop :=
  ¬ G.HasOddHole ∧ ¬ Gᶜ.HasOddHole

theorem strong_perfect_graph_theorem [Finite V] (G : SimpleGraph V) :
    G.IsPerfect ↔ G.IsBerge := by
  sorry
```

`HasOddHole` asks for an odd cycle of length at least 5 rather than at least 4. These are the
same, because an odd number that is at least 4 is at least 5. An odd antihole of `G` is an odd
hole of the complement `Gᶜ`, which is why `IsBerge` looks at both `G` and `Gᶜ`.

[`Solution.lean`](Solution.lean) repeats these definitions word for word and proves the theorem.
The file [`comparator.json`](comparator.json) lets Lean's `lake comparator` check that the two
files state the same theorem and that the proof uses no other axioms.

## Checking the proof

You need [elan](https://github.com/leanprover/elan). The Lean version is fixed by
`lean-toolchain` (Lean `v4.35.0-rc3`), and the Mathlib version is fixed by `lake-manifest.json`.

```sh
lake exe cache get   # download the compiled Mathlib
lake build           # build the library, Challenge.lean and Solution.lean
```

The full build checks about 1,200 modules on top of Mathlib. They need about two hours of CPU
time in total, so the build takes a few minutes on a machine with many cores and longer on a
laptop. The only `sorry` warning should come from `Challenge.lean`, where the `sorry` is on
purpose.

To compare the statement with the proof:

```sh
lake comparator --config comparator.json
```

This rebuilds both files in a sandbox (it needs `bwrap` on Linux), checks that `Solution.lean`
proves the theorem of `Challenge.lean` with the same definitions, and checks that the proof uses
only the axioms listed in `comparator.json`.

To print the axioms yourself, add these lines to a file that imports `Solution`:

```lean
#print axioms SimpleGraph.strong_perfect_graph_theorem
-- 'SimpleGraph.strong_perfect_graph_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## How the proof is organized

The library does not use Mathlib's definitions in its own work. It has its own definitions,
written to follow the paper's wording, so that each Lean statement can be checked against the
printed one. For example, a hole is a list of vertices in cyclic order.
[`StrongPerfectGraphTheorem/MathlibForm.lean`](StrongPerfectGraphTheorem/MathlibForm.lean)
proves that this notion of hole agrees with Mathlib's induced copies of `cycleGraph n`, and
restates the main theorem with Mathlib's notions. `Solution.lean` uses only that restatement.

The proof itself follows the paper.

* **1.2, the main theorem**, is proved in
  [`MainTheorem.lean`](StrongPerfectGraphTheorem/MainTheorem.lean) as `thm_1_2`. It follows the
  paper's short proof: a smallest graph that is Berge but not perfect would have to be
  one of the cases of 1.3, and each case is ruled out.
* **1.3, the decomposition theorem**, says that every Berge graph is basic or has one of four
  kinds of decomposition. It takes up Sections 2 to 24 of the paper. As in the paper, the proof
  shows that a counterexample to 1.3 would be *recalcitrant*, and then proves 13.5 and the
  twelve steps of 1.8 about recalcitrant graphs. These steps are 5.1, 5.2, 9.6, 10.6, 13.4,
  14.3, 16.3, 18.7, 23.2, 23.4, 23.5 and 24.1.
* **1.5** says that a smallest imperfect graph has no balanced skew partition.
* **Earlier results that the paper cites** are proved too: Lovász's theorem 1.1 and his
  replication lemma, the results of Cornuéjols and Cunningham on 2-joins, of Chvátal and Sbihi
  on homogeneous pairs, of Chvátal on star cutsets, the lemma of Roussel and Rubio used as 2.1,
  and the fact that basic graphs are perfect. The library also proves Dirac's theorem on
  subdivisions of K₄, which the paper uses without a citation.

### Layout

| Path | Contents |
|---|---|
| `Challenge.lean`, `Solution.lean`, `comparator.json` | The statement, its proof, and the Comparator configuration. |
| `StrongPerfectGraphTheorem/MainTheorem.lean` | 1.2, as `StrongPerfectGraphTheorem.MainTheorem.SPGT.thm_1_2`. |
| `StrongPerfectGraphTheorem/MathlibForm.lean` | The translation to Mathlib's notions. |
| `StrongPerfectGraphTheorem/Types/` | The definitions of the paper: holes, paths, decompositions, line graphs, prisms, wheels, the classes F₁ to F₁₁, and so on. |
| `StrongPerfectGraphTheorem/Statements/S01/` to `S24/` | One file per numbered result of the paper. For example, `S09/Thm_9_3.lean` states and proves 9.3. `S01/Thm_E2` to `Thm_E7` are the earlier results cited in Section 1. |
| `StrongPerfectGraphTheorem/ProofLemmas/` | The lemmas used to prove the numbered results. Their names say which result and which claim of its proof they belong to, for example `Thm192Claim6` for claim (6) in the proof of 19.2. |
| `StrongPerfectGraphTheorem/ProofLemmaStatements/`, `PriorWork/` | One shared lemma statement, and Dirac's theorem. |
| `StrongPerfectGraphTheorem/Counterexamples/` | A finite graph showing that 9.3 is false as printed (see below). The proof does not use it. |
| `docs/NOTES_ON_THE_PAPER.md` | Every place where the Lean departs from the printed text. |

Most numbered results have a docstring that quotes the printed statement. Most proof steps
quote the printed sentence they prove, in a comment marked `PAPER:`.

A few numbered items of the paper have no file of their own.

* 1.4 is a stronger theorem from Chudnovsky's thesis, which the paper states without proof.
  1.6 and 1.7 are conjectures.
* 1.8 is the list of the twelve steps above. Each step is proved in the file of the result
  that proves it.
* The paper says it does not use 3.1, and the Lean does not prove it.
* 18.1 is proved in the form that the proof of 18.5 needs, in `ProofLemmas/Thm181Local.lean`.
* 23.6 is a theorem of Conforti, Cornuéjols and Zambelli. The paper mentions it as an
  alternative to Section 24 but does not use it.

## Notes on the paper

The main theorem of the paper is correct, and it is stated here as printed. Still, a proof of
this length that is checked line by line turns up some local errors. Three intermediate statements
are false as printed:

* **2.5** needs the hypothesis that X is anticonnected, which the nearby results 2.1, 2.2, 2.3
  and 2.10 have;
* the **second conclusion of 18.3** fails for subpaths of length 1;
* **outcome 4 of 9.3** is false. The module
  [`Counterexamples/Thm93.lean`](StrongPerfectGraphTheorem/Counterexamples/Thm93.lean) gives an
  11-vertex counterexample and checks it by computation.

In each case the Lean proves a corrected statement, and every use of it in the paper is covered
by the corrected version. There are also about sixty-five proof steps that are wrong as written or
leave out a case. The Lean gives a correct argument for each.
[`docs/NOTES_ON_THE_PAPER.md`](docs/NOTES_ON_THE_PAPER.md) lists all of them.

**Page numbers.** Page numbers in this repository ("printed p. 48") are the printed page numbers
of the authors' manuscript dated June 20, 2002, revised July 19, 2005, available at
<https://web.math.princeton.edu/~pds/papers/perfect/perfect.pdf>. Its theorem numbering is that
of the published paper.

## How this was made

The Lean code was written with AI agents, under the direction of the authors. We describe our
agentic framework for formalizing research mathematics in

> A. Soltani Moakhar, I. Gholami, M. Springer, M. JafariRaviz and M. Hajiaghayi, *Beyond the
> Library: An Agentic Framework for Autoformalizing Research Mathematics*,
> [arXiv:2606.31134v3](https://arxiv.org/abs/2606.31134v3) (August 5, 2026).

Every proof is checked by the Lean kernel, so the trust in the result rests on the statement in
`Challenge.lean`, not on how the proofs were written. An automated audit compared every
numbered statement and every printed proof step with the Lean text. Its findings are in
`docs/NOTES_ON_THE_PAPER.md`. No human expert has yet reviewed the whole library line by line.

## Related work

Singh and Natarajan formalized the weak perfect graph theorem in Coq
(*A constructive formalization of the weak perfect graph theorem*, CPP 2020,
[doi:10.1145/3372885.3373819](https://doi.org/10.1145/3372885.3373819)). This library proves
the weak theorem independently, as 1.1. We do not know of an earlier complete formalization of
the strong theorem, but we have not done a full literature search.

## Authors

Arshia Soltani Moakhar, Iman Gholami, Max Springer, Mahdi JafariRaviz and MohammadTaghi
Hajiaghayi.

Maintainer: Mahdi JafariRaviz.

The metadata for the [Palomar registry](https://palomar-registry.org) is in
[`formalization.yaml`](formalization.yaml).

## Citing

If you use this formalization, please cite the paper it formalizes and our paper:

```bibtex
@article{chudnovsky2006strong,
  title   = {The strong perfect graph theorem},
  author  = {Chudnovsky, Maria and Robertson, Neil and Seymour, Paul and Thomas, Robin},
  journal = {Annals of Mathematics},
  volume  = {164},
  number  = {1},
  pages   = {51--229},
  year    = {2006},
  doi     = {10.4007/annals.2006.164.51}
}

@misc{soltanimoakhar2026beyond,
  title         = {Beyond the Library: An Agentic Framework for Autoformalizing Research Mathematics},
  author        = {Soltani Moakhar, Arshia and Gholami, Iman and Springer, Max and JafariRaviz, Mahdi and Hajiaghayi, MohammadTaghi},
  year          = {2026},
  eprint        = {2606.31134},
  archivePrefix = {arXiv},
  primaryClass  = {cs.AI},
  note          = {Version 3, August 5, 2026},
  url           = {https://arxiv.org/abs/2606.31134v3}
}
```

## License

Apache License 2.0. See [`LICENSE`](LICENSE).
