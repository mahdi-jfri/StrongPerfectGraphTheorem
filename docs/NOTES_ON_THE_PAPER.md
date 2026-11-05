# Notes on the paper

This file lists the places where the Lean proof departs from the printed text of

> M. Chudnovsky, N. Robertson, P. Seymour and R. Thomas, *The strong perfect graph theorem*,
> Annals of Mathematics 164 (2006), 51–229.

The main theorem, 1.2, is true and is stated as in the paper. Almost all of the paper is also
correct as printed. The points below are local. Each one is a statement or a proof step that
needs a small fix, and the Lean supplies that fix.

**Page numbers.** All page numbers below, and in the Lean docstrings ("printed p. 48"), are the
printed page numbers of the authors' manuscript dated June 20, 2002, revised July 19, 2005. It
is available at <https://web.math.princeton.edu/~pds/papers/perfect/perfect.pdf>. Its theorem
numbering is the numbering of the published paper.

**How these notes were made.** AI agents compared every numbered statement of the paper, every
definition it uses, and every printed proof step, with the Lean text. They worked one section at
a time, plus one pass over the general lemmas. Each claimed counterexample was checked again
independently, by a finite computation or by hand. No human expert has yet checked the list
below line by line. Module names refer to files under `StrongPerfectGraphTheorem/`.

The notes have three parts.

* Part A lists three numbered statements that are false as printed.
* Part B lists printed proof steps that are wrong or leave out a case.
* Part C lists places where the text allows more than one reading, and says which reading the
  Lean uses.

## Part A. Statements that are false as printed

Three intermediate statements are false as printed. None of them affects the main theorem. In
each case the Lean states and proves a corrected version, and every use of the statement in
the paper is covered by the corrected version.

### A1. Outcome 4 of 9.3 (p. 48)

**What is printed.** Outcome 4 of 9.3 ends with "f is not adjacent to y₁".

**Why it is false.** There is an 11-vertex Berge graph that satisfies all hypotheses of 9.3,
in which outcomes 1 to 3 fail and printed outcome 4 also fails. The module
`Counterexamples/Thm93.lean` builds this graph and checks these facts by finite computation
(`StrongPerfectGraphTheorem.Counterexamples.Thm93.printed_nine_three_false`).

**What the Lean does.** `Statements/S09/Thm_9_3.lean` weakens the last clause to "f has a
non-neighbour, other than x, on the antipath that contains x". The same module checks that
the weakened clause holds in the 11-vertex graph (`repaired_conclusion11`). The only uses of 9.3 are
in 9.4 and 9.5, and both ignore this clause, so nothing else changes.

### A2. The second conclusion of 18.3 (p. 110)

**What is printed.** "The length of P′ has the same parity as the number of ends of P′ in
{p₁, pₙ} that are not Y-complete", for every maximal subpath P′ of P whose internal vertices
are not Y-complete.

**Why it is false.** Take a Y-complete edge pᵢpᵢ₊₁ of P. It is such a maximal subpath, of
length 1, and none of its ends counts, so the sentence says 1 ≡ 0 (mod 2). Read literally, the
statement would force P to have no Y-complete edge. This contradicts the third conclusion of
18.3, and also the use of 18.3 in 18.4 ("P contains an odd number of Y-complete edges"). The
printed proof works only with subpaths of length at least 2, and its last paragraph has the
correct three cases, including "either it has length 1".

**What the Lean does.** `Statements/S18/Thm_18_3.lean` adds the hypothesis that P′ has length
at least 2 to the second conclusion. The Lean proofs of 18.5 and 18.6, which use 18.3, go
through with the corrected statement.

### A3. 2.5 (p. 10)

**What is printed.** 2.5 has no hypothesis that X is anticonnected. The neighbouring
statements 2.1, 2.2, 2.3 and 2.10 all have this hypothesis.

**Why it is false.** Take seven vertices x₁, x₂, p₁, p₂, p₃, p₄, v, with X = {x₁, x₂},
P = p₁-p₂-p₃-p₄, and edges

> x₁x₂, x₁p₁, x₁p₂, x₁p₄, x₁v, x₂p₁, x₂p₃, x₂p₄, x₂v, p₁p₂, p₂p₃, p₃p₄.

This graph is Berge. Its holes are three holes of length 4, and it has no odd antihole. The
vertex v is X-complete and has no neighbour on P. Both outcomes of 2.5 fail.

**What the Lean does.** `Statements/S02/Thm_2_5.lean` adds the hypothesis that X is
anticonnected. The only use of 2.5 is in 2.8, where X is anticonnected.

### A related slip that does no harm

The preamble on p. 6 says that each class F₁, …, F₁₁ is a subclass of the previous one. But F₅
is printed as "all G ∈ F₃ such that …", not "all G ∈ F₄". The Lean copies the printed
definition (`Types/Classes.lean`). An even prism has at least 9 vertices, so it is long. Hence
"no long prism" already gives "no even prism", and F₅ ⊆ F₄ holds with either reading.

## Part B. Printed proof steps

In this part every numbered statement is true and the Lean states it as printed. What fails is
one sentence of the printed proof. The Lean gives a correct argument at that step. Most Lean
files quote the printed sentence in a `PAPER:` comment just above the step that proves it.

### B1. Proof sentences that are false as written

| Where | Printed sentence | What is wrong | Lean |
|---|---|---|---|
| 4.1 (p. 14) | "Then N′ = N ∪ {b₂} is not anticonnected" | False when N is empty, that is, when a₁ is isolated. Example: vertices a₁, c, x, y, one edge xy, A = {a₁, c}, B = {x, y}. | The case N = ∅ is handled on its own (`Thm_4_1`). |
| 4.5 (p. 17) | "we may assume A₁ ⊆ L, and B₁ ⊆ X. By hypothesis (A₁,B₁) is not a path or antipath pair" | The hypothesis is that (L,Y) is balanced, which needs B₁ ⊆ Y. | Uses the part of B inside Y (`Thm_4_5`). |
| 8.5 claim (2) (p. 42) | "no v ∈ V(J) such that X ⊆ ⋃(S_uv : uv ∈ E(J))" | The union over all edges always contains X. The intended union is over the edges at v. | States the intended union (`Thm85Claim2`). |
| 8.5 claim (4) (p. 43) | "there is a unique pair (i,j)" | As an ordered pair this fails when n = 1, since then f₁ = fₙ. The proof of claim (6) then gets n ≥ 2 from (4), which is circular under the ordered reading. | Proves uniqueness of the edge, and proves n ≥ 2 from the existence part only (`Thm85EndgameTraversalUnique`, `Thm85EndgamePathTwoVertices*`). |
| 9.6, last paragraph (p. 55) | "If M₀ is nonempty then G is not connected, and since \|V(G)\| ≥ 8 it therefore admits a balanced skew partition" | False on its own: the graph with 8 vertices and no edges is Berge and disconnected, and has no skew partition. True here because the setting gives an edge. | Adds the hypothesis that G has an edge (`DisconnectedLargeGraphHasBalancedSkewPartition`), and checks it in `Thm96Body`. |
| 10.6, last paragraph (p. 63) | "Let X be the union of S₁ and all components of V(G)∖V(H) whose attachment set is a subset of S₁" | A component with no attachments would lie in all three sets X, so (X,Y) is not a partition. The paper excludes such components two sentences earlier but does not say so again here. | Splits off this case (`Thm106Steps`). |
| 10.6, last paragraph (p. 63) | "Then \|Y\| ≥ 4, and so either (X,Y) is a proper 2-join …" | \|Y\| ≥ 4 handles only the "length ≥ 3" part of the last 2-join condition, not the "odd" part. | Uses \|A₂ ∪ A₃\| ≥ 2 instead (`HyperprismEndgame`). |
| 11.4 (p. 65) | "Since some vertex in B has a nonneighbour in F" | F is anticomplete to A ∪ B ∪ C by hypothesis, so this never happens. The intended word is Q, from the second condition of 11.4. | `Thm114Antipath`. |
| 12.1 case (4) (p. 70) | "since otherwise it is minor, and statement 3 of the theorem holds" | A minor vertex gives outcome 1, not 3. The matching sentence in case (2) says "statement 1". | `Thm121Case4`. |
| 12.4 claim (4) (p. 75) | "there exist adjacent a, b ∈ R₀*, both Q-complete" | 2.1, applied in the complement, says something about a and b only against the vertices of the antipath, and Q may be larger. This part of the claim is never used later. | Proves "complete to the interior q₁ … q_k" instead (`Thm124Claim4LeapQComplete`). We have not shown the printed clause false, only that the cited argument does not give it. |
| 16.1 claim (1) (p. 98) | "Since j is odd, exactly one of i−1, j−i is even" | When j is odd, i−1 and j−i always have the same parity. The intended pair is i−1 and j−i−1. | `OddWheelClaimOne`. |
| 16.1 claim (1) (p. 98) | "from the symmetry we may assume j ≥ 4" | Y′ was chosen minimal for one of the two arcs, so the two arcs are not symmetric. | Splits on the length of the arc, with a new argument for length 2 (`OddWheelClaimOneNoEnd`). |
| 18.4 (p. 111) | "Then (C,Y) is an odd wheel, since C contains the Y-complete vertices x, pᵢ, pᵢ₊₁ and also pᵢ₋₁, pᵢ₊₂ which are not" | A wheel needs two disjoint Y-complete edges. Only pᵢpᵢ₊₁ is given, and x is adjacent to neither pᵢ nor pᵢ₊₁. | Gets a second edge from the parity clause of 2.3 (`Thm_18_4`). |
| 18.6 claim (2) (p. 114) | "there are an even number of Y-complete edges in p₁…p_{a₁}, and therefore an odd number in p_{b₁}…pₙ, since there are an odd number in P and none in P₁" | When b₁ = a₁ + 1, P₁ is a single edge, which may be Y-complete. This is the same length-1 case as in A2. | A different argument, using 2.10 (`Thm186Claim2`). |
| 18.6 claim (2) (p. 114) | "for i = 1,2 there is a subpath p_{aᵢ}…p_{bᵢ} … and either b₂ = n or a₂ = b₂ = 1" | Assumes W₂ is nonempty. The empty case is not treated. | `Thm186Claim2`. |
| 19.2 claim (1) (p. 118) | "By the minimality of \|Y\|, z is Y∖{y₂}-complete and there is a Y∖{y₂}-complete vertex in A" | The induction gives a wheel whose rim lies in {x₀, x₁, z} ∪ A₁, not in the smaller set A. Also, the printed choice of A does not make A contain a neighbour of y, and claim (3) needs this. | Proves claim (1) with A₁, then chooses A minimal with the extra condition that y has a neighbour in A (`Thm192Claim1`, `Thm192Setup`). As a result, "So y₀ = y" in claim (9) no longer follows, and the modules `Thm192Claim9YAdjX2*` handle the case x₂ ∼ y. |
| 19.2 claims (6), (10) (pp. 119–121) | "(C,Y₀) is a wheel", used to get "every vertex of Y₀ has a neighbour in {p₂,…,pₙ}" | A wheel gives at most one complete interior vertex. The fact actually follows from the other half of claim (2), that there are at least two such edges. | `Thm192Claim6`, `Thm192Claim10`. |
| 20.3 step (2) (p. 125) | "the hole z-x₁-P-x₂-z" | The hole is z-x_t-P-x_{t−1}-z. The next sentence is true only for this hole. | `Thm_20_3`. |
| 21.2 claim (9) (p. 137) | "a pseudowheel, contrary to G ∈ F₈" | The hypothesis of 21.2 is G ∈ F₇ together with a no-pseudowheel condition for the given Y. | Uses the stated hypothesis (`Thm212EndgameTools`). |
| 23.2 (p. 140) | "since G does not admit a skew partition" | The hypothesis is only that G has no *balanced* skew partition. The appeal to 15.1, which 23.4 makes at the same step, is missing. | Uses 15.1 (`Thm232PathT`). |
| 24.4 case 3 (p. 144) | "and by (1), n is odd, so n ≥ 4" | Claim (1) says n is even. The rest of the paragraph needs n even. | `Thm244Case3`. |
| 24.7 (p. 146) | "x₁-p₂-Q-p₁-x₂ is an antipath of length ≥ 5, contrary to 24.5" | This antipath has five vertices, so its length is at least 4, not 5. Also 24.5 is about a path with a vertex off the path, and does not apply. The intended reference is the last sentence of 24.6, "no antipath of length 4". | `Thm_24_7`. |
| 24.7, last sentence (p. 146) | "x₁ has two consecutive neighbours on the hole x₁′-f-P-f′-x₁-x₂-x₁′, and this hole has length > 4, contrary to 24.6" | In this case x₂ ∼ f, so fx₂ is a chord and the cycle is not a hole. Also x₁ lies on the cycle, so it cannot be the outside vertex of 24.6. | Uses the hole x₂-f-P-f′-x₁-x₂ with outside vertex x₁′ (`Thm_24_7`). |
| 24.7, other case (p. 146) | "x₂-x₁-f′-P-f-x₁′-x₂ is a hole of length ≥ 6" | Only \|P\| ≥ 2 is known, which gives length at least 5. Length 5 is excluded because G is Berge, but the text does not say so. | Applies 24.6 with a vertex of X₃, which needs only length at least 5 (`Thm_24_7`). |
| 2.11 (p. 12) | "antipath Q … with interior in X ∪ {pₙ}" | Here N(y) = X ∪ {p₁, pₙ}. The text is carried over from 2.9, where N(y) = X ∪ {pₙ}. No harm. | `Thm_2_11`. |
| 4.2 (p. 15) | "an anticomponent of B′ including B ∪ {v}" | B ∪ {v} is all of B′. The intended set is B₁ ∪ {v}. | `Thm_4_2`. |
| 5.8 step (5) (p. 27) | "the theorem holds by (5) or (2)" | Refers to itself. The intended step is (4). | The Lean does not use the step numbers. |
| 5.7 (pp. 22–25) | "Two edges of G are disjoint …"; "X ⊆ V(L(H)"; "c₁, c₂ ∈ V(G)", "V(C) = V(G)"; "since J is simple" | G is written for H three times, a parenthesis is not closed, and J is not introduced in 5.7. | Read as intended. |

### B2. Proof steps that leave out a case, a check, or a construction

| Where | What is missing | Lean |
|---|---|---|
| 2.4 (p. 10) | The case v ∈ V(Pᵢ) in the definition of linking. | `Thm_2_4`. |
| 2.8 (p. 11) | Uses 2.2 and 2.5, which both need Pᵢ ∩ X = ∅. The hypotheses of 2.8 do not give this directly. | Derived in `Thm_2_8`. |
| 2.9 (p. 12) | The last sentence of the statement ("either (V(P∖p₁),X) or (V(P∖pₙ),Y) is not balanced") is not argued. | `Thm29Aux`. |
| 5.3 (p. 20) | "There is a subgraph of H which is a subdivision of K₄" is Dirac's theorem, which is not cited. It also cannot be applied to H, because inner vertices of tracks have degree 2. It must be applied to J. | `PriorWork/DiracK4Subdivision` proves Dirac's theorem. `Thm53Step1` applies it to J. |
| 5.7 claim (1) (p. 23) | "by König's theorem, there is a vertex incident with every edge in X" is not König's theorem. It is the fact that pairwise-meeting edges in a triangle-free graph share an end. The cases X = ∅, and a common vertex inside a branch (which gives outcome 3, not 2), are skipped. | `Thm57Claim1Konig`, `Thm57Claim1`. |
| 5.7 claims (2), (4), last part (pp. 23–25) | Each use of 5.6 leaves its side conditions unchecked (H∖{u,v} connected, no vertex covering A₁ ∪ A₂). Also unproved: "there is a track in H∖{c₁,c₂} from a₁ to a₂", the König 2-cover, and a parity count. | Seven lemmas named `*_gap` in `Thm57Claim2Connectivity`, `Thm57EndgameHelpers`, `Thm57EndgameConnectivity`. |
| 5.8, one-vertex case (p. 25) | The hypothesis of 5.7, "no even track of length ≥ 4 with end-edges in X", is never checked. It follows from Berge. | `Thm58NoEvenTrackThroughAttachments`. |
| 5.8 steps (3), (4) (pp. 26–27) | "no w ∈ V(J) with A₁ ∪ A₂ ⊆ N_w" is weaker than what 5.6 needs ("no vertex of V(H)"). The premises of 5.6 are not checked for the graph with a branch deleted. | `Thm58StarStarGapLocal`, `Thm58StarStarGapOffBranch`. |
| **5.8 step (6)** (p. 28) | "Hence in L(H) there are three vertex-disjoint paths from N_{v₁}, N_{v₂}, N_u to N_w". When every neighbour of p₁ in N_u is an edge from u to the branch, the third path meets the other two, and these paths do not exist. The paper does not treat this case. | A different argument, using two holes of different parity (`Thm58StarBranchLinkConfig`, `Thm58StarBranchLinkEnd`). |
| 5.8, list of cases (p. 28) | "(2)–(7) cover all the possibilities". The case "X₁ in a branch, X₂ in a star" is (6) with the ends of P swapped, and the list of outcomes does not stay the same under this swap. | A helper lemma with a weaker, two-way conclusion (`Thm58LocalCases`). |
| 5.4, 8.5 claim (2), 8.6 claim (1), §9 (pp. 21, 42, 45) | "Then there is an appearance L(H′) of some J-enlargement J′ with L(H) an induced subgraph" is used three times and never proved. | The modules `EnlargementFromNonlocal*`. |
| 6.1 claims (2), (7), (12), and the paragraph after them (pp. 31–33) | That the third edge f in claim (2) exists; that the J-enlargement in claim (7) appears in Ḡ; the case where B has length 1 in claim (12); "from the symmetry, B₁ even and B₂ odd". | `Thm61Claim2`, `Thm61OddEndgame` (with an explicit K₃,₃ + e model), `Thm61Claim12RookExtension`, `Thm61EvenEndgameSteps`. |
| **7.5 claim (2)** (p. 37) | "replace R_{b₁b₂} by R′ … we obtain another appearance of J". In case 5.8.2(a) no parity statement is available, so the case hypothesis does not show that H′ is bipartite. This matters only when b₁b₂ ≠ c₁c₂. | Proves the parity from Berge, using a return track (`Thm75Claim2Five82CaseGaps`, `Thm75Claim2Five82CaseGapParity`). |
| 8.1, 8.3, 8.6 (pp. 40–45) | "a cycle C of J with \|V(C)\| ≥ 4 and uv ∈ E(C)"; "for some ij, R_ij has nonzero length and R′_ij length 0"; "F′ ≠ ∅"; "N_v not anticonnected"; "if A₁ ∩ A₂ = ∅ then H₀ ≠ K₃,₃". | `Thm81Cycle`, `Thm83MixedRungs`, `Thm86ClaimTwo`, `Thm86OldRungExcludesK33`. |
| 9.5 claim (1) (pp. 52–53) | The Lean does not state printed claim (1) on its own. Claim (3) needs it only when a whole antirung lies in X. The Lean proves that case directly and adds the construction of the offspring. | `Thm95Body` (`claim3_has_strip_attachment_gap`), `Thm95Offspring*`. |
| 9.5 claim (2) (p. 53) | "From the minimality of F, F is minimal such that X ∩ V(K) is not local" passes the minimality on with no argument. | Rules out outcomes 9.3.2 and 9.3.3 directly (`Thm95Body`). |
| 12.2, last part (p. 74) | "we can add p₁ to A and V(P∖p₁) to C, contrary to maximality" needs a rung through the new vertices, which is not built. | `NonlocalStaircaseRungSuffix`. |
| 12.5 (p. 77) | Cases (1), (2), (3) cover three of the four combinations at the ends. The fourth (q₁ ≁ a₀ and q_k ∼ b₀) is not mentioned, and no symmetry is invoked (unlike in 12.1). | `Thm125Case4`, by left–right symmetry. |
| 13.3 (p. 85) | "By 4.2 we may assume this skew partition is not loose". This step turns out not to be needed. | Dropped. |
| 13.7 (p. 86) | Only the first of the two bad outcomes of 2.9 (a leap in X) is ruled out. The mirror case (a leap in Y) is not. | By symmetry (`Thm_13_7`). |
| p. 86 | "every recalcitrant graph belongs to F₅, by 10.6 and 9.7". This also needs 13.4 (long odd prisms), the 9-vertex exception in 10.6, and the fact that proper homogeneous pairs are preserved by complements. | `RecalcitrantInF5`. |
| 13.4 (p. 86) | "since there is no 3-breaker" on the A side refers to the reversed staircase, without saying so. | `StrongStaircaseVertexClassification`. |
| 14.2 claim (1) (p. 88) | The Lean replaces the appeal to 10.4 by a direct parity argument. This is a simplification, not a fix. | `Thm142*`. |
| 16.1 claim (1) (p. 98) | "Choose Y′ ⊆ Y minimal such that Y′ is anticonnected and there are an odd number of Y′-complete edges in P". The next step needs v not Y′-complete, which does not follow from this choice. | Minimizes over the sets Y′ for which v is not Y′-complete (`OddWheelClaimOne`). |
| 16.2, 16.3 (pp. 99–101) | "If \|F\| = 1 the result follows from 16.1" needs a translation to the third condition of 16.2. Also "unique Y ∪ {v}-complete edge", and "By 16.2 and (1)". | `OddWheelAttachmentBase`, `OddWheelNoOddExtSegment`, `OddWheelBullets12`. |
| 16.3, 18.7, 23.2: "In particular, every recalcitrant graph belongs to F₇ / F₈ / F₉" (pp. 101, 115, 139) | Each theorem is about G only, while each class is defined by a condition on both G and Ḡ. The step that applies the theorem to Ḡ is not stated. | `thm_16_3_recalcitrant`, `thm_18_7_recalcitrant`, `thm_23_2_recalcitrant`, using the lemmas in `ClassLemmas` about complements. |
| 17.5 (p. 106) | The case X = ∅ is not mentioned. The last paragraph cites 17.2 where 17.3 is used. | `Thm175Claim3Size`, `Thm175Endgame`. |
| 18.5 (p. 112) | Two of the three appeals to 17.5 need only 17.4. | `Thm185TripleRRReduction`. |
| 18.7 (p. 115) | After 18.6, it is not shown that the two attachments lie on both sides of pᵢ, so that pᵢ is inside the subpath that 18.6 returns. | `Thm_18_7`. |
| 19.2 claim (2) (p. 118) | The one-sentence proof hides two steps. One restricts to the subgraph induced on A ∪ {x₀,x₁,x₂,z} ∪ Y₀, which needs F₇ to be closed under induced subgraphs. The other uses 2.3 to get two Y₀-complete edges. | `Thm192Claim2Localization`, `Thm192Claim2Heredity`, `Thm192Claim2RimPath`. |
| 20.1 (p. 123) | The set Y′ from 20.3 is used again in an induction over hubs that avoid A₀ ∪ {z}, without checking this condition. | `Thm_20_1`, `Thm201HubBasics`. |
| 20.5 claim (2), 21.1, 21.2 claim (5), 21.3 (pp. 128–137) | "and therefore r ∈ A_{t−3}" is not argued. "hole of length ≥ 6" is only ≥ 5 without using Berge. "The last assertion is immediate" is not. 21.3 leaves out the second half of the hypothesis of 21.2. | `Thm_20_5`, `Thm211Hole`, `Thm212`, `Thm213Steps`. |
| 22.1, 22.4, 22.2 and 22.5 (pp. 137–141) | A second X_t-complete vertex besides z is needed, and its source is not given. 22.4 uses t ≥ 1, but only t ≥ 0 is given (the Lean derives t ≥ 1). The neighbour y of the tail must lie outside Y and not be Y-complete, which is not part of the published definition of a tail. | `Thm_22_1`, `Thm224Claims`, `KiteTailBasics`. |
| 23.2 claim (5) (p. 141) | "By 2.11 … one of x₀, x₁ is nonadjacent to all of y, p₁, …, p_{k−1}". 2.11 has two outcomes, and only the first gives this directly. | `Thm232Claim5SecondOutcome`, `Thm232RemainingClaims`. |
| 23.4, applied to recalcitrant graphs (p. 142) | 23.4 is about vertices off the hole, while F₁₀ is about all vertices. The case of a vertex on the hole is easy but not stated. | `Thm_23_4_recalcitrant`. |
| 24.4 (p. 144) | "From the minimality of F there are (up to symmetry) three cases" is given with no argument. This split into three cases needs a real proof. | `Thm244Trichotomy` and the modules it uses. |
| 24.5 (p. 145) | "choose X maximal" does not say maximal with respect to what. | Fixes a precise family of sets (`Thm245MaximalAdmissibleSet`). |
| 24.6 (p. 145) | "In particular, G has no antipath of length 4" needs a short argument: the complement of a 5-vertex path is a 5-cycle plus a chord. | `Thm_24_6`. |

### B3. Proofs replaced by a different argument

Apart from the local repairs listed in B1 and B2, the Lean follows each printed proof step by
step. A printed citation becomes a call to the cited result. The one numbered statement whose
Lean proof has no printed counterpart is 2.1. The paper cites Roussel and Rubio [23] for it. The
Lean proves a stronger form that also tracks parity, and derives the printed statement from it
(`Statements/S02/Thm_2_1.lean`).

## Part C. Choices of reading

| Item | Printed | Lean reading | Why |
|---|---|---|---|
| *recalcitrant*, second condition (p. 86) | "G and Ḡ are not line graphs" | "not line graphs **of bipartite graphs**" (`Types/LongOddPrism`) | The paper says that every counterexample to 1.3 is recalcitrant. The basic classes of 1.3 are line graphs of bipartite graphs, so this is the reading under which 1.3 follows. |
| *proper homogeneous pair* (p. 2) | A₂ is "all A-anticomplete vertices in V(G)" | A₂ ranges over V(G) ∖ A (`Types/Decompositions`) | The literal reading also forces every vertex of A to have a neighbour in A (and the same for B). It is also not preserved by taking complements, while 13.4 and 1.8(5) apply the notion to Ḡ. The Lean notion is slightly broader. This is safe because the Chvátal–Sbihi result E3 is proved in Lean for the broader notion. The only effect is that the third outcome of 1.3 is slightly weaker in Lean than in print. |
| F₂ (p. 6) | "the class of all graphs G such that …" | Copied as printed. | No harm, since membership in F₁ already includes Berge. |
| F₅ (p. 6) | Defined from F₃ | Copied as printed. | Equivalent to the F₄ reading (see Part A). |
| Published paper and arXiv version | 4.6, 5.7, 8.5, 11.3, outcome 1 of 12.1, 13.6, 15.5, 21.2, 22.5, and the definition of *tail* differ between the two | The published form, in every case. | Each case is noted in the file header. |
| 2.3 | "subpath of P" | A block of consecutive vertices, in the direction of P. | 2.3 is unchanged when P is reversed. |
| 12.2, outcome 3 | "a path u-R-v" | May have length 0 when k = 1. | The paper's own convention. |
| 17.4 | "pₙ-x₁-⋯-x_k-y" | k ≥ 1. | The only reading in which x₁ exists. |
| 18.2 | "a path in G" (its neighbours say "in G∖(X∪Y)") | Copied as printed. The Lean then proves that the path is disjoint from X ∪ Y. | The Lean statement is stronger than the intended reading. |
| 10.2 | "suppose 10.1.1 holds" | Adds the hypothesis that K₄ appears in G (the "(therefore)" clause). The proof does not use it. | Formally a little weaker than the print. The only caller has this hypothesis. |
| 17.5 | Y chosen minimal under inclusion | Y chosen of least size, with the outside vertex z fixed. | A stronger choice, so the proof still works. |
| 24.5 | "choose X maximal" | Maximal in a fixed family of sets. | The only reading that supports the later steps. |
| Subdivisions (`IsSubdivision`) | — | The path from v to u is the reverse of the path from u to v. | Bookkeeping. |
| Even pairs (`HasEvenPair`) | — | u ≠ v. | The notion is empty otherwise. |
| Basic graphs (`IsBasic`) | — | Has an extra case, "Ḡ is a double split graph". | The complement of a double split graph is again a double split graph, so the extra case adds nothing. |
| Components (`IsComponent`, in `Types/Core`) | "a maximal connected subset of a **nonempty** set" | The nonempty condition is dropped, so ∅ is a component of ∅. | This matters once: claim (3) of 14.3 must be applied only to nonempty components (`TwoJoinFromSeparation`). |
| Rungs in §8 | "for each **edge** uv of J choose a uv-rung" | Rungs are indexed by ordered pairs of vertices of J. | Four lemmas need the rung from v to u to be the reverse of the rung from u to v. The Lean proves that this always holds in the setting of §8 (`FormsLineGraphForcesRungSymmetry`). |
| Classes and complements | Preamble to 1.8 | `ClassLemmas` proves that F₃ and F₅ to F₁₀ are closed under complements. It does not claim this for F₄, F₁₁ or for having a proper 2-join. | Those three are not closed under complements. Every use goes through a statement about G or Ḡ. |
| Minimum imperfect graph | "minimum counterexample" | Least number of vertices, over graphs on `Fin n`. "Berge and not perfect" is derived using E5. | Faithful. |
