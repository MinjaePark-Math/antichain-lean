# Review of the revised manuscript

Reviewed original source SHA-256: `841526a75ae6026dbd15fdf886b9a5e86054fa2d2b1d5b108f4d0a669db35466`. Previous verified source: `7223c87d97fc9c97a97b9a9affc490aa6a4f3923587d05ec92b35a4a45a42da5`.

The revision contains 35 numbered items and 46 tracked mathematical assertions. The AI disclosure has revised wording and a table-of-contents entry. The commented-out text is excluded from the annotated proof review. The manuscript removes the mean-square predictor for the lower endpoint of a weak-order interval. Its proof remains in the Lean library as a supplementary result. All 24 active proof environments retain their content.

The prior pinned-kernel build and exhaustive type and axiom audit still apply. The audit passed at `2026-11-19T14:19:55.810750+00:00` and covered 3,151 theorems and 3,708 declarations. The production sources, dependency configuration and audit collector match the audited hashes. The authoring source is preserved as supplied.

Each assertion has a separate statement and proof-method review. Appendix B develops selected proof details. The packaged authoring draft contains the full written proofs.

| Proof relationship | Claims |
|---|---:|
| expanded argument | 22 |
| no separate proof | 7 |
| same argument | 17 |

## Optional detailed proof expositions

The reviewed Lean arguments follow the current written strategies. The table links optional expositions of selected constructions and compressed steps.

| Assertion | Written argument and verified route | Complete readable proof |
|---|---|---|
| 2.1 (`ANT-2-1`) | The revised Stone-Weierstrass/Lipschitz route is now the actual production proof. Lean supplies the explicit Lipschitz sublattice, its strong two-point separation, and the one-Lipschitz clamp extension. The earlier finite Kuhn interpolation is supplementary. Absolute two-sided test estimates also imply the source one-sided finite-test estimates. Lean carries out the probability-logarithm step as direct exponential Markov bounds, including zero-probability events; the written logarithmic bound uses the usual extended-real convention log(0)=-infinity. The centered moment generating function has its written quadratic Taylor remainder. Lean checks both mgf(t)−1=O(t²) and log mgf(t)=O(t²). The actual negative tilt uses the quadratic log-moment bound. | [human-proofs-probability.tex](human-proofs-probability.tex) |
| 2.2 (`ANT-2-2`) | The earlier centered inverse-coordinate witness has been replaced in the source-facing support and shape chain by the literal manuscript common cube-shift IVT witness. Both the endpoint-divergence closure argument and the explicit mixed-boundary approximation are now formalized as written. | [human-proofs-probability.tex](human-proofs-probability.tex) |
| 3.4 (`ANT-3-4`) | The statement newly includes existence and uniqueness of the point of the closed reference simplex in each actual generated orbit. GeometryRevisionSource now gives that literal forall x existsUnique y endpoint. Other tiling, local-finiteness, unique-map and tile-count conclusions are unchanged. The revised root-hyperplane and affine-Weyl terminology is cited background, expanded by directly proved type-A geometric facts, not a claimed formalization of abstract Coxeter theory. | [human-proofs-geometry.tex](human-proofs-geometry.tex) |
| 3.6 (`ANT-3-6`) | The statement is unchanged after renaming pinned volume S_r to V_r. The written upper proof genuinely changes: delete exactly the j largest actual tree edges, yielding exactly j+1 components, and integrate parent-height intervals leaf to root rather than use a height-difference Jacobian. Both revised routes are now proved and called by the unchanged original pinned-volume source endpoint. Ties, coincident floors and the one-point zero-dimensional fiber remain included. | [human-proofs-geometry.tex](human-proofs-geometry.tex) |
| 4.1 (`ANT-4-1`) | The same two ordinary-integral inequalities and exact coefficient are retained. The pinned volume notation is consistently V_r in the current source (formerly S_r). The actual production common-height bound calls the equal-exponent Holder proof and translation invariance; square-completion estimates remain supplementary. | [human-proofs-algebra.tex](human-proofs-algebra.tex) |
| 4.3 (`ANT-4-3`) | The literal finite-intensity Poisson process, its count-conditioned iid law, actual spatial restriction independence, Poisson normalizer cancellation, finite tile exhaustion, and nonnegative coefficient bound are already formalized and used. Omitting finite-exhaustion and factorial bookkeeping from the revised prose abbreviates the same argument; Lean still proves them. The statement now explicitly permits infinite intermediate bounds until summability is established. | [human-proofs-algebra.tex](human-proofs-algebra.tex) |
| 5.3 (`ANT-5-3`) | The production gluedAlcoveHeight_directional now uses an actually constructed finite subsegment chain, not the former closed-set interval-induction substitute. The subdivision also has a literal finite endpoint-list theorem. Its source call discharges convexity and local finiteness with the actual tiles. All replication family, height and exact volume conclusions are unchanged. | [human-proofs-geometry.tex](human-proofs-geometry.tex) |
| 6.2 (`ANT-6-1`) | The active source replaces DKW by fixed-order-statistic Hoeffding. That exact route is now formalized and used by the source-facing endpoints, including2dn exp(-2ns^2/d). The sharp DKW library theorem remains supplementary. The former Hausdorff clause is relocated to separate Remark6.3 without a new mathematical conclusion. | [human-proofs-probability.tex](human-proofs-probability.tex) |

The rank certificates use the revised Hoeffding argument. The exact earlier sharp DKW estimate remains a supplementary theorem. The excluded variational context and any explicit external input are listed in [GAPS.md](GAPS.md).

Editorial wrappers are removed only from the verification companion, preserving their contents. The original authoring source is unchanged. The [complete per-claim ledger](proof-correspondence.json) records the current statement fingerprints, actual Lean certificates and method explanations.
