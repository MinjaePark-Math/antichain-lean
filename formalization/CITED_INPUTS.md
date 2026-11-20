# Mathematical inputs and verification scope

The current rank applications use the proved Hoeffding argument. The coordinate-average fluctuation claim has the general iid central limit theorem as an explicit mathematical premise. The audit and exact types are in the release evidence. The separate manuscript review is in [proof-correspondence.json](proof-correspondence.json).

## Type-A alcove geometry

The objects are the actual zero-sum Euclidean floor, printed reference simplex, and words in its side reflections. Distinct tiles are distinct image sets, so repeated words create no duplicate tiles. Every specialized geometric fact used from the Humphreys citation has a proof:

| Required fact | Lean declaration |
|---|---|
| Tiles cover the floor | `alcoveTile_covers_direct` |
| Distinct tile interiors are disjoint | `alcoveTile_disjoint_interiors_direct` |
| The tile family is locally finite | `alcoveTile_locallyFinite_direct` |
| Words producing one tile define the same affine map | `same_tile_map_unique_direct` |
| Closed-alcove representatives in one orbit agree | `closed_alcove_representative_unique_direct` |

The coordinate-permutation plus zero-sum integer-translation normal form gives finite bounded orbit pieces. A closest orbit point to an interior reference point cannot violate a simplex wall: its side reflection would reduce the distance. This proves coverage. Ordered coordinates and integer shifts prove closed-representative uniqueness; strict-interior stabilizers prove uniqueness of tile maps and disjoint interiors. `DirectAlcoveInput.lean` assembles the actual proved record. Equal tile volumes and the cube boundary layer yield the quantitative tile count.

This independently establishes the cited specialization used by the paper. It does not claim a formalization of the entire general Coxeter-group theory in Humphreys.

## Exact sharp DKW

`sharp_uniform_cdf_two_sided` in `DKWReverseMartingale.lean` proves, for every integer `n>0` and real `delta>0`, under the actual product restricted-Lebesgue uniform law,

`P(exists s in [0,1], |D_n(s)-s| > delta) <= 2 exp(-2 n delta^2)`.

No DKW bound, entropy estimate, martingale law, saddle-point property or minimax theorem is a hypothesis. The proof constructs the censoring filtration and its actual likelihood martingale from the iid law, applies a proved finite maximal inequality, and reduces a crossing to finitely many positive critical thresholds. `BinaryKLPinsker.lean` proves the binary relative-entropy quadratic bound. `DKWStationary.lean` constructs the required interior stationary point by endpoint limits and the intermediate value theorem. `DKWSaddle.lean` proves that it supplies a global common likelihood barrier, giving exactly the exponent `-2 n delta^2`. Reflecting the actual uniform sample gives the other tail; their union gives the factor two. The cases `delta>=1` are included.

The previous manuscript used this exact bound. The current finite order-statistic proof uses binomial counts and Hoeffding, with the stated two-sided constant and finite Euclidean union bound. The revised endpoints have no DKW or Hoeffding parameter. The DKW proof remains part of the checked library.

## Coordinate-average central limit theorem

[CoordinateFluctuations.lean](../Antichain/CoordinateFluctuations.lean) checks the exact finite-sample pushforward law under antichain conditioning, the uniform mean and variance, and the identification with the empirical coordinate integral. Its Gaussian convergence certificate takes `IIDFiniteVarianceCLT`, the general real iid finite-variance central limit theorem, as an explicit hypothesis. A general version has been [proved in newer Mathlib](https://github.com/leanprover-community/mathlib4/blob/05af26ba41a6dd0046cd94bfdad3d6d787950b31/Mathlib/Probability/CentralLimitTheorem.lean). The current project retains its Lean 4.24.0 dependency pin.

## Surface tension

The introductory variational sentence relies on the Kenyon–Prause private communication. The draft contains no definition of the functional or admissible class and gives no variational argument or probability-to-variational theorem. The companion marks it as cited context. The mathematical limit shape theorem has its own complete certificate.

## Logical foundations and checks

Only `propext`, `Classical.choice` and `Quot.sound` are permitted as transitive axioms. They are logical foundations, not unproved mathematical inputs. The pinned Lean kernel and checked Mathlib remain trusted dependencies. Every production declaration is freshly compiled and audited through both its type and proof value; definitions and generated declarations are included.

`coverage.json` binds every tracked assertion to exact complete certificate types and its reviewed `external_inputs` list. The release checker rejects caller-supplied alcove or DKW parameters in those certificates, compares complete structural types, and checks the source, manuscript, reviewed proof methods and PDF receipt. Those deterministic checks complement independent mathematical correspondence review; they do not replace it. Open questions, the conjecture and explanatory heuristic remain outside proved scope.
