# Maintaining verification

Start with the [current coverage](PAPER_COVERAGE.md), [proof comparisons](proof-correspondence.json), and [scope limits](GAPS.md). Stable IDs survive reorganizations. Review the exact statement when a claim changes, and separately compare the mathematical strategy when the proof changes.

The revised proof work covers Hoeffding rank concentration, Stone–Weierstrass approximation, the longest-edge tree cut with leaf-to-root Fubini, and the inversion-density corollary. See the [proof guide](PROOF_GUIDE.md) for the relevant files.

Build and audit the changed Lean sources. Regenerate the companion, record its actual theorem numbers, and inspect the rendered PDF. The release checker binds the original source, PDF and saved Lean evidence.
