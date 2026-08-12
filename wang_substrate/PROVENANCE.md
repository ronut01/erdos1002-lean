# Vendored substrate, provenance

Everything under `Erdos1002/` in this directory is **Shouqiao Wang's work**,
not ours. It is vendored here under the MIT License he applied to his
repository, at his explicit invitation, so that the Kwon formalization can
build on shared infrastructure instead of rebuilding it.

- Source: <https://github.com/ShouqiaoW/erdos>
- Pin: `d28713ac8245ca86a686b8c67370a8d19d81b242` (the commit that adds the
  MIT LICENSE; its parent `61325b1…` is the commit we audited, the two
  differ only by the LICENSE file, so the vendored code is byte-identical
  to the audited artifact)
- Original path of each file: `1002/lean/Erdos1002/<Module>.lean`
- Modification: a provenance header prepended to each file. Nothing else.
  Module names and namespaces are unchanged, so any file here diffs cleanly
  against its upstream original and fixes can be sent back.

## What was vendored, and why only this

35 modules (~12,900 lines), computed as the transitive `import` closure
within `Erdos1002.*` of the modules Kwon's §3 and §5 need:

- continued fractions and cylinder counting (`ContinuedFractions`,
  `ContinuedFractionCylinderCounting`, `GaussCylinderContraction`)
- the Gauss transfer operator (`GaussTransferAdjoint`,
  `GaussTransferContraction`, `GaussTransferCorrelation`,
  `GaussLebesgueTransfer`) and Gauss dynamics/digit statistics
- mixing (`PsiMixing`, `RareEventMixing`)
- the torus coordinate (`UnitTorus`)
- the Poisson limit chain (`CompoundPoisson`, `ContinuousCompoundPoisson`,
  `PoissonFactorialConvergence`, `MultivariatePoisson`) and
  `LevyContinuity`

Wang's development is ~146,500 lines in total. His route-specific
machinery, the `GaussPrefix*` (≈53K), `NearResonant*` (≈18K) and
`FixedAway*` (≈18K) clusters implementing his own L² shot-noise
architecture, is deliberately **not** vendored: Kwon's proof takes a
different route, and importing it would add nothing while blurring whose
work is whose.

Fixes or generalizations we make to any file here are sent upstream to
Wang, per our agreement with him.
