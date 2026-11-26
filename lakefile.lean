import Lake
open Lake DSL

package solved

@[default_target]
lean_lib Verification where
  srcDir := "lean"
  roots := #[`Verification, `Compression, `FiniteControls, `MarkedComparison,
    `PositiveExpressions, `ProductIntervals, `SignedEnvelope, `SubtractionGap,
    `TwoSmallBlocks, `ChainCoverage, `SquareInstability, `DirectedRecovery]
