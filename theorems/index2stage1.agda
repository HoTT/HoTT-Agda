{-# OPTIONS --without-K --rewriting #-}

{-
  favonia:
  On 2017/03/23, after I added back Mayer-Vietoris, it seems
  difficult to type check everything in one round on travis,
  so parts of index.agda are moved here.

  favonia:
  On 2017/05/08, I further partition the results into multiple
  independent index[n].agda files because the garbage collection
  is not really working.
-}

module index2stage1 where

{- cw complexes -}
import cw.CW
import cw.examples.Examples

{- isomorphisms between different kinds of cohomology groups for finite CWs. -}
import cw.cohomology.ReconstructedCochainsIsoCellularCochains
import cw.cohomology.cochainequiv.AugmentCommSquare
import cw.cohomology.cochainequiv.FirstCoboundaryCommSquare
import cw.cohomology.cochainequiv.HigherCoboundaryCommSquare
