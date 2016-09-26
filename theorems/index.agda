{-# OPTIONS --without-K #-}

{-
Imports everything that is not imported by something else.
This is not supposed to be used anywhere, this is just a simple way to
do `make all'

This file is intentionally named index.agda so that
Agda will generate index.html.
-}

module index where

{- some group theory results -}
import groups.ReducedWord
import groups.CoefficientExtensionality

{- homotopy groups of circles -}
import homotopy.LoopSpaceCircle
import homotopy.PinSn
import homotopy.HopfJunior
import homotopy.Hopf

{- cohomology -}
import cohomology.EMModel
import cohomology.Torus
-- this will be commented out till the long exact sequences are (re)done.
-- import cohomology.MayerVietorisExact

import homotopy.SpaceFromGroups

{- covering spaces -}
import homotopy.CoverClassification
import homotopy.AnyUniversalCoverIsPathSet
import homotopy.PathSetIsInital

{- cw complexes -}
import cw.CW
import cw.examples.Sphere

-- There are some unported theorems

-- import Spaces.IntervalProps
-- import Algebra.F2NotCommutative
-- import Homotopy.VanKampen
-- import Spaces.LoopSpaceDecidableWedgeCircles
-- import Homotopy.PullbackIsPullback
-- import Homotopy.PushoutIsPushout
-- import Homotopy.Truncation
-- import Sets.QuotientUP
