{-# OPTIONS --without-K #-}

{-
Imports everything that is not imported by something else.
This is not supposed to be used anywhere, this is just a simple way to
do `make all'

This file is intentionally named index.agda so that
Agda will generate index.html.
-}

module index where

-- import Spaces.IntervalProps

-- import Algebra.F2NotCommutative

-- XXX
-- import algebra.DecidableFreeGroupIsReducedWord

import homotopy.LoopSpaceCircle

import homotopy.HopfJunior
import homotopy.Hopf

-- cohomology
import cohomology.EMModel
import cohomology.Torus
import cohomology.MayerVietorisExact

import homotopy.SpaceFromGroups

import homotopy.CoverClassification
import homotopy.AnyUniversalCoverIsPathSet
import homotopy.PathSetIsInital

-- import Spaces.LoopSpaceDecidableWedgeCircles

-- import Homotopy.PullbackIsPullback

-- import Homotopy.PushoutIsPushout

-- import Homotopy.Truncation

-- import Sets.QuotientUP

import homotopy.PinSn

-- import Homotopy.VanKampen

import cw.CW
import cw.examples.Sphere
