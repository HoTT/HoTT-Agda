{-# OPTIONS --without-K #-}

{-
Imports everything that is not imported by something else.
This is not supposed to be used anywhere, this is just a simple way to
do `make all'

This file is intentionally named index.agda so that
Agda will generate index.html.
-}

module index where

import Base
import Spaces.IntervalProps
import Algebra.F2NotCommutative
import Spaces.LoopSpaceCircle
import Spaces.LoopSpaceDecidableWedgeCircles
import Homotopy.PullbackIsPullback
import Homotopy.PushoutIsPushout
import Homotopy.Truncation
import Sets.QuotientUP
import Spaces.PikSn
import Homotopy.VanKampen
import Homotopy.Cover
import Homotopy.Cover.ExamplePi1Circle
