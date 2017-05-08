{-# OPTIONS --without-K --rewriting #-}

{-
  favonia:
  On 2017/05/08, I further partition the results into multiple
  independent index[n].agda files because the garbage collection
  is not really working.
-}

module index3 where

{- van kampen -}
import homotopy.VanKampen

{- blakers massey -}
import homotopy.BlakersMassey

{- modalities -}
import homotopy.ModalWedgeExtension
