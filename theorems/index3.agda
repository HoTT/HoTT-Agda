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

{- cogroups and suspensions -}
import homotopy.Cogroup

{- modalities -}
import homotopy.ModalWedgeExtension

{- conjecture 3.5.3 in favonia's thesis -}
import groups.Int

{- cup product -}
import homotopy.CupProduct
{-import homotopy.CupProductCommutativity-}