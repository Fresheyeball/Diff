-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Algorithm.Diff
-- Copyright   :  (c) Sterling Clover 2008-2011, Kevin Charter 2011
-- License     :  BSD 3 Clause
-- Maintainer  :  s.clover@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- This is an implementation of the O(ND) diff algorithm as described in
-- \"An O(ND) Difference Algorithm and Its Variations (1986)\"
-- <http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.4.6927>. It is O(mn) in space.
-- The algorithm is the same one used by standared Unix diff.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE DeriveGeneric #-}

module Data.Algorithm.Diff
    ( Diff, PolyDiff(..)
    -- * Comparing lists for differences
    , getDiff
    , getDiffBy

    -- * Finding chunks of differences
    , getGroupedDiff
    , getGroupedDiffBy
    ) where

import           Data.Align
import           Data.Array   (listArray, (!))
import           Data.These
import           GHC.Generics
import           Prelude      hiding (pi)

data DI = F | S | B deriving (Show, Eq)

-- | A value is either from the 'This' list, the 'That' or from 'These'.
-- 'These' contains both the left and right values, in case you are using a form
-- of equality that doesn't check all data (for example, if you are using a
-- newtype to only perform equality on side of a tuple).
-- data PolyDiff a b = This a | That b | These a b
--   deriving (Show, Eq, Generic)

type PolyDiff a b = These a b


-- | This is 'PolyDiff' specialized so both sides are the same type.
type Diff a = PolyDiff a a

data DL = DL {poi :: !Int, poj :: !Int, path::[DI]} deriving (Show, Eq)

instance Ord DL
        where x <= y = if poi x == poi y
                then  poj x > poj y
                else poi x <= poi y

canDiag :: (a -> b -> Bool) -> [a] -> [b] -> Int -> Int -> Int -> Int -> Bool
canDiag eq as bs lena lenb = \ i j ->
   (i < lena && j < lenb) && ((arAs ! i) `eq` (arBs ! j))
    where arAs = listArray (0,lena - 1) as
          arBs = listArray (0,lenb - 1) bs

dstep :: (Int -> Int -> Bool) -> [DL] -> [DL]
dstep cd dls = hd:pairMaxes rst
  where (hd:rst) = nextDLs dls
        nextDLs [] = []
        nextDLs (dl:rest) = dl':dl'':nextDLs rest
          where dl'  = addsnake cd $ dl {poi=poi dl + 1, path=F : pdl}
                dl'' = addsnake cd $ dl {poj=poj dl + 1, path=S : pdl}
                pdl = path dl
        pairMaxes []         = []
        pairMaxes [x]        = [x]
        pairMaxes (x:y:rest) = max x y:pairMaxes rest

addsnake :: (Int -> Int -> Bool) -> DL -> DL
addsnake cd dl
    | cd pi pj = addsnake cd $
                 dl {poi = pi + 1, poj = pj + 1, path=B : path dl}
    | otherwise   = dl
    where pi = poi dl; pj = poj dl

lcs :: (a -> b -> Bool) -> [a] -> [b] -> [DI]
lcs eq as bs = path . head . dropWhile (\dl -> poi dl /= lena || poj dl /= lenb) .
            concat . iterate (dstep cd) . (:[]) . addsnake cd $
            DL {poi=0,poj=0,path=[]}
            where cd = canDiag eq as bs lena lenb
                  lena = length as; lenb = length bs

-- | Takes two lists and returns a list of differences between them. This is
-- 'getDiffBy' with '==' used as predicate.
getDiff :: (Eq a) => [a] -> [a] -> [Diff a]
getDiff = getDiffBy (==)

-- | Takes two lists and returns a list of differences between them, grouped
-- into chunks. This is 'getGroupedDiffBy' with '==' used as predicate.
getGroupedDiff :: (Eq a) => [a] -> [a] -> [Diff [a]]
getGroupedDiff = getGroupedDiffBy (==)

-- | A form of 'getDiff' with no 'Eq' constraint. Instead, an equality predicate
-- is taken as the first argument.
getDiffBy :: (a -> b -> Bool) -> [a] -> [b] -> [PolyDiff a b]
getDiffBy eq a b = markup a b . reverse $ lcs eq a b
    where markup (x:xs)   ys   (F:ds) = This x  : markup xs ys ds
          markup   xs   (y:ys) (S:ds) = That y : markup xs ys ds
          markup (x:xs) (y:ys) (B:ds) = These x y : markup xs ys ds
          markup _ _ _                = []

getGroupedDiffBy :: (a -> b -> Bool) -> [a] -> [b] -> [PolyDiff [a] [b]] -- <- this should be ([a],[b],[(a,b)])
getGroupedDiffBy eq a b = (go :: ()) $ getDiffBy eq a b
    where go (This x  : xs) = let (fs, rest) = goThiss  xs in This  (x:fs)     : go rest
          go (That x : xs) = let (fs, rest) = goThats xs in That (x:fs)     : go rest
          go (These x y : xs) = let (fs, rest) = goThese    xs
                                    (fxs, fys) = unzip fs
                               in These (x:fxs) (y:fys) : go rest
          go [] = []

          goThiss  (This x  : xs) = let (fs, rest) = goThiss  xs in (x:fs, rest)
          goThiss  xs             = ([],xs)

          goThats (That x : xs) = let (fs, rest) = goThats xs in (x:fs, rest)
          goThats xs            = ([],xs)

          goThese    (These x y : xs) = let (fs, rest) = goThese xs    in ((x,y):fs, rest)
          goThese    xs = ([],xs)
