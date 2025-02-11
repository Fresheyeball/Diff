{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import           Control.DeepSeq
import           Criterion.Main
import           System.Random

import           Data.Algorithm.Diff

instance NFData a => NFData (Diff a)


main :: IO ()
main = doBenchMarks 37

doBenchMarks :: Int -> IO ()
doBenchMarks seed =
  let rbools = randoms (mkStdGen seed) :: [Bool]
      (s1000_1, rbools1) = splitAt 1000 rbools
      (s1000_2, rbools2) = splitAt 1000 rbools1
  in s1000_1 `deepseq` s1000_2 `deepseq` defaultMain [
    bgroup "diff bool lists" $ [bench "1000 bools" $ nf (getDiff s1000_1) s1000_2]
    ]

