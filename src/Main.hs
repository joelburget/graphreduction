{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Lens
import Control.Monad
import qualified Data.Text.IO as T

import Machine.GarbageCollection
import Machine.GraphReduction
import Machine.Pretty
import Machine.Run
import Machine.Step

main :: IO ()
main = putStrLn "should there even be a main?"
