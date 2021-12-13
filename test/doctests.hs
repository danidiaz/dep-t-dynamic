module Main (main) where

import Test.DocTest
main = doctest [
      "-ilib"
    , "lib/Dep/Dynamic.hs"
    , "lib/Dep/Dynamic/Internal.hs"
    , "lib/Dep/Checked.hs"
    , "lib/Dep/SimpleChecked.hs"
    ]
