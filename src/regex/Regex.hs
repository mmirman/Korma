module Regex where


import Text.Regex.PCRE
import Text.Regex.PCRE.String


matchme :: Bool
matchme = "hello" =~ "^el*o"