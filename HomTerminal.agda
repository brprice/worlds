module HomTerminal where
-- One world is terminal

open import Basics
open import Hom
open import WorldSystemExamples
open WorldSystemExamples.OneWorld

OneWorldTerm : forall QW -> WorldHom QW oneWorld
OneWorldTerm QW = record
                    { FW = \_ -> <>
                    ; FQ = \_ -> <>
                    ; pres<< = \_ -> <>
                    ; presTyW = \_ -> <>
                    ; presAct = \_ -> refl
                    ; presSt = refl
                    ; presUnst = \_ -> refl
                    }

-- We have only proven that oneWorld is _weakly_ terminal
-- (i.e. we don't know that any two parallel homs into it are equal)
-- Note that OneWorldTerm.FW,FQ,pres<<,presTyW are both maps into One
-- and presSt : <> == <>, and presAct,presUnst are functions into Just <> == Just <>
-- and these are equivalent to One
-- Thus oneWorld is "as terminal" as the type One is
-- (e.g. if we have function extensionality then oneWorld is terminal)
