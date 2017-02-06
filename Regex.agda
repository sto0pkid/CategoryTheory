module Regex where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.List
open import Data.String
open import SetTheory
open import Relations
open import FormalLanguage

data Regex : Set where
 ⊘     : Regex                 -- empty language
 ε     : Regex                 -- language containing only the empty string
 char  : Char → Regex          -- language containing only the symbol "a"
 _*    : Regex → Regex         {- Kleene closure of a regexp e; the language
                                 obtained by concatenating strings from e zero or
                                 more times. -}
 _||_  : Regex → Regex → Regex -- union of two languages e₁ and e₂
 _&&_  : Regex → Regex → Regex {- language obtained by concatenation of a string
                                 of e₁ with a string of e₂ -}


{-

[1] Alexandre Agular, Bassel Mannaa
    "Regular Expressions in Agda"
    http://www.cse.chalmers.se/~bassel/report.pdf

[2] Sized Types; Agda Docs
    http://agda.readthedocs.io/en/latest/language/sized-types.html

[3] Dmitriy Traytel; Tobias Nipkow
    "Verified Decision Procedures for MSO on Words
    Based on Derivatives of Regular Expressions"
    https://www21.in.tum.de/~traytel/papers/jfp15-mso/mso.pdf

[4] Dmitriy Traytel
    "Formal Languages, Formally and Coinductively"
    https://arxiv.org/pdf/1611.09633.pdf

[5] Scott Owens, John Reppy, Aaron Turon
    "Regular-expression derivatives re-examined"
    https://www.cl.cam.ac.uk/~so294/documents/jfp09.pdf

[6] Haiming Chen
    "Derivatives of Regular Expressions"
    http://lcs.ios.ac.cn/~chm/papers/derivative-tr200910.pdf

[7] 
    NYC Haskell User's Group
    "Partial Derivatives of Regular Expressions"
    https://www.youtube.com/watch?v=QVdBPvOOjBA

[8] Might, Matthew; Darais, David; Spiewak, Daniel
    "Parsing with Derivatives"
    http://matt.might.net/papers/might2011derivatives.pdf

    Matthew Might explains the paper on video:
    https://www.youtube.com/watch?v=ZzsK8Am6dKU

[9] Firsov, Denis; Uustalo, Tarmo
    "Certified Normalization of Context-Free Grammars"

    Code:
    http://cs.ioc.ee/~denis/cert-norm/

    Paper:
    http://cs.ioc.ee/~denis/cert-norm/cfg-norm.pdf

[10] Firsov, Denis; Uustalo, Tarmo
     "Certified CYK parsing of context-free languages"
     http://cs.ioc.ee/~tarmo/papers/nwpt12-jlamp.pdf

[11] Younger, Daniel H.
     "Recognition and Parsing of Context-Free Languages in Time n³"
     http://ac.els-cdn.com/S001999586780007X/1-s2.0-S001999586780007X-main.pdf?_tid=7fd9ab1e-cc96-11e6-b64e-00000aacb35e&acdnat=1482885924_a614ff04651eedb0a4939386da93f45e

[12] Valiant, Leslie
     "General context-free recognition in less than cubic time"
     http://repository.cmu.edu/cgi/viewcontent.cgi?article=2751&context=compsci

[13] Chomsky, Noam
     "On Certain Formal Properties of Grammars"
     http://ac.els-cdn.com/S0019995859903626/1-s2.0-S0019995859903626-main.pdf?_tid=791917b4-cc97-11e6-b90d-00000aab0f02&acdnat=1482886342_e7ebc938aed5cf9420ca550e14a7201b

[14] Firsov, Denis; Uustalo, Tarmo
     "Certified Parsing of Regular Languages"
     http://cs.ioc.ee/~tarmo/papers/cpp13.pdf

[15] Danielsson, Nils Anders
     "Total Parser Combinators"
     http://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf

     Video: 
     https://vimeo.com/16541551

[16] Nolen, David
     "David Nolen on Parsing with Derivatives"
     http://paperswelove.org/2016/video/david-nolen-parsing-with-derivatives/

[17] Friedman, D.P.; Wise, D.S.
     "Cons should not evaluate its arguments"
     http://www.cs.indiana.edu/pub/techreports/TR44.pdf

[18] Rutten, J.J.M.M.
     "Automata and Coinduction (an exercise in coalgebra)"
     http://www.math.ucla.edu/~znorwood/290d.2.14s/papers/Rutten-v1.pdf     

[19] "Parsing with Derivatives", ESOP reviews 
     http://matt.might.net/papers/reviews/esop2010-derivatives.txt

[20] Rutten, J.J.M.M.
     "Behavioural differential equations: a coinductive calculus of
     streams, automata, and power series"
     http://homepages.cwi.nl/~janr/papers/files-of-papers/tcs308.pdf

[21] Chomsky, N; Schutzenberger M. P
     "The Algebraic Theory of Context-Free Languages"
     http://www-igm.univ-mlv.fr/~berstel/Mps/Travaux/A/1963-7ChomskyAlgebraic.pdf

[22] Publications of J.J.M.M. Rutten
     http://homepages.cwi.nl/~janr/papers/

[23] Hansen, Helle Hvid; Costa, David; Rutten, Jan
     "Synthesis of Mealy Machines Using Derivatives"
     http://homepages.cwi.nl/~janr/papers/files-of-papers/HCR06.pdf

[24] Abel, Andreas; Chapman, James
     "Normalization by Evaluation in the Delay Monad:
      An Extended Case Study for Coinduction via Copatterns and Sized Types"
     https://pdfs.semanticscholar.org/a714/8780d3c54fff800f6da558bfbb4ddc170d2a.pdf

[25] 
     "Parsing with derivatives: Introduction"
     https://maniagnosis.crsr.net/2012/04/parsing-with-derivatives-introduction.html

[26] Andersen, Leif
     "Parsing With Derivatives"
     http://leifandersen.net/papers/andersen2012parsing.pdf

[27] Might, Matthew; Adams, Michael D.; Hollenbeck, Celeste
     "On the Complexity and Performance of Parsing with Derivatives"
     https://arxiv.org/pdf/1604.04695v1.pdf

[28] Bernardy, Jean-Philippe; Jansson, Patrik
     "Certified Context-Free Parsing: A Formalisation of Valiant's Algorithm in Agda"
     http://www.cse.chalmers.se/~patrikj/papers/ValiantAgda_2014-07-03_preprint.pdf


-}
