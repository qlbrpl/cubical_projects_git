{-# OPTIONS --safe #-}

module Automata.Imports where


open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Isomorphism public

open import Cubical.Data.Sigma public
open import Cubical.Data.FinSet public
open import Cubical.Data.Bool hiding (_≤_ ; _≥_ ; isProp≤ ; elim) public
open import Cubical.Data.Nat hiding (elim) public
open import Cubical.Data.List as L hiding (elim) public
open import Cubical.Data.Sum hiding (elim ; rec ; map) public
