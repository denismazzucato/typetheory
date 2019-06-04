module Commutative where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl )

comm : {n : Set} {m : Set} → n ≡ m → m ≡ n -- or something similar
comm x rewrite comm m n= {!!}
