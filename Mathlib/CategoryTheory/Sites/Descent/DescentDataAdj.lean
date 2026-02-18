/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Descent data we have both pullbacks and pushforward

-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Bicategory Opposite

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}}

end Pseudofunctor

end CategoryTheory
