/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.UniqueUpToUniqueIso

/-!
# (Generalized) Reedy categories

## References
* https://ncatlab.org/nlab/show/generalized+Reedy+category

-/

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (α : Type w) [LinearOrder α]

structure ReedyStructure where
  deg : C → α
  plus : MorphismProperty C
  minus : MorphismProperty C
  [isMultiplicative_plus : plus.IsMultiplicative]
  [isMultiplicative_minus : minus.IsMultiplicative]
  eq_of_iso {X Y : C} (e : X ≅ Y) : deg X = deg Y
  lt_of_plus {X Y : C} (i : X ⟶ Y) : plus i → ¬IsIso i → deg X < deg Y
  lt_of_minus {X Y : C} (p : X ⟶ Y) : minus p → ¬IsIso p → deg Y < deg X
  plus_inter_minus : plus ⊓ minus = .isomorphisms C
  isUniqueUpToUniqueIso {X Y : C} (f : X ⟶ Y) :
    IsUniqueUpToUniqueIso (minus.MapFactorizationData plus f) := by infer_instance

namespace ReedyStructure

variable {C α} (h : ReedyStructure C α)

class MinusCondition : Prop where
  left_cancel {X Y : C} (p : X ⟶ Y) (hp : h.minus p) (e : Y ⟶ Y) [IsIso e] :
      p ≫ e = p → e = 𝟙 _

class PlusCondition : Prop where
  right_cancel {X Y : C} (i : X ⟶ Y) (hi : h.plus i) (e : X ⟶ X) [IsIso e] :
      e ≫ i = i → e = 𝟙 _

end ReedyStructure

end CategoryTheory
