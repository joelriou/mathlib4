/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Points of

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]

noncomputable def isInitialElementsMkShrinkYonedaObjObjEquivId (X : C) :
    IsInitial (Functor.elementsMk (shrinkYoneda.{w}.flip.obj (op X)) X
      (shrinkYonedaObjObjEquiv.symm (𝟙 X))) :=
  IsInitial.ofUniqueHom (fun u ↦ ⟨shrinkYonedaObjObjEquiv.{w} u.2, sorry⟩) (by
      rintro u ⟨m, hm⟩
      ext
      dsimp at hm ⊢
      rw [← hm]
      sorry)

namespace GrothendieckTopology

instance (X : C) : HasInitial (shrinkYoneda.{w}.flip.obj (op X)).Elements :=
  (isInitialElementsMkShrinkYonedaObjObjEquivId X).hasInitial

noncomputable def pointBot (X : C) :
    Point.{w} (⊥ : GrothendieckTopology C) where
  fiber := shrinkYoneda.flip.{w}.obj (op X)
  jointly_surjective {U} R hR x := by
    obtain rfl : R = ⊤ := by simpa using hR
    exact ⟨U, 𝟙 _, by simp, x, by simp⟩

variable (C) in
noncomputable def pointsBot :
    ObjectProperty (Point.{w} (⊥ : GrothendieckTopology C)) :=
  .ofObj pointBot


end GrothendieckTopology

end CategoryTheory
