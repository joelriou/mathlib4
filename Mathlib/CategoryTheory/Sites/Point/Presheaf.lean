/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Points of presheaf toposes

Let `C` be a category. For the Grothendieck topology `⊥`, we know
that the category of sheaves with values in `A` identify to `Cᵒᵖ ⥤ A`
(see `sheafBotEquivalence` in the file `Mathlib/CategoryTheory/Sites/Sheaf.lean`).
In this file, we show that any `X : C` defines a point for this site, and that
these point form a conservative family of points.

## TODO
* show that the fiber functors identify the evaluation functors

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]

-- to be moved
/-- The object of the category of elements `shrinkYoneda.{w}.flip.obj (op X)`
corresponding to the identity of `X` is initial. -/
noncomputable def isInitialElementsMkShrinkYonedaObjObjEquivId (X : C) :
    IsInitial (Functor.elementsMk (shrinkYoneda.{w}.flip.obj (op X)) X
      (shrinkYonedaObjObjEquiv.symm (𝟙 X))) :=
  IsInitial.ofUniqueHom (fun u ↦ ⟨shrinkYonedaObjObjEquiv.{w} u.2, by
    dsimp
    rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm]
    simp⟩) (by
    rintro u ⟨m, hm⟩
    ext
    dsimp at hm ⊢
    rw [← hm, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm]
    simp)

namespace GrothendieckTopology

instance (X : C) : HasInitial (shrinkYoneda.{w}.flip.obj (op X)).Elements :=
  (isInitialElementsMkShrinkYonedaObjObjEquivId X).hasInitial

/-- If `X` is an object of `C`, this is the point of the site `(C, ⊥)` (whose
sheaves are presheaves, see `sheafBotEquivalence`) corresponding to `X`. -/
@[simps]
noncomputable def pointBot (X : C) :
    Point.{w} (⊥ : GrothendieckTopology C) where
  fiber := shrinkYoneda.flip.{w}.obj (op X)
  jointly_surjective {U} R hR x := by
    obtain rfl : R = ⊤ := by simpa using hR
    exact ⟨U, 𝟙 _, by simp, x, by simp⟩

variable (C) in
/-- The family of points on the site `(C, ⊥)` (whose
sheaves are presheaves, see `sheafBotEquivalence`) given by the objects of `X`. -/
noncomputable def pointsBot :
    ObjectProperty (Point.{w} (⊥ : GrothendieckTopology C)) :=
  .ofObj pointBot

instance : (pointsBot.{w} C).IsConservativeFamilyOfPoints :=
  ObjectProperty.IsConservativeFamilyOfPoints.mk'.{w} (fun X S hS ↦ by
    obtain ⟨Y, a, ha, b, hb⟩ := hS ⟨_, ⟨X⟩⟩ (shrinkYonedaObjObjEquiv.symm (𝟙 X))
    obtain ⟨b, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective b
    dsimp at b hb
    have : b ≫ a = 𝟙 _ :=
      shrinkYonedaObjObjEquiv.symm.injective (by
        rw [← hb, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])
    simpa only [bot_covering, ← Sieve.id_mem_iff_eq_top, this]
      using S.downward_closed ha b)

end GrothendieckTopology

end CategoryTheory
