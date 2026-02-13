/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Points of presheaf toposes

Let `C` be a category. For the Grothendieck topology `⊥` on `C`, we know
that the category of sheaves with values in `A` identify to `Cᵒᵖ ⥤ A`
(see `sheafBotEquivalence` in the file `Mathlib/CategoryTheory/Sites/Sheaf.lean`).
In this file, we show that any `X : C` defines a point for this site, and that
these point form a conservative family of points.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]

variable [LocallySmall.{w} C]

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
  fiber := shrinkYoneda.flip.obj (op X)
  jointly_surjective {U} R hR x := by
    obtain rfl : R = ⊤ := by simpa using hR
    exact ⟨U, 𝟙 _, by simp, x, by simp⟩

/-- The functor `C ⥤ Point.{w} (⊥ : GrothendieckTopology C)` which sends
`X : C` to the point corresponding to `X`. -/
@[simps]
noncomputable def pointBotFunctor :
    C ⥤ Point.{w} (⊥ : GrothendieckTopology C) where
  obj := pointBot
  map f := { hom := shrinkYoneda.flip.map f.op }

section

variable (X : C) (A : Type*) [Category A] [HasColimitsOfSize.{w, w} A]

instance :
    IsIso ((pointBot.{w} X).toPresheafFiberNatTrans (A := A) X
      (shrinkYonedaObjObjEquiv.symm (𝟙 X))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ ↦ (colimit.isColimit _).isIso_ι_app_of_isTerminal _
    (isInitialElementsMkShrinkYonedaObjObjEquivId X).op

/-- The fiber functor `(Cᵒᵖ ⥤ A) ⥤ A` corresponding to the point
of the Grothendieck topology `⊥` attached to an object `X : C`
identifies to the evaluation functor at `X`. -/
@[simps! inv]
noncomputable def pointBotPresheafFiberIso :
    (pointBot.{w} X).presheafFiber (A := A) ≅
      (evaluation Cᵒᵖ A).obj (op X) :=
  (asIso ((pointBot X).toPresheafFiberNatTrans X
      (shrinkYonedaObjObjEquiv.symm (𝟙 X)))).symm

end

variable (C) in
/-- The family of points on the site `(C, ⊥)` (whose
sheaves are presheaves, see `sheafBotEquivalence`) given by the objects of `X`. -/
noncomputable def pointsBot :
    ObjectProperty (Point.{w} (⊥ : GrothendieckTopology C)) :=
  .ofObj pointBot

lemma isConservative_pointsBot :
    (pointsBot.{w} C).IsConservativeFamilyOfPoints :=
  .mk' (fun X S hS ↦ by
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
