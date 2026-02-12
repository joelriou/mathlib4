/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Initial and terminal objects in the category of functors

We show that if a functor `F : C ⥤ D` is such that `F.obj X`
is terminal for all `X`, then `F` is a terminal object.

-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category D]

/-- If `F : C ⥤ D` is such that `F.obj X` is terminal for any `X : C`,
then `F` is a terminal object. -/
def isTerminal {F : C ⥤ D} (hF : ∀ (X : C), IsTerminal (F.obj X)) :
    IsTerminal F := evaluationJointlyReflectsLimits _ fun X ↦ by
  refine IsLimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cones.ext (Iso.refl _) (by cat_disch)

/-- If `F : C ⥤ D` is such that `F.obj X` is initial for any `X : C`,
then `F` is an initial object. -/
def isInitial {F : C ⥤ D} (hF : ∀ (X : C), IsInitial (F.obj X)) :
    IsInitial F :=
  IsInitial.ofUniqueHom
    (fun G ↦
      { app _ := (hF _).to _
        naturality _ _ _ := (hF _).hom_ext _ _ })
    (fun _ _ ↦ by
      ext
      apply (hF _).hom_ext )

end CategoryTheory.Functor
