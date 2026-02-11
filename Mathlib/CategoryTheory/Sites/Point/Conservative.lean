/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Conservative families of points

Let `J` be a Grothendieck topology on a category `C`.
Let `P : ObjectProperty J.Point` be a family of points. We say that
`P` is a conservative family of points if the corresponding
fiber functors `Sheaf J (Type w) ⥤ Type w` are conservative.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (P : ObjectProperty (GrothendieckTopology.Point.{w} J))

namespace ObjectProperty

/-- Let `P : ObjectProperty J.Point` a family of points of a
site `(C, J)`). We say that it is a conservative family of points
if the corresponding fiber functors `Sheaf J (Type w) ⥤ Type w`
jointly reflect isomorphisms. -/
@[stacks 00YJ]
class IsConservativeFamilyOfPoints : Prop where
  jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := Type w))

end ObjectProperty

namespace GrothendieckTopology.Point

variable [P.IsConservativeFamilyOfPoints]
  (A : Type u') [Category.{v'} A] [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} A] [HasFiniteLimits A]
  {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC]
  [AB5OfSize.{w, w} A]
  [(forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]

lemma jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  have := ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms
    (P := P)
  sorry

lemma jointlyReflectMonomorphisms [LocallySmall.{w} C] :
    JointlyReflectMonomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (jointlyReflectIsomorphisms P A).jointlyReflectMonomorphisms

lemma jointlyReflectEpimorphisms [LocallySmall.{w} C]
    [J.WEqualsLocallyBijective A] [HasSheafify J A] :
    JointlyReflectEpimorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (jointlyReflectIsomorphisms P A).jointlyReflectEpimorphisms

end GrothendieckTopology.Point

end CategoryTheory
