/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Points of `Over` sites

Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`,
we define a point `Φ.over x` of the site `(Over X, J.over X)`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {C₀ : Type w} [SmallCategory C₀]
  (F : C₀ ⥤ C) {X : C} (Y : Over X)

namespace CostructuredArrow.costructuredArrowToOverEquivalence

@[simps]
def functor : CostructuredArrow (toOver F X) Y ⥤ CostructuredArrow F Y.left where
  obj Z := CostructuredArrow.mk Z.hom.left
  map f :=
    CostructuredArrow.homMk f.left.left (by rw [← CostructuredArrow.w f]; dsimp)

@[simps]
def inverse : CostructuredArrow F Y.left ⥤ CostructuredArrow (toOver F X) Y where
  obj Z :=
    CostructuredArrow.mk (Y := CostructuredArrow.mk (Z.hom ≫ Y.hom))
      (Over.homMk Z.hom)
  map f :=
    CostructuredArrow.homMk
      (CostructuredArrow.homMk f.left)
        (by ext; exact CostructuredArrow.w f)

end CostructuredArrow.costructuredArrowToOverEquivalence

def CostructuredArrow.costructuredArrowToOverEquivalence :
    CostructuredArrow (toOver F X) Y ≌ CostructuredArrow F Y.left where
  functor := costructuredArrowToOverEquivalence.functor F Y
  inverse := costructuredArrowToOverEquivalence.inverse F Y
  unitIso :=
    NatIso.ofComponents (fun _ ↦
      CostructuredArrow.isoMk (CostructuredArrow.isoMk (Iso.refl _)))
  counitIso := Iso.refl _

end

namespace InitiallySmall

variable {C : Type u} [Category.{v} C] {C₀ : Type w} [SmallCategory C₀]

section

instance (F : C₀ ⥤ C) (X : C) [F.Initial] :
    (CostructuredArrow.toOver F X).Initial where
  out Y := by
    rw [isConnected_iff_of_equivalence
      (CostructuredArrow.costructuredArrowToOverEquivalence F Y)]
    infer_instance

end

instance [LocallySmall.{w} C] [InitiallySmall.{w} C] (X : C) :
    InitiallySmall.{w} (Over X) := by
  have : InitiallySmall.{w} (CostructuredArrow (fromInitialModel.{w} C) X) :=
    initiallySmall_of_essentiallySmall _
  exact initiallySmall_of_initial_of_initiallySmall
    (CostructuredArrow.toOver (fromInitialModel.{w} C) X)

end InitiallySmall

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

variable [LocallySmall.{w} C] (Φ : Point.{w} J) {X : C} (x : Φ.fiber.obj X)

open InitiallySmall in
/-- Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`,
this is the point of the site `(Over X, J.over X)` such that the fiber of
an object of `Over X` corresponding to a morphism `f : Y ⟶ X` identifies
to subtype of `Φ.fiber.obj Y` consisting of elemnts `y` such
that `Φ.fiber.map f y = x`. -/
def over : Point.{w} (J.over X) where
  fiber := FunctorToTypes.fromOverFunctor Φ.fiber x
  initiallySmall :=
    initiallySmall_of_initial_of_initiallySmall
      (FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).inverse
  jointly_surjective := by
    rintro U R hR ⟨u, hu⟩
    obtain ⟨R, rfl⟩ := (Sieve.overEquiv _).symm.surjective R
    simp only [mem_over_iff, Equiv.apply_symm_apply] at hR
    obtain ⟨Y, f, hf, v, rfl⟩ := Φ.jointly_surjective R hR u
    refine ⟨Over.mk (f ≫ U.hom), Over.homMk f, hf, ⟨v, ?_⟩, rfl⟩
    rw [FunctorToTypes.mem_fromOverSubfunctor_iff] at hu ⊢
    simpa

end GrothendieckTopology.Point

end CategoryTheory
