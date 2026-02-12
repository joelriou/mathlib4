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
fiber functors `Sheaf J (Type w) ⥤ Type w` jointly reflect
isomorphisms. Under suitable assumptions on the coefficient
category `A`, this implies that the fiber functors
`Sheaf J A ⥤ A` corresponding to the points in `P`
jointly reflect isomorphisms, epimorphisms and monomorphisms,
and they are also jointly faithful.

## TODO
* Formalize SGA 4 IV 6.5 (a) which characterizes conservative families
of points.

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
@[stacks 00YJ "(1)"]
class IsConservativeFamilyOfPoints : Prop where
  jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := Type w))

end ObjectProperty

namespace GrothendieckTopology.Point

variable [P.IsConservativeFamilyOfPoints]
  (A : Type u') [Category.{v'} A] [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} A]
  {FC : A → A → Type*} {CC : A → Type w}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} A FC]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]

@[stacks 00YJ "(1)"]
lemma jointlyReflectIsomorphisms
    [J.HasSheafCompose (forget A)] [(forget A).ReflectsIsomorphisms] :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) where
  isIso {K L} f _ := by
    rw [← isIso_iff_of_reflects_iso _ (sheafCompose J (forget A)),
      (ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms
        (P := P)).isIso_iff]
    exact fun Φ ↦ ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (Φ.obj.sheafFiberCompIso (forget A))).app (Arrow.mk f))).2
          (inferInstanceAs (IsIso ((forget A).map (Φ.obj.sheafFiber.map f))))

@[stacks 00YK "(1)"]
lemma jointlyReflectMonomorphisms [AB5OfSize.{w, w} A] [HasFiniteLimits A]
    [J.HasSheafCompose (forget A)] [(forget A).ReflectsIsomorphisms] :
    JointlyReflectMonomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (jointlyReflectIsomorphisms P A).jointlyReflectMonomorphisms

@[stacks 00YK "(2)"]
lemma jointlyReflectEpimorphisms
    [J.WEqualsLocallyBijective A] [HasSheafify J A]
    [J.HasSheafCompose (forget A)] [(forget A).ReflectsIsomorphisms] :
    JointlyReflectEpimorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (jointlyReflectIsomorphisms P A).jointlyReflectEpimorphisms

@[stacks 00YK "(3)"]
lemma jointlyFaithful [AB5OfSize.{w, w} A] [HasFiniteLimits A]
    [J.HasSheafCompose (forget A)] [(forget A).ReflectsIsomorphisms] :
    JointlyFaithful
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (jointlyReflectIsomorphisms P A).jointlyFaithful

variable {A} in
lemma jointly_reflect_isLocallySurjective
    [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
    {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y)
    (hf : ∀ (Φ : P.FullSubcategory),
      Function.Surjective (Φ.obj.presheafFiber.map f)) :
    Presheaf.IsLocallySurjective J f := by
  simp only [← epi_iff_surjective] at hf
  rw [Presheaf.isLocallySurjective_iff_whisker_forget,
    ← Presheaf.isLocallySurjective_presheafToSheaf_map_iff,
    Sheaf.isLocallySurjective_iff_epi,
    (jointlyReflectEpimorphisms P (Type w)).epi_iff]
  exact fun Φ ↦ ((MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso
      ((Φ.obj.presheafFiberCompIso (forget A)).symm ≪≫
        Functor.isoWhiskerLeft _ (Φ.obj.presheafToSheafCompSheafFiber (Type w)).symm)).app
          (Arrow.mk f))).1 (hf Φ)

section

variable [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  {X : C} {ι : Type*} [Small.{w} ι] {U : ι → C} (f : ∀ i, U i ⟶ X)

lemma jointly_reflect_ofArrows_mem :
    Sieve.ofArrows _ f ∈ J X ↔
      ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
        ∃ (i : ι) (y : Φ.obj.fiber.obj (U i)), Φ.obj.fiber.map (f i) y = x := by
  refine ⟨fun hf Φ x ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨Z, _, ⟨_, p, _, ⟨i⟩, rfl⟩, z, rfl⟩ := Φ.obj.jointly_surjective _ hf x
    exact ⟨i, Φ.obj.fiber.map p z, by simp⟩
  · rw [ofArrows_mem_iff_isLocallySurjective]
    refine jointly_reflect_isLocallySurjective P _ (fun Φ x ↦ ?_)
    obtain ⟨x, rfl⟩ := (Φ.obj.shrinkYonedaCompPresheafFiberIso.app X).toEquiv.symm.surjective x
    obtain ⟨i, y, rfl⟩ := hf Φ x
    refine ⟨Φ.obj.presheafFiber.map (Sigma.ι (fun i ↦ shrinkYoneda.{w}.obj (U i)) i)
      (Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.app _ y), ?_⟩
    have  := congr_fun (Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.naturality (f i)) y
    dsimp at this ⊢
    rw [this, ← Sigma.ι_desc (fun i ↦ shrinkYoneda.{w}.map (f i)) i, Functor.map_comp]
    rfl

end

end GrothendieckTopology.Point

end CategoryTheory
