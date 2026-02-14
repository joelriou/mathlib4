/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!

# Points of the étale site

In this file, we show that a morphism `Spec (.of Ω) ⟶ S` where `Ω` is
a separably closed field defined a point on the small étale site of `S`.

-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

instance : IsCofiltered (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))).Elements :=
  Functor.isCofiltered_elements _

/-- A morphism `s : Spec (.of Ω) ⟶ S` where `Ω` is a separably closed field
defines a point for the small étale site of `S`. -/
noncomputable def pointSmallEtale : (smallEtaleTopology S).Point where
  fiber := Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))
  initiallySmall :=
    initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
      (Functor.Elements.precomp (AffineEtale.Spec S)
        (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s)))).essImage (by
      rintro ⟨X, x⟩
      induction X with | _ Y f
      obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
      dsimp at y hy
      obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
          (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
        obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
          (x := y.base default) (U := ⊤) (by simp)
        refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
        rintro _ ⟨a, rfl⟩
        rwa [Subsingleton.elim a default]
      exact ⟨_,
        ⟨Functor.elementsMk _ (AffineEtale.mk (j ≫ f)) (Over.homMk y'), ⟨Iso.refl _⟩⟩,
        ⟨⟨MorphismProperty.Over.homMk j rfl (by simp), by cat_disch⟩⟩⟩)
  jointly_surjective {X} R hR φ := by
    induction X with | _ X f
    obtain ⟨φ : Spec (.of Ω) ⟶ X, rfl : φ ≫ f = s, rfl⟩ := Over.homMk_surjective φ
    obtain ⟨𝒰, h, _, le⟩ := (mem_smallGrothendieckTopology _ _).1 hR
    obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective φ
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    have hf : 𝒰.f i ≫ f = 𝒰.X i ↘ S := (h.isOver_map i).comp_over
    let m := ((𝒰.f i).residueFieldMap y).hom
    dsimp at m
    algebraize [m, a.hom]
    let b : (𝒰.X i).residueField y →ₐ[X.residueField (𝒰.f i y)] Ω :=
      IsSepClosed.lift
    have fac : Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          (𝒰.X i).fromSpecResidueField y ≫ 𝒰.f i =
        (SpecToEquivOfField Ω X).symm ⟨(𝒰.f i) y, a⟩ := by
      have : (𝒰.f i).residueFieldMap y ≫ CommRingCat.ofHom b.toRingHom = a := by
        ext1; exact b.comp_algebraMap
      simp [SpecToEquivOfField, ← this]
    dsimp at fac
    exact ⟨(𝒰.X i).asOverProp S inferInstance,
      MorphismProperty.Over.homMk (𝒰.f i), le _ ⟨i⟩,
      Over.homMk (Spec.map (CommRingCat.ofHom b.toRingHom) ≫
        (𝒰.X i).fromSpecResidueField y) (by simp [Etale.forget, ← fac, hf]), by cat_disch⟩

end AlgebraicGeometry.Scheme
