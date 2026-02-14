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


-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- A morphism `s : Spec (.of Ω) ⟶ S` where `Ω` is a separably closed field
defines a point for the small étale site of `S`. -/
noncomputable def pointSmallEtale : (smallEtaleTopology S).Point where
  fiber := Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := by
    sorry
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
