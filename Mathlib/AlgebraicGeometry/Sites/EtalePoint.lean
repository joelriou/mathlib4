/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Category

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
@[simps -isSimp]
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

variable {s₀ : S} (hs₀ : s default = s₀)

@[simps]
def pointSmallEtaleFiberObjToPreimage {X : S.Etale}
    (t : (pointSmallEtale s).fiber.obj X) :
    X.hom ⁻¹' {s₀} :=
  ⟨t.left (default : Spec (.of Ω)), by
    have := Over.w t
    dsimp at this
    rw [← this] at hs₀
    simpa⟩

lemma pointSmallEtaleFiberObjToPreimage_surjective (X : S.Etale) :
    Function.Surjective
      (pointSmallEtaleFiberObjToPreimage s hs₀ (X := X)) := sorry

-- The following will have to wait for #35175
variable {ι : Type*} {S : Scheme.{u}}
  {Ω : ι → Type u} [∀ i, Field (Ω i)] [∀ i, IsSepClosed (Ω i)]
  (s : ∀ i, Spec (.of (Ω i)) ⟶ S)
  (hs : ⋃ i, Set.range (s i) = .univ)

include hs in
lemma isConservative_aux {X : S.Etale} {α : Type*} {Y : α → S.Etale} (f : ∀ a, Y a ⟶ X)
    (hf : ∀ (i : ι) (x : (pointSmallEtale (s i)).fiber.obj X),
      ∃ (a : α) (y : (pointSmallEtale (s i)).fiber.obj (Y a)),
        (pointSmallEtale (s i)).fiber.map (f a) y = x) :
    Sieve.ofArrows _ f ∈ smallEtaleTopology _ _ := by
  rw [ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨i, hi⟩ : ∃ i, s i default = X.hom x := by
    have := Set.mem_univ (X.hom x)
    simp only [← hs, Functor.const_obj_obj, Functor.id_obj, Set.mem_iUnion,
      Set.mem_range] at this
    obtain ⟨i, y, hy⟩ := this
    obtain rfl := Subsingleton.elim y default
    exact ⟨i, hy⟩
  obtain ⟨x', hx'⟩ :=pointSmallEtaleFiberObjToPreimage_surjective (s i) hi X ⟨x, by simp⟩
  rw [Subtype.ext_iff] at hx'
  dsimp at hx'
  obtain ⟨a, y, hy⟩ := hf i x'
  exact ⟨a, (pointSmallEtaleFiberObjToPreimage (s i) hi y).1, by aesop⟩

end AlgebraicGeometry.Scheme
