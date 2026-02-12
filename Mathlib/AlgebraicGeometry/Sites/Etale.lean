/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!

# The étale site

In this file we define the big étale site, i.e. the étale topology as a Grothendieck topology
on the category of schemes.

-/

@[expose] public section

universe v u

open CategoryTheory MorphismProperty Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Big étale site: the étale precoverage on the category of schemes. -/
def etalePrecoverage : Precoverage Scheme.{u} :=
  precoverage @Etale

/-- Big étale site: the étale pretopology on the category of schemes. -/
def etalePretopology : Pretopology Scheme.{u} :=
  pretopology @Etale

/-- Big étale site: the étale topology on the category of schemes. -/
abbrev etaleTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology @Etale

lemma zariskiTopology_le_etaleTopology : zariskiTopology ≤ etaleTopology := by
  apply grothendieckTopology_monotone
  intro X Y f hf
  infer_instance

/-- The small étale site of a scheme is the Grothendieck topology on the
category of schemes étale over `X` induced from the étale topology on `Scheme.{u}`. -/
def smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  X.smallGrothendieckTopology (P := @Etale)

/-- The pretopology generating the small étale site. -/
def smallEtalePretopology (X : Scheme.{u}) : Pretopology X.Etale :=
  X.smallPretopology (Q := @Etale) (P := @Etale)

instance {S : Scheme.{u}} (𝒰 : S.Cover (precoverage @Etale)) (i : 𝒰.I₀) : Etale (𝒰.f i) :=
  𝒰.map_prop i

/-- A separably closed field `Ω` defines a point on the étale topology by the fiber
functor `X ↦ Hom(Spec Ω, X)`. -/
noncomputable
def geometricFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] : etaleTopology.Point where
  fiber := coyoneda.obj ⟨Spec (.of Ω)⟩
  jointly_surjective {S} R hR (f : Spec (.of Ω) ⟶ S) := by
    obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective f
    rw [mem_grothendieckTopology_iff] at hR
    obtain ⟨𝒰, hle⟩ := hR
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    refine ⟨𝒰.X i, 𝒰.f i, hle _ ⟨i⟩, ?_⟩
    let k := (𝒰.X i).residueField y
    let m : S.residueField (𝒰.f i y) ⟶ (𝒰.X i).residueField y :=
      (𝒰.f i).residueFieldMap y
    algebraize [((𝒰.f i).residueFieldMap y).hom, a.hom]
    let b : (𝒰.X i).residueField y →ₐ[S.residueField (𝒰.f i y)] Ω :=
      IsSepClosed.lift
    have hfac : (𝒰.f i).residueFieldMap y ≫ CommRingCat.ofHom b.toRingHom = a := by
      ext1; exact b.comp_algebraMap
    use Spec.map (CommRingCat.ofHom b.toRingHom) ≫ (𝒰.X i).fromSpecResidueField y
    simp [SpecToEquivOfField, ← hfac]

section

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

noncomputable def pointSmallEtale : (smallEtaleTopology S).Point where
  fiber := Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := sorry
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
    have hfac : (𝒰.f i).residueFieldMap y ≫ CommRingCat.ofHom b.toRingHom = a := by
      ext1; exact b.comp_algebraMap
    have fac : Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          (𝒰.X i).fromSpecResidueField y ≫ 𝒰.f i =
        (SpecToEquivOfField Ω X).symm ⟨(𝒰.f i) y, a⟩ := by
      have : (𝒰.f i).residueFieldMap y ≫ CommRingCat.ofHom b.toRingHom = a := by
        ext1; exact b.comp_algebraMap
      simp [SpecToEquivOfField, ← this]
    dsimp at fac
    refine ⟨(𝒰.X i).asOverProp S inferInstance,
      MorphismProperty.Over.homMk (𝒰.f i), le _ ⟨i⟩,
      Over.homMk (Spec.map (CommRingCat.ofHom b.toRingHom) ≫
        (𝒰.X i).fromSpecResidueField y) ?_, ?_⟩
    · simp [Etale.forget, ← fac, hf]
    · cat_disch

end

end AlgebraicGeometry.Scheme
