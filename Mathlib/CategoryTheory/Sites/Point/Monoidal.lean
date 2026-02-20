/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.Multifunctor

/-!
# Fiber functors are monoidal


-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory.Limits

open Functor

instance isIso_colimMap {J C : Type*} [Category* J] [Category* C] {F G : J ⥤ C}
    [HasColimit F] [HasColimit G] (τ : F ⟶ G) [IsIso τ] :
    IsIso (colimMap τ) :=
  ⟨colimMap (inv τ), by cat_disch, by cat_disch⟩

variable
  {C₁ C₂ C : Type*} [Category* C₁] [Category* C₂] [Category* C]
  (F : C₁ ⥤ C₂ ⥤ C)

section

variable (J₁ J₂ : Type*) [Category* J₁] [Category* J₂]
  [HasColimitsOfShape J₁ C₁] [HasColimitsOfShape J₂ C₂]
  [HasColimitsOfShape (J₁ × J₂) C]

noncomputable def colim₂Comparison :
    curry.obj (prodFunctor ⋙
      (whiskeringRight (J₁ × J₂) (C₁ × C₂) C).obj (uncurry.obj F) ⋙ colim) ⟶
    colim (J := J₁) ⋙ (colim (J := J₂) ⋙ F.flip).flip where
  app G₁ :=
    { app G₂ := colimit.desc _ (F.mapCocone₂ (colimit.cocone G₁) (colimit.cocone G₂))
      naturality G₂ G₂' f := by
        dsimp
        ext j
        have h₁ : colimit.ι (G₁.prod G₂' ⋙ uncurry.obj F) j ≫ _ = _ :=
          colimit.ι_desc
            (F.mapCocone₂ (colimit.cocone G₁) (colimit.cocone G₂')) _
        have h₂ : colimit.ι (G₁.prod G₂ ⋙ uncurry.obj F) j ≫ _ = _ :=
          colimit.ι_desc (F.mapCocone₂ (colimit.cocone G₁) (colimit.cocone G₂)) _
        simp [h₁, reassoc_of% h₂, ← Functor.map_comp] }
  naturality G₁ G₁' f := by
    ext G₂
    dsimp
    ext j
    have h₁ : colimit.ι (G₁'.prod G₂ ⋙ uncurry.obj F) j ≫ _ = _ :=
      colimit.ι_desc (F.mapCocone₂ (colimit.cocone G₁') (colimit.cocone G₂)) j
    have h₂ : colimit.ι (G₁.prod G₂ ⋙ uncurry.obj F) j ≫ _ = _ :=
      colimit.ι_desc (F.mapCocone₂ (colimit.cocone G₁) (colimit.cocone G₂)) j
    simp [h₁, reassoc_of% h₂, ← NatTrans.comp_app_assoc, ← Functor.map_comp]

variable {J₁ J₂} in
@[reassoc (attr := simp)]
lemma ι_colim₂Comparison_app_app (G₁ : J₁ ⥤ C₁) (G₂ : J₂ ⥤ C₂) (j : J₁ × J₂) :
    colimit.ι (G₁.prod G₂ ⋙ uncurry.obj F) j ≫ ((colim₂Comparison F J₁ J₂).app G₁).app G₂ =
      (F.map (colimit.ι G₁ j.1)).app _ ≫ (F.obj _).map (colimit.ι G₂ j.2) :=
  colimit.ι_desc _ _

variable [∀ (G₁ : J₁ ⥤ C₁) (G₂ : J₂ ⥤ C₂), PreservesColimit₂ G₁ G₂ F]

instance isIso_colim₂Comparison :
    IsIso (colim₂Comparison F J₁ J₂) := by
  simp only [NatTrans.isIso_iff_isIso_app]
  intro G₁ G₂
  exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfPreserves₂ F (colimit.isColimit G₁) (colimit.isColimit G₂))).isIso_hom

@[simps! hom]
noncomputable def colim₂ComparisonIso :
    curry.obj (prodFunctor ⋙
      (whiskeringRight (J₁ × J₂) (C₁ × C₂) C).obj (uncurry.obj F) ⋙ colim) ≅
    colim (J := J₁) ⋙ (colim (J := J₂) ⋙ F.flip).flip :=
  asIso (colim₂Comparison F J₁ J₂)

end

section

variable (J : Type*) [Category* J]
  [HasColimitsOfShape (J × J) C]
  [HasColimitsOfShape J C]
  (G₁ : J ⥤ C₁) (G₂ : J ⥤ C₂)

noncomputable def colim₂DiagComparison :
    curry.obj (prodFunctorToFunctorProd J C₁ C₂ ⋙ (whiskeringRight J _ C).obj (uncurry.obj F) ⋙
      colim (J := J)) ⟶
    curry.obj (prodFunctor ⋙
      (whiskeringRight (J × J) (C₁ × C₂) C).obj (uncurry.obj F) ⋙ colim) where
  app G₁ :=
    { app G₂ := colimit.pre (E := Functor.diag J) (F := G₁.prod G₂ ⋙ uncurry.obj F)
      naturality G₂ G₂' f := by dsimp; symm; apply colimit.pre_map }
  naturality G₁ G₁' f := by ext; dsimp; symm; apply colimit.pre_map

@[reassoc (attr := simp)]
lemma ι_colim₂DiagComparison_app_app (G₁ : J ⥤ C₁) (G₂ : J ⥤ C₂) (j : J) :
    colimit.ι (G₁.prod' G₂ ⋙ uncurry.obj F) j ≫ ((colim₂DiagComparison F J).app G₁).app G₂ =
      colimit.ι (G₁.prod G₂ ⋙ uncurry.obj F) ⟨j, j⟩ :=
  colimit.ι_desc _ _

instance isIso_colim₂DiagComparison [IsSiftedOrEmpty J] :
    IsIso (colim₂DiagComparison F J) := by
  simp only [NatTrans.isIso_iff_isIso_app]
  intro _ _
  dsimp [colim₂DiagComparison]
  infer_instance

@[simps! hom]
noncomputable def colim₂DiagComparisonIso [IsSiftedOrEmpty J] :
    curry.obj (prodFunctorToFunctorProd J C₁ C₂ ⋙ (whiskeringRight J _ C).obj (uncurry.obj F) ⋙
      colim (J := J)) ≅
    curry.obj (prodFunctor ⋙
      (whiskeringRight (J × J) (C₁ × C₂) C).obj (uncurry.obj F) ⋙ colim) :=
  asIso (colim₂DiagComparison F J)

end

end CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite MonoidalCategory Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  [MonoidalCategory A]

instance : HasColimitsOfShape (Φ.fiber.Elementsᵒᵖ × Φ.fiber.Elementsᵒᵖ) A :=
  hasColimitsOfShape_of_finallySmall _ _

attribute [local simp] tensorHom_def toPresheafFiber presheafFiber in
noncomputable def δ : curriedTensorPost (Φ.presheafFiber (A := A)) ⟶
    curriedTensorPre Φ.presheafFiber :=
  letI α := (whiskeringLeft _ _ A).obj (CategoryOfElements.π Φ.fiber).op
  { app G₁ := { app G₂ := colimMap { app j := by exact 𝟙 _  } } } ≫
    (((whiskeringLeft₂ _).obj α).obj α).map
      (colim₂DiagComparison (curriedTensor A) Φ.fiber.Elementsᵒᵖ ≫
        colim₂Comparison _ _ _)

attribute [local simp] tensorHom_def δ toPresheafFiber in
@[reassoc (attr := simp)]
lemma toPresheafFiber_δ_app_app (X : C) (x : Φ.fiber.obj X) (G₁ G₂ : Cᵒᵖ ⥤ A) :
    Φ.toPresheafFiber X x (G₁ ⊗ G₂) ≫ (Φ.δ.app G₁).app G₂ =
      Φ.toPresheafFiber X x G₁ ⊗ₘ Φ.toPresheafFiber X x G₂ := by
  cat_disch

noncomputable def η : Φ.presheafFiber.obj (𝟙_ (Cᵒᵖ ⥤ A)) ⟶ 𝟙_ A :=
  Φ.presheafFiberDesc (fun _ _ ↦ 𝟙 _)

@[reassoc (attr := simp)]
lemma toPresheafFiber_η (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x (𝟙_ (Cᵒᵖ ⥤ A)) ≫ Φ.η (A := A) = 𝟙 (𝟙_ A) := by
  simp [η]

attribute [local instance] IsFiltered.isConnected in
instance : IsIso (Φ.η (A := A)) :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitConstCocone _ (𝟙_ A))).isIso_hom

noncomputable instance : (Φ.presheafFiber (A := A)).OplaxMonoidal :=
  .ofBifunctor Φ.η Φ.δ (by
    ext G₁ G₂ G₃
    refine Φ.presheafFiber_hom_ext (fun X x ↦ ?_)
    dsimp
    rw [toPresheafFiber_δ_app_app_assoc, tensorHom_def'_assoc,
      ← comp_whiskerRight_assoc, toPresheafFiber_δ_app_app, ← tensorHom_def'_assoc,
      toPresheafFiber_naturality_assoc, toPresheafFiber_δ_app_app_assoc]
    nth_rw 2 [tensorHom_def_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp, toPresheafFiber_δ_app_app, ← tensorHom_def,
      associator_naturality]
    dsimp)
    (by ext; simp [tensorHom_def', ← comp_whiskerRight])
    (by ext; simp [tensorHom_def, ← MonoidalCategory.whiskerLeft_comp])

instance :
    IsIso (Functor.OplaxMonoidal.η (Φ.presheafFiber (A := A))) :=
  inferInstanceAs (IsIso Φ.η)

variable [LocallySmall.{w} C]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

instance (M : A) :
    PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ ((curriedTensor A).flip.obj M) :=
  Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

instance (M : A) :
    PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ ((curriedTensor A).obj M) :=
  Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

instance : IsIso (Φ.δ (A := A)) := by
  simp only [NatTrans.isIso_iff_isIso_app]
  intro G₁ G₂
  dsimp [δ]
  rw [isIso_comp_right_iff]
  apply +allowSynthFailures isIso_colimMap
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  dsimp
  infer_instance

instance (G₁ G₂ : Cᵒᵖ ⥤ A) :
    IsIso (Functor.OplaxMonoidal.δ (Φ.presheafFiber) G₁ G₂) :=
  inferInstanceAs (IsIso ((Φ.δ.app G₁).app G₂))

noncomputable instance : (Φ.presheafFiber (A := A)).Monoidal :=
  .ofOplaxMonoidal _

end CategoryTheory.GrothendieckTopology.Point
