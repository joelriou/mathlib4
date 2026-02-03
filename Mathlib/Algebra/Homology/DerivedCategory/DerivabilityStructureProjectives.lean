/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Minus
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.ModelCategory.Projective
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureCofibrant
public import Mathlib.CategoryTheory.GuitartExact.Quotient
public import Mathlib.CategoryTheory.ObjectProperty.HomologicalComplex
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences

/-!
# The projective derivability structure

-/

@[expose] public section

universe w₁ w₂

open HomotopicalAlgebra CategoryTheory Limits ZeroObject Category

variable (C : Type*) [Category C] [Abelian C]
  {H : Type*} [Category H]

namespace CategoryTheory

abbrev ProjectiveObject := ObjectProperty.FullSubcategory (fun (X : C) => Projective X)

namespace ProjectiveObject

instance closedUnderLimitsOfShapeDiscrete (J : Type*) :
    ObjectProperty.IsClosedUnderColimitsOfShape (fun (X : C) => Projective X) (Discrete J) where
  colimitsOfShape_le := by
    rintro Y ⟨p⟩
    have : HasColimit p.diag := ⟨_, p.isColimit⟩
    let X := fun j => p.diag.obj ⟨j⟩
    let e := Discrete.natIsoFunctor (F := p.diag)
    have : HasCoproduct X := hasColimit_of_iso e.symm
    have : HasColimit (Discrete.functor (p.diag.obj ∘ Discrete.mk)) := by
      change HasCoproduct X
      infer_instance
    have : ∀ j, Projective (X j) := fun j => p.prop_diag_obj ⟨j⟩
    have e' : ∐ X ≅ Y := IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      ((IsColimit.precomposeInvEquiv e _).symm p.isColimit)
    exact Projective.of_iso e' inferInstance

instance : HasFiniteCoproducts (ProjectiveObject C) where
  out n := by infer_instance

instance : HasFiniteBiproducts (ProjectiveObject C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

instance : HasBinaryBiproducts (ProjectiveObject C) := hasBinaryBiproducts_of_finite_biproducts _

instance : HasZeroObject (ProjectiveObject C) where
  zero := by
    refine ⟨⟨0, inferInstance⟩, ?_⟩
    rw [IsZero.iff_id_eq_zero]
    ext : 1
    apply id_zero

abbrev ι : ProjectiveObject C ⥤ C := ObjectProperty.ι _

instance (X : ProjectiveObject C) : Projective ((ι C).obj X) := X.2

instance (X : ProjectiveObject C) : Projective X.obj := X.2

instance (X : HomotopyCategory.Plus (ProjectiveObject C)) (n : ℤ) :
    Projective (((ι C).mapHomotopyCategoryPlus.obj X).obj.as.X n) := by
  change Projective ((ι C).obj (X.obj.as.X n))
  infer_instance

instance (K : CochainComplex.Minus (ProjectiveObject C)) :
    CochainComplex.IsKProjective
      (((ProjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K.obj) := by
  obtain ⟨K, n, hn⟩ := K
  let L := ((ProjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K
  have (n : ℤ) : Projective (L.X n) := by dsimp [L]; infer_instance
  exact CochainComplex.isKProjective_of_projective L n

end ProjectiveObject

end CategoryTheory

namespace CochainComplex.Minus

@[simps]
def localizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (ProjectiveObject.ι C).mapCochainComplexMinus)
      (quasiIso C) where
  functor := (ProjectiveObject.ι C).mapCochainComplexMinus
  map := by rfl

instance : (localizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance (K : Minus (ProjectiveObject C)) (n : ℤ) :
    Projective (K.obj.X n).obj :=
  (K.obj.X n).property

variable [EnoughProjectives C]

open modelCategoryQuillen

instance (K : CofibrantObject (Minus C)) (n : ℤ) :
    Projective (K.obj.obj.X n) := by
  obtain ⟨K, hK⟩ := K
  rw [cofibrantObjects, modelCategoryQuillen.isCofibrant_iff] at hK
  dsimp
  infer_instance

def cofibrantObjectEquivalence :
    Minus (ProjectiveObject C) ≌ CofibrantObject (Minus C) where
  functor := ObjectProperty.lift _ (ProjectiveObject.ι C).mapCochainComplexMinus (fun K ↦ by
    dsimp [cofibrantObjects]
    rw [modelCategoryQuillen.isCofibrant_iff]
    intro n
    dsimp
    infer_instance)
  inverse := ObjectProperty.lift _
    (HomologicalComplex.liftFunctorObjectProperty _ (CofibrantObject.ι ⋙ Minus.ι C)
      (fun K n ↦ by dsimp; infer_instance)) (by
        rintro ⟨⟨K, n, hn⟩, _⟩
        refine ⟨n, ?_⟩
        rw [isStrictlyLE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero]
        ext
        apply (K.isZero_of_isStrictlyLE n i hi).eq_of_src)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simps]
def cofibrantObjectLocalizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (ProjectiveObject.ι C).mapCochainComplexMinus)
      (weakEquivalences (CofibrantObject (Minus C))) where
  functor := (cofibrantObjectEquivalence C).functor
  map := by rfl

instance : (cofibrantObjectLocalizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance : (cofibrantObjectLocalizerMorphism C).functor.IsEquivalence := by
  dsimp; infer_instance

instance : (localizerMorphism C).IsLeftDerivabilityStructure := by
  rw [LocalizerMorphism.isLeftDerivabilityStructure_iff_of_equivalences
    (T := localizerMorphism C) (B := (CofibrantObject.localizerMorphism (Minus C)))
    (R := .id _) (L := cofibrantObjectLocalizerMorphism C) (Iso.refl _)]
  infer_instance

end CochainComplex.Minus

namespace HomotopyCategory.Minus

def localizerMorphism : LocalizerMorphism
  (MorphismProperty.isomorphisms (HomotopyCategory.Minus (ProjectiveObject C)))
    (HomotopyCategory.Minus.quasiIso C) where
  functor := (ProjectiveObject.ι C).mapHomotopyCategoryMinus
  map K L f (hf : IsIso f) := by
    dsimp only [MorphismProperty.inverseImage, HomotopyCategory.Minus.quasiIso]
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    infer_instance

variable {C} in
lemma isIso_quotient_map
    {K L : CochainComplex.Minus (ProjectiveObject C)} (f : K ⟶ L) :
    IsIso ((quotient _).map f) ↔
    CochainComplex.Minus.quasiIso C ((ProjectiveObject.ι C).mapCochainComplexMinus.map f) := by
  rw [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Minus.ι (ProjectiveObject C)),
    ← isIso_iff_of_reflects_iso _ (Functor.mapHomotopyCategory (ProjectiveObject.ι C) (.up ℤ))]
  dsimp
  rw [CochainComplex.IsKProjective.isIso_quotient_map_iff_quasiIso]
  rfl

namespace isLeftDerivabilityStructure

open MorphismProperty

@[simps]
def L : LocalizerMorphism
  ((CochainComplex.Minus.quasiIso C).inverseImage (ProjectiveObject.ι C).mapCochainComplexMinus)
      (isomorphisms (Minus (ProjectiveObject C))) where
  functor := HomotopyCategory.Minus.quotient (ProjectiveObject C)
  map _ _ f hf := (isIso_quotient_map f).2 hf

instance : (L C).IsInduced where
  inverseImage_eq := by ext; apply isIso_quotient_map

@[simps]
def R : LocalizerMorphism (CochainComplex.Minus.quasiIso C) (quasiIso C) where
  functor := HomotopyCategory.Minus.quotient C
  map := by
    intro X Y f hf
    simpa [quasiIso, quotient_map_mem_quasiIso_iff]

instance : (R C).IsInduced where
  inverseImage_eq := by ext; apply quotient_map_mem_quasiIso_iff

open HomologicalComplex in
lemma inverseImage_quasiIso_mapCochainComplexMinus_projectivesι :
    (CochainComplex.Minus.quasiIso C).inverseImage (ProjectiveObject.ι C).mapCochainComplexMinus =
    (homotopyEquivalences (ProjectiveObject C) (ComplexShape.up ℤ)).inverseImage
      (CochainComplex.Minus.ι (ProjectiveObject C)) := by
  ext K L f
  simp [CochainComplex.Minus.quasiIso, Functor.mapCochainComplexMinus,
    ← CochainComplex.IsKProjective.isIso_quotient_map_iff_quasiIso,
    ← isIso_quotient_map_iff_homotopyEquivalences,
    ← isIso_iff_of_reflects_iso _ ((ProjectiveObject.ι C).mapHomotopyCategory (.up ℤ))]

instance : (HomotopyCategory.Minus.quotient (ProjectiveObject C)).IsLocalization
      ((CochainComplex.Minus.quasiIso C).inverseImage
      (ProjectiveObject.ι C).mapCochainComplexMinus) := by
  rw [inverseImage_quasiIso_mapCochainComplexMinus_projectivesι]
  infer_instance

instance : (L C).IsLocalizedEquivalence := by
  have :
      ((L C).functor ⋙ 𝟭 (Minus (ProjectiveObject C))).IsLocalization
        ((CochainComplex.Minus.quasiIso C).inverseImage
          (ProjectiveObject.ι C).mapCochainComplexMinus) :=
    inferInstanceAs ((HomotopyCategory.Minus.quotient (ProjectiveObject C)).IsLocalization _)
  exact LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization (L C) (𝟭 _)

open HomologicalComplex in
instance {D : Type*} [Category* D] (L : Minus C ⥤ D) [L.IsLocalization (quasiIso C)] :
    (quotient C ⋙ L).IsLocalization (CochainComplex.Minus.quasiIso C) := by
  refine Functor.IsLocalization.comp _ _
    ((homotopyEquivalences C (.up ℤ)).inverseImage (CochainComplex.Minus.ι C))
    (quasiIso C) _ ?_ ?_ ?_
  · intro _ _ f hf
    refine Localization.inverts L (quasiIso C) _ ?_
    simpa [quasiIso, quotient_map_mem_quasiIso_iff]
  · intro K L f hf
    exact homotopyEquivalences_le_quasiIso _ _ _ hf
  · rintro K L f hf
    obtain ⟨K, rfl⟩ := Minus.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := Minus.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (Minus.quotient C).map_surjective f
    apply MorphismProperty.map_mem_map
    simpa [quasiIso, HomotopyCategory.quotient_map_mem_quasiIso_iff] using hf

instance {D : Type*} [Category* D] (L : Minus C ⥤ D) [L.IsLocalization (quasiIso C)] :
    ((R C).functor ⋙ L).IsLocalization (CochainComplex.Minus.quasiIso C) := by
  dsimp; infer_instance

instance : (R C).IsLocalizedEquivalence :=
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization
    (R C) ((quasiIso C).Q)

instance : (L C).functor.Full := by dsimp; infer_instance
instance : (R C).functor.Full := by dsimp; infer_instance
instance : (L C).functor.EssSurj := by dsimp; infer_instance
instance : (R C).functor.EssSurj := by dsimp; infer_instance

def iso : (CochainComplex.Minus.localizerMorphism C).functor ⋙
  (R C).functor ≅ (L C).functor ⋙ (localizerMorphism C).functor := Iso.refl _

open HomologicalComplex in
instance : TwoSquare.GuitartExact (iso C).inv :=
  TwoSquare.GuitartExact.quotient (iso C).symm (by
    rintro ⟨K₁, n₁, hn₁⟩ ⟨K₂, n₂, hn₂⟩ f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    dsimp [Functor.mapCochainComplexMinus] at f₀ f₁
    refine ⟨⟨K₁.cylinder, CochainComplex.minus_cylinder _ ⟨_, hn₁⟩⟩,
      ObjectProperty.homMk (cylinder.ι₀ _),
      ObjectProperty.homMk (cylinder.ι₁ _), ?_,
      ObjectProperty.homMk ?_, ?_, ?_⟩
    · ext : 1
      exact eq_of_homotopy _ _ (cylinder.homotopy₀₁ _ (fun n ↦ ⟨n - 1, by simp⟩))
    · exact (cylinder.mapHomologicalComplexObjIso K₁ (ProjectiveObject.ι C)
          (fun n ↦ ⟨n - 1, by simp⟩)).hom ≫
        cylinder.desc f₀ f₁ (homotopyOfEq _ _ ((HomotopyCategory.Minus.ι C).congr_map hf))
    · dsimp [Functor.mapCochainComplexMinus]
      cat_disch
    · dsimp [Functor.mapCochainComplexMinus]
      cat_disch)

end isLeftDerivabilityStructure

variable [EnoughProjectives C]

instance isLeftDerivabilityStructure : (localizerMorphism C).IsLeftDerivabilityStructure :=
  LocalizerMorphism.isLeftDerivabilityStructure_of_isLocalizedEquivalence
    (isLeftDerivabilityStructure.iso C)

end HomotopyCategory.Minus
