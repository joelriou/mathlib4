/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.ModelCategory.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Existence
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Homology
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureCofibrant

/-!
# The projective derivability structure

-/

@[expose] public section

universe w₁ w₂

open HomotopicalAlgebra CategoryTheory Limits ZeroObject Category

variable (C : Type*) [Category C] [Abelian C]
  [HasDerivedCategory.{w₁} C]
  {H : Type*} [Category H]

namespace HomologicalComplex

@[simps X d]
def liftObjectProperty {ι : Type*} {c : ComplexShape ι}
    {V : Type*} [Category* V] [Preadditive V] (P : ObjectProperty V)
    (K : HomologicalComplex V c) (hK : ∀ (n : ι), P (K.X n)) :
    HomologicalComplex P.FullSubcategory c where
  X n := ⟨_, hK n⟩
  d i j := ObjectProperty.homMk (K.d i j)

@[simps]
def liftFunctorObjectProperty {D : Type*} [Category* D] {ι : Type*} {c : ComplexShape ι}
    {V : Type*} [Category* V] [Preadditive V] (P : ObjectProperty V)
    (F : D ⥤ HomologicalComplex V c) (hF : ∀ (X : D) (n : ι), P ((F.obj X).X n)) :
    D ⥤ HomologicalComplex P.FullSubcategory c where
  obj X := liftObjectProperty _ (F.obj X) (hF X)
  map f := { f n := ObjectProperty.homMk ((F.map f).f n) }

end HomologicalComplex

namespace CategoryTheory

abbrev Projectives := ObjectProperty.FullSubcategory (fun (X : C) => Projective X)

namespace Projectives

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

instance : HasFiniteCoproducts (Projectives C) where
  out n := by infer_instance

instance : HasFiniteBiproducts (Projectives C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

instance : HasBinaryBiproducts (Projectives C) := hasBinaryBiproducts_of_finite_biproducts _

instance : HasZeroObject (Projectives C) where
  zero := by
    refine ⟨⟨0, inferInstance⟩, ?_⟩
    rw [IsZero.iff_id_eq_zero]
    ext : 1
    apply id_zero

abbrev ι : Projectives C ⥤ C := ObjectProperty.ι _

instance (X : Projectives C) : Projective ((ι C).obj X) := X.2

instance (X : HomotopyCategory.Plus (Projectives C)) (n : ℤ) :
    Projective (((ι C).mapHomotopyCategoryPlus.obj X).obj.as.X n) := by
  change Projective ((ι C).obj (X.obj.as.X n))
  infer_instance

variable {C}

def liftHomotopyCategoryPlusOfProjective (K : HomotopyCategory.Plus C)
  [∀ (n : ℤ), Projective (K.obj.as.X n)] : HomotopyCategory.Plus (Projectives C) :=
    { obj :=
       ⟨{ X n := ⟨K.obj.as.X n, inferInstance⟩
          d i j := ObjectProperty.homMk (K.obj.as.d i j)
          shape i j hij := by ext : 1; exact K.obj.as.shape i j hij
          d_comp_d' i j k _ _ := by ext : 1; exact K.obj.as.d_comp_d i j k }⟩
      property := by
        obtain ⟨n, hn⟩ := K.2
        refine ⟨n, ?_⟩
        rw [CochainComplex.isStrictlyGE_iff]
        intro i hi
        have := CochainComplex.isZero_of_isStrictlyGE K.obj.as n i hi
        rw [IsZero.iff_id_eq_zero] at this ⊢
        ext : 1
        exact this }

def isoMapHomotopyCategoryPlusιObj (K : HomotopyCategory.Plus C)
    [∀ (n : ℤ), Projective (K.obj.as.X n)] :
    (ι C).mapHomotopyCategoryPlus.obj (liftHomotopyCategoryPlusOfProjective K) ≅ K := Iso.refl _

omit [HasDerivedCategory C] in
lemma mem_essImage_mapHomotopyCategoryPlus_ι_of_projective (K : HomotopyCategory.Plus C)
    [∀ (n : ℤ), Projective (K.obj.as.X n)] :
    (ι C).mapHomotopyCategoryPlus.essImage K :=
  ⟨_, ⟨isoMapHomotopyCategoryPlusιObj K⟩⟩

end Projectives

end CategoryTheory

namespace CochainComplex.Minus

def localizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (Projectives.ι C).mapCochainComplexMinus)
      (quasiIso C) where
  functor := (Projectives.ι C).mapCochainComplexMinus
  map := by rfl

instance : (localizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance (K : Minus (Projectives C)) (n : ℤ) :
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
    Minus (Projectives C) ≌ CofibrantObject (Minus C) where
  functor := ObjectProperty.lift _ (Projectives.ι C).mapCochainComplexMinus (fun K ↦ by
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
    LocalizerMorphism ((quasiIso C).inverseImage (Projectives.ι C).mapCochainComplexMinus)
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
