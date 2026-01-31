/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# C^-

-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category C]

protected def plus [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyGE n

instance [HasZeroMorphisms C] : (CochainComplex.plus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyGE_of_iso e n⟩

abbrev Plus [HasZeroMorphisms C] :=
  (CochainComplex.plus C).FullSubcategory

namespace Plus

section

variable [HasZeroMorphisms C]

abbrev ι : Plus C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance : (ι C).Full := ObjectProperty.full_ι _
instance : (ι C).Faithful := ObjectProperty.faithful_ι _

def quasiIso [CategoryWithHomology C] : MorphismProperty (Plus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)

end

variable [Preadditive C]

noncomputable instance : HasShift (Plus C) ℤ :=
  (fullyFaithfulι C).hasShift
    (fun (n : ℤ) => ObjectProperty.lift _
    (Plus.ι C ⋙ CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) (by
      rintro ⟨K, k, hk⟩
      exact ⟨k - n, K.isStrictlyGE_shift k n _ (by omega)⟩))
    (fun n => ObjectProperty.liftCompιIso _ _ _)

instance : (ι C).CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful _ _ _

end Plus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

def mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D :=
  ObjectProperty.lift _ (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Plus.ι]
    infer_instance)

def mapCochainComplexPlusCompι :
    F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D ≅
      CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

end Functor

end CategoryTheory
