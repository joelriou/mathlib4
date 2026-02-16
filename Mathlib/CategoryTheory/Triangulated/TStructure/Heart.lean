/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# The heart of a t-structures


## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*][bbd-1982]

-/

@[expose] public section

namespace CategoryTheory.Triangulated.TStructure

open Pretriangulated Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

/-- The heart of a t-structure, as the property of objects
that are both `≤ 0` and `≥ 0`. -/
def heart : ObjectProperty C := t.le 0 ⊓ t.ge 0
  deriving ObjectProperty.IsClosedUnderIsomorphisms

lemma mem_heart_iff (X : C) :
    t.heart X ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  simp [heart]

/-- Given `t : TStructure C`, a `t.HasHeart` instance consists of a choice
of a preadditive category which identifies to the fullsubcategory of `C`
consisting of the objects satisfying the property `t.heart`. This
category can be accessed as `t.Heart`. -/
@[nolint checkUnivs]
class HasHeart where
  /-- A preadditive category which is equivalent to the fullsubcategory defined by
  the property `t.heart`. -/
  H : Type*
  /-- The category structure on the heart. -/
  [category : Category H]
  /-- The heart is a preadditive category. -/
  [preadditive : Preadditive H]
  /-- The inclusion functor. -/
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  fullι : ι.Full := by infer_instance
  faithful_ι : ι.Faithful := by infer_instance
  essImage_eq_heart : ι.essImage = t.heart := by simp

/-- Unless a better candidate category is available, the full subcategory
of objects satisfying `t.heart` can be chosen as the heart of a t-structure `t`. -/
def hasHeartFullSubcategory : t.HasHeart where
  H := t.heart.FullSubcategory
  ι := t.heart.ι
  essImage_eq_heart := by
    ext X
    exact ⟨fun ⟨⟨Y, hY⟩, ⟨e⟩⟩ ↦ t.heart.prop_of_iso e hY,
      fun hX ↦ ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩⟩

variable [t.HasHeart]

/-- The heart of a t-structure, when an instance `t.HasHeart` is available. -/
def Heart := HasHeart.H (t := t)

instance : Category t.Heart := HasHeart.category

instance : Preadditive t.Heart := HasHeart.preadditive

/-- The inclusion functor `t.Heart ⥤ C` of the heart of
a t-structure `t : TStructure C`. -/
def ιHeart : t.Heart ⥤ C := HasHeart.ι

instance : t.ιHeart.Full := HasHeart.fullι
instance : t.ιHeart.Faithful := HasHeart.faithful_ι
instance : t.ιHeart.Additive := HasHeart.additive_ι

@[simp]
lemma essImage_ιHeart :
    t.ιHeart.essImage = t.heart :=
  HasHeart.essImage_eq_heart

lemma ιHeart_obj_mem (X : t.Heart) : t.heart (t.ιHeart.obj X) := by
  rw [← t.essImage_ιHeart]
  exact t.ιHeart.obj_mem_essImage X

instance (X : t.Heart) : t.IsLE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).1⟩

instance (X : t.Heart) : t.IsGE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).2⟩

end CategoryTheory.Triangulated.TStructure
