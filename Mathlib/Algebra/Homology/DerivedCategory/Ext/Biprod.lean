/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Ext and binary biproducts

In this file, we decompose the abelian group
`Ext (X₁ ⊞ X₂) Y n` as the product of `Ext X₁ Y n` and `Ext X₂ Y n`.

-/

universe w v u

namespace CategoryTheory

open Limits

-- to be generalized to concrete categories, and moved
section
variable {G H : AddCommGrpCat.{u}} (e : G ≅ H)

def Iso.toEquivOfConcrete : G ≃ H where
  toFun := e.hom
  invFun := e.inv
  left_inv _ := by simp
  right_inv _ := by simp

lemma Iso.hom_bijective : Function.Bijective e.hom :=
    e.toEquivOfConcrete.bijective

lemma Iso.inv_bijective : Function.Bijective e.inv :=
    e.symm.hom_bijective

lemma Iso.hom_injective :
    Function.Injective e.hom := e.hom_bijective.1

lemma Iso.inv_injective :
    Function.Injective e.inv := e.inv_bijective.1

lemma Iso.hom_surjective :
    Function.Surjective e.hom := e.hom_bijective.2

lemma Iso.inv_surjective :
    Function.Surjective e.inv := e.inv_bijective.2

end

lemma AddCommGrpCat.fst_biprodIsoProd_inv_apply
    {G H : AddCommGrpCat.{u}} (g : G × H) :
    (biprod.fst : G ⊞ H ⟶ G) ((AddCommGrpCat.biprodIsoProd G H).inv g) = g.1 :=
  AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply _ _ _

lemma AddCommGrpCat.snd_biprodIsoProd_inv_apply
    {G H : AddCommGrpCat.{u}} (g : G × H) :
    (biprod.snd : G ⊞ H ⟶ H) ((AddCommGrpCat.biprodIsoProd G H).inv g) = g.2 :=
  AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply _ _ _

@[simp]
lemma AddCommGrpCat.biprodIsoProd_hom_apply_fst
    {G H : AddCommGrpCat.{u}} (g : (G ⊞ H :)) :
    ((AddCommGrpCat.biprodIsoProd G H).hom g).1 = (biprod.fst : G ⊞ H ⟶ _) g :=
  rfl

@[simp]
lemma AddCommGrpCat.biprodIsoProd_hom_apply_snd
    {G H : AddCommGrpCat.{u}} (g : (G ⊞ H :)) :
    ((AddCommGrpCat.biprodIsoProd G H).hom g).2 = (biprod.snd : G ⊞ H ⟶ _) g :=
  rfl

@[simp]
lemma AddCommGrpCat.fst_inl_apply {G H : AddCommGrpCat.{u}} (g : G) :
    (biprod.fst : G ⊞ H ⟶ _) ((biprod.inl : _ ⟶ G ⊞ H) g) = g := by
  simp [← ConcreteCategory.comp_apply]

@[simp]
lemma AddCommGrpCat.snd_inl_apply {G H : AddCommGrpCat.{u}} (g : G) :
    (biprod.snd : G ⊞ H ⟶ _) ((biprod.inl : _ ⟶ G ⊞ H) g) = 0 := by
  simp [← ConcreteCategory.comp_apply]

@[simp]
lemma AddCommGrpCat.fst_inr_apply {G H : AddCommGrpCat.{u}} (h : H) :
    (biprod.fst : G ⊞ H ⟶ _) ((biprod.inr : _ ⟶ G ⊞ H) h) = 0 := by
  simp [← ConcreteCategory.comp_apply]

@[simp]
lemma AddCommGrpCat.snd_inr_apply {G H : AddCommGrpCat.{u}} (h : H) :
    (biprod.snd : G ⊞ H ⟶ _) ((biprod.inr : _ ⟶ G ⊞ H) h) = h := by
  simp [← ConcreteCategory.comp_apply]

lemma AddCommGrpCat.biprodIsoProd_inv_comp_apply
    {G H K : AddCommGrpCat.{u}} (f : G ⊞ H ⟶ K) (g : G) (h : H) :
    ((AddCommGrpCat.biprodIsoProd G H).inv ≫ f) ⟨g, h⟩ =
    (biprod.inl ≫ f) g + (biprod.inr ≫ f) h := by
  dsimp
  rw [← map_add]
  congr 1
  apply (AddCommGrpCat.biprodIsoProd G H).hom_injective
  simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    AddCommGrpCat.hom_id, AddMonoidHom.id_apply, map_add]
  ext
  · dsimp
    rw [AddCommGrpCat.biprodIsoProd_hom_apply_fst,
      AddCommGrpCat.biprodIsoProd_hom_apply_fst]
    simp
  · dsimp
    rw [AddCommGrpCat.biprodIsoProd_hom_apply_snd,
      AddCommGrpCat.biprodIsoProd_hom_apply_snd]
    simp


variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Abelian

namespace Ext

variable {X₁ X₂ Y : C} {n : ℕ}

/-- The additive equivalence `Ext.{w} (X₁ ⊞ X₂) Y n ≃+ Ext.{w} X₁ Y n × Ext.{w} X₂ Y n`. -/
@[simps -isSimp apply apply_fst apply_snd symm_apply]
noncomputable def fromBiprodEquiv : Ext.{w} (X₁ ⊞ X₂) Y n ≃+ Ext.{w} X₁ Y n × Ext.{w} X₂ Y n where
  toFun e := ⟨(mk₀ biprod.inl).comp e (zero_add n), (mk₀ biprod.inr).comp e (zero_add n)⟩
  invFun e := (mk₀ biprod.fst).comp e.1 (zero_add n) + (mk₀ biprod.snd).comp e.2 (zero_add n)
  left_inv e := by simp [← add_comp, ← mk₀_add]
  right_inv e := by aesop
  map_add' e₁ e₂ := by aesop

variable (X₁ X₂ Y n)

/-- The isomorphism in the category `AddCommGrpCat` between
`AddCommGrpCat.of (Ext.{w} (X₁ ⊞ X₂) Y n)`
and `AddCommGrpCat.of (Ext.{w} X₁ Y n) ⊞ AddCommGrpCat.of (Ext.{w} X₂ Y n)`. -/
noncomputable def fromBiprodIso : AddCommGrpCat.of (Ext.{w} (X₁ ⊞ X₂) Y n) ≅
    AddCommGrpCat.of (Ext.{w} X₁ Y n) ⊞ AddCommGrpCat.of (Ext.{w} X₂ Y n) :=
  (AddEquiv.toAddCommGrpIso fromBiprodEquiv).trans (AddCommGrpCat.biprodIsoProd _ _).symm

variable {X₁ X₂ Y n}

lemma fromBiprodIso_inv_apply (e₁ : Ext.{w} X₁ Y n) (e₂ : Ext.{w} X₂ Y n) :
  (fromBiprodIso X₁ X₂ Y n).inv
    ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨e₁, e₂⟩) =
      fromBiprodEquiv.symm ⟨e₁, e₂⟩ :=
  fromBiprodEquiv.injective (by simp [fromBiprodIso, ← ConcreteCategory.comp_apply])

lemma biprod_inl_comp_fromBiprodIso_inv_apply
    (x : ((AddCommGrpCat.of (Ext X₁ Y n) ⊞ AddCommGrpCat.of (Ext X₂ Y n)) :)) :
    (mk₀ biprod.inl).comp ((fromBiprodIso X₁ X₂ Y n).inv x) (zero_add n) =
      (biprod.fst : AddCommGrpCat.of (Ext X₁ Y n) ⊞ AddCommGrpCat.of (Ext X₂ Y n) ⟶ _) x := by
  obtain ⟨⟨x₁, x₂⟩, rfl⟩ := (AddCommGrpCat.biprodIsoProd _ _).inv_surjective x
  rw [fromBiprodIso_inv_apply, fromBiprodEquiv_symm_apply,
    ← ConcreteCategory.comp_apply, AddCommGrpCat.biprodIsoProd_inv_comp_fst]
  simp

lemma biprod_inr_comp_fromBiprodIso_inv_apply
    (x : ((AddCommGrpCat.of (Ext X₁ Y n) ⊞ AddCommGrpCat.of (Ext X₂ Y n)) :)) :
    (mk₀ biprod.inr).comp ((fromBiprodIso X₁ X₂ Y n).inv x) (zero_add n) =
      (biprod.snd : AddCommGrpCat.of (Ext X₁ Y n) ⊞ AddCommGrpCat.of (Ext X₂ Y n) ⟶ _) x := by
  obtain ⟨⟨x₁, x₂⟩, rfl⟩ := (AddCommGrpCat.biprodIsoProd _ _).inv_surjective x
  rw [fromBiprodIso_inv_apply, fromBiprodEquiv_symm_apply,
    ← ConcreteCategory.comp_apply, AddCommGrpCat.biprodIsoProd_inv_comp_snd]
  simp

end Ext

end Abelian

end CategoryTheory
