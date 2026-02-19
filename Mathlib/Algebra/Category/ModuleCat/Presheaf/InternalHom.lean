/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# The internal hom for presheaves of modules


-/

@[expose] public section

open CategoryTheory Category Opposite

universe v u v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModules

instance (U : Cᵒᵖ) (F G : (PresheafOfModules ((Over.forget U.unop).op ⋙ R ⋙ forget₂ _ _))) :
    SMul (R.obj U) (F ⟶ G) where
  smul a φ :=
    { app V := ModuleCat.ofHom
        { toFun s :=
            (show ((Over.forget (unop U)).op ⋙ R ⋙
                forget₂ CommRingCat RingCat).obj V from R.map V.unop.hom.op a) • φ.app _ s
          map_smul' b s := by dsimp at b; simp [smul_smul, mul_comm b]
          map_add' := by simp }
      naturality f := by
        ext x
        have := ConcreteCategory.congr_hom (φ.naturality f) x
        rw [ConcreteCategory.comp_apply] at this
        dsimp at this ⊢
        simp only [this, map_smul, ModuleCat.restrictScalars.smul_def,
          ← ConcreteCategory.comp_apply, ← R.map_comp, ← op_comp, Over.w] }

lemma over_smul_app_apply
    {U : Cᵒᵖ} {F G : (PresheafOfModules ((Over.forget U.unop).op ⋙ R ⋙ forget₂ _ _))}
    (a : R.obj U) (φ : F ⟶ G) {V : (Over U.unop)ᵒᵖ} (s : F.obj V) :
    (a • φ).app V s =
      letI b : ((Over.forget (unop U)).op ⋙ R ⋙ forget₂ CommRingCat RingCat).obj V :=
        R.map V.unop.hom.op a
      b • φ.app _ s :=
  rfl

instance (U : Cᵒᵖ) :
    Linear (R.obj U)
      (PresheafOfModules ((Over.forget U.unop).op ⋙ R ⋙ forget₂ _ _)) where
  homModule F G :=
    { zero_smul _ := by
        ext
        dsimp
        exact (over_smul_app_apply ..).trans (by rw [map_zero, zero_smul])
      one_smul _ := by
        ext
        dsimp
        exact (over_smul_app_apply ..).trans (by rw [map_one, one_smul]; rfl)
      mul_smul _ _ _ := by
        ext
        dsimp
        erw [over_smul_app_apply, over_smul_app_apply, over_smul_app_apply]
        rw [map_mul]
        apply mul_smul
      add_smul _ _ _ := by
        ext
        dsimp
        erw [over_smul_app_apply, over_smul_app_apply, over_smul_app_apply]
        rw [map_add]
        apply add_smul
      smul_zero _ := by
        ext
        erw [over_smul_app_apply]
        apply smul_zero
      smul_add _ _ _ := by
        ext
        apply smul_add }
  smul_comp _ _ _ _ _ _ := by
    ext
    dsimp
    rw [comp_app]
    dsimp
    erw [over_smul_app_apply, over_smul_app_apply]
    rw [map_smul]
    rfl
  comp_smul _ _ _ _ _ _ := by
    ext
    dsimp
    rw [comp_app]
    apply over_smul_app_apply

variable (F G : PresheafOfModules.{max u u₁ v₁} (R ⋙ forget₂ _ _))

abbrev InternalHomObj (U : C) : Type _ := F.over U ⟶ G.over U

@[simps]
noncomputable def internalHomMap {U V : C} (f : V ⟶ U) (φ : InternalHomObj F G U) :
    InternalHomObj F G V where
  app W := φ.app ((Over.map f).op.obj W)
  naturality g := φ.naturality ((Over.map f).op.map g)

noncomputable def internalHom : PresheafOfModules.{max u u₁ v₁} (R ⋙ forget₂ _ _) where
  obj U := ModuleCat.of (R.obj U) (InternalHomObj F G U.unop)
  map {U V} f := ConcreteCategory.ofHom (C := ModuleCat (R.obj U))
    { toFun := internalHomMap _ _ f.unop
      map_add' _ _ := rfl
      map_smul' _ _ := PresheafOfModules.hom_ext (fun _ ↦ by
        ext
        dsimp [internalHomMap]
        erw [over_smul_app_apply, over_smul_app_apply]
        dsimp
        rw [Functor.map_comp]
        rfl ) }
  map_id _ := by
    ext
    dsimp [internalHomMap]
    refine PresheafOfModules.hom_ext (fun _ ↦ ?_)
    dsimp
    ext
    dsimp
    rw [ModuleCat.restrictScalarsId'App_inv_apply]
    congr
    simp [Over.mapId_eq]
  map_comp {X₁ X₂ X₃} f g := by
    ext
    dsimp [internalHomMap]
    refine PresheafOfModules.hom_ext (fun _ ↦ ?_)
    dsimp
    congr 2
    simp [Over.mapComp_eq]

end PresheafOfModules
