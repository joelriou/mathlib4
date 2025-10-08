/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Compatibilities for left adjoints from compatibilities satisfied by right adjoints

-/

namespace CategoryTheory

variable {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]

open Functor

namespace Adjunction

@[simps! -isSimp]
def leftAdjointIdIso {F : C₀ ⥤ C₀} {G : C₀ ⥤ C₀} (adj : F ⊣ G) (e : G ≅ 𝟭 C₀) :
    F ≅ 𝟭 C₀ := (conjugateIsoEquiv .id adj).symm e.symm

section

variable {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}

@[simps! -isSimp]
def leftAdjointCompIso
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)
    (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    F₀₁ ⋙ F₁₂ ≅ F₀₂ :=
  (conjugateIsoEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm e₀₁₂.symm

end

lemma leftAdjointCompIso_comp_id
    {F₀₁ : C₀ ⥤ C₁} {F₁₁' : C₁ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀} {G₁'₁ : C₁ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₁' : F₁₁' ⊣ G₁'₁)
    (e₀₁₁' : G₁'₁ ⋙ G₁₀ ≅ G₁₀) (e₁'₁ : G₁'₁ ≅ 𝟭 _)
    (h : e₀₁₁' = isoWhiskerRight e₁'₁ G₁₀ ≪≫ leftUnitor G₁₀) :
    leftAdjointCompIso adj₀₁ adj₁₁' adj₀₁ e₀₁₁' =
      isoWhiskerLeft _ (leftAdjointIdIso adj₁₁' e₁'₁) ≪≫ rightUnitor F₀₁ := by
  subst h
  ext X₀
  simp [leftAdjointCompIso_hom_app, leftAdjointIdIso_hom_app,
    ← Functor.map_comp_assoc, -Functor.map_comp]

lemma leftAdjointCompIso_id_comp
    {F₀₀' : C₀ ⥤ C₀} {F₀'₁ : C₀ ⥤ C₁} {G₀'₀ : C₀ ⥤ C₀} {G₁₀' : C₁ ⥤ C₀}
    (adj₀₀' : F₀₀' ⊣ G₀'₀) (adj₀'₁ : F₀'₁ ⊣ G₁₀')
    (e₀₀'₁ : G₁₀' ⋙ G₀'₀ ≅ G₁₀') (e₀'₀ : G₀'₀ ≅ 𝟭 _)
    (h : e₀₀'₁ = isoWhiskerLeft G₁₀' e₀'₀ ≪≫ rightUnitor G₁₀') :
    leftAdjointCompIso adj₀₀' adj₀'₁ adj₀'₁ e₀₀'₁ =
      isoWhiskerRight (leftAdjointIdIso adj₀₀' e₀'₀) F₀'₁ ≪≫ leftUnitor F₀'₁ := by
  subst h
  ext X₀
  have h₁ := congr_map F₀'₁ (adj₀₀'.counit.naturality (adj₀'₁.unit.app X₀))
  have h₂ := congr_map (F₀₀' ⋙ F₀'₁) (e₀'₀.inv.naturality (adj₀'₁.unit.app X₀))
  simp only [id_obj, comp_obj, Functor.id_map, Functor.comp_map, Functor.map_comp] at h₁ h₂
  simp [leftAdjointCompIso_hom_app, leftAdjointIdIso_hom_app,
    reassoc_of% h₂, reassoc_of% h₁]

section

variable
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₃₂ : C₃ ⥤ C₂} {G₂₀ : C₂ ⥤ C₀} {G₃₁ : C₃ ⥤ C₁} {G₃₀ : C₃ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₂₃ : F₂₃ ⊣ G₃₂) (adj₀₂ : F₀₂ ⊣ G₂₀)
  (adj₁₃ : F₁₃ ⊣ G₃₁) (adj₀₃ : F₀₃ ⊣ G₃₀)
  (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁)
  (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) (e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀)

lemma leftAdjointCompIso₀₁₃_eq_conjugateIsoEquiv_symm :
    isoWhiskerLeft _ (leftAdjointCompIso adj₁₂ adj₂₃ adj₁₃ e₁₂₃) ≪≫
      leftAdjointCompIso adj₀₁ adj₁₃ adj₀₃ e₀₁₃ =
    (conjugateIsoEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).symm
      (e₀₁₃.symm ≪≫ isoWhiskerRight e₁₂₃.symm G₁₀) := by
  ext X₀
  sorry

lemma leftAdjointCompIso₀₂₃_eq_conjugateIsoEquiv_symm :
    (associator _ _ _).symm ≪≫
        isoWhiskerRight (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂) F₂₃ ≪≫
          leftAdjointCompIso adj₀₂ adj₂₃ adj₀₃ e₀₂₃ =
    (conjugateIsoEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).symm
      (e₀₂₃.symm ≪≫ isoWhiskerLeft G₃₂ e₀₁₂.symm ≪≫ (associator _ _ _).symm) := by
  sorry

lemma leftAdjointCompIso_assoc
    (h : isoWhiskerLeft G₃₂ e₀₁₂ ≪≫ e₀₂₃ =
      (associator _ _ _).symm ≪≫ isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃) :
    isoWhiskerLeft _ (leftAdjointCompIso adj₁₂ adj₂₃ adj₁₃ e₁₂₃) ≪≫
        leftAdjointCompIso adj₀₁ adj₁₃ adj₀₃ e₀₁₃ =
      (associator _ _ _).symm ≪≫
        isoWhiskerRight (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂) F₂₃ ≪≫
          leftAdjointCompIso adj₀₂ adj₂₃ adj₀₃ e₀₂₃ := by
  rw [leftAdjointCompIso₀₁₃_eq_conjugateIsoEquiv_symm,
    leftAdjointCompIso₀₂₃_eq_conjugateIsoEquiv_symm]
  congr 1
  ext X₃
  simpa using congr_app (congr_arg Iso.inv h.symm) X₃

end

end Adjunction

end CategoryTheory
