/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Order.WithBotTop

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a triangulated category `C`.
In this file, we extend the definition of the truncation functors
`truncLT` and `truncGE` for indices in `ℤ` to `EInt`,
as `t.eTruncLT : EInt ⥤ C ⥤ C` and `t.eTruncGE : EInt ⥤ C ⥤ C`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

/-- The functor `EInt ⥤ C ⥤ C` which sends `⊥` to the zero functor,
`n : ℤ` to `t.truncLT n` and `⊤` to `𝟭 C`. -/
noncomputable def eTruncLT : EInt ⥤ C ⥤ C where
  obj n := by
    induction n using WithBotTop.rec with
    | bot => exact 0
    | coe a => exact t.truncLT a
    | top => exact 𝟭 C
  map {x y} f := by
    induction x using WithBotTop.rec with
    | bot =>
      induction y using WithBotTop.rec with
      | bot => exact 𝟙 _
      | coe b => exact 0
      | top => exact 0
    | coe a =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact t.natTransTruncLTOfLE a b (by simpa using leOfHom f)
      | top => exact t.truncLTι a
    | top =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n using WithBotTop.rec <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x using WithBotTop.rec <;> induction y using WithBotTop.rec <;>
      induction z using WithBotTop.rec <;> cat_disch

@[simp]
lemma eTruncLT_obj_top : t.eTruncLT.obj ⊤ = 𝟭 _ := rfl

@[simp]
lemma eTruncLT_obj_bot : t.eTruncLT.obj ⊥ = 0 := rfl

@[simp]
lemma eTruncLT_obj_coe (n : ℤ) : t.eTruncLT.obj n = t.truncLT n := rfl

@[simp]
lemma eTruncLT_map_eq_truncLTι (n : ℤ) :
    t.eTruncLT.map (homOfLE (show (n : EInt) ≤ ⊤ by simp)) = t.truncLTι n := rfl

instance (i : EInt) : (t.eTruncLT.obj i).Additive := by
  induction i using WithBotTop.rec <;> constructor <;> cat_disch

/-- The functor `EInt ⥤ C ⥤ C` which sends `⊥` to `𝟭 C`,
`n : ℤ` to `t.truncGE n` and `⊤` to the zero functor. -/
noncomputable def eTruncGE : EInt ⥤ C ⥤ C where
  obj n := by
    induction n using WithBotTop.rec with
    | bot => exact 𝟭 C
    | coe a => exact t.truncGE a
    | top => exact 0
  map {x y} f := by
    induction x using WithBotTop.rec with
    | bot =>
      induction y using WithBotTop.rec with
      | bot => exact 𝟙 _
      | coe b => exact t.truncGEπ b
      | top => exact 0
    | coe a =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact t.natTransTruncGEOfLE a b (by simpa using leOfHom f)
      | top => exact 0
    | top =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n using WithBotTop.rec <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x using WithBotTop.rec <;> induction y using WithBotTop.rec <;>
      induction z using WithBotTop.rec <;> cat_disch

@[simp]
lemma eTruncGE_obj_bot :
    t.eTruncGE.obj ⊥ = 𝟭 _ := rfl

@[simp]
lemma eTruncGE_obj_top :
    t.eTruncGE.obj ⊤ = 0 := rfl

@[simp]
lemma eTruncGE_obj_coe (n : ℤ) : t.eTruncGE.obj n = t.truncGE n := rfl

instance (i : EInt) : (t.eTruncGE.obj i).Additive := by
  induction i using WithBotTop.rec <;> constructor <;> cat_disch

/-- The connecting homomorphism from `t.eTruncGE` to the
shift by `1` of `t.eTruncLT`. -/
noncomputable def eTruncGEδLT :
    t.eTruncGE ⟶ t.eTruncLT ⋙ ((Functor.whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) where
  app a := by
    induction a using WithBotTop.rec with
    | bot => exact 0
    | coe a => exact t.truncGEδLT a
    | top => exact 0
  naturality {a b} hab := by
    replace hab := leOfHom hab
    induction a using WithBotTop.rec; rotate_right
    · apply (isZero_zero _).eq_of_src
    all_goals
      induction b using WithBotTop.rec <;> simp at hab <;>
        dsimp [eTruncGE, eTruncLT] <;>
        simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]
lemma eTruncGEδLT_coe (n : ℤ) :
    t.eTruncGEδLT.app n = t.truncGEδLT n := rfl

/-- The natural transformation `t.eTruncLT.obj i ⟶ 𝟭 C` for all `i : EInt`. -/
noncomputable abbrev eTruncLTι (i : EInt) : t.eTruncLT.obj i ⟶ 𝟭 _ :=
  t.eTruncLT.map (homOfLE (le_top))

@[simp] lemma eTruncLT_ι_bot : t.eTruncLTι ⊥ = 0 := rfl
@[simp] lemma eTruncLT_ι_coe (n : ℤ) : t.eTruncLTι n = t.truncLTι n := rfl
@[simp] lemma eTruncLT_ι_top : t.eTruncLTι ⊤ = 𝟙 _ := rfl

@[reassoc]
lemma eTruncLTι_naturality (i : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncLT.obj i).map f ≫ (t.eTruncLTι i).app Y = (t.eTruncLTι i).app X ≫ f :=
  (t.eTruncLTι i).naturality f

instance : IsIso (t.eTruncLTι ⊤) := by
  dsimp [eTruncLTι]
  infer_instance

@[reassoc (attr := simp)]
lemma eTruncLT_map_app_eTruncLTι_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncLT.map f).app X ≫ (t.eTruncLTι j).app X = (t.eTruncLTι i).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

@[reassoc]
lemma eTruncLT_obj_map_eTruncLTι_app (i : EInt) (X : C) :
    (t.eTruncLT.obj i).map ((t.eTruncLTι i).app X) =
    (t.eTruncLTι i).app ((t.eTruncLT.obj i).obj X) := by
  induction i using WithBotTop.rec with
  | bot => simp
  | coe n => simp [truncLT_map_truncLTι_app]
  | top => simp

/-- The natural transformation `𝟭 C ⟶ t.eTruncGE.obj i` for all `i : EInt`. -/
noncomputable abbrev eTruncGEπ (i : EInt) : 𝟭 C ⟶ t.eTruncGE.obj i :=
  t.eTruncGE.map (homOfLE (bot_le))

@[simp] lemma eTruncGEπ_bot : t.eTruncGEπ ⊥ = 𝟙 _ := rfl
@[simp] lemma eTruncGEπ_coe (n : ℤ) : t.eTruncGEπ n = t.truncGEπ n := rfl
@[simp] lemma eTruncGEπ_top : t.eTruncGEπ ⊤ = 0 := rfl

@[reassoc (attr := simp)]
lemma eTruncGEπ_naturality (i : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.obj i).map f = f ≫ (t.eTruncGEπ i).app Y :=
  ((t.eTruncGEπ i).naturality f).symm

instance : IsIso (t.eTruncGEπ ⊥) := by
  dsimp [eTruncGEπ]
  infer_instance

@[reassoc (attr := simp)]
lemma eTruncGEπ_app_eTruncGE_map_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.map f).app X = (t.eTruncGEπ j).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

@[reassoc]
lemma eTruncGE_obj_map_eTruncGEπ_app (i : EInt) (X : C) :
    (t.eTruncGE.obj i).map ((t.eTruncGEπ i).app X) =
    (t.eTruncGEπ i).app ((t.eTruncGE.obj i).obj X) := by
  induction i using WithBotTop.rec with
  | bot => simp
  | coe n => simp [truncGE_map_truncGEπ_app]
  | top => simp

/-- The (distinguished) triangles given by the natural transformations
`t.eTruncLT.obj i ⟶ 𝟭 C ⟶ t.eTruncGE.obj i ⟶ ...` for all `i : EInt`. -/
@[simps!]
noncomputable def eTriangleLTGE : EInt ⥤ C ⥤ Triangle C where
  obj i := Triangle.functorMk (t.eTruncLTι i) (t.eTruncGEπ i) (t.eTruncGEδLT.app i)
  map f := Triangle.functorHomMk _ _ (t.eTruncLT.map f) (𝟙 _) (t.eTruncGE.map f)

lemma eTriangleLTGE_distinguished (i : EInt) (X : C) :
    (t.eTriangleLTGE.obj i).obj X ∈ distTriang _ := by
  induction i using WithBotTop.rec with
  | bot =>
    rw [Triangle.distinguished_iff_of_isZero₁ _ (Functor.zero_obj X)]
    dsimp
    infer_instance
  | coe n => exact t.triangleLTGE_distinguished n X
  | top =>
    rw [Triangle.distinguished_iff_of_isZero₃ _ (Functor.zero_obj X)]
    dsimp
    infer_instance

instance (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncLT.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact isLE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isGE_of_isZero _ (by simp) _

lemma isGE_eTruncGE_obj_obj (n : ℤ) (i : EInt) (h : n ≤ i) (X : C) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => simp at h
  | coe i =>
    dsimp
    exact t.isGE_of_ge  _ _ _ (by simpa using h)
  | top => exact t.isGE_of_isZero (Functor.zero_obj _) _

lemma isLE_eTruncLT_obj_obj (n : ℤ) (i : EInt) (h : i ≤ (n + 1 :)) (X : C) :
    t.IsLE (((t.eTruncLT.obj i)).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact t.isLE_of_isZero (by simp) _
  | coe i =>
    simp only [WithBotTop.coe_le_coe] at h
    dsimp
    exact t.isLE_of_le _ (i - 1) n (by lia)
  | top => simp at h

lemma isZero_eTruncLT_obj_obj (X : C) (n : ℤ) [t.IsGE X n] (j : EInt) (hj : j ≤ n) :
    IsZero ((t.eTruncLT.obj j).obj X) := by
  induction j using WithBotTop.rec with
  | bot => simp
  | coe j =>
    have := t.isGE_of_ge X j n (by simpa using hj)
    exact t.isZero_truncLT_obj_of_isGE _ _
  | top => simp at hj

lemma isZero_eTruncGE_obj_obj (X : C) (n : ℤ) [t.IsLE X n] (j : EInt) (hj : n < j) :
    IsZero ((t.eTruncGE.obj j).obj X) := by
  induction j using WithBotTop.rec with
  | bot => simp at hj
  | coe j =>
    simp only [WithBotTop.coe_lt_coe] at hj
    have := t.isLE_of_le X n (j - 1) (by lia)
    exact t.isZero_truncGE_obj_of_isLE (j - 1) j (by lia) _
  | top => simp

end TStructure

end Triangulated

end CategoryTheory
