/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# HoFunctor preserves binary products
-/

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialObject.Truncated
  CartesianMonoidalCategory

namespace CategoryTheory

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

@[simps]
def prod.desc (obj : C₁ × C₂ → D)
    (map₁ : ∀ ⦃x₁ y₁ : C₁⦄ (_f₁ : x₁ ⟶ y₁) (x₂ : C₂), obj (x₁, x₂) ⟶ obj (y₁, x₂))
    (map₂ : ∀ (x₁ : C₁) ⦃x₂ y₂ : C₂⦄ (_f₂ : x₂ ⟶ y₂), obj (x₁, x₂) ⟶ obj (x₁, y₂))
    (map₁_id : ∀ (x₁ : C₁) (x₂ : C₂), map₁ (𝟙 x₁) x₂ = 𝟙 _)
    (map₂_id : ∀ (x₁ : C₁) (x₂ : C₂), map₂ x₁ (𝟙 x₂) = 𝟙 _)
    (map₁_comp : ∀ ⦃x₁ y₁ z₁ : C₁⦄ (f₁ : x₁ ⟶ y₁) (g₁ : y₁ ⟶ z₁) (x₂ : C₂),
      map₁ (f₁ ≫ g₁) x₂ = map₁ f₁ x₂ ≫ map₁ g₁ x₂)
    (map₂_comp : ∀ (x₁ : C₁) ⦃x₂ y₂ z₂ : C₂⦄ (f₂ : x₂ ⟶ y₂) (g₂ : y₂ ⟶ z₂),
      map₂ x₁ (f₂ ≫ g₂) = map₂ x₁ f₂ ≫ map₂ x₁ g₂)
    (comm : ∀ ⦃x₁ y₁ : C₁⦄ (f₁ : x₁ ⟶ y₁) ⦃x₂ y₂ : C₂⦄ (f₂ : x₂ ⟶ y₂),
      map₁ f₁ x₂ ≫ map₂ y₁ f₂ = map₂ x₁ f₂ ≫ map₁ f₁ y₂) :
    C₁ × C₂ ⥤ D where
  obj := obj
  map {x y} f := map₁ f.1 x.2 ≫ map₂ y.1 f.2
  map_id := by aesop
  map_comp {x y z} f g := by
    dsimp
    rw [Category.assoc, reassoc_of% map₁_comp, map₂_comp, reassoc_of% comm]

end CategoryTheory

namespace SSet

namespace Truncated

instance (n : ℕ) : CartesianMonoidalCategory (Truncated.{u} n) :=
  inferInstanceAs (CartesianMonoidalCategory (_ ⥤ Type u))

variable (X Y : Truncated.{u} 2)

variable {X Y} in
def const (y : Y _⦋0⦌₂) : X ⟶ Y where
  app := by
    rintro ⟨n, _⟩ _
    induction n using SimplexCategory.rec with | _ n
    induction n with
    | zero => exact y
    | succ => exact Y.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.const _ _ 0)).op y
  naturality := sorry

namespace HomotopyCategory

def hom_induction {motive : ∀ {x x' : X.HomotopyCategory} (f : x ⟶ x'), Prop}
    (id : ∀ x, motive (𝟙 x))
    (comp : ∀ {x x' x''} (f : x ⟶ x') (g : x' ⟶ x''), motive f → motive g → motive (f ≫ g))
    (toPath : ∀ {x x' : OneTruncation₂ X} (e : x ⟶ x'),
      motive ((Cat.FreeRefl.quotientFunctor _ ⋙ quotientFunctor X).map e.toPath))
    {x x' : X.HomotopyCategory} (f : x ⟶ x') : motive f := by
  obtain ⟨⟨x⟩⟩ := x
  obtain ⟨⟨x'⟩⟩ := x'
  obtain ⟨⟨f⟩⟩ := f
  expose_names; clear a f_1 -- needs cleanup...
  dsimp at f
  induction f with
  | nil => apply id
  | cons p g hp => exact comp _ _ hp (toPath g)

variable {X} in
@[simps]
def objEquiv : X.HomotopyCategory ≃ X _⦋0⦌₂ where
  toFun x := x.1.1
  invFun x := ⟨⟨x⟩⟩

namespace BinaryProduct

variable {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂}

def functor : (X ⊗ Y).HomotopyCategory ⥤ (X.HomotopyCategory × Y.HomotopyCategory) :=
  Functor.prod' (mapHomotopyCategory (fst _ _)) (mapHomotopyCategory (snd _ _))

namespace inverse

variable {Y} in
def ι₁ (y : Y _⦋0⦌₂) : X.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  mapHomotopyCategory (lift (𝟙 X) (const y))

variable {X} in
def ι₂ (x : X _⦋0⦌₂) : Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  mapHomotopyCategory (lift (const x) (𝟙 Y))

variable {X Y}

def obj (x : X.HomotopyCategory × Y.HomotopyCategory) : (X ⊗ Y).HomotopyCategory :=
  objEquiv.symm ⟨objEquiv x.1, objEquiv x.2⟩

lemma comm
    {x x' : X.HomotopyCategory} (f : x ⟶ x') {y y' : Y.HomotopyCategory} (g : y ⟶ y') :
    (ι₁ X (objEquiv y)).map f ≫ (ι₂ Y (objEquiv x')).map g =
      (ι₂ Y (objEquiv x)).map g ≫ (ι₁ X (objEquiv y')).map f := by
  induction g using hom_induction with
  | id =>
    simp [ι₁, ι₂]
    apply Category.comp_id
  | comp g₁ g₂ h₁ h₂ =>
    rw [Functor.map_comp_assoc, Functor.map_comp, reassoc_of% h₁, h₂]
  | @toPath y y' g =>
    induction f using hom_induction with
    | id =>
      simp [ι₁, ι₂]
      symm
      apply Category.comp_id
    | comp f₁ f₂ h₁ h₂ =>
      dsimp at h₁ h₂ ⊢
      rw [Functor.map_comp_assoc, Functor.map_comp, h₂, reassoc_of% h₁]
    | @toPath x x' f =>
      dsimp
      change (HomotopyCategory.quotientFunctor _).map _ ≫
        (HomotopyCategory.quotientFunctor _).map _ = _
      sorry

end inverse

open inverse in
def inverse : (X.HomotopyCategory × Y.HomotopyCategory) ⥤ (X ⊗ Y).HomotopyCategory :=
  prod.desc obj
    (fun x x' f y ↦ (ι₁ X (objEquiv y)).map f)
    (fun x y y' g ↦ (ι₂ Y (objEquiv x)).map g)
    (fun _ _ ↦ by cat_disch)
    (fun _ _ ↦ by cat_disch)
    (fun _ _ _ _ _ _ ↦ by cat_disch)
    (fun _ _ _ _ _ _ ↦ by cat_disch)
    (fun x x' f y y' g ↦ comm f g)

def equivalence : (X ⊗ Y).HomotopyCategory ≌ (X.HomotopyCategory × Y.HomotopyCategory) where
  functor := functor X Y
  inverse := inverse X Y
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry
  functor_unitIso_comp := sorry

end BinaryProduct

end HomotopyCategory

end Truncated

end SSet
