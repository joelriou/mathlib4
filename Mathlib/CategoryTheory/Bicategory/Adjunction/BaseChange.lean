/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor

/-!
# The base change morphism


-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {C : Type u'} [Bicategory.{w', v'} C]
  [Strict B] (F : B ⥤ᵖ Adj C)

namespace Pseudofunctor

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : B}

section

variable {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂}
  (sq : CommSq t l r b)

def baseChange : (F.map l).r ≫ (F.map t).l ⟶ (F.map b).l ≫ (F.map r).r :=
  Bicategory.mateEquiv (F.map l).adj (F.map r).adj (F.isoMapOfCommSq sq).hom.τl

def baseChange₂ : (F.map t).l ⟶ (F.map l ≫ F.map b).l ≫ (F.map r).r :=
  (F.map r).adj.homEquiv₂ (F.isoMapOfCommSq sq).hom.τl

lemma baseChange₂_def :
    F.baseChange₂ sq = (F.map r).adj.homEquiv₂ (F.isoMapOfCommSq sq).hom.τl := rfl

lemma baseChange₂_eq :
    F.baseChange₂ sq =
      (F.map l).adj.homEquiv₁.symm (F.baseChange sq) ≫ (α_ _ _ _).inv := by
  simp [baseChange, baseChange₂, mateEquiv_apply]

def baseChange₁ : (F.map l).r ≫ (F.map t).l ≫ (F.map r).l ⟶ (F.map b).l :=
  (F.map l).adj.homEquiv₁ (F.isoMapOfCommSq sq).hom.τl

lemma baseChange₁_def :
    F.baseChange₁ sq = (F.map l).adj.homEquiv₁ (F.isoMapOfCommSq sq).hom.τl := rfl

lemma baseChange₁_eq :
    F.baseChange₁ sq = (α_ _ _ _).inv ≫
      (F.map r).adj.homEquiv₂.symm (F.baseChange sq) := by
  simp [baseChange, baseChange₁, mateEquiv_apply'']

lemma baseChange_eq₁ :
    F.baseChange sq =
      (F.map r).adj.homEquiv₂ ((α_ _ _ _).hom ≫ F.baseChange₁ sq) := by
  simp [baseChange, mateEquiv_apply'', baseChange₁_def]

lemma baseChange_eq₂ :
    F.baseChange sq =
      (F.map l).adj.homEquiv₁ (F.baseChange₂ sq ≫ (α_ _ _ _).hom) := by
  rw [baseChange, mateEquiv_apply, baseChange₂_def]
  dsimp

end

lemma baseChange_horiz_comp' {t₁₂ : X₁ ⟶ X₂} {t₂₃ : X₂ ⟶ X₃}
    {l : X₁ ⟶ Y₁} {m : X₂ ⟶ Y₂} {r : X₃ ⟶ Y₃}
    {b₁₂ : Y₁ ⟶ Y₂} {b₂₃ : Y₂ ⟶ Y₃}
    (sq₁₂ : CommSq t₁₂ l m b₁₂) (sq₂₃ : CommSq t₂₃ m r b₂₃)
    {t₁₃ : X₁ ⟶ X₃} {b₁₃ : Y₁ ⟶ Y₃}
    (ht : t₁₂ ≫ t₂₃ = t₁₃) (hb : b₁₂ ≫ b₂₃ = b₁₃) :
    F.baseChange (sq₁₂.horiz_comp' sq₂₃ ht hb) =
      (F.map l).r  ◁ (F.mapComp' t₁₂ t₂₃ t₁₃).hom.τl ≫ (α_ _ _ _).inv ≫
        F.baseChange sq₁₂ ▷ (F.map t₂₃).l ≫ (α_ _ _ _).hom ≫
        (F.map b₁₂).l ◁ F.baseChange sq₂₃ ≫ (α_ _ _ _).inv ≫
        (F.mapComp' b₁₂ b₂₃ b₁₃).inv.τl ▷ (F.map r).r := by
  rw [baseChange, baseChange, baseChange]
  sorry

end Pseudofunctor

end CategoryTheory
