/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Cycles
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.ComposableArrows.Three

/-!
# Spectral objects in abelian categories

Let `X` be a spectral object index by the category `ι`
in the abelian category `C`. The purpose of this file
is to introduce the homology `X.E` of the short complex `X.shortComplexE`
`(X.H n₀).obj (mk₁ f₃) ⟶ (X.H n₁).obj (mk₁ f₂) ⟶ (X.H n₂).obj (mk₁ f₁)`
when `f₁`, `f₂` and `f₃` are composable morphisms in `ι` and the
equalities `n₀ + 1 = n₁` and `n₁ + 1 = n₂` hold (both maps in the
short complex are given by `X.δ`). All the relevant objects in the
spectral sequence attached to spectral objects can be defined
in terms of this homology `X.E`: the objects in all pages, including
the page at infinity.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)

/-- The short complex consisting of the composition of
two morphisms `X.δ`, given three composable morphisms `f₁`, `f₂`
and `f₃` in `ι`, and three consecutive integers. -/
@[simps]
def shortComplexE : ShortComplex C where
  X₁ := (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ n₀ n₁ hn₁ f₂ f₃
  g := X.δ n₁ n₂ hn₂ f₁ f₂

/-- The homology of the short complex `shortComplexE` consisting of
two morphisms `X.δ`. In the documentation, we shorten it as `E^n₁(f₁, f₂, f₃)` -/
noncomputable def E : C := (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homology

lemma isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂))) :
    IsZero (X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) :=
  (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι}
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  {i'' j'' k'' l'' : ι} (f₁'' : i'' ⟶ j'') (f₂'' : j'' ⟶ k'') (f₃'' : k'' ⟶ l'')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (β : mk₃ f₁' f₂' f₃' ⟶ mk₃ f₁'' f₂'' f₃'')
  (γ : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁'' f₂'' f₃'')

/-- The functoriality of `shortComplexE` with respect to morphisms
in `ComposableArrows ι 3`. -/
@[simps]
def shortComplexEMap :
    X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶
      X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' where
  τ₁ := (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := δ_naturality ..
  comm₂₃ := δ_naturality ..

@[simp]
lemma shortComplexEMap_id :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) = 𝟙 _ := by
  ext
  all_goals dsimp; convert (X.H _).map_id _; cat_disch

@[reassoc, simp]
lemma shortComplexEMap_comp :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) =
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β := by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

/-- The functoriality of `E` with respect to morphisms
in `ComposableArrows ι 3`. -/
noncomputable def EMap :
    X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' :=
  ShortComplex.homologyMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α)

@[simp]
lemma EMap_id :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) = 𝟙 _ := by
  dsimp only [EMap]
  rw [shortComplexEMap_id, ShortComplex.homologyMap_id]
  rfl

@[reassoc, simp]
lemma EMap_comp :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) =
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β := by
  dsimp only [EMap]
  rw [shortComplexEMap_comp, ShortComplex.homologyMap_comp]

lemma isIso_EMap
    (h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α)))
    (h₁ : IsIso ((X.H n₁).map ((functorArrows ι 1 2 3).map α)))
    (h₂ : IsIso ((X.H n₂).map ((functorArrows ι 0 1 3).map α))) :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) := by
  have : IsIso (shortComplexEMap X n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) := by
    apply (config := { allowSynthFailures := true})
      ShortComplex.isIso_of_isIso <;> assumption
  dsimp [EMap]
  infer_instance

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

lemma δ_eq_zero_of_isIso₁ (hf : IsIso f) :
    X.δ n₀ n₁ hn₁ f g = 0 := by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ n₀ n₁ hn₁ f g _ rfl

lemma δ_eq_zero_of_isIso₂ (hg : IsIso g) :
    X.δ n₀ n₁ hn₁ f g = 0 := by
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ n₀ n₁ hn₁ f g _ rfl

end

lemma isZero_H_obj_of_isIso (n : ℤ) {i j : ι} (f : i ⟶ j) (hf : IsIso f) :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ n (𝟙 i) (𝟙 i) (𝟙 i) (by simp)
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← h]
  congr 1
  cat_disch

end SpectralObject

end Abelian

end CategoryTheory
