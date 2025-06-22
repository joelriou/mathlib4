/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The bicategory of adjunctions in a bicategory

Given a bicategory `B`, we construct a bicategory `Adj B` that has the same
objects but whose `1`-morphisms are adjunctions (in the same direction
as the left adjoints), and `2`-morphisms are tuples of mate maps between
the left and right adjoints (where the map between right
adjoints is in the opposite direction).

Certain pseudofunctors to the bicategory `Adj Cat` are analogous to bifibered categories:
in various contexts, this may be used in order to formalize the properties of
both pullback and pushforward functors.

## References

* https://ncatlab.org/nlab/show/2-category+of+adjunctions
* https://ncatlab.org/nlab/show/transformation+of+adjoints
* https://ncatlab.org/nlab/show/mate

-/

universe w v u

namespace CategoryTheory

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

variable (B) in
/--
The bicategory that has the same objects as a bicategory `B`, in which `1`-morphisms
are adjunctions (in the same direction as the left adjoints),
and `2`-morphisms are tuples of mate maps between the left and right
adjoints (where the map between right adjoints is in the opposite direction).
-/
def Adj : Type u := B

namespace Adj

/-- If `a : Adj B`, `a.obj : B` is the underlying object of `B`. -/
abbrev obj (a : Adj B) : B := a

section

variable (a b : B)

/--
Given two objects `a` and `b` in a bicategory,
this is the type of adjunctions between `a` and `b`.
-/
structure Hom where
  /-- Default constructor for `1`-morphisms in the bicategory `Adj B`, see
  `CategoryTheory.Bicategory.Adj.Hom.mk` for a constructor where the morphisms
  are implicit. -/
  mk'::
  /-- the left adjoint -/
  l : a ⟶ b
  /-- the right adjoint -/
  r : b ⟶ a
  /-- the adjunction -/
  adj : l ⊣ r

variable {a b} in
/-- Constructor for `1`-morphisms in the bicategory `Adj B`. -/
@[simps]
def Hom.mk {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r) : Hom a b where
  l := l
  r := r
  adj := adj

end

instance : CategoryStruct (Adj B) where
  Hom (a : B) b := Hom a b
  id (a : B) := .mk' (Adjunction.id a)
  comp f g := .mk' (f.adj.comp g.adj)

@[simp] lemma id_l (a : Adj B) : Hom.l (𝟙 a) = 𝟙 a.obj := rfl
@[simp] lemma id_r (a : Adj B) : Hom.r (𝟙 a) = 𝟙 a.obj := rfl
@[simp] lemma id_adj (a : Adj B) : Hom.adj (𝟙 a) = Adjunction.id a.obj := rfl

variable {a b c d : Adj B}

@[simp] lemma comp_l (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).l = α.l ≫ β.l := rfl
@[simp] lemma comp_r (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).r = β.r ≫ α.r := rfl
@[simp] lemma comp_adj (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).adj = α.adj.comp β.adj := rfl

/-- A morphism between two adjunctions consists of a tuple of mate maps. -/
@[ext]
structure Hom₂ (α β : a ⟶ b) where
  /-- the morphism between left adjoints -/
  τl : α.l ⟶ β.l
  /-- the morphism in the opposite direction between right adjoints -/
  τr : β.r ⟶ α.r
  conjugateEquiv_τl : conjugateEquiv β.adj α.adj τl = τr := by aesop_cat

lemma Hom₂.conjugateEquiv_symm_τr {α β : a ⟶ b} (p : Hom₂ α β) :
    (conjugateEquiv β.adj α.adj).symm p.τr = p.τl := by
  rw [← Hom₂.conjugateEquiv_τl, Equiv.symm_apply_apply]

instance : CategoryStruct (a ⟶ b) where
  Hom α β := Hom₂ α β
  id α :=
    { τl := 𝟙 _
      τr := 𝟙 _ }
  comp {a b c} x y :=
    { τl := x.τl ≫ y.τl
      τr := y.τr ≫ x.τr
      conjugateEquiv_τl := by simp [← conjugateEquiv_comp c.adj b.adj a.adj y.τl x.τl,
        Hom₂.conjugateEquiv_τl] }

@[ext]
lemma hom₂_ext {α β : a ⟶ b} {x y : α ⟶ β} (hl : x.τl = y.τl) : x = y :=
  Hom₂.ext hl (by simp only [← Hom₂.conjugateEquiv_τl, hl])

@[simp] lemma id_τl (α : a ⟶ b) : Hom₂.τl (𝟙 α) = 𝟙 α.l := rfl
@[simp] lemma id_τr (α : a ⟶ b) : Hom₂.τr (𝟙 α) = 𝟙 α.r := rfl

section

variable {α β γ : a ⟶ b}

@[simp, reassoc] lemma comp_τl (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τl = x.τl ≫ y.τl := rfl
@[simp, reassoc] lemma comp_τr (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τr = y.τr ≫ x.τr := rfl

end

instance : Category (a ⟶ b) where

/-- Constructor for isomorphisms between 1-morphisms in the bicategory `Adj B`. -/
@[simps]
def iso₂Mk {α β : a ⟶ b} (el : α.l ≅ β.l) (er : β.r ≅ α.r)
    (h : conjugateEquiv β.adj α.adj el.hom = er.hom) :
    α ≅ β where
  hom :=
    { τl := el.hom
      τr := er.hom
      conjugateEquiv_τl := h }
  inv :=
    { τl := el.inv
      τr := er.inv
      conjugateEquiv_τl := by
        rw [← cancel_mono er.hom, Iso.inv_hom_id, ← h,
          conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id] }

/-- The associator in the bicategory `Adj B`. -/
@[simps!]
def associator (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) : (α ≫ β) ≫ γ ≅ α ≫ β ≫ γ :=
  iso₂Mk (α_ _ _ _) (α_ _ _ _) (conjugateEquiv_associator_hom _ _ _)

/-- The left unitor in the bicategory `Adj B`. -/
@[simps!]
def leftUnitor (α : a ⟶ b) : 𝟙 a ≫ α ≅ α :=
  iso₂Mk (λ_ _) (ρ_ _).symm
    (by simpa using conjugateEquiv_id_comp_right_apply α.adj α.adj (𝟙 _))

/-- The right unitor in the bicategory `Adj B`. -/
@[simps!]
def rightUnitor (α : a ⟶ b) : α ≫ 𝟙 b ≅ α :=
  iso₂Mk (ρ_ _) (λ_ _).symm
    (by simpa using conjugateEquiv_comp_id_right_apply α.adj α.adj (𝟙 _))

/-- The left whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerLeft (α : a ⟶ b) {β β' : b ⟶ c} (y : β ⟶ β') : α ≫ β ⟶ α ≫ β' where
  τl := _ ◁ y.τl
  τr := y.τr ▷ _
  conjugateEquiv_τl := by
    dsimp
    simp only [conjugateEquiv_whiskerLeft, Hom₂.conjugateEquiv_τl]

/-- The right whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerRight {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) : α ≫ β ⟶ α' ≫ β where
  τl := x.τl ▷ _
  τr := _ ◁ x.τr
  conjugateEquiv_τl := by
    dsimp
    simp only [conjugateEquiv_whiskerRight, Hom₂.conjugateEquiv_τl]

attribute [local simp] whisker_exchange

instance : Bicategory (Adj B) where
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

@[simp] lemma whiskerRight_τr' {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) :
    (x ▷ β).τr = β.r ◁ x.τr := rfl

@[simp] lemma whiskerRight_τl' {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) :
    (x ▷ β).τl = x.τl ▷ β.l := rfl

/-- The forget pseudofunctor from `Adj B` to `B`. -/
@[simps]
def forget₁ : Pseudofunctor (Adj B) B where
  obj a := a.obj
  map x := x.l
  map₂ α := α.τl
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

/-- Given an isomorphism between two 1-morphisms in `Adj B`, this is the
underlying isomorphisms between the left adjoints. -/
@[simps]
def lIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.l ≅ adj₂.l where
  hom := e.hom.τl
  inv := e.inv.τl
  hom_inv_id := by rw [← comp_τl, e.hom_inv_id, id_τl]
  inv_hom_id := by rw [← comp_τl, e.inv_hom_id, id_τl]

/-- Given an isomorphism between two 1-morphisms in `Adj B`, this is the
underlying isomorphisms between the right adjoints. -/
@[simps]
def rIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.r ≅ adj₂.r where
  hom := e.inv.τr
  inv := e.hom.τr
  hom_inv_id := by rw [← comp_τr, e.hom_inv_id, id_τr]
  inv_hom_id := by rw [← comp_τr, e.inv_hom_id, id_τr]

end Adj

end Bicategory

end CategoryTheory
