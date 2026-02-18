/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Adjunction.BaseChange
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Descent data we have both pullbacks and pushforwards

depends on
#35401
#35396
#35393
-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Bicategory Opposite Limits

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}}


namespace DescentDataAdj

section

variable {X₁₂ X₁ X₂ : C}
  {obj₁ : (F.obj (.mk (op X₁))).obj} {obj₂ : (F.obj (.mk (op X₂))).obj}
  {p₁ : X₁₂ ⟶ X₁} {p₂ : X₁₂ ⟶ X₂}
  (hom : obj₁ ⟶ (F.map p₁.op.toLoc).r.toFunctor.obj
    ((F.map p₂.op.toLoc).l.toFunctor.obj obj₂))

/-- Given morphims `p₁ : X₁₂ ⟶ X₁`, `p₂ : X₁₂ ⟶ X₂`, `p₁₂ : Y₁₂ ⟶ X₁₂`,,
`q₁ : Y₁₂ ⟶ X₁`, `q₂ : Y₁₂ ⟶ X₂` such that `p₁₂ ≫ p₁ = q₁` and `p₁₂ ≫ p₂ = q₂`,
this is the morphism `obj₁ ⟶ q₁_*q₂^* obj₂` that is deduced from a morphism
`obj₁ ⟶ p₁_*p₂^* obj₂`. -/
def pullHom ⦃Y₁₂ : C⦄ (p₁₂ : Y₁₂ ⟶ X₁₂) (q₁ : Y₁₂ ⟶ X₁) (q₂ : Y₁₂ ⟶ X₂)
    (hq₁ : p₁₂ ≫ p₁ = q₁ := by cat_disch) (hq₂ : p₁₂ ≫ p₂ = q₂ := by cat_disch) :
    obj₁ ⟶ (F.map q₁.op.toLoc).r.toFunctor.obj ((F.map q₂.op.toLoc).l.toFunctor.obj obj₂) :=
  hom ≫ (F.map p₁.op.toLoc).r.toFunctor.map ((F.map p₁₂.op.toLoc).adj.unit.toNatTrans.app _) ≫
    (Adj.rIso (F.mapComp' p₁.op.toLoc p₁₂.op.toLoc q₁.op.toLoc)).inv.toNatTrans.app _ ≫
      (F.map q₁.op.toLoc).r.toFunctor.map
    ((Adj.lIso (F.mapComp' p₂.op.toLoc p₁₂.op.toLoc q₂.op.toLoc)).inv.toNatTrans.app _)

end

section

variable
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
  {i₁ i₂ i₃ : ι} {obj₁ : (F.obj (.mk (op (X i₁)))).obj}
  {obj₂ : (F.obj (.mk (op (X i₂)))).obj}
  {obj₃ : (F.obj (.mk (op (X i₃)))).obj}
  (hom₁₂ : obj₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.obj
    ((F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.obj obj₂))
  (hom₂₃ : obj₂ ⟶ (F.map (sq i₂ i₃).p₁.op.toLoc).r.toFunctor.obj
    ((F.map (sq i₂ i₃).p₂.op.toLoc).l.toFunctor.obj obj₃))

def homComp : obj₁ ⟶ (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).r.toFunctor.obj
      ((F.map (sq₃ i₁ i₂ i₃).p₃.op.toLoc).l.toFunctor.obj obj₃) :=
  hom₁₂ ≫ (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.map hom₂₃) ≫
        (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map
          ((F.baseChange (sq₃ i₁ i₂ i₃).isPullback₂.toCommSq.flip.op.toLoc).toNatTrans.app _) ≫
    (Adj.rIso (F.mapComp' (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc
          (sq₃ i₁ i₂ i₃).p₁.op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).inv.toNatTrans.app _ ≫
    (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).r.toFunctor.map
      ((Adj.lIso (F.mapComp' (sq i₂ i₃).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc
          (sq₃ i₁ i₂ i₃).p₃.op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).inv.toNatTrans.app _)

end

end DescentDataAdj

variable
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  {sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}

open DescentDataAdj in
variable (F sq sq₃) in
structure DescentDataAdj where
  obj (i : ι) : (F.obj (.mk (op (X i)))).obj
  hom (i₁ i₂ : ι) : obj i₁ ⟶
    (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.obj (obj i₂))
  hom_self (i : ι) (δ : (sq i i).Diagonal) :
    pullHom (hom i i) δ.f (𝟙 _) (𝟙 _) =
      (F.map (𝟙 (.mk (op (X i))))).adj.unit.toNatTrans.app _
  hom_comp (i₁ i₂ i₃ : ι) :
    homComp sq sq₃ (hom i₁ i₂) (hom i₂ i₃) =
      pullHom (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _

namespace DescentDataAdj

@[ext]
structure Hom (D₁ D₂ : F.DescentDataAdj sq sq₃) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.map (hom i₂)) =
    hom i₁ ≫ D₂.hom i₁ i₂ := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

instance : Category (F.DescentDataAdj sq sq₃) where
  Hom := Hom
  id _ := { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentDataAdj sq sq₃} {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext (funext h)

@[simp]
lemma id_hom (D : F.DescentDataAdj sq sq₃) (i : ι) :
    Hom.hom (𝟙 D) i = 𝟙 _ :=
  rfl

@[reassoc, simp]
lemma comp_hom {D₁ D₂ D₃ : F.DescentDataAdj sq sq₃} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) (i : ι) :
    (f ≫ g).hom i = f.hom i ≫ g.hom i :=
  rfl

@[simps]
def isoMk {D₁ D₂ : F.DescentDataAdj sq sq₃} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ (i₁ i₂ : ι), D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.map (e i₂).hom) =
        (e i₁).hom ≫ D₂.hom i₁ i₂ := by cat_disch) :
    D₁ ≅ D₂ where
  hom :=
    { hom i := (e i).hom
      comm := comm }
  inv :=
    { hom i := (e i).inv
      comm i₁ i₂ := by
        rw [← cancel_epi (e i₁).hom, ← reassoc_of% comm i₁ i₂]
        simp [← Functor.map_comp] }

namespace equivalenceDescentData'

variable {obj : ∀ i, (F.obj (.mk (op (X i)))).obj}

@[simps! -isSimp apply symm_apply]
def homEquiv :
    (∀ i₁ i₂, obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.obj (obj i₂))) ≃
    (∀ i₁ i₂, (F.map (sq i₁ i₂).p₁.op.toLoc).l.toFunctor.obj (obj i₁) ⟶
      (F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.obj (obj i₂)) :=
  Equiv.piCongrRight (fun i₁ ↦ Equiv.piCongrRight (fun i₂ ↦
    ((Adjunction.ofCat (F.map (sq i₁ i₂).p₁.op.toLoc).adj).homEquiv _ _).symm))

variable (hom : ∀ i₁ i₂, obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.obj (obj i₂)))

lemma homEquiv_self_iff (i : ι) :
    DescentData'.pullHom' (F := (F.comp Adj.forget₁)) (homEquiv hom)
        (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ ↔
    ∀ (δ : (sq i i).Diagonal),
      pullHom (hom i i) δ.f (𝟙 _) (𝟙 _) =
      (F.map (𝟙 (.mk (op (X i))))).adj.unit.toNatTrans.app _ := by
  sorry

lemma homEquiv_comp_iff (i₁ i₂ i₃ : ι) :
    DescentData'.pullHom' (F := F.comp Adj.forget₁) (homEquiv hom)
      (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    DescentData'.pullHom' (homEquiv hom)
      (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    DescentData'.pullHom' (homEquiv hom)
      (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ ↔
    homComp sq sq₃ (hom i₁ i₂) (hom i₂ i₃) =
      pullHom (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _ := by
  sorry

end equivalenceDescentData'

variable (F sq sq₃)

set_option backward.isDefEq.respectTransparency false in
open equivalenceDescentData' in
@[simps!]
def toDescentData' : F.DescentDataAdj sq sq₃ ⥤ (F.comp Adj.forget₁).DescentData' sq sq₃ where
  obj D :=
    { obj := D.obj
      hom := homEquiv D.hom
      pullHom'_hom_self i := by simpa only [homEquiv_self_iff] using D.hom_self i
      pullHom'_hom_comp i₁ i₂ i₃ := by
        simpa only [homEquiv_comp_iff] using D.hom_comp i₁ i₂ i₃ }
  map {D₁ D₂} φ :=
    { hom := φ.hom
      comm i₁ i₂ := by
        dsimp
        rw [homEquiv_apply, homEquiv_apply,
          ← Adjunction.homEquiv_naturality_right_symm, φ.comm,
          Adjunction.homEquiv_naturality_left_symm] }

set_option backward.isDefEq.respectTransparency false in
open equivalenceDescentData' in
@[simps!]
def fromDescentData' : (F.comp Adj.forget₁).DescentData' sq sq₃ ⥤ F.DescentDataAdj sq sq₃ where
  obj D :=
    { obj := D.obj
      hom := homEquiv.symm D.hom
      hom_self i := by
        obtain ⟨φ, hφ⟩ := homEquiv.surjective D.hom
        simpa only [← homEquiv_self_iff, Equiv.apply_symm_apply] using D.pullHom'_hom_self i
      hom_comp i₁ i₂ i₃ := by
        obtain ⟨φ, hφ⟩ := homEquiv.surjective D.hom
        simpa only [← homEquiv_comp_iff, Equiv.apply_symm_apply]
          using D.pullHom'_hom_comp i₁ i₂ i₃ }
  map φ :=
    { hom := φ.hom
      comm i₁ i₂ := by
        have := φ.comm i₁ i₂
        dsimp at this ⊢
        rw [homEquiv_symm_apply, homEquiv_symm_apply,
          ← Adjunction.homEquiv_naturality_left, this,
          ← Adjunction.homEquiv_naturality_right] }

set_option backward.isDefEq.respectTransparency false in
def equivalenceDescentData' :
    F.DescentDataAdj sq sq₃ ≌ (F.comp Adj.forget₁).DescentData' sq sq₃ where
  functor := toDescentData' F sq sq₃
  inverse := fromDescentData' F sq sq₃
  unitIso :=
    NatIso.ofComponents (fun D ↦ isoMk (fun _ ↦ Iso.refl _)
      (by simp [toDescentData']))
  counitIso :=
    NatIso.ofComponents (fun D ↦ DescentData'.isoMk (fun _ ↦ Iso.refl _)
      (by simp [fromDescentData']))

end DescentDataAdj

end Pseudofunctor

end CategoryTheory
