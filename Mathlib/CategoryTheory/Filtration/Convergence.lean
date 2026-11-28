/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Filtration.Quotients
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

/-!
# ...


-/

public section

namespace CategoryTheory

open Limits ZeroObject

variable {C I : Type*} [Category* C] [Category* I]

namespace Filtration

variable {X : C}

@[expose, simps, implicit_reducible]
def coconeDiagram (F : Filtration X I) : Cocone F.diagram where
  pt := X
  ι := F.ι

class IsWeaklyConvergent (F : Filtration X I) : Prop where
  nonempty_isColimit : Nonempty (IsColimit F.coconeDiagram)

noncomputable def isColimitCoconeDiagram (F : Filtration X I) [F.IsWeaklyConvergent] :
    IsColimit F.coconeDiagram :=
  IsWeaklyConvergent.nonempty_isColimit.some

class IsConvergent [HasZeroMorphisms C] (F : Filtration X I) : Prop
    extends F.IsWeaklyConvergent where
  π_eq_zero (F) (c : Cone F.diagram) : c.π = 0

attribute [simp] IsConvergent.π_eq_zero

section

variable [HasZeroMorphisms C] [HasZeroObject C]

@[expose, simps, implicit_reducible]
noncomputable def coneDiagram (F : Filtration X I) : Cone F.diagram where
  pt := 0
  π := 0

noncomputable def isLimitConeDiagram (F : Filtration X I) [F.IsConvergent] :
    IsLimit F.coneDiagram where
  lift _ := 0

end

section

variable [HasZeroMorphisms C] [HasCokernels C] (F : Filtration X I)

class IsStronglyConvergent (F : Filtration X I) : Prop
    extends F.IsWeaklyConvergent where
  nonempty_isLimit : Nonempty (IsLimit F.coneCokernelιAppFunctor)

noncomputable def isLimitConeCokernelι [F.IsStronglyConvergent] :
    IsLimit F.coneCokernelιAppFunctor :=
  IsStronglyConvergent.nonempty_isLimit.some

open IsCofiltered in
instance [IsCofiltered I] [F.IsStronglyConvergent] : F.IsConvergent where
  π_eq_zero c := by
    ext i
    rw [← cancel_mono (F.ι.app i)]
    refine F.isLimitConeCokernelι.hom_ext (fun j ↦ ?_)
    rw [Category.assoc, ← c.w_assoc (minToLeft i j)]
    simp [F.w_assoc (minToLeft i j), ← F.w_assoc (minToRight i j)]

end

section

variable [Abelian C] (F : Filtration X I)

def isLimitConeCokernelDiagramMapFunctor [F.IsStronglyConvergent] (i : I) :
    IsLimit (F.coneCokernelDiagramMapFunctor i) := by
  sorry

end

lemma isZero_obj_of_hom [HasZeroMorphisms C] (F : Filtration X I) {i j : I} (f : i ⟶ j)
    (hj : IsZero (F.obj j)) : IsZero (F.obj i) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (F.diagram.map f)]
  exact hj.eq_of_tgt ..

lemma isIso_ι_app_of_hom (F : Filtration X I) {i j : I} (f : i ⟶ j)
    (hi : IsIso (F.ι.app i) := by infer_instance) : IsIso (F.ι.app j) :=
  ⟨inv (F.ι.app i) ≫ F.diagram.map f, by simp [← cancel_mono (F.ι.app j)], by simp⟩

lemma isEventuallyConstantFrom_diagram_of_isIso
    (F : Filtration X I) (i : I) (hi : IsIso (F.ι.app i) := by infer_instance) :
    F.diagram.IsEventuallyConstantFrom i := by
  intro j f
  have := F.isIso_ι_app_of_hom f
  exact IsIso.of_isIso_fac_right (F.w f)

lemma isEventuallyConstantTo_cokernelιAppFunctor_of_isZero
    [HasZeroMorphisms C] [HasCokernels C]
    (F : Filtration X I) (i : I) (hi : IsZero (F.obj i)) :
    (F.cokernelιAppFunctor).IsEventuallyConstantTo i := by
  intro j f
  have hj : IsZero (F.obj j) := IsZero.of_mono (F.diagram.map f) hi
  let e : F.diagram.obj j ≅ F.diagram.obj i :=
    { hom := F.diagram.map f
      inv := 0
      hom_inv_id := hj.eq_of_src ..
      inv_hom_id := hi.eq_of_src .. }
  exact (cokernel.mapIso (F.ι.app j) (F.ι.app i) e (Iso.refl _) (hj.eq_of_src ..)).isIso_hom

class IsBounded (F : Filtration X I) : Prop where
  exists_isZero_obj (F) : ∃ (i : I), IsZero (F.obj i)
  exists_isIso_ι_app (F) : ∃ (i : I), IsIso (F.ι.app i)

export IsBounded (exists_isZero_obj exists_isIso_ι_app)

instance [IsFiltered I] (F : Filtration X I) [F.IsBounded] : F.IsWeaklyConvergent where
  nonempty_isColimit := by
    obtain ⟨i, hi⟩ := F.exists_isIso_ι_app
    have : IsIso (F.coconeDiagram.ι.app i) := hi
    exact ⟨(F.isEventuallyConstantFrom_diagram_of_isIso i).isColimitOfIsIso _⟩

instance [IsFiltered I] [IsCofiltered I] [HasZeroMorphisms C] [HasCokernels C]
    (F : Filtration X I) [F.IsBounded] :
    F.IsStronglyConvergent where
  nonempty_isLimit := by
    obtain ⟨i, hi⟩ := F.exists_isZero_obj
    have : IsIso (F.coneCokernelιAppFunctor.π.app i) :=
      cokernel.π_of_zero (hi.eq_of_src ..)
    exact ⟨(F.isEventuallyConstantTo_cokernelιAppFunctor_of_isZero i hi).isLimitOfIsIso _⟩

end Filtration

namespace FilteredObject

abbrev IsWeaklyConvergent (F : FilteredObject C I) : Prop :=
  F.filtration.IsWeaklyConvergent

abbrev IsConvergent [HasZeroMorphisms C] (F : FilteredObject C I) : Prop :=
  F.filtration.IsConvergent

abbrev IsStronglyConvergent [HasZeroMorphisms C] [HasCokernels C] (F : FilteredObject C I) : Prop :=
  F.filtration.IsStronglyConvergent

abbrev IsBounded (F : FilteredObject C I) : Prop :=
  F.filtration.IsBounded

namespace Hom

variable {F G : FilteredObject C I} (f : F ⟶ G)

lemma isIso_hom_of_isIso_natTrans [F.IsWeaklyConvergent] [G.IsWeaklyConvergent]
    (hf : IsIso f.natTrans := by infer_instance) :
    IsIso f.hom := by
  have :
      (IsColimit.coconePointUniqueUpToIso F.filtration.isColimitCoconeDiagram
        (((IsColimit.precomposeHomEquiv (asIso f.natTrans) _).symm
          (G.filtration.isColimitCoconeDiagram)))).hom = f.hom :=
    F.filtration.isColimitCoconeDiagram.hom_ext (fun i ↦ by
      simp [dsimp% F.filtration.isColimitCoconeDiagram.comp_coconePointUniqueUpToIso_hom])
  rw [← this]
  infer_instance

lemma isIso_of_isIso_natTrans [F.IsWeaklyConvergent] [G.IsWeaklyConvergent]
    (hf : IsIso f.natTrans := by infer_instance) : IsIso f := by
  rw [isIso_iff]
  exact ⟨f.isIso_hom_of_isIso_natTrans, hf⟩

lemma isIso_natTrans_app [Abelian C] [F.IsStronglyConvergent] [G.IsStronglyConvergent] (i : I)
    (h : IsIso (f.mapCokernelDiagramMapFunctor i) := by infer_instance) :
    IsIso (f.natTrans.app i) := by
  let hF := (IsLimit.postcomposeHomEquiv (asIso ((f.mapCokernelDiagramMapFunctor i))) _).symm
          (F.filtration.isLimitConeCokernelDiagramMapFunctor i)
  let hG := G.filtration.isLimitConeCokernelDiagramMapFunctor i
  have : (IsLimit.conePointUniqueUpToIso hF hG).hom = f.natTrans.app i :=
    hG.hom_ext (fun g ↦ by simp [dsimp% IsLimit.conePointUniqueUpToIso_hom_comp hF hG])
  rw [← this]
  infer_instance

end Hom

end FilteredObject

end CategoryTheory
