/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Filtration.Basic

/-!
# ...


-/

public section

namespace CategoryTheory

open Limits ZeroObject

variable {C I : Type*} [Category* C] [Category* I]

namespace Filtration

variable [HasZeroMorphisms C] [HasCokernels C] {X : C}
  (F : Filtration X I)

@[expose, simps, implicit_reducible]
noncomputable def cokernelιAppFunctor : I ⥤ C where
  obj i := cokernel (F.ι.app i)
  map f := cokernel.map _ _ (F.diagram.map f) (𝟙 X) (by simp)

@[expose, simps, implicit_reducible]
noncomputable def cokernelDiagramMapFunctor (i : I) : Over i ⥤ C where
  obj j := cokernel (F.diagram.map j.hom)
  map f := cokernel.map _ _ (F.diagram.map f.left) (𝟙 _) (by simp [← f.w, -Over.w])

@[expose, simps, implicit_reducible]
noncomputable def coneCokernelιAppFunctor : Cone F.cokernelιAppFunctor where
  pt := X
  π.app _ := cokernel.π _

@[expose, simps, implicit_reducible]
noncomputable def coneCokernelDiagramMapFunctor (i : I) :
    Cone (F.cokernelDiagramMapFunctor i) where
  pt := F.obj i
  π.app _ := cokernel.π _

@[expose, simps]
noncomputable def cokernelDiagramMapFunctorToCokernelιAppFunctor (i : I) :
    F.cokernelDiagramMapFunctor i ⟶ Over.forget i ⋙ F.cokernelιAppFunctor where
  app j := cokernel.map _ _ (𝟙 _) (F.ι.app i) (by simp)

@[expose, simps]
noncomputable def cokernelιAppFunctorToConstObjCokernel (i : I) :
    Over.forget i ⋙ F.cokernelιAppFunctor ⟶ (Functor.const _).obj (cokernel (F.ι.app i)) where
  app j := cokernel.map _ _ (F.diagram.map j.hom) (𝟙 _) (by simp)

@[reassoc (attr := simp)]
lemma cokernelDiagramMapFunctorToCokernelιAppFunctor_cokernelιAppFunctorToConstObjCokernel (i : I) :
    F.cokernelDiagramMapFunctorToCokernelιAppFunctor i ≫
      F.cokernelιAppFunctorToConstObjCokernel i = 0 := by
  cat_disch

noncomputable abbrev kernelForkCokernelιAppFunctorToConstObjCokernel (i : I) :
    KernelFork (F.cokernelιAppFunctorToConstObjCokernel i) :=
  KernelFork.ofι _
    (F.cokernelDiagramMapFunctorToCokernelιAppFunctor_cokernelιAppFunctorToConstObjCokernel i)

def isLimitKernelForkCokernelιAppFunctorToConstObjCokernelMapEvaluationObj {i : I} (j : Over i) :
    IsLimit ((F.kernelForkCokernelιAppFunctorToConstObjCokernel i).map ((evaluation _ _).obj j)) :=
  sorry

noncomputable def isLimitKernelForkCokernelιAppFunctorToConstObjCokernel (i : I) :
    IsLimit (F.kernelForkCokernelιAppFunctorToConstObjCokernel i) :=
  evaluationJointlyReflectsLimits _
    (fun j ↦ (KernelFork.isLimitMapConeEquiv _ _).symm
      (F.isLimitKernelForkCokernelιAppFunctorToConstObjCokernelMapEvaluationObj j))

end Filtration

namespace FilteredObject

variable [HasZeroMorphisms C] [HasCokernels C]
  {F G : FilteredObject C I}

namespace Hom

variable (φ : F ⟶ G) (i : I)

@[expose, simps]
noncomputable def mapCokernelDiagramMapFunctor :
    F.filtration.cokernelDiagramMapFunctor i ⟶
    G.filtration.cokernelDiagramMapFunctor i where
  app f := cokernel.map _ _ (φ.natTrans.app _) (φ.natTrans.app _)
    (φ.natTrans.naturality f.hom).symm

end Hom

end FilteredObject

end CategoryTheory
