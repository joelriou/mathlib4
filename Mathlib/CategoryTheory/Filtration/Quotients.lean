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
