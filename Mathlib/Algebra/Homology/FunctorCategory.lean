/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Evaluation jointly reflects quasi-isomorphisms in functor categories

-- merge with `Functor.lean`?

-/

@[expose] public section

open CategoryTheory

variable {J C : Type*} [Category J] [Category C] [Abelian C]

namespace CategoryTheory.ShortComplex

variable {S₁ S₂ : ShortComplex (J ⥤ C)} (f : S₁ ⟶ S₂)

lemma quasiIso_iff_evaluation :
    QuasiIso f ↔ ∀ (j : J),
      QuasiIso (((evaluation J C).obj j).mapShortComplex.map f) :=
  ⟨fun _ ↦ inferInstance, fun hf ↦ by
    rw [quasiIso_iff, NatTrans.isIso_iff_isIso_app]
    exact fun j ↦ ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
      ((homologyFunctorIso ((evaluation J C).obj j)))).app (Arrow.mk f))).1
        ((quasiIso_iff _).1 (hf j))⟩

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} {K₁ K₂ : HomologicalComplex (J ⥤ C) c}
  (f : K₁ ⟶ K₂)

lemma quasiIsoAt_iff_evaluation (i : ι) :
    QuasiIsoAt f i ↔ ∀ (j : J),
      QuasiIsoAt ((((evaluation J C).obj j).mapHomologicalComplex c).map f) i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff_evaluation]
  rfl

lemma quasiIso_iff_evaluation :
    QuasiIso f ↔ ∀ (j : J),
      QuasiIso ((((evaluation J C).obj j).mapHomologicalComplex c).map f) := by
  simp only [quasiIso_iff, quasiIsoAt_iff_evaluation]
  tauto

end HomologicalComplex
