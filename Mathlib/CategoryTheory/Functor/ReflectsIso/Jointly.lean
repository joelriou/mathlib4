/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Families of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a family of functors. The family is said to jointly reflect
isomorphisms (resp. monomorphisms, resp. epimorphisms) if every `f : X ⟶ Y`
in `C` for which `Fᵢ.map f` is an isomorphism (resp. monomorphism, resp. epimorphism)
for all `i` is an isomorphism.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {I : Type*} {D : I → Type*} [∀ i, Category (D i)]
  (F : ∀ i, C ⥤ D i)

/-- A family of functors jointly reflects isomorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an isomorphism, then `f` is an isomorphism. -/
structure JointlyReflectIsomorphisms (F : ∀ i, C ⥤ D i) : Prop where
  isIso {X Y : C} (f : X ⟶ Y) [∀ i, IsIso ((F i).map f)] : IsIso f

/-- A family of functors jointly reflects monomorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an monomorphism, then `f` is an monomorphism. -/
structure JointlyReflectMonomorphisms (F : ∀ i, C ⥤ D i) : Prop where
  mono {X Y : C} (f : X ⟶ Y) [∀ i, Mono ((F i).map f)] : Mono f

/-- A family of functors jointly reflects epimorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an epimorphism, then `f` is an epimorphism. -/
structure JointlyReflectEpimorphisms (F : ∀ i, C ⥤ D i) : Prop where
  epi {X Y : C} (f : X ⟶ Y) [∀ i, Epi ((F i).map f)] : Epi f

namespace JointlyReflectIsomorphisms

variable {F} (h : JointlyReflectIsomorphisms F)

include h in
lemma isIso_iff {X Y : C} (f : X ⟶ Y) : IsIso f ↔ ∀ i, IsIso ((F i).map f) := by
  constructor
  · intro hf i
    infer_instance
  · intro
    exact h.isIso f

include h in
lemma mono {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Mono ((F i).map f)]
    [∀ i, PreservesLimit (cospan f f) (F i)] [HasPullback f f] : Mono f := by
  have hc := pullbackIsPullback f f
  rw [mono_iff_isIso_fst hc, h.isIso_iff]
  intro i
  exact (mono_iff_isIso_fst ((isLimitMapConePullbackConeEquiv (F i) pullback.condition).1
    (isLimitOfPreserves (F i) hc))).1 (hf i)

include h in
lemma jointlyReflectMonomorphisms [∀ i, PreservesLimitsOfShape WalkingCospan (F i)]
    [HasPullbacks C] :
    JointlyReflectMonomorphisms F where
  mono f _ := h.mono f

include h in
lemma epi {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Epi ((F i).map f)]
    [∀ i, PreservesColimit (span f f) (F i)] [HasPushout f f] : Epi f := by
  have hc := pushoutIsPushout f f
  rw [epi_iff_isIso_inl hc, h.isIso_iff]
  intro i
  exact (epi_iff_isIso_inl ((isColimitMapCoconePushoutCoconeEquiv (F i) pushout.condition).1
    (isColimitOfPreserves (F i) hc))).1 (hf i)

include h in
lemma jointlyReflectEpimorphisms [∀ i, PreservesColimitsOfShape WalkingSpan (F i)]
    [HasPushouts C] :
    JointlyReflectEpimorphisms F where
  epi f _ := h.epi f

end JointlyReflectIsomorphisms

namespace JointlyReflectMonomorphisms

variable {F} (h : JointlyReflectMonomorphisms F)

include h in
lemma mono_iff [∀ i, (F i).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ i, Mono ((F i).map f) := by
  constructor
  · intros
    infer_instance
  · intro
    exact h.mono f

end JointlyReflectMonomorphisms

namespace JointlyReflectEpimorphisms

variable {F} (h : JointlyReflectEpimorphisms F)

include h in
lemma epi_iff [∀ i, (F i).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ i, Epi ((F i).map f) := by
  constructor
  · intros
    infer_instance
  · intro
    exact h.epi f

end JointlyReflectEpimorphisms

end CategoryTheory
