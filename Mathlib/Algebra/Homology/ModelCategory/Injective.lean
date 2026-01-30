/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.ModelCategory.Lifting
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Factorization lemma

-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C]

namespace Plus

instance (J : Type) [Category J] [FinCategory J] :
    (CochainComplex.plus C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyGE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.min' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyGE_of_ge _ _ (Finset.min'_le _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval _ _ i) p.isLimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyGE (p.diag.obj j) n i).eq_of_tgt _ _)

instance (J : Type) [Category J] [FinCategory J] :
    (CochainComplex.plus C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyGE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.min' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyGE_of_ge _ _ (Finset.min'_le _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval _ _ i) p.isColimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyGE (p.diag.obj j) n i).eq_of_src _ _)

instance : HasFiniteLimits (Plus C) where
  out J _ _ := by infer_instance

instance : HasFiniteColimits (Plus C) where
  out J _ _ := by infer_instance

lemma mono_iff {X Y : Plus C} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom := by
  refine ⟨fun _ ↦ inferInstanceAs (Mono ((ι C).map f)),
    fun _ ↦ Functor.mono_of_mono_map (ι C) (by assumption)⟩

namespace modelCategoryQuillen

scoped instance : CategoryWithWeakEquivalences (CochainComplex.Plus C) where
  weakEquivalences := quasiIso C

scoped instance : CategoryWithCofibrations (CochainComplex.Plus C) where
  cofibrations := .monomorphisms _

scoped instance : CategoryWithFibrations (CochainComplex.Plus C) where
  fibrations := degreewiseEpiWithInjectiveKernel.inverseImage (ι C)

instance : (quasiIso C).HasTwoOutOfThreeProperty := by
  dsimp [quasiIso]
  infer_instance

instance : (quasiIso C).IsStableUnderRetracts := by
  dsimp [quasiIso]
  infer_instance

instance : (weakEquivalences (Plus C)).HasTwoOutOfThreeProperty :=
  inferInstanceAs (quasiIso C).HasTwoOutOfThreeProperty

instance : (weakEquivalences (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (quasiIso C).IsStableUnderRetracts

instance : (cofibrations (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (MorphismProperty.monomorphisms _).IsStableUnderRetracts

instance : (fibrations (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (degreewiseEpiWithInjectiveKernel.inverseImage (ι C)).IsStableUnderRetracts

lemma cofibration_iff {X Y : Plus C} (f : X ⟶ Y) :
    Cofibration f ↔ Mono f :=
  HomotopicalAlgebra.cofibration_iff _

variable [EnoughInjectives C]

instance {A B : CochainComplex.Plus C} (i : A ⟶ B) [Cofibration i] :
    Mono i := by
  rwa [← cofibration_iff]

/-open HomComplex in
lemma lifting {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] (hip : WeakEquivalence i ∨ WeakEquivalence p) :
    HasLiftingProperty i p where
  sq_hasLift {t b} sq := by
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    obtain ⟨X, hX⟩ := X
    obtain ⟨Y, hY⟩ := Y
    have := (mono_iff i).1 inferInstance
    have hp : degreewiseEpiWithInjectiveKernel p.hom :=
      (fibration_iff p).1 inferInstance
    obtain ⟨i, rfl⟩ := ObjectProperty.homMk_surjective i
    obtain ⟨p, rfl⟩ := ObjectProperty.homMk_surjective p
    obtain ⟨t, rfl⟩ := ObjectProperty.homMk_surjective t
    obtain ⟨b, rfl⟩ := ObjectProperty.homMk_surjective b
    dsimp at i p t b hp
    have : Mono i := by assumption
    have hip : QuasiIso i ∨ QuasiIso p := by
      simpa only [weakEquivalence_iff] using hip
    replace sq : CommSq t i p b := ⟨(ObjectProperty.ι _).congr_map sq.w⟩
    suffices sq.HasLift from ⟨⟨{ l := ObjectProperty.homMk sq.lift }⟩⟩
    have sq' (n : ℤ) : CommSq (t.f n) (i.f n) (p.f n) (b.f n) :=
      (sq.map (HomologicalComplex.eval _ _ n))
    have (n : ℤ) : (sq' n).HasLift := by
      have := (hp n).hasLiftingProperty (i.f n)
      infer_instance
    let β := Lifting.cocycle₁ sq (fun n ↦ { l := (sq' n).lift })
      (cokernelIsCokernel i) (kernelIsKernel p) (hπ := by simp) (hι := by simp)
    obtain ⟨α, hα⟩ : ∃ (α : Cochain (cokernel i) (kernel p) 0), δ 0 1 α = β.1 := sorry
    exact Lifting.hasLift sq _ (cokernelIsCokernel _) (kernelIsKernel _)
      (hπ := by simp) (hι := by simp) α hα

instance {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [WeakEquivalence i] [Fibration p] :
    HasLiftingProperty i p :=
  lifting _ _ (Or.inl inferInstance)

instance {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p :=
  lifting _ _ (Or.inr inferInstance)

instance : (trivialCofibrations (Plus C)).HasFactorization (fibrations (Plus C)) where
  nonempty_mapFactorizationData := by
    rintro ⟨K, n, hn⟩ ⟨L, m, hm⟩ f
    obtain ⟨(f : K ⟶ L), rfl⟩ := ObjectProperty.homMk_surjective f
    obtain ⟨d, _, _⟩ : ∃ (d : ℤ), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d := by
      refine ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by simp), L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, _, hp, fac⟩ := CochainComplex.cm5a f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi :=
        ⟨by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff],
          by assumption⟩
      hp := hp
    }⟩

instance : (cofibrations (Plus C)).HasFactorization (trivialFibrations (Plus C)) where
  nonempty_mapFactorizationData := by
    rintro ⟨K, n, hn⟩ ⟨L, m, hm⟩ f
    obtain ⟨(f : K ⟶ L), rfl⟩ := ObjectProperty.homMk_surjective f
    obtain ⟨d, _, _⟩ : ∃ (d : ℤ), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d := by
      refine ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by simp), L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, hp, _, fac⟩ := CochainComplex.cm5b f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi := by
        rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff]
      hp := ⟨hp, by assumption⟩
    }⟩

scoped instance : ModelCategory (CochainComplex.Plus C) where-/

end modelCategoryQuillen

end Plus

end CochainComplex
