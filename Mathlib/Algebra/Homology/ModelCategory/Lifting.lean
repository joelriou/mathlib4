/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Factorization lemma

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory HomotopicalAlgebra Limits HomComplex

variable {C : Type*} [Category C] [Abelian C]

namespace Lifting

variable {A B : CochainComplex C ℤ} {S : ShortComplex (CochainComplex C ℤ)}
  {t : A ⟶ S.X₂} {i : A ⟶ B} {b : B ⟶ S.X₃}
  (sq : CommSq t i S.g b)
  (hsq : ∀ n, (sq.map (HomologicalComplex.eval _ _ n)).LiftStruct)
  (hS : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting)

abbrev cochain₀ : Cochain B S.X₂ 0 := Cochain.ofHoms (fun n ↦ (hsq n).l)

def cocycle₁' : Cocycle B S.X₂ 1 :=
  Cocycle.mk (δ 0 1 (cochain₀ sq hsq) - (Cochain.ofHom b).comp
      ((cocycleOfDegreewiseSplit S hS).1.comp (Cochain.ofHom S.f) (add_zero 1)) (zero_add 1)) 2
    (by simp) (by simp [δ_δ])

@[reassoc (attr := simp)]
lemma coe_cocycle₁'_v_comp_eq_zero (p q : ℤ) (hpq : p + 1 = q) :
    (cocycle₁' sq hsq hS).1.v p q hpq ≫ S.g.f q = 0 := by
  have fac_right (n : ℤ) := (hsq n).fac_right
  dsimp at fac_right
  simp [cocycle₁', -HomologicalComplex.Hom.comm, ← HomologicalComplex.comp_f, S.zero,
    ← S.g.comm, fac_right, reassoc_of% fac_right, b.comm]

def cocycle₁ : Cocycle B S.X₁ 1 :=
  Cocycle.mk (Cochain.mk
    (fun p q hpq ↦ (cocycle₁' sq hsq hS).1.v p q hpq ≫ (hS q).r)) 2 (by simp) (by
      have eq : (Cochain.mk (fun p q hpq ↦ (cocycle₁' sq hsq hS).1.v p q hpq ≫ (hS q).r)).comp
          (Cochain.ofHom S.f) (add_zero 1) = (cocycle₁' sq hsq hS).1 := by
        ext p _ rfl
        have := (hS (p + 1)).id
        dsimp at this
        rw [← eq_sub_iff_add_eq] at this
        simp [this]
      replace eq := congr_arg (δ 1 2) eq
      rw [Cocycle.δ_eq_zero, δ_comp_ofHom] at eq
      ext p _ rfl
      have : Mono (S.f.f (p + 2)) := (hS (p + 2)).mono_f
      replace eq := Cochain.congr_v eq p _ rfl
      rw [Cochain.zero_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at eq
      rw [Cochain.zero_v, ← cancel_mono (S.f.f (p + 2)), zero_comp, eq])

@[reassoc (attr := simp)]
lemma cocycle₁_v_comp (p q : ℤ) (hpq : p + 1 = q) :
    (cocycle₁ sq hsq hS).1.v p q hpq ≫ S.f.f q =
      (cocycle₁' sq hsq hS).1.v p q hpq := by
  have := (hS q).id
  dsimp [cocycle₁] at this ⊢
  rw [← eq_sub_iff_add_eq] at this
  simp [this]

end Lifting

end CochainComplex
