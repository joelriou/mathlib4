/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexInduction
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# K-injective cochain complexes

We define the notion of K-injective cochain complex in an abelian category,
and show that bounded below complexes of injective objects are K-injective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using an injective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex Preadditive

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `K`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `K`.)
/-- A cochain complex `L` is K-injective if any morphism `K ⟶ L`
with `K` acyclic is homotopic to zero. -/
class IsKInjective (L : CochainComplex C ℤ) : Prop where
  nonempty_homotopy_zero {K : CochainComplex C ℤ} (f : K ⟶ L) :
    K.Acyclic → Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from an acyclic
cochain complex to a K-injective cochain complex. -/
noncomputable irreducible_def IsKInjective.homotopyZero {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : K.Acyclic) [L.IsKInjective] :
    Homotopy f 0 :=
  (IsKInjective.nonempty_homotopy_zero f hK).some

lemma _root_.HomotopyEquiv.isKInjective {L₁ L₂ : CochainComplex C ℤ}
    (e : HomotopyEquiv L₁ L₂)
    [L₁.IsKInjective] : L₂.IsKInjective where
  nonempty_homotopy_zero {K} f hK :=
    ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compLeft f).trans (.ofEq (by simp))))
        (((IsKInjective.homotopyZero (f ≫ e.inv) hK).compRight e.hom).trans (.ofEq (by simp)))⟩

lemma isKInjective_of_iso {L₁ L₂ : CochainComplex C ℤ} (e : L₁ ≅ L₂)
    [L₁.IsKInjective] :
    L₂.IsKInjective :=
  (HomotopyEquiv.ofIso e).isKInjective

lemma isKInjective_iff_of_iso {L₁ L₂ : CochainComplex C ℤ} (e : L₁ ≅ L₂) :
    L₁.IsKInjective ↔ L₂.IsKInjective :=
  ⟨fun _ ↦ isKInjective_of_iso e, fun _ ↦ isKInjective_of_iso e.symm⟩

lemma isKInjective_iff_rightOrthogonal (L : CochainComplex C ℤ) :
    L.IsKInjective ↔
      (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  refine ⟨fun _ K f hK ↦ ?_,
      fun hL ↦ ⟨fun {K} f hK ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKInjective.homotopyZero f hK), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK, Functor.map_zero]

lemma IsKInjective.rightOrthogonal (L : CochainComplex C ℤ) [L.IsKInjective] :
    (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  rwa [← isKInjective_iff_rightOrthogonal]

instance (L : CochainComplex C ℤ) [hL : L.IsKInjective] (n : ℤ) :
    (L⟦n⟧).IsKInjective := by
  rw [isKInjective_iff_rightOrthogonal] at hL ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app L)
    ((HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.le_shift n _ hL)

lemma isKInjective_shift_iff (L : CochainComplex C ℤ) (n : ℤ) :
    (L⟦n⟧).IsKInjective ↔ L.IsKInjective :=
  ⟨fun _ ↦ isKInjective_of_iso (show L⟦n⟧⟦-n⟧ ≅ L from (shiftEquiv _ n).unitIso.symm.app L),
    fun _ ↦ inferInstance⟩

lemma isKInjective_of_injective_aux {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n + 1 = m)
    (hK : K.ExactAt m) [Injective (L.X m)]
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n + 2) ⟶ L.X (n + 1)),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by lia) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by lia)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; lia)] at hK
  obtain ⟨β, hβ⟩ : ∃ (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by lia) n (n + 2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]

open Cochain.InductionUp in
lemma isKInjective_of_injective (L : CochainComplex C ℤ) (d : ℤ)
    [L.IsStrictlyGE d] [∀ (n : ℤ), Injective (L.X n)] :
    L.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    /- The strategy of the proof is express the `0`-cocycle in `Cochain K L 0`
    corresponding to `f` as the coboundary of a `-1`-cochain. An approximate
    solution for some `n : ℕ` is an element in the subset `X n` consisting
    of the `-1`-cochains such that `δ (-1) 0 α` coincide with `Cochain.ofHom f`
    up to the degree `n + d - 1`. The assumption on `L` implies that
    the zero `-1`-cochain belongs to `X 0`, and we use the lemma
    `isKInjective_of_injective_aux` in order to get better approximations,
    and we pass to the limit. -/
    let X (n : ℕ) : Set (Cochain K L (-1)) :=
      setOf (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
    let x₀ : X 0 := ⟨0, fun p q hpq hp ↦
      IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
    let φ (n : ℕ) (α : X n) : X (n + 1) :=
      ⟨_, (isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : ℕ) + d - 1)
        (by lia) (hK _) α.2).choose_spec⟩
    have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero]
    ext n
    let k₀ := (n - d + 1).toNat
    rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
      limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by lia) (by lia),
      limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by lia) (by lia)]

instance (K L : CochainComplex C ℤ) [hK : K.IsKInjective] [hL : L.IsKInjective] :
    (K ⊞ L).IsKInjective := by
  let S := (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  rw [isKInjective_iff_rightOrthogonal] at hK hL ⊢
  have : PreservesBinaryBiproducts (HomotopyCategory.quotient C (.up ℤ)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  refine ObjectProperty.prop_of_iso _
    ((HomotopyCategory.quotient C (.up ℤ)).mapBiprod K L).symm ?_
  apply ObjectProperty.biprod_stable_of_isTriangulated
  all_goals assumption

lemma IsKInjective.eq_δ_of_cocycle {K L : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle K L n) [L.IsKInjective] (hK : K.Acyclic) (m : ℤ) (hm : m + 1 = n) :
    ∃ (α : Cochain K L m), δ m n α = z.1 := by
  obtain ⟨φ, hφ⟩ := (Cocycle.equivHom ..).surjective (z.rightShift n 0 (zero_add n))
  rw [Subtype.ext_iff] at hφ
  dsimp at hφ
  obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero φ hK
  obtain ⟨f, hf⟩ := Cochain.equivHomotopy _ _ h
  simp only [Int.reduceNeg, Cochain.ofHom_zero, add_zero] at hf
  refine ⟨n.negOnePow • Cochain.rightUnshift f m (by lia), ?_⟩
  apply (Cochain.rightShiftAddEquiv _ _ _ n 0 (by simp)).injective
  dsimp
  rw [← hφ, hf, δ_units_smul, Cochain.rightShift_units_smul,
    Cochain.δ_rightUnshift _ _ _ _ 0 (by simp),
    Cochain.rightShift_units_smul, Cochain.rightShift_rightUnshift,
    smul_smul, Int.units_mul_self, one_smul]

lemma IsKInjective.eq_δ_of_cocycle' {K L : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle K L n) [L.IsKInjective] (hL : L.Acyclic) (m : ℤ) (hm : m + 1 = n) :
    ∃ (α : Cochain K L m), δ m n α = z.1 := by
  obtain ⟨β, hβ⟩ :=
    IsKInjective.eq_δ_of_cocycle (Cocycle.ofHom (𝟙 L)) hL (-1) (by simp)
  exact ⟨z.1.comp β (by lia), by simp [δ_comp z.1 β _ _ 0 _ hm rfl (by simp), hβ]⟩

end CochainComplex
