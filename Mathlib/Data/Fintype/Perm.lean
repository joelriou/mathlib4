/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Factorial.Basic

/-!
# `Fintype` instances for `Equiv` and `Perm`

Main declarations:
* `permsOfFinset s`: The finset of permutations of the finset `s`.

-/

assert_not_exists MonoidWithZero

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset List Equiv Equiv.Perm

variable [DecidableEq α] [DecidableEq β]

/-- Given a list, produce a list of all permutations of its elements. -/
def permsOfList : List α → List (Perm α)
  | [] => [1]
  | a :: l => permsOfList l ++ l.flatMap fun b => (permsOfList l).map fun f => Equiv.swap a b * f

theorem length_permsOfList : ∀ l : List α, length (permsOfList l) = l.length !
  | [] => rfl
  | a :: l => by
    simp [Nat.factorial_succ, permsOfList, length_permsOfList, succ_mul, add_comm]

theorem mem_permsOfList_of_mem {l : List α} {f : Perm α} (h : ∀ x, f x ≠ x → x ∈ l) :
    f ∈ permsOfList l := by
  induction l generalizing f with
  | nil =>
    simp only [not_mem_nil] at h
    exact List.mem_singleton.2 (Equiv.ext fun x => Decidable.byContradiction <| h x)
  | cons a l IH =>
  by_cases hfa : f a = a
  · refine mem_append_left _ (IH fun x hx => mem_of_ne_of_mem ?_ (h x hx))
    rintro rfl
    exact hx hfa
  have hfa' : f (f a) ≠ f a := mt (fun h => f.injective h) hfa
  have : ∀ x : α, (Equiv.swap a (f a) * f) x ≠ x → x ∈ l := by
    intro x hx
    have hxa : x ≠ a := by
      rintro rfl
      apply hx
      simp only [mul_apply, swap_apply_right]
    refine List.mem_of_ne_of_mem hxa (h x fun h => ?_)
    simp only [mul_apply, swap_apply_def, mul_apply, Ne, apply_eq_iff_eq] at hx
    split_ifs at hx with h_1
    exacts [hxa (h.symm.trans h_1), hx h]
  suffices f ∈ permsOfList l ∨ ∃ b ∈ l, ∃ g ∈ permsOfList l, Equiv.swap a b * g = f by
    simpa only [permsOfList, exists_prop, List.mem_map, mem_append, List.mem_flatMap]
  refine or_iff_not_imp_left.2 fun _hfl => ⟨f a, ?_, Equiv.swap a (f a) * f, IH this, ?_⟩
  · exact mem_of_ne_of_mem hfa (h _ hfa')
  · rw [← mul_assoc, mul_def (swap a (f a)) (swap a (f a)), swap_swap, ← Perm.one_def, one_mul]

theorem mem_of_mem_permsOfList :
    ∀ {l : List α} {f : Perm α}, f ∈ permsOfList l → {x : α} → f x ≠ x → x ∈ l
  | [], f, h, heq_iff_eq => by
    have : f = 1 := by simpa [permsOfList] using h
    rw [this]; simp
  | a :: l, f, h, x =>
    (mem_append.1 h).elim (fun h hx => mem_cons_of_mem _ (mem_of_mem_permsOfList h hx))
      fun h hx =>
      let ⟨y, hy, hy'⟩ := List.mem_flatMap.1 h
      let ⟨g, hg₁, hg₂⟩ := List.mem_map.1 hy'
      if hxa : x = a then by simp [hxa]
      else
        if hxy : x = y then mem_cons_of_mem _ <| by rwa [hxy]
        else mem_cons_of_mem a <| mem_of_mem_permsOfList hg₁ <| by
              rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def]
              split_ifs <;> [exact Ne.symm hxy; exact Ne.symm hxa; exact hx]

theorem mem_permsOfList_iff {l : List α} {f : Perm α} :
    f ∈ permsOfList l ↔ ∀ {x}, f x ≠ x → x ∈ l :=
  ⟨mem_of_mem_permsOfList, mem_permsOfList_of_mem⟩

theorem nodup_permsOfList : ∀ {l : List α}, l.Nodup → (permsOfList l).Nodup
  | [], _ => by simp [permsOfList]
  | a :: l, hl => by
    have hl' : l.Nodup := hl.of_cons
    have hln' : (permsOfList l).Nodup := nodup_permsOfList hl'
    have hmeml : ∀ {f : Perm α}, f ∈ permsOfList l → f a = a := fun {f} hf =>
      not_not.1 (mt (mem_of_mem_permsOfList hf) (nodup_cons.1 hl).1)
    rw [permsOfList, List.nodup_append', List.nodup_flatMap, pairwise_iff_getElem]
    refine ⟨?_, ⟨⟨?_,?_ ⟩, ?_⟩⟩
    · exact hln'
    · exact fun _ _ => hln'.map fun _ _ => mul_left_cancel
    · intros i j hi hj hij x hx₁ hx₂
      let ⟨f, hf⟩ := List.mem_map.1 hx₁
      let ⟨g, hg⟩ := List.mem_map.1 hx₂
      have hix : x a = l[i] := by
        rw [← hf.2, mul_apply, hmeml hf.1, swap_apply_left]
      have hiy : x a = l[j] := by
        rw [← hg.2, mul_apply, hmeml hg.1, swap_apply_left]
      have hieqj : i = j := hl'.getElem_inj_iff.1 (hix.symm.trans hiy)
      exact absurd hieqj (_root_.ne_of_lt hij)
    · intros f hf₁ hf₂
      let ⟨x, hx, hx'⟩ := List.mem_flatMap.1 hf₂
      let ⟨g, hg⟩ := List.mem_map.1 hx'
      have hgxa : g⁻¹ x = a := f.injective <| by rw [hmeml hf₁, ← hg.2]; simp
      have hxa : x ≠ a := fun h => (List.nodup_cons.1 hl).1 (h ▸ hx)
      exact (List.nodup_cons.1 hl).1 <|
          hgxa ▸ mem_of_mem_permsOfList hg.1 (by rwa [apply_inv_self, hgxa])

/-- Given a finset, produce the finset of all permutations of its elements. -/
def permsOfFinset (s : Finset α) : Finset (Perm α) :=
  Quotient.hrecOn s.1 (fun l hl => ⟨permsOfList l, nodup_permsOfList hl⟩)
    (fun a b hab =>
      hfunext (congr_arg _ (Quotient.sound hab)) fun ha hb _ =>
        heq_of_eq <| Finset.ext <| by simp [mem_permsOfList_iff, hab.mem_iff])
    s.2

theorem mem_perms_of_finset_iff :
    ∀ {s : Finset α} {f : Perm α}, f ∈ permsOfFinset s ↔ ∀ {x}, f x ≠ x → x ∈ s := by
  rintro ⟨⟨l⟩, hs⟩ f; exact mem_permsOfList_iff

theorem card_perms_of_finset : ∀ s : Finset α, #(permsOfFinset s) = (#s)! := by
  rintro ⟨⟨l⟩, hs⟩; exact length_permsOfList l

/-- The collection of permutations of a fintype is a fintype. -/
def fintypePerm [Fintype α] : Fintype (Perm α) :=
  ⟨permsOfFinset (@Finset.univ α _), by simp [mem_perms_of_finset_iff]⟩

instance Equiv.instFintype [Fintype α] [Fintype β] : Fintype (α ≃ β) :=
  if h : Fintype.card β = Fintype.card α then
    Trunc.recOnSubsingleton (Fintype.truncEquivFin α) fun eα =>
      Trunc.recOnSubsingleton (Fintype.truncEquivFin β) fun eβ =>
        @Fintype.ofEquiv _ (Perm α) fintypePerm
          (equivCongr (Equiv.refl α) (eα.trans (Eq.recOn h eβ.symm)) : α ≃ α ≃ (α ≃ β))
  else ⟨∅, fun x => False.elim (h (Fintype.card_eq.2 ⟨x.symm⟩))⟩

@[deprecated (since := "2024-11-19")] alias equivFintype := Equiv.instFintype

@[to_additive]
instance MulEquiv.instFintype
    {α β : Type*} [Mul α] [Mul β] [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    Fintype (α ≃* β) where
  elems := Equiv.instFintype.elems.filterMap
    (fun e => if h : ∀ a b : α, e (a * b) = e a * e b then (⟨e, h⟩ : α ≃* β) else none) (by aesop)
  complete me := (Finset.mem_filterMap ..).mpr ⟨me.toEquiv, Finset.mem_univ _, by {simp; rfl}⟩

theorem Fintype.card_perm [Fintype α] : Fintype.card (Perm α) = (Fintype.card α)! :=
  Subsingleton.elim (@fintypePerm α _ _) (@Equiv.instFintype α α _ _ _ _) ▸ card_perms_of_finset _

theorem Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card (α ≃ β) = (Fintype.card α)! :=
  Fintype.card_congr (equivCongr (Equiv.refl α) e) ▸ Fintype.card_perm
