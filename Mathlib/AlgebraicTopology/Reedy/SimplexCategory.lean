/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.Reedy.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# The simplex category is a Reedy category

-/

open CategoryTheory

namespace SimplexCategory

def reedyStructure : ReedyStructure SimplexCategory ℕ where
  deg := len
  plus := .monomorphisms _
  minus := .epimorphisms _
  eq_of_iso e := len_eq_of_isIso e.hom
  lt_of_minus p (hp : Epi p) h := lt_of_le_of_ne (len_le_of_epi p)
    (Ne.symm (by rwa [isIso_iff_of_epi] at h))
  lt_of_plus i (hi : Mono i) h := lt_of_le_of_ne (len_le_of_mono i)
    (by rwa [isIso_iff_of_mono] at h)
  plus_inter_minus := by ext; simp [isIso_iff_mono_and_epi]
  isUniqueUpToUniqueIso := by infer_instance

instance : reedyStructure.MinusCondition where
  left_cancel _ _ e _ _ := eq_id_of_isIso e

instance : reedyStructure.PlusCondition where
  right_cancel _ _ e _ _ := eq_id_of_isIso e

end SimplexCategory
