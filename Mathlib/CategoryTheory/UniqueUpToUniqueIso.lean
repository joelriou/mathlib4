/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Iso

/-!
# Categories with a unique object up to a unique isomorphism

-/

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

class IsUniqueUpToUniqueIso : Prop where
  nonempty : Nonempty C := by infer_instance
  subsingleton_iso (X Y : C) : Subsingleton (X ≅ Y) := by infer_instance
  nonempty_iso (X Y : C) : Nonempty (X ≅ Y) := by infer_instance

namespace IsUniqueUpToUniqueIso

attribute [instance] nonempty subsingleton_iso nonempty_iso

end IsUniqueUpToUniqueIso

end CategoryTheory
