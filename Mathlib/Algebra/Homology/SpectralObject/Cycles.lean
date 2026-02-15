/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ExactSequenceFour
public import Mathlib.CategoryTheory.Abelian.Exact
public import Batteries.Tactic.Lint

/-!
# Kernel and cokernel of the differentiel of a spectral object

Let `X` be a spectral object index by the category `ι`
in the abelian category `C`. In this file, we introduce
the kernel `X.cycles` and the cokernel `X.opcycles` of `X.δ`.
These are defined when `f` and `g` are composable morphisms
in `ι` and for any integer `n`.
In the documentation, the kernel `X.cycles n f g` of
`δ : H^n(g) ⟶ H^{n+1}(f)` shall be denoted `Z^n(f, g)`,
and the cokernel `X.opcycles n f g` of `δ : H^{n-1}(g) ⟶ H^n(f)`
shall be denoted `opZ^n(f, g)`.
The definitions `cyclesMap` and `opcyclesMap` give the
functoriality of these definitions with respect
to morphisms in `ComposableArrows ι 2`.

We record that `Z^n(f, g)` is a kernel by the lemma
`kernelSequenceCycles_exact` and that `opZ^n(f, g)` is
a cokernel by the lemma `cokernelSequenceOpcycles_exact`.
We also provide a constructor `X.liftCycles` for morphisms
to cycles and `X.descOpcycles` for morphisms from opcycles.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]
-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable (n : ℤ) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

/-- The kernel of `δ : H^n(g) ⟶ H^{n+1}(f)`. In the documentation,
this may be shortened as `Z^n(f, g)` -/
noncomputable def cycles : C := kernel (X.δ n (n + 1) rfl f g)

/-- The cokernel of `δ : H^{n-1}(g) ⟶ H^n(g)`. In the documentation,
this may be shortened as `opZ^n₁(f, g)`. -/
noncomputable def opcycles : C := cokernel (X.δ (n - 1) n (by lia) f g)

/-- The inclusion `Z^n(f, g) ⟶ H^n(g)` of the kernel of `δ`. -/
noncomputable def iCycles :
    X.cycles n f g ⟶ (X.H n).obj (mk₁ g) :=
  kernel.ι _

/-- The projection `H^n(f) ⟶ opZ^n(f, g)` to the cokernel of `δ`. -/
noncomputable def pOpcycles :
    (X.H n).obj (mk₁ f) ⟶ X.opcycles n f g :=
  cokernel.π _

instance : Mono (X.iCycles n f g) := by
  dsimp [iCycles]
  infer_instance

instance : Epi (X.pOpcycles n f g) := by
  dsimp [pOpcycles]
  infer_instance

lemma isZero_opcycles (h : IsZero ((X.H n).obj (mk₁ f))) :
    IsZero (X.opcycles n f g) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src

lemma isZero_cycles (h : IsZero ((X.H n).obj (mk₁ g))) :
    IsZero (X.cycles n f g) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

@[reassoc (attr := simp)]
lemma iCycles_δ : X.iCycles n₀ f g ≫ X.δ n₀ n₁ hn₁ f g = 0 := by
  subst hn₁
  simp [iCycles]

@[reassoc (attr := simp)]
lemma δ_pOpcycles : X.δ n₀ n₁ hn₁ f g ≫ X.pOpcycles n₁ f g = 0 := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [pOpcycles]

/-- The short complex which expresses `X.cycles` as the kernel of `X.δ`. -/
@[simps]
noncomputable def kernelSequenceCycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.iCycles_δ n₀ n₁ hn₁ f g)

/-- The short complex which expresses `X.opcycles` as the cokernel of `X.δ`. -/
@[simps]
noncomputable def cokernelSequenceOpcycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.δ_pOpcycles n₀ n₁ hn₁ f g)

instance : Mono (X.kernelSequenceCycles n₀ n₁ hn₁ f g).f := by
  dsimp
  infer_instance

instance : Epi (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).g := by
  dsimp
  infer_instance

lemma kernelSequenceCycles_exact :
    (X.kernelSequenceCycles n₀ n₁ hn₁ f g).Exact := by
  subst hn₁
  apply ShortComplex.exact_kernel

lemma cokernelSequenceOpcycles_exact :
    (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).Exact := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  apply ShortComplex.exact_cokernel

section

variable {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g)) (hx : x ≫ X.δ n₀ n₁ hn₁ f g = 0)

/-- Constructor for morphisms to `X.cycles`. -/
noncomputable def liftCycles :
    A ⟶ X.cycles n₀ f g :=
  kernel.lift _ x (by subst hn₁; exact hx)

@[reassoc (attr := simp)]
lemma liftCycles_i : X.liftCycles n₀ n₁ hn₁ f g x hx ≫ X.iCycles n₀ f g = x := by
  apply kernel.lift_ι

end

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A) (hx : X.δ n₀ n₁ hn₁ f g ≫ x = 0)

/-- Constructor for morphisms from `X.opcycles`. -/
noncomputable def descOpcycles :
    X.opcycles n₁ f g ⟶ A :=
  cokernel.desc _ x (by
    obtain rfl : n₀ = n₁ -1 := by lia
    exact hx)

@[reassoc (attr := simp)]
lemma p_descOpcycles : X.pOpcycles n₁ f g ≫ X.descOpcycles n₀ n₁ hn₁ f g x hx = x := by
  apply cokernel.π_desc

end

end

section

variable (n : ℤ) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

/-- The functoriality of `X.cycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
noncomputable def cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') :
    X.cycles n f g ⟶ X.cycles n f' g' :=
  X.liftCycles _ _ rfl _ _
    (X.iCycles n f g ≫ (X.H n).map (homMk₁ (α.app 1) (α.app 2)
      (naturality' α 1 2))) (by
      rw [Category.assoc, X.δ_naturality n _ rfl f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl,
        iCycles_δ_assoc, zero_comp])

@[reassoc]
lemma cyclesMap_i (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g')
    (hβ : β = homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) :
    X.cyclesMap n f g f' g' α ≫ X.iCycles n f' g' =
      X.iCycles n f g ≫ (X.H n).map β := by
  subst hβ
  simp [cyclesMap]

@[simp]
lemma cyclesMap_id :
    X.cyclesMap n f g f g (𝟙 _) = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles n f g),
    X.cyclesMap_i n f g f g (𝟙 _) (𝟙 _) (by cat_disch),
    Functor.map_id, Category.comp_id, Category.id_comp]

@[reassoc]
lemma cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (h : α ≫ α' = α'') :
    X.cyclesMap n f g f' g' α ≫ X.cyclesMap n f' g' f'' g'' α' =
      X.cyclesMap n f g f'' g'' α'' := by
  subst h
  rw [← cancel_mono (X.iCycles n f'' g''), Category.assoc,
    X.cyclesMap_i n f' g' f'' g'' α' _ rfl,
    X.cyclesMap_i_assoc n f g f' g' α _ rfl,
    ← Functor.map_comp]
  symm
  apply X.cyclesMap_i
  cat_disch

/-- The functoriality of `X.opcycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
noncomputable def opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') :
    X.opcycles n f g ⟶ X.opcycles n f' g' :=
  X.descOpcycles (n - 1) n (by lia) _ _
    ((X.H n).map (homMk₁ (by exact α.app 0) (by exact α.app 1)
      (naturality' α 0 1)) ≫ X.pOpcycles n f' g') (by
        rw [← X.δ_naturality_assoc (n - 1) n (by lia) f g f' g'
          (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl,
          δ_pOpcycles, comp_zero])

@[reassoc]
lemma p_opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f')
    (hβ : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)) :
    X.pOpcycles n f g ≫ X.opcyclesMap n f g f' g' α =
      (X.H n).map β ≫ X.pOpcycles n f' g' := by
  subst hβ
  simp [opcyclesMap]

@[simp]
lemma opcyclesMap_id :
    X.opcyclesMap n f g f g (𝟙 _) = 𝟙 _ := by
  rw [← cancel_epi (X.pOpcycles n f g),
    X.p_opcyclesMap n f g f g (𝟙 _) (𝟙 _) (by cat_disch),
    Functor.map_id, Category.comp_id, Category.id_comp]

lemma opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (h : α ≫ α' = α'') :
    X.opcyclesMap n f g f' g' α ≫ X.opcyclesMap n f' g' f'' g'' α' =
      X.opcyclesMap n f g f'' g'' α'' := by
  subst h
  rw [← cancel_epi (X.pOpcycles n f g),
    X.p_opcyclesMap_assoc n f g f' g' α _ rfl,
    X.p_opcyclesMap n f' g' f'' g'' α' _ rfl,
    ← Functor.map_comp_assoc]
  symm
  apply X.p_opcyclesMap
  cat_disch

end

end SpectralObject

end Abelian

end CategoryTheory
