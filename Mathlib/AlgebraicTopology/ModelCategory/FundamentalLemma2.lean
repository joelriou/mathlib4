/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma1

/-!
# The fundamental lemma of homotopical algebra

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type*) [Category C] [ModelCategory C]

namespace BifibrantObject

def homRel : HomRel (BifibrantObject C) :=
  fun X Y ↦ RightHomotopyRel (X := X.1) (Y := Y.1)

instance : Congruence (homRel C) where
  equivalence := RightHomotopyRel.equivalence _ _
  compLeft p _ _ h := h.precomp p
  compRight p h := h.postcomp p

variable {C} {X Y : BifibrantObject C} (f g : X ⟶ Y)

lemma homRel_iff_rightHomotopyRel :
    homRel C f g ↔ RightHomotopyRel (ι.map f) (ι.map g) := Iff.rfl

lemma homRel_iff_leftHomotopyRel :
    homRel C f g ↔ LeftHomotopyRel (ι.map f) (ι.map g) := by
  rw [homRel_iff_rightHomotopyRel, leftHomotopyRel_iff_rightHomotopyRel]

variable (C) in
abbrev π := Quotient (BifibrantObject.homRel C)

def toπ : BifibrantObject C ⥤ π C := Quotient.functor _

lemma toπ_obj_surjective : Function.Surjective (toπ (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toπ (C := C)) := by dsimp [toπ]; infer_instance

lemma toπ_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) :
    toπ.map f = toπ.map g ↔ homRel C f g :=
  Quotient.functor_map_eq_iff _ _ _

section

variable (E : Type*) [Category E]

lemma inverts_iff_factors (F : BifibrantObject C ⥤ E) :
    (weakEquivalences _).IsInvertedBy F ↔
    ∀ ⦃K L : BifibrantObject C⦄ (f g : K ⟶ L),
      homRel C f g → F.map f = F.map g := by
  constructor
  · intro H K L f g h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good
    have := isCofibrant_of_cofibration P.ι
    let γ : K ⟶ mk P.P := h.h
    let p₀ : mk P.P ⟶ L := P.p₀
    let p₁ : mk P.P ⟶ L := P.p₁
    let s : L ⟶ mk P.P := P.ι
    have : IsIso (F.map s) := H _ (by
      rw [← weakEquivalence_iff, weakEquivalence_iff_ι_map]
      exact inferInstanceAs (WeakEquivalence P.ι))
    simp only [← h.h₀, ← h.h₁]
    change F.map (γ ≫ p₀) = F.map (γ ≫ p₁)
    simp only [Functor.map_comp]
    congr 1
    simp only [← cancel_epi (F.map s), ← Functor.map_comp]
    congr 1
    exact ι.map_injective (P.ι_p₀.trans P.ι_p₁.symm)
  · intro h X Y f hf
    rw [← weakEquivalence_iff, weakEquivalence_iff_ι_map] at hf
    let f' := (bifibrantObjects C).ι.map f
    obtain ⟨g', h₁, h₂⟩ := RightHomotopyClass.exists_homotopy_inverse f'
    refine ⟨F.map g', ?_, ?_⟩
    all_goals
    · rw [← F.map_comp, ← F.map_id]
      apply h
      assumption

def strictUniversalPropertyFixedTargetToπ :
    Localization.StrictUniversalPropertyFixedTarget
    toπ (weakEquivalences (BifibrantObject C)) E where
  inverts := by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end

instance : toπ.IsLocalization (weakEquivalences (BifibrantObject C)) :=
  .mk' _ _ (strictUniversalPropertyFixedTargetToπ _)
    (strictUniversalPropertyFixedTargetToπ _)

instance {X Y : BifibrantObject C} (f : X ⟶ Y) [hf : WeakEquivalence f] :
    IsIso (toπ.map f) :=
  Localization.inverts toπ (weakEquivalences _) f (by rwa [weakEquivalence_iff] at hf)

abbrev ιCofibrantObject : BifibrantObject C ⥤ CofibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_cofibrantObject C)

abbrev ιFibrantObject : BifibrantObject C ⥤ FibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)

instance (X : BifibrantObject C) :
    IsFibrant (BifibrantObject.ιCofibrantObject.obj X).obj := X.2.2

instance (X : BifibrantObject C) :
    IsCofibrant (BifibrantObject.ιFibrantObject.obj X).obj := X.2.1

protected def π.ιCofibrantObject : π C ⥤ CofibrantObject.π C :=
  CategoryTheory.Quotient.lift _
    (ιCofibrantObject ⋙ CofibrantObject.toπ)
    (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ h)

protected def π.ιFibrantObject : π C ⥤ FibrantObject.π C :=
  CategoryTheory.Quotient.lift _
    (ιFibrantObject ⋙ FibrantObject.toπ)
    (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ (by
      simpa [FibrantObject.homRel, leftHomotopyRel_iff_rightHomotopyRel]))

end BifibrantObject

namespace CofibrantObject

variable {C}

lemma exists_bifibrant (X : CofibrantObject C) :
    ∃ (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.ιCofibrantObject.obj Y),
      Cofibration (ι.map i) ∧ WeakEquivalence (ι.map i) := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from X.obj)
  have := isCofibrant_of_cofibration h.i
  have : IsFibrant h.Z := by
    rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, h.i, inferInstanceAs (Cofibration h.i),
    inferInstanceAs (WeakEquivalence h.i)⟩

noncomputable def bifibrantResolutionObj (X : CofibrantObject C) :
    BifibrantObject C :=
  (exists_bifibrant X).choose

noncomputable def iBifibrantResolutionObj (X : CofibrantObject C) :
    X ⟶ BifibrantObject.ιCofibrantObject.obj (bifibrantResolutionObj X) :=
  (exists_bifibrant X).choose_spec.choose

instance (X : CofibrantObject C) :
    Cofibration (ι.map (iBifibrantResolutionObj X)) :=
  (exists_bifibrant X).choose_spec.choose_spec.1

instance (X : CofibrantObject C) :
    WeakEquivalence (ι.map (iBifibrantResolutionObj X)) :=
  (exists_bifibrant X).choose_spec.choose_spec.2

instance (X : BifibrantObject C) :
    IsFibrant (ι.obj (BifibrantObject.ιCofibrantObject.obj X)) := X.2.2

lemma exists_bifibrant_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    ∃ (g : bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂),
      iBifibrantResolutionObj X₁ ≫ (BifibrantObject.ιCofibrantObject.map g) =
      f ≫ iBifibrantResolutionObj X₂ := by
  have sq : CommSq (ι.map (f ≫ iBifibrantResolutionObj X₂))
    (ι.map (iBifibrantResolutionObj X₁)) (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

noncomputable def bifibrantResolutionMap {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose

@[reassoc (attr := simp)]
noncomputable def bifibrantResolutionMap_fac {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    iBifibrantResolutionObj X₁ ≫
      (BifibrantObject.ιCofibrantObject.map (bifibrantResolutionMap f)) =
      f ≫ iBifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose_spec

@[reassoc (attr := simp)]
noncomputable def bifibrantResolutionMap_fac' {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    toπ.map X₁.iBifibrantResolutionObj ≫
      BifibrantObject.π.ιCofibrantObject.map
        (BifibrantObject.toπ.map (bifibrantResolutionMap f)) =
    toπ.map f ≫ toπ.map X₂.iBifibrantResolutionObj :=
  toπ.congr_map (bifibrantResolutionMap_fac f)

lemma bifibrantResolutionObj_hom_ext
    {X : CofibrantObject C} {Y : BifibrantObject.π C} {f g :
      BifibrantObject.toπ.obj (bifibrantResolutionObj X) ⟶ Y}
    (h : CofibrantObject.toπ.map (iBifibrantResolutionObj X) ≫
      BifibrantObject.π.ιCofibrantObject.map f =
      CofibrantObject.toπ.map (iBifibrantResolutionObj X) ≫
        BifibrantObject.π.ιCofibrantObject.map g) :
    f = g := by
  obtain ⟨Y, rfl⟩ := BifibrantObject.toπ_obj_surjective Y
  obtain ⟨f, rfl⟩ := BifibrantObject.toπ.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toπ.map_surjective g
  change toπ.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map f) =
    toπ.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map g) at h
  rw [CofibrantObject.toπ_map_eq_iff,
    CofibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff] at h
  rw [BifibrantObject.toπ_map_eq_iff,
    BifibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff]
  apply (RightHomotopyClass.bijective_precomp_of_cofibration_of_weakEquivalence
    _ (ι.map (iBifibrantResolutionObj X))).1
  simpa only [ObjectProperty.ι_obj, ObjectProperty.ιOfLE_obj_obj, ObjectProperty.ι_map,
    RightHomotopyClass.precomp_mk] using h

@[simps]
noncomputable def bifibrantResolution : CofibrantObject C ⥤ BifibrantObject.π C where
  obj X := BifibrantObject.toπ.obj (bifibrantResolutionObj X)
  map f := BifibrantObject.toπ.map (bifibrantResolutionMap f)
  map_id X := by
    apply bifibrantResolutionObj_hom_ext
    simp only [bifibrantResolutionMap_fac', CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact (Category.comp_id _).symm
  map_comp {X₁ X₂ X₃} f g := by
    apply bifibrantResolutionObj_hom_ext
    simp

noncomputable def π.bifibrantResolution :
    CofibrantObject.π C ⥤ BifibrantObject.π C :=
  CategoryTheory.Quotient.lift _ CofibrantObject.bifibrantResolution (by
    intro X Y f g h
    dsimp
    apply bifibrantResolutionObj_hom_ext
    simp only [bifibrantResolutionMap_fac', toπ_map_eq h])

@[simp]
lemma π.bifibrantResolution_obj (X : CofibrantObject C) :
    π.bifibrantResolution.obj (CofibrantObject.toπ.obj X) =
      BifibrantObject.toπ.obj (bifibrantResolutionObj X) := rfl

@[simp]
lemma π.bifibrantResolution_map {X Y : CofibrantObject C} (f : X ⟶ Y) :
    π.bifibrantResolution.map (CofibrantObject.toπ.map f) =
      BifibrantObject.toπ.map (bifibrantResolutionMap f) := rfl

noncomputable def π.adj.unit :
    𝟭 (π C) ⟶ bifibrantResolution ⋙ BifibrantObject.π.ιCofibrantObject :=
  Quotient.natTransLift _
    { app X := toπ.map (iBifibrantResolutionObj X)
      naturality _ _ f := (bifibrantResolutionMap_fac' f).symm }

lemma π.adj.unit_app (X : CofibrantObject C) :
    π.adj.unit.app (toπ.obj X) =
      toπ.map (iBifibrantResolutionObj X) := rfl

noncomputable def π.adj.counit' :
    𝟭 (BifibrantObject.π C) ⟶ BifibrantObject.π.ιCofibrantObject ⋙ bifibrantResolution :=
  Quotient.natTransLift _
    { app X := BifibrantObject.toπ.map (iBifibrantResolutionObj (.mk X.obj))
      naturality X₁ X₂ f := BifibrantObject.toπ.congr_map
        (bifibrantResolutionMap_fac (f : .mk X₁.obj ⟶ .mk X₂.obj )).symm }

lemma π.adj.counit'_app (X : BifibrantObject C) :
    π.adj.counit'.app (BifibrantObject.toπ.obj X) =
      BifibrantObject.toπ.map (iBifibrantResolutionObj (.mk X.obj)) := rfl

instance (X : BifibrantObject.π C) : IsIso (π.adj.counit'.app X) := by
  obtain ⟨X, rfl⟩ := BifibrantObject.toπ_obj_surjective X
  rw [π.adj.counit'_app]
  have : WeakEquivalence (C := BifibrantObject C) ((mk X.obj).iBifibrantResolutionObj) := by
    rw [weakEquivalence_iff_ι_map]
    change WeakEquivalence (ι.map (CofibrantObject.mk X.obj).iBifibrantResolutionObj)
    infer_instance
  infer_instance

instance : IsIso (π.adj.counit' (C := C)) := NatIso.isIso_of_isIso_app _

noncomputable def π.adj.counitIso :
    BifibrantObject.π.ιCofibrantObject ⋙ bifibrantResolution ≅ 𝟭 (BifibrantObject.π C) :=
  (asIso π.adj.counit').symm

lemma π.adj.counitIso_inv_app (X : BifibrantObject C) :
    π.adj.counitIso.inv.app (BifibrantObject.toπ.obj X) =
      BifibrantObject.toπ.map (iBifibrantResolutionObj (.mk X.obj)) := rfl

noncomputable def π.adj :
    π.bifibrantResolution (C := C) ⊣ BifibrantObject.π.ιCofibrantObject where
  unit := π.adj.unit
  counit := π.adj.counitIso.hom
  left_triangle_components X := by
    obtain ⟨X, rfl⟩ := toπ_obj_surjective X
    rw [← cancel_mono (π.adj.counitIso.inv.app _), Category.assoc, Iso.hom_inv_id_app]
    dsimp
    apply bifibrantResolutionObj_hom_ext
    rw [Category.comp_id, Category.id_comp, π.adj.unit_app,
      bifibrantResolution_map, π.adj.counitIso_inv_app,
      bifibrantResolutionMap_fac']
    rfl
  right_triangle_components X := by
    obtain ⟨X, rfl⟩ := BifibrantObject.toπ_obj_surjective X
    rw [← cancel_mono (BifibrantObject.π.ιCofibrantObject.map (π.adj.counitIso.inv.app _)),
      Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp only [Functor.id_obj, Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp]
    rfl

end CofibrantObject

namespace FibrantObject

variable {C}

lemma exists_bifibrant (X : FibrantObject C) :
    ∃ (Y : BifibrantObject C) (p : BifibrantObject.ιFibrantObject.obj Y ⟶ X),
      Fibration (ι.map p) ∧ WeakEquivalence (ι.map p) := by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
      (initial.to X.obj)
  have := isFibrant_of_fibration h.p
  have : IsCofibrant h.Z := by
    rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, h.p, inferInstanceAs (Fibration h.p),
    inferInstanceAs (WeakEquivalence h.p)⟩

-- TODO: dualize

end FibrantObject

namespace BifibrantObject

@[simps]
def ιCofibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (CofibrantObject C)) where
  functor := ιCofibrantObject
  map _ _ _ h := h

@[simps]
def ιFibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (FibrantObject C)) where
  functor := ιFibrantObject
  map _ _ _ h := h

--instance : (ιCofibrantObjectLocalizerMorphism C).IsLocalizedEquivalence := sorry

end BifibrantObject



end HomotopicalAlgebra
