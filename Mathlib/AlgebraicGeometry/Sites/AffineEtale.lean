/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense

/-!
# Affine étale site

In this file we define the small affine étale site of a scheme `S`. The underlying
category is the category of commutative rings `R` equipped with an étale structure
morphism `Spec R ⟶ S`.

## Main results
- `AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv`: The category of sheaves on the
  small affine étale site is equivalent to the category of schemes on the small étale site.
-/

@[expose] public section

universe u v u'

open CategoryTheory Opposite Limits MorphismProperty

-- to be moved
/-- The equivalence of rings between two equals subrings. -/
@[simps!]
def Subring.equivOfEq {R : Type u} [Ring R] {s t : Subring R} (h : s = t) :
    s ≃+* t where
  toEquiv := (Equiv.refl _).subtypeEquiv (by simp [h])
  map_mul' := by simp
  map_add' := by simp

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

section

/-- Construct an object of affine `P`-schemes over `S` by giving a morphism `Spec R ⟶ S`. -/
@[simps! hom left]
def affineOverMk {P : MorphismProperty Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ S) (hf : P f) :
    P.CostructuredArrow ⊤ Scheme.Spec S :=
  .mk ⊤ f hf

/-- The `Spec` functor from affine `P`-schemes over `S` to `P`-schemes over `S` is dense
if `P` is local at the source. -/
instance isCoverDense_toOver_Spec (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (CostructuredArrow.toOver P Scheme.Spec S).IsCoverDense
      (smallGrothendieckTopology P) where
  is_cover U := by
    rw [Scheme.mem_smallGrothendieckTopology]
    let 𝒰 : Cover.{u} (precoverage P) U.left :=
      U.left.affineCover.changeProp
      (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    refine ⟨𝒰, ⟨fun i ↦ inferInstance, fun i ↦ ⟨rfl⟩⟩, ?_, ?_⟩
    · intro i
      exact P.comp_mem _ _ (𝒰.map_prop i) U.prop
    · rintro X f ⟨i⟩
      rw [Sieve.coverByImage]
      refine ⟨⟨affineOverMk (𝒰.f i ≫ U.hom) (P.comp_mem _ _ (𝒰.map_prop i) U.prop), ?_, ?_, ?_⟩⟩
      · exact CostructuredArrow.homMk (𝟙 _) ⟨⟩ rfl
      · exact Over.homMk (𝒰.f i) (by simp) trivial
      · ext
        simp

instance isOneHypercoverDense_toOver_Spec
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    Functor.IsOneHypercoverDense.{u} (CostructuredArrow.toOver P Scheme.Spec S)
    ((CostructuredArrow.toOver P Scheme.Spec S).inducedTopology (smallGrothendieckTopology P))
    (smallGrothendieckTopology P) :=
  Functor.IsOneHypercoverDense.of_hasPullbacks (fun X ↦ by
    let 𝒰 := affineOpenCover X.left
    refine ⟨𝒰.I₀, fun i ↦ affineOverMk (𝒰.f i ≫ X.hom)
      (P.comp_mem _ _ (IsZariskiLocalAtSource.of_isOpenImmersion (𝒰.f i)) X.prop),
      fun i ↦ CostructuredArrow.homMk (𝒰.f i) (by simp), ?_⟩
    rw [Scheme.mem_smallGrothendieckTopology]
    let 𝒱 : Cover (precoverage P) X.left :=
      𝒰.openCover.changeProp (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒱.I₀) : (𝒱.X i).Over S := ⟨𝒰.f i ≫ X.hom⟩
    let : Cover.Over S 𝒱 := { isOver_map _ := by cat_disch }
    refine ⟨𝒱, inferInstance, fun i ↦ P.comp_mem _ _ (𝒱.map_prop i) X.prop, ?_⟩
    rintro _ _ ⟨i⟩
    exact (Sieve.mem_ofArrows_iff ..).2 ⟨i, 𝟙 _, by cat_disch⟩)

variable (S) in
structure FinitelyPresentedOverAffineOpen : Type u where
  U : Opens S
  hU : IsAffineOpen U
  g : ℕ
  r : ℕ
  rel (x : Fin r) : MvPolynomial (Fin g) Γ(S, U)

namespace FinitelyPresentedOverAffineOpen

variable (P : S.FinitelyPresentedOverAffineOpen)

abbrev R : Type u :=
  MvPolynomial (Fin P.g) Γ(S, P.U) ⧸ Ideal.span (Set.range P.rel)

noncomputable abbrev scheme : Scheme.{u} := Spec (.of P.R)

noncomputable def π : P.scheme ⟶ P.U :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ P.hU.isoSpec.inv

noncomputable def a : P.scheme ⟶ S := P.π ≫ P.U.ι

@[reassoc (attr := simp)]
lemma fac : P.π ≫ P.U.ι = P.a := rfl

lemma exists_nhd {X : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (P : S.FinitelyPresentedOverAffineOpen),
      Nonempty (U.toScheme ≅ P.scheme) := by
  obtain ⟨U, V, hx, hUV⟩ :
      ∃ (U : X.affineOpens) (V : S.affineOpens), x ∈ U.val ∧ U ≤ f.base ⁻¹' V := by
    obtain ⟨U, h₁, h₂, _⟩ := exists_isAffineOpen_mem_and_subset (x := f.base x) (U := ⊤) (by simp)
    obtain ⟨V, h₃, h₄, h₅⟩ := exists_isAffineOpen_mem_and_subset (x := x)
      (U := ⟨_, IsOpen.preimage f.continuous U.2⟩) (by simpa)
    exact ⟨⟨V, h₃⟩, ⟨U, h₁⟩, h₄, h₅⟩
  letI := (f.appLE V U hUV).hom.toAlgebra
  obtain ⟨n, φ, h₁, h₂⟩ :=
    (LocallyOfFinitePresentation.finitePresentation_appLE f V.prop U.prop hUV).out
  obtain ⟨r, ρ, hρ⟩ : ∃ (r : ℕ) (γ : Fin r → MvPolynomial (Fin n) Γ(S, V)),
      Ideal.span (Set.range γ) = RingHom.ker φ.toRingHom := by
    obtain ⟨s, hs⟩ := h₂
    exact ⟨s.card, Subtype.val ∘ s.equivFin.symm, by rw [← hs]; simp⟩
  let P : S.FinitelyPresentedOverAffineOpen :=
    { U := V.1
      hU := V.prop
      g := n
      r := r
      rel := ρ }
  let e : P.R ≃+* Γ(X, U.1) :=
    (Ideal.quotEquivOfEq hρ).trans (φ.toRingHom.quotientKerEquivRange.trans
      ((Subring.equivOfEq (RingHom.range_eq_top_of_surjective _ h₁)).trans Subring.topEquiv))
  exact ⟨U, hx, P, ⟨asIso (toSpecΓ U) ≪≫ Scheme.Spec.mapIso U.1.topIso.op.symm ≪≫
    Scheme.Spec.mapIso e.toCommRingCatIso.op⟩⟩

lemma exists_subring
    {A : CommRingCat.{u}} (f : Spec (.of A) ⟶ S) [LocallyOfFinitePresentation f] :
    ∃ (n : ℕ) (P : Fin n → S.FinitelyPresentedOverAffineOpen)
      (R₀ : Subring (∀ i, (P i).R)), Nonempty (A ≅ CommRingCat.of R₀) := by
  choose U hU P e using exists_nhd f
  let iso (x) := (e x).some
  obtain ⟨n, α, hα⟩ : ∃ (n : ℕ) (α : Fin n → Spec (.of A)),
    ⋃ (i : Fin n), (U (α i) : Set (Spec (.of A))) = Set.univ := by
      obtain ⟨s, hs⟩ := CompactSpace.isCompact_univ.elim_finite_subcover _
        (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion_of_mem x (hU x))
      refine ⟨s.card, Subtype.val ∘ (Finset.equivFin s).symm,
        subset_antisymm (by simp) (hs.trans ?_)⟩
      simp only [Function.comp_apply, Set.iUnion_subset_iff]
      exact fun i hi _ _ ↦ Set.mem_iUnion_of_mem ((Finset.equivFin s) ⟨i, hi⟩) (by simpa)
  have (i : Fin n) := (U (α i)).ι
  let β (i : Fin n) : A →+* ((P ∘ α) i).R := (Spec.preimage ((iso (α i)).inv ≫ (U (α i)).ι)).hom
  let φ : A →+* ∀ i, ((P ∘ α) i).R :=
    { toFun a i := β i a
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp
      map_one' := by ext; simp
      map_mul' _ _ := by ext; simp }
  have hφ : Function.Injective φ := by
    suffices ∀ a, φ a = 0 → a = 0 from
      fun a b h ↦ by
        rw [← sub_eq_zero] at h ⊢
        exact this _ (by simpa)
    intro a ha
    replace ha (i : Fin n) : β i a = 0 := congr_fun ha i
    obtain ⟨a, rfl⟩ := (ΓSpecIso A).commRingCatIsoToRingEquiv.surjective a
    simp only [EmbeddingLike.map_eq_zero_iff]
    refine (openCoverOfIsOpenCover _ (U ∘ α) (.mk (by aesop))).ext_elem _ _ (fun i ↦ ?_)
    dsimp at i ⊢
    replace ha : (ΓSpecIso _).hom (((iso (α i)).inv ≫ (U (α i)).ι).appTop a) = 0 := by
      simpa [← ha] using (ConcreteCategory.congr_hom (ΓSpecIso_naturality
        (Spec.preimage ((iso (α i)).inv ≫ (U (α i)).ι))) a)
    apply (asIso (iso (α i)).inv.appTop ≪≫
      ΓSpecIso (.of (P (α i)).R)).commRingCatIsoToRingEquiv.injective
    simpa [-EmbeddingLike.map_eq_zero_iff] using ha
  exact ⟨n, P ∘ α, RingHom.range φ, ⟨RingEquiv.toCommRingCatIso
    (RingEquiv.ofBijective φ.rangeRestrict
      ⟨(Function.Injective.of_comp_iff Subtype.val_injective _).1 hφ,
        RingHom.rangeRestrict_surjective φ⟩)⟩⟩

end FinitelyPresentedOverAffineOpen

lemma essentiallySmall_costructuredArrow_Spec
    (P : MorphismProperty Scheme.{u}) (hP : P ≤ @LocallyOfFinitePresentation) [P.RespectsIso] :
    EssentiallySmall.{u} (P.CostructuredArrow ⊤ Scheme.Spec S) := by
  suffices ∃ (ι : Type u) (R : ι → CommRingCat.{u}),
      ∀ (Z : P.CostructuredArrow ⊤ Scheme.Spec S),
        ∃ (i : ι), Nonempty (R i ≅ Z.left.unop) by
    rw [essentiallySmall_iff_objectPropertyEssentiallySmall_top]
    obtain ⟨ι, R, hR⟩ := this
    let P₀ : ObjectProperty (P.CostructuredArrow ⊤ Scheme.Spec S) :=
      .ofObj (fun (t : Σ (i : ι) (f : Scheme.Spec.obj (Opposite.op (R i)) ⟶ S), PLift (P f)) ↦
        .mk (A := op (R t.1)) _ t.2.1 t.2.2.down)
    refine ObjectProperty.EssentiallySmall.of_le (Q := P₀.isoClosure) (fun Z _ ↦ ?_)
    obtain ⟨i, ⟨e⟩⟩ := hR Z
    refine ⟨_, ⟨i, Spec.map e.inv ≫ Z.hom, ⟨RespectsIso.precomp _ _ _ Z.prop⟩⟩, ⟨?_⟩⟩
    exact MorphismProperty.CostructuredArrow.isoMk e.op (by simp) (by simp)
      (by simp [← Spec.map_comp_assoc, e.inv_hom_id])
  refine ⟨Σ (n : ℕ) (P : Fin n → S.FinitelyPresentedOverAffineOpen), Subring (∀ i, (P i).R),
    fun ⟨n, P, R₀⟩ ↦ .of R₀, fun Z ↦ ?_⟩
  have : LocallyOfFinitePresentation Z.hom := hP _ Z.prop
  obtain ⟨n, P, R₀, ⟨e⟩⟩ := FinitelyPresentedOverAffineOpen.exists_subring Z.hom
  exact ⟨⟨n, P, R₀⟩, ⟨e.symm⟩⟩

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]

instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
    {ι : Type*} [Small.{u} ι] {C : Type*} [Category C] [HasColimitsOfShape (Discrete ι) C]
    (L : C ⥤ Scheme.{u}) [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape (Discrete ι) := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape ?_ ?_ ?_ _
  · intro D _
    exact Sigma.cocone _
  · intro D
    exact coproductIsCoproduct' _
  · intro D _ X s h
    exact IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]

instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out n := by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) :=
      IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete _ _
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

end

/-- The small affine étale site: The category of affine schemes étale over `S`, whose objects are
commutative rings `R` with an étale structure morphism `Spec R ⟶ S`. -/
def AffineEtale (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow @Etale.{u} ⊤ Scheme.Spec.{u} S

namespace AffineEtale

/-- Construct an object of the small affine étale site. -/
@[simps!]
protected def mk {R : CommRingCat.{u}} (f : Spec R ⟶ S) [Etale f] : AffineEtale S :=
  MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›

instance : Category S.AffineEtale :=
  inferInstanceAs <| Category (MorphismProperty.CostructuredArrow _ _ _ _)

/-- The `Spec` functor from the small affine étale site of `S` to the small étale site of `S`. -/
@[simps! obj_left obj_hom map_left]
protected noncomputable def Spec (S : Scheme.{u}) : S.AffineEtale ⥤ S.Etale :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

instance : (AffineEtale.Spec S).Faithful :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

instance : (AffineEtale.Spec S).Full :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

instance : (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).IsCoverDense
    (smallGrothendieckTopology _)

instance : HasPullbacks S.AffineEtale :=
  inferInstanceAs <| HasPullbacks (MorphismProperty.CostructuredArrow _ _ _ _)

variable (S) in
/-- The topology on the small affine étale site is the topology induced by `Spec` from
the small étale site. -/
def topology : GrothendieckTopology S.AffineEtale :=
  (AffineEtale.Spec S).inducedTopology (smallEtaleTopology S)

instance : Functor.IsDenseSubsite (topology S) (S.smallEtaleTopology) (AffineEtale.Spec S) := by
  dsimp [topology]
  infer_instance

instance : Functor.IsOneHypercoverDense.{u} (AffineEtale.Spec S)
    (topology S) (S.smallEtaleTopology) :=
  isOneHypercoverDense_toOver_Spec _

instance : EssentiallySmall.{u} S.AffineEtale :=
  essentiallySmall_costructuredArrow_Spec _ (fun _ _ _ _ ↦ inferInstance)

section

variable {A : Type u'} [Category.{u} A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

instance : HasSheafify (topology S) A := hasSheafifyEssentiallySmallSite.{u} _ _

example : HasSheafify (topology S) (Type u) := by
  infer_instance

example : Abelian (Sheaf (topology S) AddCommGrpCat.{u}) := by
  infer_instance

end

/-- The category of sheafs on the small affine étale site is equivalent to the category of
sheafs on the small étale site. -/
noncomputable def sheafEquiv (A : Type*) [Category A]
    [∀ (X : S.Etaleᵒᵖ), Limits.HasLimitsOfShape (StructuredArrow X (AffineEtale.Spec S).op) A] :
    Sheaf (AffineEtale.topology S) A ≌ Sheaf (smallEtaleTopology S) A :=
  (AffineEtale.Spec S).sheafInducedTopologyEquivOfIsCoverDense _ _

end AlgebraicGeometry.Scheme.AffineEtale
