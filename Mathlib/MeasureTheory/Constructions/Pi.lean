/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Encodable.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Constructions

/-!
# Indexed product measures

In this file we define and prove properties about finite products of measures
(and at some point, countable products of measures).

## Main definition

* `MeasureTheory.Measure.pi`: The product of finitely many σ-finite measures.
  Given `μ : (i : ι) → Measure (α i)` for `[Fintype ι]` it has type `Measure ((i : ι) → α i)`.

To apply Fubini's theorem or Tonelli's theorem along some subset, we recommend using the marginal
construction `MeasureTheory.lmarginal` and (todo) `MeasureTheory.marginal`. This allows you to
apply the theorems without any bookkeeping with measurable equivalences.

## Implementation Notes

We define `MeasureTheory.OuterMeasure.pi`, the product of finitely many outer measures, as the
maximal outer measure `n` with the property that `n (pi univ s) ≤ ∏ i, m i (s i)`,
where `pi univ s` is the product of the sets `{s i | i : ι}`.

We then show that this induces a product of measures, called `MeasureTheory.Measure.pi`.
For a collection of σ-finite measures `μ` and a collection of measurable sets `s` we show that
`Measure.pi μ (pi univ s) = ∏ i, m i (s i)`. To do this, we follow the following steps:
* We know that there is some ordering on `ι`, given by an element of `[Countable ι]`.
* Using this, we have an equivalence `MeasurableEquiv.piMeasurableEquivTProd` between
  `∀ ι, α i` and an iterated product of `α i`, called `List.tprod α l` for some list `l`.
* On this iterated product we can easily define a product measure `MeasureTheory.Measure.tprod`
  by iterating `MeasureTheory.Measure.prod`
* Using the previous two steps we construct `MeasureTheory.Measure.pi'` on `(i : ι) → α i` for
  countable `ι`.
* We know that `MeasureTheory.Measure.pi'` sends products of sets to products of measures, and
  since `MeasureTheory.Measure.pi` is the maximal such measure (or at least, it comes from an outer
  measure which is the maximal such outer measure), we get the same rule for
  `MeasureTheory.Measure.pi`.

## Tags

finitary product measure

-/

noncomputable section

open Function Set MeasureTheory.OuterMeasure Filter MeasurableSpace Encodable

open scoped Topology ENNReal

universe u v

variable {ι ι' : Type*} {α : ι → Type*}

namespace MeasureTheory

variable [Fintype ι] {m : ∀ i, OuterMeasure (α i)}

/-- An upper bound for the measure in a finite product space.
  It is defined to by taking the image of the set under all projections, and taking the product
  of the measures of these images.
  For measurable boxes it is equal to the correct measure. -/
@[simp]
def piPremeasure (m : ∀ i, OuterMeasure (α i)) (s : Set (∀ i, α i)) : ℝ≥0∞ :=
  ∏ i, m i (eval i '' s)

theorem piPremeasure_pi {s : ∀ i, Set (α i)} (hs : (pi univ s).Nonempty) :
    piPremeasure m (pi univ s) = ∏ i, m i (s i) := by simp [hs, piPremeasure]

theorem piPremeasure_pi' {s : ∀ i, Set (α i)} : piPremeasure m (pi univ s) = ∏ i, m i (s i) := by
  cases isEmpty_or_nonempty ι
  · simp [piPremeasure]
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩
    simpa [h, Finset.card_univ, zero_pow Fintype.card_ne_zero, @eq_comm _ (0 : ℝ≥0∞),
      Finset.prod_eq_zero_iff, piPremeasure]
  · simp [h, piPremeasure]

theorem piPremeasure_pi_mono {s t : Set (∀ i, α i)} (h : s ⊆ t) :
    piPremeasure m s ≤ piPremeasure m t :=
  Finset.prod_le_prod' fun _ _ => measure_mono (Set.image_mono h)

theorem piPremeasure_pi_eval {s : Set (∀ i, α i)} :
    piPremeasure m (pi univ fun i => eval i '' s) = piPremeasure m s := by
  simp only [eval, piPremeasure_pi']; rfl

namespace OuterMeasure

/-- `OuterMeasure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{s i | i : ι}`. -/
protected def pi (m : ∀ i, OuterMeasure (α i)) : OuterMeasure (∀ i, α i) :=
  boundedBy (piPremeasure m)

theorem pi_pi_le (m : ∀ i, OuterMeasure (α i)) (s : ∀ i, Set (α i)) :
    OuterMeasure.pi m (pi univ s) ≤ ∏ i, m i (s i) := by
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · simp [h]
  exact (boundedBy_le _).trans_eq (piPremeasure_pi h)

theorem le_pi {m : ∀ i, OuterMeasure (α i)} {n : OuterMeasure (∀ i, α i)} :
    n ≤ OuterMeasure.pi m ↔
      ∀ s : ∀ i, Set (α i), (pi univ s).Nonempty → n (pi univ s) ≤ ∏ i, m i (s i) := by
  rw [OuterMeasure.pi, le_boundedBy']; constructor
  · intro h s hs; refine (h _ hs).trans_eq (piPremeasure_pi hs)
  · intro h s hs; refine le_trans (n.mono <| subset_pi_eval_image univ s) (h _ ?_)
    simp [univ_pi_nonempty_iff, hs]

end OuterMeasure

namespace Measure

variable [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))

section Tprod

open List

variable {δ : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)]

-- for some reason the equation compiler doesn't like this definition
/-- A product of measures in `tprod α l`. -/
protected def tprod (l : List δ) (μ : ∀ i, Measure (X i)) : Measure (TProd X l) := by
  induction l with
  | nil => exact dirac PUnit.unit
  | cons i l ih => exact (μ i).prod (α := X i) ih

@[simp]
theorem tprod_nil (μ : ∀ i, Measure (X i)) : Measure.tprod [] μ = dirac PUnit.unit :=
  rfl

@[simp]
theorem tprod_cons (i : δ) (l : List δ) (μ : ∀ i, Measure (X i)) :
    Measure.tprod (i :: l) μ = (μ i).prod (Measure.tprod l μ) :=
  rfl

instance sigmaFinite_tprod (l : List δ) (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] :
    SigmaFinite (Measure.tprod l μ) := by
  induction l with
  | nil => rw [tprod_nil]; infer_instance
  | cons i l ih => rw [tprod_cons]; exact @prod.instSigmaFinite _ _ _ _ _ _ _ ih

theorem tprod_tprod (l : List δ) (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (s : ∀ i, Set (X i)) :
    Measure.tprod l μ (Set.tprod l s) = (l.map fun i => (μ i) (s i)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [tprod_cons, Set.tprod]
    dsimp only [foldr_cons, map_cons, prod_cons]
    rw [prod_prod, ih]

end Tprod

section Encodable

open List MeasurableEquiv

variable [Encodable ι]

open scoped Classical in
/-- The product measure on an encodable finite type, defined by mapping `Measure.tprod` along the
  equivalence `MeasurableEquiv.piMeasurableEquivTProd`.
  The definition `MeasureTheory.Measure.pi` should be used instead of this one. -/
def pi' : Measure (∀ i, α i) :=
  Measure.map (TProd.elim' mem_sortedUniv) (Measure.tprod (sortedUniv ι) μ)

theorem pi'_pi [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) :
    pi' μ (pi univ s) = ∏ i, μ i (s i) := by
  classical
  rw [pi']
  rw [← MeasurableEquiv.piMeasurableEquivTProd_symm_apply, MeasurableEquiv.map_apply,
    MeasurableEquiv.piMeasurableEquivTProd_symm_apply, elim_preimage_pi, tprod_tprod _ μ, ←
    List.prod_toFinset, sortedUniv_toFinset] <;>
  exact sortedUniv_nodup ι

end Encodable

theorem pi_caratheodory :
    MeasurableSpace.pi ≤ (OuterMeasure.pi fun i => (μ i).toOuterMeasure).caratheodory := by
  refine iSup_le ?_
  intro i s hs
  rw [MeasurableSpace.comap] at hs
  rcases hs with ⟨s, hs, rfl⟩
  apply boundedBy_caratheodory
  intro t
  simp_rw [piPremeasure]
  refine Finset.prod_add_prod_le' (Finset.mem_univ i) ?_ ?_ ?_
  · simp [image_inter_preimage, image_diff_preimage, measure_inter_add_diff _ hs, le_refl]
  · rintro j - _; gcongr; apply inter_subset_left
  · rintro j - _; gcongr; apply diff_subset

/-- `Measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be measure corresponding to `MeasureTheory.OuterMeasure.pi`. -/
protected irreducible_def pi : Measure (∀ i, α i) :=
  toMeasure (OuterMeasure.pi fun i => (μ i).toOuterMeasure) (pi_caratheodory μ)

instance _root_.MeasureTheory.MeasureSpace.pi {α : ι → Type*} [∀ i, MeasureSpace (α i)] :
    MeasureSpace (∀ i, α i) :=
  ⟨Measure.pi fun _ => volume⟩

theorem pi_pi_aux [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) (hs : ∀ i, MeasurableSet (s i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  refine le_antisymm ?_ ?_
  · rw [Measure.pi, toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    apply OuterMeasure.pi_pi_le
  · haveI : Encodable ι := Fintype.toEncodable ι
    simp_rw [← pi'_pi μ s, Measure.pi,
      toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    suffices (pi' μ).toOuterMeasure ≤ OuterMeasure.pi fun i => (μ i).toOuterMeasure by exact this _
    clear hs s
    rw [OuterMeasure.le_pi]
    intro s _
    exact (pi'_pi μ s).le

variable {μ}

/-- `Measure.pi μ` has finite spanning sets in rectangles of finite spanning sets. -/
def FiniteSpanningSetsIn.pi {C : ∀ i, Set (Set (α i))}
    (hμ : ∀ i, (μ i).FiniteSpanningSetsIn (C i)) :
    (Measure.pi μ).FiniteSpanningSetsIn (pi univ '' pi univ C) := by
  haveI := fun i => (hμ i).sigmaFinite
  haveI := Fintype.toEncodable ι
  refine ⟨fun n => Set.pi univ fun i => (hμ i).set ((@decode (ι → ℕ) _ n).iget i),
    fun n => ?_, fun n => ?_, ?_⟩ <;>
  -- TODO (kmill) If this let comes before the refine, while the noncomputability checker
  -- correctly sees this definition is computable, the Lean VM fails to see the binding is
  -- computationally irrelevant. The `noncomputable section` doesn't help because all it does
  -- is insert `noncomputable` for you when necessary.
  let e : ℕ → ι → ℕ := fun n => (@decode (ι → ℕ) _ n).iget
  · refine mem_image_of_mem _ fun i _ => (hμ i).set_mem _
  · calc
      Measure.pi μ (Set.pi univ fun i => (hμ i).set (e n i)) ≤
          Measure.pi μ (Set.pi univ fun i => toMeasurable (μ i) ((hμ i).set (e n i))) :=
        measure_mono (pi_mono fun i _ => subset_toMeasurable _ _)
      _ = ∏ i, μ i (toMeasurable (μ i) ((hμ i).set (e n i))) :=
        (pi_pi_aux μ _ fun i => measurableSet_toMeasurable _ _)
      _ = ∏ i, μ i ((hμ i).set (e n i)) := by simp only [measure_toMeasurable]
      _ < ∞ := ENNReal.prod_lt_top fun i _ => (hμ i).finite _
  · simp_rw [(surjective_decode_iget (ι → ℕ)).iUnion_comp fun x =>
        Set.pi univ fun i => (hμ i).set (x i),
      iUnion_univ_pi fun i => (hμ i).set, (hμ _).spanning, Set.pi_univ]

/-- A measure on a finite product space equals the product measure if they are equal on rectangles
  with as sides sets that generate the corresponding σ-algebras. -/
theorem pi_eq_generateFrom {C : ∀ i, Set (Set (α i))}
    (hC : ∀ i, generateFrom (C i) = by apply_assumption) (h2C : ∀ i, IsPiSystem (C i))
    (h3C : ∀ i, (μ i).FiniteSpanningSetsIn (C i)) {μν : Measure (∀ i, α i)}
    (h₁ : ∀ s : ∀ i, Set (α i), (∀ i, s i ∈ C i) → μν (pi univ s) = ∏ i, μ i (s i)) :
    Measure.pi μ = μν := by
  have h4C : ∀ (i) (s : Set (α i)), s ∈ C i → MeasurableSet s := by
    intro i s hs; rw [← hC]; exact measurableSet_generateFrom hs
  refine
    (FiniteSpanningSetsIn.pi h3C).ext
      (generateFrom_eq_pi hC fun i => (h3C i).isCountablySpanning).symm (IsPiSystem.pi h2C) ?_
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_univ_pi] at hs
  haveI := fun i => (h3C i).sigmaFinite
  simp_rw [h₁ s hs, pi_pi_aux μ s fun i => h4C i _ (hs i)]

/-- A measure on a finite product space equals the product measure if they are equal on
  rectangles. -/
theorem pi_eq [∀ i, SigmaFinite (μ i)] {μ' : Measure (∀ i, α i)}
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) → μ' (pi univ s) = ∏ i, μ i (s i)) :
    Measure.pi μ = μ' :=
  pi_eq_generateFrom (fun _ => generateFrom_measurableSet) (fun _ => isPiSystem_measurableSet)
    (fun i => (μ i).toFiniteSpanningSetsIn) h

variable (μ)

theorem pi'_eq_pi [Encodable ι] [∀ i, SigmaFinite (μ i)] : pi' μ = Measure.pi μ :=
  Eq.symm <| pi_eq fun s _ => pi'_pi μ s

@[simp]
theorem pi_pi [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  haveI : Encodable ι := Fintype.toEncodable ι
  rw [← pi'_eq_pi, pi'_pi]

nonrec theorem pi_univ [∀ i, SigmaFinite (μ i)] : Measure.pi μ univ = ∏ i, μ i univ := by
  rw [← pi_univ, pi_pi μ]

instance pi.instIsFiniteMeasure [∀ i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (Measure.pi μ) :=
  ⟨Measure.pi_univ μ ▸ ENNReal.prod_lt_top (fun i _ ↦ measure_lt_top (μ i) _)⟩

instance {α : ι → Type*} [∀ i, MeasureSpace (α i)] [∀ i, IsFiniteMeasure (volume : Measure (α i))] :
    IsFiniteMeasure (volume : Measure (∀ i, α i)) :=
  pi.instIsFiniteMeasure _

instance pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) :=
  ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

instance {α : ι → Type*} [∀ i, MeasureSpace (α i)]
    [∀ i, IsProbabilityMeasure (volume : Measure (α i))] :
    IsProbabilityMeasure (volume : Measure (∀ i, α i)) :=
  pi.instIsProbabilityMeasure _

variable [∀ i, SigmaFinite (μ i)]

theorem pi_ball [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 < r) :
    Measure.pi μ (Metric.ball x r) = ∏ i, μ i (Metric.ball (x i) r) := by rw [ball_pi _ hr, pi_pi]

theorem pi_closedBall [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 ≤ r) :
    Measure.pi μ (Metric.closedBall x r) = ∏ i, μ i (Metric.closedBall (x i) r) := by
  rw [closedBall_pi _ hr, pi_pi]

instance pi.sigmaFinite : SigmaFinite (Measure.pi μ) :=
  (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).sigmaFinite

instance {α : ι → Type*} [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] :
    SigmaFinite (volume : Measure (∀ i, α i)) :=
  pi.sigmaFinite _

theorem pi_of_empty {α : Type*} [Fintype α] [IsEmpty α] {β : α → Type*}
    {m : ∀ a, MeasurableSpace (β a)} (μ : ∀ a : α, Measure (β a)) (x : ∀ a, β a := isEmptyElim) :
    Measure.pi μ = dirac x := by
  haveI : ∀ a, SigmaFinite (μ a) := isEmptyElim
  refine pi_eq fun s _ => ?_
  rw [Fintype.prod_empty, dirac_apply_of_mem]
  exact isEmptyElim (α := α)

lemma volume_pi_eq_dirac {ι : Type*} [Fintype ι] [IsEmpty ι]
    {α : ι → Type*} [∀ i, MeasureSpace (α i)] (x : ∀ a, α a := isEmptyElim) :
    (volume : Measure (∀ i, α i)) = Measure.dirac x :=
  Measure.pi_of_empty _ _

@[simp]
theorem pi_empty_univ {α : Type*} [Fintype α] [IsEmpty α] {β : α → Type*}
    {m : ∀ α, MeasurableSpace (β α)} (μ : ∀ a : α, Measure (β a)) :
    Measure.pi μ (Set.univ) = 1 := by
  rw [pi_of_empty, measure_univ]

theorem pi_eval_preimage_null {i : ι} {s : Set (α i)} (hs : μ i s = 0) :
    Measure.pi μ (eval i ⁻¹' s) = 0 := by
  classical
  -- WLOG, `s` is measurable
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, _, hμt⟩
  suffices Measure.pi μ (eval i ⁻¹' t) = 0 from measure_mono_null (preimage_mono hst) this
  -- Now rewrite it as `Set.pi`, and apply `pi_pi`
  rw [← univ_pi_update_univ, pi_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hμt]

theorem quasiMeasurePreserving_eval (i : ι) :
    QuasiMeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  classical
  refine ⟨by fun_prop, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply (by fun_prop) hs, pi_eval_preimage_null μ h2s]

lemma pi_map_eval [DecidableEq ι] (i : ι) :
     (Measure.pi μ).map (Function.eval i) = (∏ j ∈ Finset.univ.erase i, μ j Set.univ) • (μ i) := by
   ext s hs
   classical
   rw [Measure.map_apply (measurable_pi_apply i) hs, ← Set.univ_pi_update_univ, Measure.pi_pi,
     Measure.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (a := i) (by simp)]
   congrm ?_ * ?_
   swap; · simp
   refine Finset.prod_congr rfl fun j hj ↦ ?_
   simp [Function.update, Finset.ne_of_mem_erase hj]

lemma _root_.MeasureTheory.measurePreserving_eval [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  classical
  rw [Measure.pi_map_eval, Finset.prod_eq_one, one_smul]
  exact fun _ _ ↦ measure_univ

theorem pi_hyperplane (i : ι) [NoAtoms (μ i)] (x : α i) :
    Measure.pi μ { f : ∀ i, α i | f i = x } = 0 :=
  show Measure.pi μ (eval i ⁻¹' {x}) = 0 from pi_eval_preimage_null _ (measure_singleton x)

theorem ae_eval_ne (i : ι) [NoAtoms (μ i)] (x : α i) : ∀ᵐ y : ∀ i, α i ∂Measure.pi μ, y i ≠ x :=
  compl_mem_ae_iff.2 (pi_hyperplane μ i x)

theorem restrict_pi_pi (s : (i : ι) → Set (α i)) :
    (Measure.pi μ).restrict (Set.univ.pi fun i ↦ s i) = .pi (fun i ↦ (μ i).restrict (s i)) := by
  refine (pi_eq fun _ h ↦ ?_).symm
  simp_rw [restrict_apply (MeasurableSet.univ_pi h), restrict_apply (h _),
    ← Set.pi_inter_distrib, pi_pi]

variable {μ}

theorem tendsto_eval_ae_ae {i : ι} : Tendsto (eval i) (ae (Measure.pi μ)) (ae (μ i)) := fun _ hs =>
  pi_eval_preimage_null μ hs

theorem ae_pi_le_pi : ae (Measure.pi μ) ≤ Filter.pi fun i => ae (μ i) :=
  le_iInf fun _ => tendsto_eval_ae_ae.le_comap

theorem ae_eq_pi {β : ι → Type*} {f f' : ∀ i, α i → β i} (h : ∀ i, f i =ᵐ[μ i] f' i) :
    (fun (x : ∀ i, α i) i => f i (x i)) =ᵐ[Measure.pi μ] fun x i => f' i (x i) :=
  (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => funext hx

theorem ae_le_pi {β : ι → Type*} [∀ i, Preorder (β i)] {f f' : ∀ i, α i → β i}
    (h : ∀ i, f i ≤ᵐ[μ i] f' i) :
    (fun (x : ∀ i, α i) i => f i (x i)) ≤ᵐ[Measure.pi μ] fun x i => f' i (x i) :=
  (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => hx

theorem ae_le_set_pi {I : Set ι} {s t : ∀ i, Set (α i)} (h : ∀ i ∈ I, s i ≤ᵐ[μ i] t i) :
    Set.pi I s ≤ᵐ[Measure.pi μ] Set.pi I t :=
  ((eventually_all_finite I.toFinite).2 fun i hi => tendsto_eval_ae_ae.eventually (h i hi)).mono
    fun _ hst hx i hi => hst i hi <| hx i hi

theorem ae_eq_set_pi {I : Set ι} {s t : ∀ i, Set (α i)} (h : ∀ i ∈ I, s i =ᵐ[μ i] t i) :
    Set.pi I s =ᵐ[Measure.pi μ] Set.pi I t :=
  (ae_le_set_pi fun i hi => (h i hi).le).antisymm (ae_le_set_pi fun i hi => (h i hi).symm.le)

lemma pi_map_piCongrLeft [hι' : Fintype ι'] (e : ι ≃ ι') {β : ι' → Type*}
    [∀ i, MeasurableSpace (β i)] (μ : (i : ι') → Measure (β i)) [∀ i, SigmaFinite (μ i)] :
    (Measure.pi fun i ↦ μ (e i)).map (MeasurableEquiv.piCongrLeft (fun i ↦ β i) e)
      = Measure.pi μ := by
  let e_meas : ((b : ι) → β (e b)) ≃ᵐ ((a : ι') → β a) :=
    MeasurableEquiv.piCongrLeft (fun i ↦ β i) e
  refine Measure.pi_eq (fun s _ ↦ ?_) |>.symm
  rw [e_meas.measurableEmbedding.map_apply]
  let s' : (i : ι) → Set (β (e i)) := fun i ↦ s (e i)
  have : e_meas ⁻¹' pi univ s = pi univ s' := by
    ext x
    simp only [mem_preimage, Set.mem_pi, mem_univ, forall_true_left, s']
    refine (e.forall_congr ?_).symm
    intro i
    rw [MeasurableEquiv.piCongrLeft_apply_apply e x i]
  rw [this, pi_pi, Finset.prod_equiv e.symm]
  · simp only [Finset.mem_univ, implies_true]
  intro i _
  simp only [s']
  congr
  all_goals rw [e.apply_symm_apply]

lemma pi_map_piOptionEquivProd {β : Option ι → Type*} [∀ i, MeasurableSpace (β i)]
    (μ : (i : Option ι) → Measure (β i)) [∀ (i : Option ι), SigmaFinite (μ i)] :
    ((Measure.pi fun i ↦ μ (some i)).prod (μ none)).map
      (MeasurableEquiv.piOptionEquivProd β).symm = Measure.pi μ := by
  refine pi_eq (fun s _ ↦ ?_) |>.symm
  let e_meas : ((i : ι) → β (some i)) × β none ≃ᵐ ((i : Option ι) → β i) :=
    MeasurableEquiv.piOptionEquivProd β |>.symm
  have me := MeasurableEquiv.measurableEmbedding e_meas
  have : e_meas ⁻¹' pi univ s = (pi univ (fun i ↦ s (some i))) ×ˢ (s none) := by
    ext x
    simp only [mem_preimage, Set.mem_pi, mem_univ, forall_true_left, mem_prod]
    refine ⟨by tauto, fun _ i ↦ ?_⟩
    rcases i <;> tauto
  simp only [e_meas, me.map_apply, univ_option, Finset.prod_insertNone, this,
    prod_prod, pi_pi, mul_comm]

section Intervals

variable [∀ i, PartialOrder (α i)] [∀ i, NoAtoms (μ i)]

theorem pi_Iio_ae_eq_pi_Iic {s : Set ι} {f : ∀ i, α i} :
    (pi s fun i => Iio (f i)) =ᵐ[Measure.pi μ] pi s fun i => Iic (f i) :=
  ae_eq_set_pi fun _ _ => Iio_ae_eq_Iic

theorem pi_Ioi_ae_eq_pi_Ici {s : Set ι} {f : ∀ i, α i} :
    (pi s fun i => Ioi (f i)) =ᵐ[Measure.pi μ] pi s fun i => Ici (f i) :=
  ae_eq_set_pi fun _ _ => Ioi_ae_eq_Ici

theorem univ_pi_Iio_ae_eq_Iic {f : ∀ i, α i} :
    (pi univ fun i => Iio (f i)) =ᵐ[Measure.pi μ] Iic f := by
  rw [← pi_univ_Iic]; exact pi_Iio_ae_eq_pi_Iic

theorem univ_pi_Ioi_ae_eq_Ici {f : ∀ i, α i} :
    (pi univ fun i => Ioi (f i)) =ᵐ[Measure.pi μ] Ici f := by
  rw [← pi_univ_Ici]; exact pi_Ioi_ae_eq_pi_Ici

theorem pi_Ioo_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioo_ae_eq_Icc

theorem pi_Ioo_ae_eq_pi_Ioc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Ioc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioo_ae_eq_Ioc

theorem univ_pi_Ioo_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ioo_ae_eq_pi_Icc

theorem pi_Ioc_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioc_ae_eq_Icc

theorem univ_pi_Ioc_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ioc_ae_eq_pi_Icc

theorem pi_Ico_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc

theorem univ_pi_Ico_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ico_ae_eq_pi_Icc

end Intervals

/-- If one of the measures `μ i` has no atoms, them `Measure.pi µ`
has no atoms. The instance below assumes that all `μ i` have no atoms. -/
theorem pi_noAtoms (i : ι) [NoAtoms (μ i)] : NoAtoms (Measure.pi μ) :=
  ⟨fun x => flip measure_mono_null (pi_hyperplane μ i (x i)) (singleton_subset_iff.2 rfl)⟩

instance pi_noAtoms' [h : Nonempty ι] [∀ i, NoAtoms (μ i)] : NoAtoms (Measure.pi μ) :=
  h.elim fun i => pi_noAtoms i

instance {α : ι → Type*} [Nonempty ι] [∀ i, MeasureSpace (α i)]
    [∀ i, SigmaFinite (volume : Measure (α i))] [∀ i, NoAtoms (volume : Measure (α i))] :
    NoAtoms (volume : Measure (∀ i, α i)) :=
  pi_noAtoms'

instance pi.isLocallyFiniteMeasure
    [∀ i, TopologicalSpace (α i)] [∀ i, IsLocallyFiniteMeasure (μ i)] :
    IsLocallyFiniteMeasure (Measure.pi μ) := by
  refine ⟨fun x => ?_⟩
  choose s hxs ho hμ using fun i => (μ i).exists_isOpen_measure_lt_top (x i)
  refine ⟨pi univ s, set_pi_mem_nhds finite_univ fun i _ => IsOpen.mem_nhds (ho i) (hxs i), ?_⟩
  rw [pi_pi]
  exact ENNReal.prod_lt_top fun i _ => hμ i

instance {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasureSpace (X i)]
    [∀ i, SigmaFinite (volume : Measure (X i))]
    [∀ i, IsLocallyFiniteMeasure (volume : Measure (X i))] :
    IsLocallyFiniteMeasure (volume : Measure (∀ i, X i)) :=
  pi.isLocallyFiniteMeasure

variable (μ)

@[to_additive]
instance pi.isMulLeftInvariant [∀ i, Group (α i)] [∀ i, MeasurableMul (α i)]
    [∀ i, IsMulLeftInvariant (μ i)] : IsMulLeftInvariant (Measure.pi μ) := by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_const_mul _) (MeasurableSet.univ_pi hs),
    show (v * ·) ⁻¹' univ.pi s = univ.pi fun i => (v i * ·) ⁻¹' s i by rfl, pi_pi]
  simp_rw [measure_preimage_mul]

@[to_additive]
instance {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasureSpace (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, SigmaFinite (volume : Measure (G i))] [∀ i, IsMulLeftInvariant (volume : Measure (G i))] :
    IsMulLeftInvariant (volume : Measure (∀ i, G i)) :=
  pi.isMulLeftInvariant _

@[to_additive]
instance pi.isMulRightInvariant [∀ i, Group (α i)] [∀ i, MeasurableMul (α i)]
    [∀ i, IsMulRightInvariant (μ i)] : IsMulRightInvariant (Measure.pi μ) := by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_mul_const _) (MeasurableSet.univ_pi hs),
    show (· * v) ⁻¹' univ.pi s = univ.pi fun i => (· * v i) ⁻¹' s i by rfl, pi_pi]
  simp_rw [measure_preimage_mul_right]

@[to_additive]
instance {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasureSpace (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, SigmaFinite (volume : Measure (G i))]
    [∀ i, IsMulRightInvariant (volume : Measure (G i))] :
    IsMulRightInvariant (volume : Measure (∀ i, G i)) :=
  pi.isMulRightInvariant _

@[to_additive]
instance pi.isInvInvariant [∀ i, Group (α i)] [∀ i, MeasurableInv (α i)]
    [∀ i, IsInvInvariant (μ i)] : IsInvInvariant (Measure.pi μ) := by
  refine ⟨(Measure.pi_eq fun s hs => ?_).symm⟩
  have A : Inv.inv ⁻¹' pi univ s = Set.pi univ fun i => Inv.inv ⁻¹' s i := by ext; simp
  simp_rw [Measure.inv, Measure.map_apply measurable_inv (MeasurableSet.univ_pi hs), A, pi_pi,
    measure_preimage_inv]

@[to_additive]
instance {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasureSpace (G i)] [∀ i, MeasurableInv (G i)]
    [∀ i, SigmaFinite (volume : Measure (G i))] [∀ i, IsInvInvariant (volume : Measure (G i))] :
    IsInvInvariant (volume : Measure (∀ i, G i)) :=
  pi.isInvInvariant _

instance pi.isOpenPosMeasure [∀ i, TopologicalSpace (α i)] [∀ i, IsOpenPosMeasure (μ i)] :
    IsOpenPosMeasure (MeasureTheory.Measure.pi μ) := by
  constructor
  rintro U U_open ⟨a, ha⟩
  obtain ⟨s, ⟨hs, hsU⟩⟩ := isOpen_pi_iff'.1 U_open a ha
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsU))
  simp only [pi_pi]
  rw [CanonicallyOrderedAdd.prod_pos]
  intro i _
  apply (hs i).1.measure_pos (μ i) ⟨a i, (hs i).2⟩

instance {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasureSpace (X i)]
    [∀ i, IsOpenPosMeasure (volume : Measure (X i))] [∀ i, SigmaFinite (volume : Measure (X i))] :
    IsOpenPosMeasure (volume : Measure (∀ i, X i)) :=
  pi.isOpenPosMeasure _

instance pi.isFiniteMeasureOnCompacts [∀ i, TopologicalSpace (α i)]
    [∀ i, IsFiniteMeasureOnCompacts (μ i)] :
    IsFiniteMeasureOnCompacts (MeasureTheory.Measure.pi μ) := by
  constructor
  intro K hK
  suffices Measure.pi μ (Set.univ.pi fun j => Function.eval j '' K) < ⊤ by
    exact lt_of_le_of_lt (measure_mono (univ.subset_pi_eval_image K)) this
  rw [Measure.pi_pi]
  refine WithTop.prod_lt_top ?_
  exact fun i _ => IsCompact.measure_lt_top (IsCompact.image hK (continuous_apply i))

instance {X : ι → Type*} [∀ i, MeasureSpace (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, SigmaFinite (volume : Measure (X i))]
    [∀ i, IsFiniteMeasureOnCompacts (volume : Measure (X i))] :
    IsFiniteMeasureOnCompacts (volume : Measure (∀ i, X i)) :=
  pi.isFiniteMeasureOnCompacts _

@[to_additive]
instance pi.isHaarMeasure [∀ i, Group (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, IsHaarMeasure (μ i)] [∀ i, MeasurableMul (α i)] : IsHaarMeasure (Measure.pi μ) where

@[to_additive]
instance {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasureSpace (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, SigmaFinite (volume : Measure (G i))]
    [∀ i, IsHaarMeasure (volume : Measure (G i))] : IsHaarMeasure (volume : Measure (∀ i, G i)) :=
  pi.isHaarMeasure _

end Measure

theorem volume_pi [∀ i, MeasureSpace (α i)] :
    (volume : Measure (∀ i, α i)) = Measure.pi fun _ => volume :=
  rfl

theorem volume_pi_pi [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    (s : ∀ i, Set (α i)) : volume (pi univ s) = ∏ i, volume (s i) :=
  Measure.pi_pi (fun _ => volume) s

theorem volume_pi_ball [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x r) = ∏ i, volume (Metric.ball (x i) r) :=
  Measure.pi_ball _ _ hr

theorem volume_pi_closedBall [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall x r) = ∏ i, volume (Metric.closedBall (x i) r) :=
  Measure.pi_closedBall _ _ hr

open Measure

/-- We intentionally restrict this only to the nondependent function space, since type-class
inference cannot find an instance for `ι → ℝ` when this is stated for dependent function spaces. -/
@[to_additive "We intentionally restrict this only to the nondependent function space, since
type-class inference cannot find an instance for `ι → ℝ` when this is stated for dependent function
spaces."]
instance Pi.isMulLeftInvariant_volume {α} [Group α] [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] [MeasurableMul α] [IsMulLeftInvariant (volume : Measure α)] :
    IsMulLeftInvariant (volume : Measure (ι → α)) :=
  pi.isMulLeftInvariant _

/-- We intentionally restrict this only to the nondependent function space, since type-class
inference cannot find an instance for `ι → ℝ` when this is stated for dependent function spaces. -/
@[to_additive "We intentionally restrict this only to the nondependent function space, since
type-class inference cannot find an instance for `ι → ℝ` when this is stated for dependent function
spaces."]
instance Pi.isInvInvariant_volume {α} [Group α] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    [MeasurableInv α] [IsInvInvariant (volume : Measure α)] :
    IsInvInvariant (volume : Measure (ι → α)) :=
  pi.isInvInvariant _

/-!
### Measure preserving equivalences

In this section we prove that some measurable equivalences (e.g., between `Fin 1 → α` and `α` or
between `Fin 2 → α` and `α × α`) preserve measure or volume. These lemmas can be used to prove that
measures of corresponding sets (images or preimages) have equal measures and functions `f ∘ e` and
`f` have equal integrals, see lemmas in the `MeasureTheory.measurePreserving` prefix.
-/


section MeasurePreserving

variable {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
variable [Fintype ι']

theorem measurePreserving_piEquivPiSubtypeProd (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) (Measure.pi μ)
      ((Measure.pi fun i : Subtype p => μ i).prod (Measure.pi fun i => μ i)) := by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd α p).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  have : e ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i :=
    Equiv.preimage_piEquivPiSubtypeProd_symm_pi p s
  rw [e.map_apply, this, prod_prod, pi_pi, pi_pi]
  exact Fintype.prod_subtype_mul_prod_subtype p fun i => μ i (s i)

theorem volume_preserving_piEquivPiSubtypeProd (α : ι → Type*)
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] (p : ι → Prop)
    [DecidablePred p] : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) :=
  measurePreserving_piEquivPiSubtypeProd (fun _ => volume) p

theorem measurePreserving_piCongrLeft (f : ι' ≃ ι) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f)
      (Measure.pi fun i' => μ (f i')) (Measure.pi μ) where
  measurable := (MeasurableEquiv.piCongrLeft α f).measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_piCongrLeft f,
      Equiv.piCongrLeft_preimage_univ_pi, pi_pi _ _, f.prod_comp (fun i => μ i (s i))]

theorem volume_measurePreserving_piCongrLeft (α : ι → Type*) (f : ι' ≃ ι)
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f) volume volume :=
  measurePreserving_piCongrLeft (fun _ ↦ volume) f

theorem measurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α]
    [MeasurableSpace β] [Fintype γ] (μ : γ → Measure α) (ν : γ → Measure β) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β γ)
      (.pi fun i ↦ (μ i).prod (ν i))
        ((Measure.pi fun i ↦ μ i).prod (Measure.pi fun i ↦ ν i)) where
  measurable := (MeasurableEquiv.arrowProdEquivProdArrow α β γ).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply, MeasurableEquiv.arrowProdEquivProdArrow,
        MeasurableEquiv.coe_mk]
      rw [show Equiv.arrowProdEquivProdArrow γ _ _ ⁻¹' (univ.pi s ×ˢ univ.pi t) =
          (univ.pi fun i ↦ s i ×ˢ t i) by
          ext; simp [Set.mem_pi, forall_and]]
      simp_rw [pi_pi, prod_prod, pi_pi, Finset.prod_mul_distrib]

theorem volume_measurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasureSpace α]
    [MeasureSpace β] [Fintype γ] [SigmaFinite (volume : Measure α)]
    [SigmaFinite (volume : Measure β)] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β γ) :=
  measurePreserving_arrowProdEquivProdArrow α β γ (fun _ ↦ volume) (fun _ ↦ volume)

theorem measurePreserving_sumPiEquivProdPi_symm {X : ι ⊕ ι' → Type*}
    {m : ∀ i, MeasurableSpace (X i)} (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm
      ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) (Measure.pi μ) where
  measurable := (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    simp_rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi_symm_preimage_univ_pi, Measure.prod_prod, Measure.pi_pi,
      Fintype.prod_sum_type]

theorem volume_measurePreserving_sumPiEquivProdPi_symm (X : ι ⊕ ι' → Type*)
    [∀ i, MeasureSpace (X i)] [∀ i, SigmaFinite (volume : Measure (X i))] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm volume volume :=
  measurePreserving_sumPiEquivProdPi_symm (fun _ ↦ volume)

theorem measurePreserving_sumPiEquivProdPi {X : ι ⊕ ι' → Type*} {_m : ∀ i, MeasurableSpace (X i)}
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X)
      (Measure.pi μ) ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) :=
  measurePreserving_sumPiEquivProdPi_symm μ |>.symm

theorem volume_measurePreserving_sumPiEquivProdPi (X : ι ⊕ ι' → Type*)
    [∀ i, MeasureSpace (X i)] [∀ i, SigmaFinite (volume : Measure (X i))] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X) volume volume :=
  measurePreserving_sumPiEquivProdPi (fun _ ↦ volume)

theorem measurePreserving_piFinSuccAbove {n : ℕ} {α : Fin (n + 1) → Type u}
    {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) (Measure.pi μ)
      ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j)) := by
  set e := (MeasurableEquiv.piFinSuccAbove α i).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  rw [e.map_apply, i.prod_univ_succAbove _, ← pi_pi, ← prod_prod]
  congr 1 with ⟨x, f⟩
  simp [e, i.forall_iff_succAbove]

theorem volume_preserving_piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type u)
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) :=
  measurePreserving_piFinSuccAbove (fun _ => volume) i

theorem measurePreserving_piUnique {X : ι → Type*} [Unique ι] {m : ∀ i, MeasurableSpace (X i)}
    (μ : ∀ i, Measure (X i)) :
    MeasurePreserving (MeasurableEquiv.piUnique X) (Measure.pi μ) (μ default) where
  measurable := (MeasurableEquiv.piUnique X).measurable
  map_eq := by
    set e := MeasurableEquiv.piUnique X
    have : (piPremeasure fun i => (μ i).toOuterMeasure) = Measure.map e.symm (μ default) := by
      ext1 s
      rw [piPremeasure, Fintype.prod_unique, e.symm.map_apply, coe_toOuterMeasure]
      congr 1; exact e.toEquiv.image_eq_preimage s
    simp_rw [Measure.pi, OuterMeasure.pi, this, ← coe_toOuterMeasure, boundedBy_eq_self,
      toOuterMeasure_toMeasure, MeasurableEquiv.map_map_symm]

theorem volume_preserving_piUnique (X : ι → Type*) [Unique ι] [∀ i, MeasureSpace (X i)] :
    MeasurePreserving (MeasurableEquiv.piUnique X) volume volume :=
  measurePreserving_piUnique _

theorem measurePreserving_funUnique {β : Type u} {_m : MeasurableSpace β} (μ : Measure β)
    (α : Type v) [Unique α] :
    MeasurePreserving (MeasurableEquiv.funUnique α β) (Measure.pi fun _ : α => μ) μ :=
  measurePreserving_piUnique _

theorem volume_preserving_funUnique (α : Type u) (β : Type v) [Unique α] [MeasureSpace β] :
    MeasurePreserving (MeasurableEquiv.funUnique α β) volume volume :=
  measurePreserving_funUnique volume α

theorem measurePreserving_piFinTwo {α : Fin 2 → Type u} {m : ∀ i, MeasurableSpace (α i)}
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) (Measure.pi μ) ((μ 0).prod (μ 1)) := by
  refine ⟨MeasurableEquiv.measurable _, (Measure.prod_eq fun s t _ _ => ?_).symm⟩
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.piFinTwo_apply, Fin.preimage_apply_01_prod,
    Measure.pi_pi, Fin.prod_univ_two]
  rfl

theorem volume_preserving_piFinTwo (α : Fin 2 → Type u) [∀ i, MeasureSpace (α i)]
    [∀ i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) volume volume :=
  measurePreserving_piFinTwo _

theorem measurePreserving_finTwoArrow_vec {α : Type u} {_ : MeasurableSpace α} (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi ![μ, ν]) (μ.prod ν) :=
  haveI : ∀ i, SigmaFinite (![μ, ν] i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  measurePreserving_piFinTwo _

theorem measurePreserving_finTwoArrow {α : Type u} {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi fun _ => μ) (μ.prod μ) := by
  simpa only [Matrix.vec_single_eq_const, Matrix.vecCons_const] using
    measurePreserving_finTwoArrow_vec μ μ

theorem volume_preserving_finTwoArrow (α : Type u) [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (@MeasurableEquiv.finTwoArrow α _) volume volume :=
  measurePreserving_finTwoArrow volume

theorem measurePreserving_pi_empty {ι : Type u} {α : ι → Type v} [Fintype ι] [IsEmpty ι]
    {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) :
    MeasurePreserving (MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit) (Measure.pi μ)
      (Measure.dirac ()) := by
  set e := MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit
  refine ⟨e.measurable, ?_⟩
  rw [Measure.pi_of_empty, Measure.map_dirac e.measurable]

theorem volume_preserving_pi_empty {ι : Type u} (α : ι → Type v) [Fintype ι] [IsEmpty ι]
    [∀ i, MeasureSpace (α i)] :
    MeasurePreserving (MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit) volume volume :=
  measurePreserving_pi_empty fun _ => volume

theorem measurePreserving_piFinsetUnion {ι : Type*} {α : ι → Type*}
    {_ : ∀ i, MeasurableSpace (α i)} [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t)
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinsetUnion α h)
      ((Measure.pi fun i : s ↦ μ i).prod (Measure.pi fun i : t ↦ μ i))
      (Measure.pi fun i : ↥(s ∪ t) ↦ μ i) :=
  let e := Equiv.Finset.union s t h
  measurePreserving_piCongrLeft (fun i : ↥(s ∪ t) ↦ μ i) e |>.comp <|
    measurePreserving_sumPiEquivProdPi_symm fun b ↦ μ (e b)

theorem volume_preserving_piFinsetUnion {ι : Type*} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι}
    (h : Disjoint s t) [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piFinsetUnion α h) volume volume :=
  measurePreserving_piFinsetUnion h (fun _ ↦ volume)

theorem measurePreserving_pi {ι : Type*} [Fintype ι] {α : ι → Type v} {β : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
    (μ : (i : ι) → Measure (α i)) (ν : (i : ι) → Measure (β i))
    {f : (i : ι) → (α i) → (β i)} [∀ i, SigmaFinite (ν i)]
    (hf : ∀ i, MeasurePreserving (f i) (μ i) (ν i)) :
    MeasurePreserving (fun a i ↦ f i (a i)) (Measure.pi μ) (Measure.pi ν) where
  measurable :=
    measurable_pi_iff.mpr <| fun i ↦ (hf i).measurable.comp (measurable_pi_apply i)
  map_eq := by
    haveI : ∀ i, SigmaFinite (μ i) := fun i ↦ (hf i).sigmaFinite
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    rw [Measure.map_apply, Set.preimage_pi, Measure.pi_pi]
    · simp_rw [← MeasurePreserving.measure_preimage (hf _) (hs _).nullMeasurableSet]
    · exact measurable_pi_iff.mpr <| fun i ↦ (hf i).measurable.comp (measurable_pi_apply i)
    · exact MeasurableSet.univ_pi hs

theorem volume_preserving_pi {α' β' : ι → Type*} [∀ i, MeasureSpace (α' i)]
    [∀ i, MeasureSpace (β' i)] [∀ i, SigmaFinite (volume : Measure (β' i))]
    {f : (i : ι) → (α' i) → (β' i)} (hf : ∀ i, MeasurePreserving (f i)) :
    MeasurePreserving (fun (a : (i : ι) → α' i) (i : ι) ↦ (f i) (a i)) :=
  measurePreserving_pi _ _ hf

/-- The measurable equiv `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁ ≃ᵐ β₂` is
measure preserving. -/
theorem measurePreserving_arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
    [MeasurableSpace β₁] [MeasurableSpace β₂] (μ : α₁ → Measure β₁) (ν : α₂ → Measure β₂)
    [∀ i, SigmaFinite (ν i)] (eα : α₁ ≃ α₂) (eβ : β₁ ≃ᵐ β₂)
    (hm : ∀ i, MeasurePreserving eβ (μ i) (ν (eα i))) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' eα eβ) (Measure.pi fun i ↦ μ i)
      (Measure.pi fun i ↦ ν i) := by
  classical
  convert (measurePreserving_piCongrLeft (fun i : α₂ ↦ ν i) eα).comp
    (measurePreserving_pi μ (fun i : α₁ ↦ ν (eα i)) hm)
  simp only [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, EquivLike.coe_coe,
    comp_def, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.symm_symm, Equiv.piCongrLeft', eq_rec_constant, Equiv.coe_fn_symm_mk]

/-- The measurable equiv `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁ ≃ᵐ β₂` is
volume preserving. -/
theorem volume_preserving_arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
    [MeasureSpace β₁] [MeasureSpace β₂] [SigmaFinite (volume : Measure β₂)]
    (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) (hm : MeasurePreserving hβ) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' hα hβ) :=
  measurePreserving_arrowCongr' (fun _ ↦ volume) (fun _ ↦ volume) hα hβ (fun _ ↦ hm)

end MeasurePreserving

end MeasureTheory
