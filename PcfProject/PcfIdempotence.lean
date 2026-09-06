import PcfProject.CanonicalProduct

/-!
# Fubini flattening and PCF idempotence

This file formalizes Jech, Lemma 24.24.  An outer reduced product of true
cofinalities is flattened through the witnessing inner ultrafilters.  The
pointwise supremum stays inside the original product under the source
hypothesis `|pcf A| < min A`.
-/

namespace PcfProject

universe u

open Cardinal Set
open scoped Cardinal

/-! Eventual comparison of two levels of a cardinal scale reflects the
order of their indices. -/
theorem cardinalScaleLength_le_of_scale_eventuallyLe
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (s : Scale (cardinalProductFrame A J) (cardinalScaleLength theta))
    {alpha beta : (cardinalScaleLength theta).Level}
    (hLe : (cardinalProductFrame A J).eventuallyLe
      (s.seq alpha) (s.seq beta)) :
    (show theta.ord.ToType from alpha) <=
      (show theta.ord.ToType from beta) := by
  by_contra hNotLe
  have hLt : (show theta.ord.ToType from beta) <
      (show theta.ord.ToType from alpha) :=
    lt_of_not_ge hNotLe
  exact (s.not_eventuallyLe_of_lt (by
    simpa only [cardinalScaleLength] using hLt)) hLe

#print axioms cardinalScaleLength_le_of_scale_eventuallyLe

/-! The source pointwise supremum used to flatten an iterated product. -/
noncomputable def cardinalProductFubiniFlatten
    {A B : CardSet.{u}}
    {J : Ideal (CardinalIndex B)}
    (hARegulars : SetOfRegulars A)
    (hSmall : forall a : CardinalIndex A,
      Cardinal.mk (CardinalIndex B) < Cardinal.lift.{u + 1} a.1)
    (D : CardinalIndex B -> Ideal (CardinalIndex A))
    (s : forall b : CardinalIndex B,
      Scale (cardinalProductFrame A (D b))
        (cardinalScaleLength b.1))
    (g : ProductElement (cardinalProductFrame B J)) :
    ProductElement (cardinalProductFrame A (J.fubini D)) :=
  cardinalProductPointwiseSupOfSmallFamily hARegulars hSmall
    (fun b => (s b).seq (g b))

/-! Every inner term used in a flattening is pointwise below the flattened
supremum. -/
theorem cardinalProductFubiniFlatten_inner_le
    {A B : CardSet.{u}}
    {J : Ideal (CardinalIndex B)}
    (hARegulars : SetOfRegulars A)
    (hSmall : forall a : CardinalIndex A,
      Cardinal.mk (CardinalIndex B) < Cardinal.lift.{u + 1} a.1)
    (D : CardinalIndex B -> Ideal (CardinalIndex A))
    (s : forall b : CardinalIndex B,
      Scale (cardinalProductFrame A (D b))
        (cardinalScaleLength b.1))
    (g : ProductElement (cardinalProductFrame B J))
    (b : CardinalIndex B)
    (a : CardinalIndex A) :
    (show a.1.ord.ToType from (s b).seq (g b) a) <=
      (show a.1.ord.ToType from
        cardinalProductFubiniFlatten hARegulars hSmall D s g a) := by
  exact cardinalProduct_le_pointwiseSupOfSmallFamily
    hARegulars hSmall (fun b => (s b).seq (g b)) b a

#print axioms cardinalProductFubiniFlatten_inner_le

/-! Flattening an outer cofinal scale gives a cofinal (not necessarily
increasing) family in the Fubini product. -/
theorem cardinalProductFubiniFlatten_isCofinalFamily
    {A B : CardSet.{u}}
    {J : Ideal (CardinalIndex B)}
    (hARegulars : SetOfRegulars A)
    (hSmall : forall a : CardinalIndex A,
      Cardinal.mk (CardinalIndex B) < Cardinal.lift.{u + 1} a.1)
    (D : CardinalIndex B -> Ideal (CardinalIndex A))
    (s : forall b : CardinalIndex B,
      Scale (cardinalProductFrame A (D b))
        (cardinalScaleLength b.1))
    {theta : Cardinal.{u}}
    (t : Scale (cardinalProductFrame B J)
      (cardinalScaleLength theta)) :
    (cardinalProductFrame A (J.fubini D)).IsCofinalFamily
      (fun alpha => cardinalProductFubiniFlatten
        hARegulars hSmall D s (t.seq alpha)) := by
  classical
  intro x
  choose r hr using fun b : CardinalIndex B => (s b).cofinal x
  obtain ⟨alpha, hAlpha⟩ := t.cofinal r
  refine ⟨alpha, ?_⟩
  change J.Eventually (fun b => (D b).Eventually (fun a =>
    (show a.1.ord.ToType from x a) <=
      (show a.1.ord.ToType from cardinalProductFubiniFlatten
        hARegulars hSmall D s (t.seq alpha) a)))
  exact J.eventually_mono hAlpha (by
    intro b hb
    have hLevels : (cardinalProductFrame A (D b)).eventuallyLe
        ((s b).seq (r b)) ((s b).seq (t.seq alpha b)) := by
      rcases hb.eq_or_lt with hEq | hLt
      · rw [hEq]
        exact (cardinalProductFrame A (D b)).eventuallyLe_refl _
      · exact (s b).eventuallyLe_of_lt (by
          simpa only [cardinalScaleLength] using hLt)
    have hxLevel : (D b).Eventually (fun a =>
        (show a.1.ord.ToType from x a) <=
          (show a.1.ord.ToType from (s b).seq (t.seq alpha b) a)) :=
      (cardinalProductFrame A (D b)).eventuallyLe_trans (hr b) hLevels
    exact (D b).eventually_mono hxLevel (by
      intro a ha
      exact ha.trans (cardinalProductFubiniFlatten_inner_le
        hARegulars hSmall D s (t.seq alpha) b a)))

#print axioms cardinalProductFubiniFlatten_isCofinalFamily

/-! The Fubini quotient has cofinality at least that of the outer quotient.
A least cofinal set in the Fubini quotient is represented by raw functions;
inner scale stages assigned to those representatives form an outer cofinal
family. -/
theorem cardinalProductQuotient_cof_le_fubini
    {A B : CardSet.{u}}
    {J : Ideal (CardinalIndex B)}
    (hARegulars : SetOfRegulars A)
    (hSmall : forall a : CardinalIndex A,
      Cardinal.mk (CardinalIndex B) < Cardinal.lift.{u + 1} a.1)
    (D : CardinalIndex B -> Ideal (CardinalIndex A))
    (s : forall b : CardinalIndex B,
      Scale (cardinalProductFrame A (D b))
        (cardinalScaleLength b.1)) :
    Order.cof (CardinalProductQuotient B J) <=
      Order.cof (CardinalProductQuotient A (J.fubini D)) := by
  classical
  let E : Ideal (CardinalIndex A) := J.fubini D
  let QE := CardinalProductQuotient A E
  obtain ⟨C, hCCofinal, hCardC⟩ := Order.exists_cof_eq QE
  choose rep hRep using fun q : C => Quotient.exists_rep q.1
  choose stage hStage using fun (q : C) (b : CardinalIndex B) =>
    (s b).cofinal (rep q)
  let outerStage : C -> ProductElement (cardinalProductFrame B J) :=
    fun q b => stage q b
  have hOuterCofinal :
      (cardinalProductFrame B J).IsCofinalFamily outerStage := by
    intro g
    let flat : ProductElement (cardinalProductFrame A E) :=
      cardinalProductFubiniFlatten hARegulars hSmall D s g
    obtain ⟨q, hqC, hFlatQ⟩ := hCCofinal
      (Quotient.mk (cardinalProductFrameEventualSetoid A E) flat)
    let c : C := ⟨q, hqC⟩
    refine ⟨c, ?_⟩
    have hFlatRep : (cardinalProductFrame A E).eventuallyLe flat (rep c) := by
      change (Quotient.mk (cardinalProductFrameEventualSetoid A E) flat : QE) <=
        Quotient.mk (cardinalProductFrameEventualSetoid A E) (rep c)
      rw [hRep c]
      exact hFlatQ
    change J.Eventually (fun b =>
      (show b.1.ord.ToType from g b) <=
        (show b.1.ord.ToType from outerStage c b))
    change J.Eventually (fun b => (D b).Eventually (fun a =>
      (show a.1.ord.ToType from flat a) <=
        (show a.1.ord.ToType from rep c a))) at hFlatRep
    exact J.eventually_mono hFlatRep (by
      intro b hb
      have hInnerFlat : (D b).Eventually (fun a =>
          (show a.1.ord.ToType from (s b).seq (g b) a) <=
            (show a.1.ord.ToType from flat a)) :=
        (D b).eventually_of_forall (fun a =>
          cardinalProductFubiniFlatten_inner_le
            hARegulars hSmall D s g b a)
      have hInnerRep : (cardinalProductFrame A (D b)).eventuallyLe
          ((s b).seq (g b)) (rep c) :=
        (cardinalProductFrame A (D b)).eventuallyLe_trans hInnerFlat hb
      have hInnerStage : (cardinalProductFrame A (D b)).eventuallyLe
          ((s b).seq (g b)) ((s b).seq (stage c b)) :=
        (cardinalProductFrame A (D b)).eventuallyLe_trans
          hInnerRep (hStage c b)
      exact cardinalScaleLength_le_of_scale_eventuallyLe
        (s b) hInnerStage)
  let quotientStage : C -> CardinalProductQuotient B J := fun c =>
    Quotient.mk (cardinalProductFrameEventualSetoid B J) (outerStage c)
  have hQuotientCofinal : cardinalProductQuotientIsCofinalFamily
      quotientStage :=
    (cardinalProductQuotient_mk_isCofinalFamily_iff outerStage).mp
      hOuterCofinal
  have hRangeCofinal : IsCofinal (Set.range quotientStage) := by
    intro q
    obtain ⟨c, hc⟩ := hQuotientCofinal q
    exact ⟨quotientStage c, ⟨c, rfl⟩, hc⟩
  calc
    Order.cof (CardinalProductQuotient B J) <=
        Cardinal.mk (Set.range quotientStage) :=
      Order.cof_le hRangeCofinal
    _ <= Cardinal.mk C := Cardinal.mk_range_le
    _ = Order.cof QE := hCardC
    _ = Order.cof (CardinalProductQuotient A (J.fubini D)) := rfl

#print axioms cardinalProductQuotient_cof_le_fubini

/-! The Fubini product realizes the same regular true cofinality as the
outer scale.  The flattened family supplies the upper bound, while the
preceding theorem supplies the matching lower bound on quotient cofinality. -/
theorem cardinalProductFubini_hasTrueCofinality
    {A B : CardSet.{u}}
    {J : Ideal (CardinalIndex B)}
    (hARegulars : SetOfRegulars A)
    (hSmall : forall a : CardinalIndex A,
      Cardinal.mk (CardinalIndex B) < Cardinal.lift.{u + 1} a.1)
    (D : CardinalIndex B -> Ideal (CardinalIndex A))
    (hJUltra : J.IsUltrafilterDual)
    (hDUltra : forall b, (D b).IsUltrafilterDual)
    (s : forall b : CardinalIndex B,
      Scale (cardinalProductFrame A (D b))
        (cardinalScaleLength b.1))
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (t : Scale (cardinalProductFrame B J)
      (cardinalScaleLength theta)) :
    HasTrueCofinality
      (cardinalProductFrame A (J.fubini D))
      (cardinalScaleLength theta) := by
  have hFubiniUltra : (J.fubini D).IsUltrafilterDual :=
    hJUltra.fubini D hDUltra
  let flat : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A (J.fubini D)) :=
    fun alpha => cardinalProductFubiniFlatten
      hARegulars hSmall D s (t.seq alpha)
  have hFlatCofinal :
      (cardinalProductFrame A (J.fubini D)).IsCofinalFamily flat :=
    cardinalProductFubiniFlatten_isCofinalFamily
      hARegulars hSmall D s t
  let d : (cardinalScaleLength theta).Level ->
      CardinalProductQuotient A (J.fubini D) := fun alpha =>
    Quotient.mk (cardinalProductFrameEventualSetoid A (J.fubini D))
      (flat alpha)
  have hDCofinal : cardinalProductQuotientIsCofinalFamily d :=
    (cardinalProductQuotient_mk_isCofinalFamily_iff flat).mp hFlatCofinal
  have hCofLower : Cardinal.lift.{u + 1} theta <=
      Order.cof (CardinalProductQuotient A (J.fubini D)) := by
    calc
      Cardinal.lift.{u + 1} theta =
          Order.cof (CardinalProductQuotient B J) :=
        (cardinalProductQuotient_cof_eq_lift_of_regular_quotientScale
          hThetaRegular hJUltra
          (CardinalProductQuotientScale.ofScale t)).symm
      _ <= Order.cof (CardinalProductQuotient A (J.fubini D)) :=
        cardinalProductQuotient_cof_le_fubini
          hARegulars hSmall D s
  exact
    (cardinalScaleLength_hasTrueCofinality_iff_exists_quotientCofinalFamily_of_lift_le
      hARegulars hFubiniUltra hThetaRegular).mpr
        ⟨d, hDCofinal, hCofLower⟩

#print axioms cardinalProductFubini_hasTrueCofinality

/-! Same-universe formulation of Jech's hypothesis `|pcf A| < min A`.
Writing it coordinatewise avoids introducing a separate minimum operation
on predicates. -/
def CardinalProductPcfSpectrumSmallBelowCoordinates
    (A : CardSet.{u}) : Prop :=
  forall a : CardinalIndex A,
    Cardinal.mk (CardinalIndex
      (cardinalProductRepresentation.pcf A)) <
        Cardinal.lift.{u + 1} a.1

/-! Jech, Lemma 24.24: under `|pcf A| < min A`, taking possible
cofinalities twice adds no new cardinal. -/
theorem cardinalProductRepresentation_pcf_pcf_eq_of_spectrumSmall
    (A : CardSet.{u})
    (hARegulars : SetOfRegulars A)
    (hSmall : CardinalProductPcfSpectrumSmallBelowCoordinates A) :
    cardinalProductRepresentation.pcf
        (cardinalProductRepresentation.pcf A) =
      cardinalProductRepresentation.pcf A := by
  classical
  funext theta
  apply propext
  constructor
  · intro hTheta
    obtain ⟨hThetaRegular, J, hJUltra, hOuterTcf⟩ :=
      (cardinalProductRepresentation_mem_pcf_iff.mp hTheta)
    have hInner : forall b : CardinalIndex
        (cardinalProductRepresentation.pcf A),
        exists D : Ideal (CardinalIndex A),
          D.IsUltrafilterDual /\
            HasTrueCofinality
              (cardinalProductFrame A D)
              (cardinalScaleLength b.1) := by
      intro b
      exact (cardinalProductRepresentation_mem_pcf_iff.mp b.2).2
    let D : CardinalIndex (cardinalProductRepresentation.pcf A) ->
        Ideal (CardinalIndex A) := fun b => Classical.choose (hInner b)
    have hDUltra : forall b, (D b).IsUltrafilterDual := fun b =>
      (Classical.choose_spec (hInner b)).1
    have hDTcf : forall b,
        HasTrueCofinality
          (cardinalProductFrame A (D b))
          (cardinalScaleLength b.1) := fun b =>
      (Classical.choose_spec (hInner b)).2
    let s : forall b : CardinalIndex
        (cardinalProductRepresentation.pcf A),
        Scale (cardinalProductFrame A (D b))
          (cardinalScaleLength b.1) := fun b =>
      (hDTcf b).hasScaleWitness.some
    obtain ⟨t⟩ := hOuterTcf.hasScaleWitness
    have hFubiniTcf : HasTrueCofinality
        (cardinalProductFrame A (J.fubini D))
        (cardinalScaleLength theta) :=
      cardinalProductFubini_hasTrueCofinality
        hARegulars hSmall D hJUltra hDUltra s hThetaRegular t
    exact cardinalProductRepresentation_mem_pcf_iff.mpr
      ⟨hThetaRegular, J.fubini D, hJUltra.fubini D hDUltra, hFubiniTcf⟩
  · intro hTheta
    exact cardinalProductRepresentation_mem_pcf_of_mem
      (cardinalProductRepresentation.pcf_is_setOfRegulars A) hTheta

#print axioms
  cardinalProductRepresentation_pcf_pcf_eq_of_spectrumSmall

/-! Choose one witnessing ultrafilter-dual ideal for each canonical PCF
value.  Distinct values must choose distinct ideals because true cofinality
is unique on a fixed reduced product. -/
noncomputable def cardinalProductPcfWitnessIdeal
    {A : CardSet.{u}}
    (theta : CardinalIndex (cardinalProductRepresentation.pcf A)) :
    Ideal (CardinalIndex A) :=
  Classical.choose
    (cardinalProductRepresentation_mem_pcf_iff.mp theta.2).2

theorem cardinalProductPcfWitnessIdeal_hasTrueCofinality
    {A : CardSet.{u}}
    (theta : CardinalIndex (cardinalProductRepresentation.pcf A)) :
    HasTrueCofinality
      (cardinalProductFrame A (cardinalProductPcfWitnessIdeal theta))
      (cardinalScaleLength theta.1) :=
  (Classical.choose_spec
    (cardinalProductRepresentation_mem_pcf_iff.mp theta.2).2).2

theorem cardinalProductPcfWitnessIdeal_injective
    {A : CardSet.{u}} :
    Function.Injective
      (cardinalProductPcfWitnessIdeal (A := A)) := by
  intro theta mu hIdeal
  apply Subtype.ext
  have hTheta := cardinalProductPcfWitnessIdeal_hasTrueCofinality theta
  have hMu := cardinalProductPcfWitnessIdeal_hasTrueCofinality mu
  rw [hIdeal] at hTheta
  simpa only [mk_cardinalScaleLength_level] using
    cardinal_mk_level_eq_of_hasTrueCofinality hTheta hMu

#print axioms cardinalProductPcfWitnessIdeal_injective

/-! There are at most `2^(2^|A|)` ideals on the coordinate type, hence at
most that many canonical PCF values. -/
theorem cardinal_mk_cardinalIndex_pcf_le_two_power_two_power
    (A : CardSet.{u}) :
    Cardinal.mk (CardinalIndex (cardinalProductRepresentation.pcf A)) <=
      (2 : Cardinal.{u + 1}) ^
        ((2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A)) := by
  calc
    Cardinal.mk (CardinalIndex (cardinalProductRepresentation.pcf A)) <=
        Cardinal.mk (Ideal (CardinalIndex A)) :=
      Cardinal.mk_le_of_injective
        cardinalProductPcfWitnessIdeal_injective
    _ <= Cardinal.mk (((CardinalIndex A -> Prop) -> Prop)) := by
      apply Cardinal.mk_le_of_injective
        (f := fun J : Ideal (CardinalIndex A) => J.Small)
      intro J K hJK
      apply Ideal.ext
      intro S
      exact iff_of_eq (congrFun hJK S)
    _ = (2 : Cardinal.{u + 1}) ^
        ((2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A)) := by
      simp only [Cardinal.mk_pi, Cardinal.mk_Prop,
        Cardinal.lift_ofNat, Cardinal.prod_const,
        Cardinal.lift_id'.{0, u + 1}]

#print axioms
  cardinal_mk_cardinalIndex_pcf_le_two_power_two_power

/-! A convenient hereditary sufficient condition for Lemma 24.24.  It is
the elementary pre-generator bound `2^(2^|A|) < min A` from (24.7)(iv). -/
def CardinalProductDoublePowerBelowCoordinates
    (A : CardSet.{u}) : Prop :=
  forall a : CardinalIndex A,
    (2 : Cardinal.{u + 1}) ^
        ((2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A)) <
      Cardinal.lift.{u + 1} a.1

theorem cardinalProductPcfSpectrumSmallBelowCoordinates_of_doublePower_subset
    {A E : CardSet.{u}}
    (hEA : SubsetOf E A)
    (hDouble : CardinalProductDoublePowerBelowCoordinates A) :
    CardinalProductPcfSpectrumSmallBelowCoordinates E := by
  intro e
  have hIndex : Cardinal.mk (CardinalIndex E) <=
      Cardinal.mk (CardinalIndex A) :=
    Cardinal.mk_subtype_mono hEA
  have hPower : (2 : Cardinal.{u + 1}) ^
        Cardinal.mk (CardinalIndex E) <=
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) :=
    Cardinal.power_le_power_left two_ne_zero hIndex
  have hDoublePower : (2 : Cardinal.{u + 1}) ^
        ((2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex E)) <=
      (2 : Cardinal.{u + 1}) ^
        ((2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A)) :=
    Cardinal.power_le_power_left two_ne_zero hPower
  exact (cardinal_mk_cardinalIndex_pcf_le_two_power_two_power E).trans_lt
    (hDoublePower.trans_lt (hDouble ⟨e.1, hEA e.1 e.2⟩))

#print axioms
  cardinalProductPcfSpectrumSmallBelowCoordinates_of_doublePower_subset

theorem cardinalProductRepresentation_pcf_pcf_eq_of_doublePowerBelow
    (A : CardSet.{u})
    (hARegulars : SetOfRegulars A)
    (hDouble : CardinalProductDoublePowerBelowCoordinates A) :
    cardinalProductRepresentation.pcf
        (cardinalProductRepresentation.pcf A) =
      cardinalProductRepresentation.pcf A :=
  cardinalProductRepresentation_pcf_pcf_eq_of_spectrumSmall A hARegulars
    (cardinalProductPcfSpectrumSmallBelowCoordinates_of_doublePower_subset
      (A := A) (E := A) (fun _ h => h) hDouble)

#print axioms
  cardinalProductRepresentation_pcf_pcf_eq_of_doublePowerBelow

end PcfProject
