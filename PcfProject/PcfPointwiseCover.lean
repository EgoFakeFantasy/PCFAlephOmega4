import PcfProject.ShelahClosure

/-!
# A uniform pointwise cover from all canonical ultrafilter scales

This module formalizes the product-theoretic content of Jech's Lemma 24.21.
For a small set of uncountable regular cardinals, every ultrafilter quotient
has a genuine canonical true-cofinality scale.  Choosing all those scales at
once gives one raw product family which is cofinal modulo every ultrafilter.
The already proved ultrafilter compactness lemma then turns quotient
cofinality into a finite pointwise cover of every product element.
-/

open Cardinal Set
open scoped Cardinal

namespace PcfProject

universe u

/-- An ultrafilter-dual ideal on the canonical coordinate type. -/
def CardinalProductUltrafilterIdeal (A : CardSet.{u}) :=
  {J : Ideal (CardinalIndex A) // J.IsUltrafilterDual}

/-- A selected regular true-cofinality scale for one canonical ultrafilter
quotient. -/
structure CardinalProductUltrafilterScaleChoice
    (A : CardSet.{u})
    (U : CardinalProductUltrafilterIdeal A) where
  theta : Cardinal.{u}
  regular : Cardinal.IsRegular theta
  tcf : HasTrueCofinality
    (cardinalProductFrame A U.1)
    (cardinalScaleLength theta)
  aleph0_lt : Cardinal.aleph0 < theta

theorem nonempty_cardinalProductUltrafilterScaleChoice
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (U : CardinalProductUltrafilterIdeal A) :
    Nonempty (CardinalProductUltrafilterScaleChoice A U) := by
  obtain ⟨theta, hRegular, hTcf, hThetaAleph0⟩ :=
    cardinalProductFrame_exists_trueCofinality_of_small_cardinalIndex_of_aleph0_lt
      hRegulars U.2 hSmall hAleph0
  exact ⟨⟨theta, hRegular, hTcf, hThetaAleph0⟩⟩

#print axioms nonempty_cardinalProductUltrafilterScaleChoice

noncomputable def cardinalProductUltrafilterScaleChoice
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (U : CardinalProductUltrafilterIdeal A) :
    CardinalProductUltrafilterScaleChoice A U :=
  Classical.choice
    (nonempty_cardinalProductUltrafilterScaleChoice
      A hRegulars hSmall hAleph0 U)

noncomputable def cardinalProductUltrafilterScale
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (U : CardinalProductUltrafilterIdeal A) :
    Scale
      (cardinalProductFrame A U.1)
      (cardinalScaleLength
        (cardinalProductUltrafilterScaleChoice
          A hRegulars hSmall hAleph0 U).theta) :=
  Classical.choice
    (cardinalProductUltrafilterScaleChoice
      A hRegulars hSmall hAleph0 U).tcf.hasScaleWitness

theorem cardinalProductUltrafilterScaleChoice_mem_pcf
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (U : CardinalProductUltrafilterIdeal A) :
    cardinalProductRepresentation.pcf A
      (cardinalProductUltrafilterScaleChoice
        A hRegulars hSmall hAleph0 U).theta := by
  apply cardinalProductRepresentation_mem_pcf_iff.mpr
  exact ⟨
    (cardinalProductUltrafilterScaleChoice
      A hRegulars hSmall hAleph0 U).regular,
    U.1, U.2,
    (cardinalProductUltrafilterScaleChoice
      A hRegulars hSmall hAleph0 U).tcf⟩

#print axioms cardinalProductUltrafilterScaleChoice_mem_pcf

theorem mk_cardinalProductUltrafilterIdeal_le_two_power_two_power
    (A : CardSet.{u}) :
    Cardinal.mk (CardinalProductUltrafilterIdeal A) <=
      (2 : Cardinal.{u + 1}) ^
        ((2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A)) := by
  calc
    Cardinal.mk (CardinalProductUltrafilterIdeal A) <=
        Cardinal.mk (Ideal (CardinalIndex A)) :=
      Cardinal.mk_subtype_le _
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
  mk_cardinalProductUltrafilterIdeal_le_two_power_two_power

/-- The disjoint union of the level types of all selected ultrafilter
scales. -/
def CardinalProductAllUltrafilterScaleIndex
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta) :=
  Sigma fun U : CardinalProductUltrafilterIdeal A =>
    (cardinalScaleLength
    (cardinalProductUltrafilterScaleChoice
        A hRegulars hSmall hAleph0 U).theta).Level

theorem mk_cardinalProductAllUltrafilterScaleIndex_le_maxPcf
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (M : MaxPcfWitness cardinalProductRepresentation A)
    (hPower :
      (2 : Cardinal.{u + 1}) ^
          ((2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A)) <=
        Cardinal.lift.{u + 1} M.theta) :
    Cardinal.mk
        (CardinalProductAllUltrafilterScaleIndex
          A hRegulars hSmall hAleph0) <=
      Cardinal.lift.{u + 1} M.theta := by
  unfold CardinalProductAllUltrafilterScaleIndex
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun U : CardinalProductUltrafilterIdeal A =>
        Cardinal.mk
          (cardinalScaleLength
            (cardinalProductUltrafilterScaleChoice
              A hRegulars hSmall hAleph0 U).theta).Level) <=
        Cardinal.lift.{u}
            (Cardinal.mk (CardinalProductUltrafilterIdeal A)) *
          ⨆ U : CardinalProductUltrafilterIdeal A,
            Cardinal.lift.{u + 1} (Cardinal.mk
              (cardinalScaleLength
                (cardinalProductUltrafilterScaleChoice
                  A hRegulars hSmall hAleph0 U).theta).Level) := by
      exact Cardinal.sum_le_lift_mk_mul_iSup_lift
          (fun U : CardinalProductUltrafilterIdeal A =>
            Cardinal.mk
              (cardinalScaleLength
                (cardinalProductUltrafilterScaleChoice
                  A hRegulars hSmall hAleph0 U).theta).Level)
    _ <= Cardinal.lift.{u + 1} M.theta *
        Cardinal.lift.{u + 1} M.theta := by
      apply mul_le_mul'
      · exact
          (Cardinal.lift_id'.{u, u + 1}
              (Cardinal.mk (CardinalProductUltrafilterIdeal A))).le.trans
            ((mk_cardinalProductUltrafilterIdeal_le_two_power_two_power A).trans
              hPower)
      · apply ciSup_le'
        intro U
        rw [mk_cardinalScaleLength_level]
        exact Cardinal.lift_le.mpr
          (M.bounds
            (cardinalProductUltrafilterScaleChoice_mem_pcf
              A hRegulars hSmall hAleph0 U))
    _ = Cardinal.lift.{u + 1} M.theta :=
      Cardinal.mul_eq_self
        (Cardinal.aleph0_le_lift.mpr M.isRegular.aleph0_le)

#print axioms
  mk_cardinalProductAllUltrafilterScaleIndex_le_maxPcf

/-- The raw product family obtained by putting every chosen quotient scale
into one common family.  The product-element type does not depend on the
ideal, only its eventual order does. -/
noncomputable def cardinalProductAllUltrafilterScaleFamily
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta) :
    CardinalProductAllUltrafilterScaleIndex
        A hRegulars hSmall hAleph0 ->
      ProductElement
        (cardinalProductFrame A
          (Ideal.emptyOnly (CardinalIndex A))) := fun z =>
  cardinalProductUltrafilterScale
    A hRegulars hSmall hAleph0 z.1 |>.seq z.2

theorem cardinalProductAllUltrafilterScaleFamily_isCofinal
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (J : Ideal (CardinalIndex A))
    (hUltra : J.IsUltrafilterDual) :
    (cardinalProductFrame A J).IsCofinalFamily
      (cardinalProductAllUltrafilterScaleFamily
        A hRegulars hSmall hAleph0) := by
  intro g
  let U : CardinalProductUltrafilterIdeal A := ⟨J, hUltra⟩
  obtain ⟨alpha, hAlpha⟩ :=
    (cardinalProductUltrafilterScale
      A hRegulars hSmall hAleph0 U).cofinal g
  exact ⟨⟨U, alpha⟩, hAlpha⟩

#print axioms cardinalProductAllUltrafilterScaleFamily_isCofinal

/-! Every product element is pointwise dominated by the maximum of finitely
many members of the uniform family.  This is the exact order-theoretic
statement of Lemma 24.21, before its cardinality estimate. -/
theorem exists_finset_cardinalProductAllUltrafilterScaleFamily_pointwise_cover
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta) :
    forall g : ProductElement
        (cardinalProductFrame A
          (Ideal.emptyOnly (CardinalIndex A))),
      exists s : Finset
          (CardinalProductAllUltrafilterScaleIndex
            A hRegulars hSmall hAleph0),
        forall i, exists k, k ∈ s /\
          (cardinalProductFrame A
            (Ideal.emptyOnly (CardinalIndex A))).le i
              (g i)
              (cardinalProductAllUltrafilterScaleFamily
                A hRegulars hSmall hAleph0 k i) := by
  apply
    cardinalProductFrame_exists_finset_pointwise_cover_of_forall_ultrafilterDual_isCofinalFamily
      (cardinalProductAllUltrafilterScaleFamily
        A hRegulars hSmall hAleph0)
  intro J hUltra
  exact cardinalProductAllUltrafilterScaleFamily_isCofinal
    A hRegulars hSmall hAleph0 J hUltra

#print axioms
  exists_finset_cardinalProductAllUltrafilterScaleFamily_pointwise_cover

/-- Nonempty finite subfamilies index the actual pointwise maxima supplied
by the finite-cover conclusion. -/
def CardinalProductFiniteMaxIndex
    (K : Type v) :=
  {s : Finset K // s.Nonempty}

/-- Replace the raw all-ultrafilter scale family by all of its nonempty
finite pointwise maxima. -/
noncomputable def cardinalProductAllUltrafilterFiniteMaxFamily
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta) :
    CardinalProductFiniteMaxIndex
        (CardinalProductAllUltrafilterScaleIndex
          A hRegulars hSmall hAleph0) ->
      ProductElement
        (cardinalProductFrame A
          (Ideal.emptyOnly (CardinalIndex A))) := fun s i =>
  Ordinal.ToType.mk
    ⟨s.1.sup' s.2 (fun k =>
        cardinalProductOrdinalValue
          (cardinalProductAllUltrafilterScaleFamily
            A hRegulars hSmall hAleph0 k) i),
      (Finset.sup'_lt_iff s.2).mpr (by
        intro k _hk
        exact cardinalProductOrdinalValue_lt
          (cardinalProductAllUltrafilterScaleFamily
            A hRegulars hSmall hAleph0 k) i)⟩

theorem cardinalProductAllUltrafilterScaleFamily_le_finiteMax
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (s : CardinalProductFiniteMaxIndex
      (CardinalProductAllUltrafilterScaleIndex
        A hRegulars hSmall hAleph0))
    {k : CardinalProductAllUltrafilterScaleIndex
      A hRegulars hSmall hAleph0}
    (hk : k ∈ s.1)
    (i : CardinalIndex A) :
    (cardinalProductFrame A
      (Ideal.emptyOnly (CardinalIndex A))).le i
        (cardinalProductAllUltrafilterScaleFamily
          A hRegulars hSmall hAleph0 k i)
        (cardinalProductAllUltrafilterFiniteMaxFamily
          A hRegulars hSmall hAleph0 s i) := by
  rw [← (Ordinal.ToType.mk : Set.Iio i.1.ord ≃o
    i.1.ord.ToType).apply_symm_apply
      (cardinalProductAllUltrafilterScaleFamily
        A hRegulars hSmall hAleph0 k i)]
  apply (Ordinal.ToType.mk : Set.Iio i.1.ord ≃o
    i.1.ord.ToType).monotone
  change cardinalProductOrdinalValue
      (cardinalProductAllUltrafilterScaleFamily
        A hRegulars hSmall hAleph0 k) i <=
    s.1.sup' s.2 (fun j =>
      cardinalProductOrdinalValue
        (cardinalProductAllUltrafilterScaleFamily
          A hRegulars hSmall hAleph0 j) i)
  exact Finset.le_sup'
    (s := s.1)
    (fun j : CardinalProductAllUltrafilterScaleIndex
        A hRegulars hSmall hAleph0 =>
      cardinalProductOrdinalValue
        (cardinalProductAllUltrafilterScaleFamily
          A hRegulars hSmall hAleph0 j) i)
    hk

#print axioms
  cardinalProductAllUltrafilterScaleFamily_le_finiteMax

/-! The finite-max family is literally pointwise cofinal in the full
product, rather than merely cofinal modulo every ultrafilter. -/
theorem cardinalProductAllUltrafilterFiniteMaxFamily_pointwise_cofinal
    (A : CardSet.{u})
    [Nonempty (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta) :
    forall g : ProductElement
        (cardinalProductFrame A
          (Ideal.emptyOnly (CardinalIndex A))),
      exists s : CardinalProductFiniteMaxIndex
          (CardinalProductAllUltrafilterScaleIndex
            A hRegulars hSmall hAleph0),
        forall i,
          (cardinalProductFrame A
            (Ideal.emptyOnly (CardinalIndex A))).le i
              (g i)
              (cardinalProductAllUltrafilterFiniteMaxFamily
                A hRegulars hSmall hAleph0 s i) := by
  intro g
  obtain ⟨s, hs⟩ :=
    exists_finset_cardinalProductAllUltrafilterScaleFamily_pointwise_cover
      A hRegulars hSmall hAleph0 g
  have hSNonempty : s.Nonempty := by
    let i : CardinalIndex A := Classical.choice inferInstance
    obtain ⟨k, hk, _⟩ := hs i
    exact ⟨k, hk⟩
  refine ⟨⟨s, hSNonempty⟩, ?_⟩
  intro i
  obtain ⟨k, hk, hgk⟩ := hs i
  exact hgk.trans
    (cardinalProductAllUltrafilterScaleFamily_le_finiteMax
      A hRegulars hSmall hAleph0 ⟨s, hSNonempty⟩ hk i)

#print axioms
  cardinalProductAllUltrafilterFiniteMaxFamily_pointwise_cofinal

theorem mk_cardinalProductFiniteMaxIndex_le
    {K : Type v}
    {mu : Cardinal.{v}}
    (hK : Cardinal.mk K <= mu)
    (hMu : Cardinal.aleph0 <= mu) :
    Cardinal.mk (CardinalProductFiniteMaxIndex K) <= mu := by
  calc
    Cardinal.mk (CardinalProductFiniteMaxIndex K) <=
        Cardinal.mk (Finset K) := Cardinal.mk_subtype_le _
    _ <= max Cardinal.aleph0 (Cardinal.mk K) :=
      mk_finset_le_max_aleph0_mk K
    _ <= mu := max_le hMu hK

#print axioms mk_cardinalProductFiniteMaxIndex_le

/-! Under the strong-limit hypothesis, the complete family of selected
ultrafilter scales on the successor-aleph core has size at most its maximum
PCF value.  This is the cardinal estimate in Jech's Lemma 24.21. -/
theorem alephSuccSet_mk_allUltrafilterScaleIndex_le_maxPcf
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    (M : MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u}) :
    Cardinal.mk
        (CardinalProductAllUltrafilterScaleIndex
          alephSuccSet.{u} alephSuccSet_regulars
          alephSuccSet_cardinalIndex_small
          (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta)) <=
      Cardinal.lift.{u + 1} M.theta := by
  apply mk_cardinalProductAllUltrafilterScaleIndex_le_maxPcf
  let delta : Cardinal.{u} :=
    (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Cardinal.aleph0)
  have hContinuum : (2 : Cardinal.{u}) ^ Cardinal.aleph0 <
      targetAlephOmega :=
    two_power_aleph0_lt_targetAlephOmega_of_strongLimit hStrongLimit
  have hDelta : delta < targetAlephOmega :=
    hStrongLimit.isStrongPrelimit hContinuum
  rw [alephSuccSet_cardinalIndex_mk_eq_aleph0]
  have hLiftDelta : Cardinal.lift.{u + 1} delta =
      (2 : Cardinal.{u + 1}) ^
        ((2 : Cardinal.{u + 1}) ^ Cardinal.aleph0) := by
    simp only [delta, Cardinal.lift_power, Cardinal.lift_ofNat,
      Cardinal.lift_aleph0]
  rw [← hLiftDelta]
  exact Cardinal.lift_le.mpr
    (hDelta.le.trans
      (alephSuccSet_maxPcf_theta_ge_targetAlephOmega M.isMax))

#print axioms
  alephSuccSet_mk_allUltrafilterScaleIndex_le_maxPcf

theorem alephSuccSet_mk_allUltrafilterFiniteMaxIndex_le_maxPcf
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    (M : MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u}) :
    Cardinal.mk
        (CardinalProductFiniteMaxIndex
          (CardinalProductAllUltrafilterScaleIndex
            alephSuccSet.{u} alephSuccSet_regulars
            alephSuccSet_cardinalIndex_small
            (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta))) <=
      Cardinal.lift.{u + 1} M.theta := by
  apply mk_cardinalProductFiniteMaxIndex_le
  · exact alephSuccSet_mk_allUltrafilterScaleIndex_le_maxPcf
      hStrongLimit M
  · exact Cardinal.aleph0_le_lift.mpr M.isRegular.aleph0_le

#print axioms
  alephSuccSet_mk_allUltrafilterFiniteMaxIndex_le_maxPcf

/-! Canonical successor-aleph specialization of Lemma 24.21's pointwise
cover conclusion. -/
theorem alephSuccSet_exists_finset_allUltrafilterScaleFamily_pointwise_cover :
    forall g : ProductElement
        (cardinalProductFrame alephSuccSet.{u}
          (Ideal.emptyOnly (CardinalIndex alephSuccSet.{u}))),
      exists s : Finset
          (CardinalProductAllUltrafilterScaleIndex
            alephSuccSet.{u} alephSuccSet_regulars
            alephSuccSet_cardinalIndex_small
            (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta)),
        forall i, exists k, k ∈ s /\
          (cardinalProductFrame alephSuccSet.{u}
            (Ideal.emptyOnly (CardinalIndex alephSuccSet.{u}))).le i
              (g i)
              (cardinalProductAllUltrafilterScaleFamily
                alephSuccSet.{u} alephSuccSet_regulars
                alephSuccSet_cardinalIndex_small
                (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta) k i) :=
  exists_finset_cardinalProductAllUltrafilterScaleFamily_pointwise_cover
    alephSuccSet.{u} alephSuccSet_regulars
    alephSuccSet_cardinalIndex_small
    (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta)

#print axioms
  alephSuccSet_exists_finset_allUltrafilterScaleFamily_pointwise_cover

theorem alephSuccSet_allUltrafilterFiniteMaxFamily_pointwise_cofinal :
    forall g : ProductElement
        (cardinalProductFrame alephSuccSet.{u}
          (Ideal.emptyOnly (CardinalIndex alephSuccSet.{u}))),
      exists s : CardinalProductFiniteMaxIndex
          (CardinalProductAllUltrafilterScaleIndex
            alephSuccSet.{u} alephSuccSet_regulars
            alephSuccSet_cardinalIndex_small
            (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta)),
        forall i,
          (cardinalProductFrame alephSuccSet.{u}
            (Ideal.emptyOnly (CardinalIndex alephSuccSet.{u}))).le i
              (g i)
              (cardinalProductAllUltrafilterFiniteMaxFamily
                alephSuccSet.{u} alephSuccSet_regulars
                alephSuccSet_cardinalIndex_small
                (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta) s i) :=
  by
    letI : Nonempty (CardinalIndex alephSuccSet.{u}) :=
      ⟨⟨Cardinal.aleph (((0 : Nat) : Ordinal.{u}) + 1), ⟨0, rfl⟩⟩⟩
    exact cardinalProductAllUltrafilterFiniteMaxFamily_pointwise_cofinal
      alephSuccSet.{u} alephSuccSet_regulars
      alephSuccSet_cardinalIndex_small
      (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta)

#print axioms
  alephSuccSet_allUltrafilterFiniteMaxFamily_pointwise_cofinal

end PcfProject
