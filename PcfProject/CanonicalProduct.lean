import PcfProject.PcfBasics
import PcfProject.Stationary
import Mathlib.SetTheory.Cardinal.Cofinality.Basic
import Mathlib.Data.W.Cardinal

/-!
# Concrete cardinal-indexed reduced products

This file instantiates the abstract reduced-product and `PcfRepresentation`
interfaces with actual cardinal-indexed coordinate types. For a member
`theta` of `A`, the coordinate type is `theta.ord.ToType`, whose cardinality is
provably `theta`. Product ideals are required to be duals of ultrafilters,
matching the standard definition of `pcf A`.

For a general cardinal set, the representation still assumes a concrete scale
as input. From such a scale and regularity of its cardinal length, however,
this file proves the genuine true-cofinality minimality statement: every
cofinal family has cardinality at least that length. For a singleton regular
cardinal set, it constructs the scale and proves `pcf {theta} = {theta}`.
The later modules build general scales and generators from additional PCF
hypotheses, then prove the no-holes and max-pcf results.  This module stops at
the concrete reduced-product interface and the singleton computation.
-/

namespace PcfProject

universe u v w

abbrev CardinalIndex (A : CardSet.{u}) : Type (u + 1) :=
  { theta : Cardinal.{u} // A theta }

def singletonCardSet
    (theta : Cardinal.{u}) : CardSet.{u} :=
  fun beta => beta = theta

def singletonCardinalIndex
    (theta : Cardinal.{u}) : CardinalIndex (singletonCardSet theta) :=
  ⟨theta, rfl⟩

theorem CardinalIndex.eq_singletonCardinalIndex
    {theta : Cardinal.{u}}
    (i : CardinalIndex (singletonCardSet theta)) :
    i = singletonCardinalIndex theta :=
  Subtype.ext i.property

noncomputable def cardinalProductFrame
    (A : CardSet.{u})
    (J : Ideal (CardinalIndex A)) :
    ReducedProductFrame.{u + 1, u} where
  Index := CardinalIndex A
  Coord i := i.1.ord.ToType
  le _ := (· <= ·)
  le_refl _ := le_refl
  le_trans _ := le_trans
  J := J

@[simp] theorem mk_cardinalProductFrame_coord
    {A : CardSet.{u}}
    (J : Ideal (CardinalIndex A))
    (i : CardinalIndex A) :
    Cardinal.mk ((cardinalProductFrame A J).Coord i) = i.1 := by
  exact Cardinal.mk_ord_toType i.1

/-! Exact upper bounds in Jech 24.10 may reach the closed coordinate
`theta.ord`, although members of the cardinal product have values strictly
below it.  The following closed product is therefore deliberately larger
than `ProductElement (cardinalProductFrame A J)`. -/
abbrev CardinalProductClosedElement (A : CardSet.{u}) : Type (u + 1) :=
  (k : CardinalIndex A) -> Set.Iic k.1.ord

noncomputable def cardinalProductOrdinalValue
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (x : ProductElement (cardinalProductFrame A J))
    (k : CardinalIndex A) : Ordinal.{u} :=
  ((Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm
    (x k)).1

theorem cardinalProductOrdinalValue_lt
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (x : ProductElement (cardinalProductFrame A J))
    (k : CardinalIndex A) :
    cardinalProductOrdinalValue x k < k.1.ord :=
  ((Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm
    (x k)).2

noncomputable def cardinalProductClosedTop
    (A : CardSet.{u}) : CardinalProductClosedElement A :=
  fun k => ⟨k.1.ord,
    (show k.1.ord <= k.1.ord from le_rfl)⟩

/-! On coordinates where a closed function is strictly below the top,
convert it back to a genuine product member.  A supplied product member fills
the remaining coordinates, so no nonemptiness assumption on the factors is
hidden in this conversion. -/
noncomputable def cardinalProductClosedToProductOn
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (d0 : ProductElement (cardinalProductFrame A J))
    (f : CardinalProductClosedElement A)
    (X : CardinalIndex A -> Prop)
    (hX : forall k, X k -> (f k).1 < k.1.ord) :
    ProductElement (cardinalProductFrame A J) := by
  classical
  exact fun k => if hk : X k then
      Ordinal.ToType.mk ⟨(f k).1, hX k hk⟩
    else d0 k

theorem cardinalProductOrdinalValue_closedToProductOn
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (d0 : ProductElement (cardinalProductFrame A J))
    (f : CardinalProductClosedElement A)
    (X : CardinalIndex A -> Prop)
    (hX : forall k, X k -> (f k).1 < k.1.ord)
    (k : CardinalIndex A)
    (hk : X k) :
    cardinalProductOrdinalValue
      (cardinalProductClosedToProductOn d0 f X hX) k = (f k).1 := by
  simp only [cardinalProductOrdinalValue, cardinalProductClosedToProductOn,
    dif_pos hk]
  exact congrArg Subtype.val
    ((Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm_apply_apply
      ⟨(f k).1, hX k hk⟩)

theorem cardinalProductOrdinalValue_lt_iff
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (x y : ProductElement (cardinalProductFrame A J))
    (k : CardinalIndex A) :
    cardinalProductOrdinalValue x k < cardinalProductOrdinalValue y k <->
      (show k.1.ord.ToType from x k) <
        (show k.1.ord.ToType from y k) := by
  exact
    ((Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm.lt_iff_lt)

def CardinalProductEventuallyLtClosed
    {A : CardSet.{u}}
    (J : Ideal (CardinalIndex A))
    (x : ProductElement (cardinalProductFrame A J))
    (f : CardinalProductClosedElement A) : Prop :=
  J.Eventually (fun k => cardinalProductOrdinalValue x k < (f k).1)

theorem cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (x y : ProductElement (cardinalProductFrame A J)) :
    (cardinalProductFrame A J).eventuallyPointwiseLt x y <->
      J.Eventually (fun k =>
        cardinalProductOrdinalValue x k < cardinalProductOrdinalValue y k) := by
  constructor
  · intro h
    exact J.eventually_mono h (by
      intro k hk
      apply (cardinalProductOrdinalValue_lt_iff x y k).mpr
      exact lt_of_le_of_ne hk.1 (fun hxy => hk.2 hxy.ge))
  · intro h
    exact J.eventually_mono h (by
      intro k hk
      have hxy := (cardinalProductOrdinalValue_lt_iff x y k).mp hk
      exact ⟨hxy.le, not_le_of_gt hxy⟩)

/-! Ordinal-valued specialization of the coordinate-extraction lemma used
in Lemma 24.14. -/
theorem cardinalProduct_exists_ordinalValue_strict_chain_of_not_eventuallyLe
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {s f h next : ProductElement (cardinalProductFrame A J)}
    (hsf : (cardinalProductFrame A J).eventuallyPointwiseLt s f)
    (hfh : (cardinalProductFrame A J).eventuallyPointwiseLt f h)
    (hNotNextLe : Not ((cardinalProductFrame A J).eventuallyLe next h)) :
    exists k : CardinalIndex A,
      cardinalProductOrdinalValue s k < cardinalProductOrdinalValue f k /\
      cardinalProductOrdinalValue f k < cardinalProductOrdinalValue h k /\
      cardinalProductOrdinalValue h k < cardinalProductOrdinalValue next k := by
  obtain ⟨k, hsfk, hfhk, hhnk⟩ :=
    (cardinalProductFrame A J).exists_pointwiseStrict_chain_of_not_eventuallyLe
      (by
        intro k x y
        change (show k.1.ord.ToType from x) <=
            (show k.1.ord.ToType from y) \/
          (show k.1.ord.ToType from y) <=
            (show k.1.ord.ToType from x)
        exact le_total _ _)
      hsf hfh hNotNextLe
  refine ⟨k, (cardinalProductOrdinalValue_lt_iff s f k).mpr ?_,
    (cardinalProductOrdinalValue_lt_iff f h k).mpr ?_,
    (cardinalProductOrdinalValue_lt_iff h next k).mpr ?_⟩
  · exact lt_of_le_of_ne hsfk.1 (fun hEq => hsfk.2 hEq.ge)
  · exact lt_of_le_of_ne hfhk.1 (fun hEq => hfhk.2 hEq.ge)
  · exact lt_of_le_of_ne hhnk.1 (fun hEq => hhnk.2 hEq.ge)

/-! A closed ordinal function can occur on the left of the rapidity
comparison even when it reaches a coordinate top off the eventual set. -/
def CardinalProductClosedEventuallyLtProduct
    {A : CardSet.{u}}
    (J : Ideal (CardinalIndex A))
    (s : CardinalProductClosedElement A)
    (f : ProductElement (cardinalProductFrame A J)) : Prop :=
  J.Eventually (fun k => (s k).1 < cardinalProductOrdinalValue f k)

theorem cardinalProduct_exists_closedOrdinalValue_strict_chain_of_not_eventuallyLe_of_eventually
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {B : CardinalIndex A -> Prop}
    {s : CardinalProductClosedElement A}
    {f h next : ProductElement (cardinalProductFrame A J)}
    (hB : J.Eventually B)
    (hsf : CardinalProductClosedEventuallyLtProduct J s f)
    (hfh : (cardinalProductFrame A J).eventuallyPointwiseLt f h)
    (hNotNextLe : Not ((cardinalProductFrame A J).eventuallyLe next h)) :
    exists k : CardinalIndex A,
      B k /\
      (s k).1 < cardinalProductOrdinalValue f k /\
      cardinalProductOrdinalValue f k < cardinalProductOrdinalValue h k /\
      cardinalProductOrdinalValue h k < cardinalProductOrdinalValue next k := by
  classical
  by_contra hNoChain
  apply hNotNextLe
  have hfh' :=
    (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue f h).mp hfh
  exact J.eventually_mono
    (J.eventually_and (J.eventually_and hsf hfh') hB) (by
      intro k hk
      by_contra hNextNotLe
      have hLast : cardinalProductOrdinalValue h k <
          cardinalProductOrdinalValue next k :=
        (cardinalProductOrdinalValue_lt_iff h next k).mpr
          (lt_of_not_ge hNextNotLe)
      exact hNoChain ⟨k, hk.2, hk.1.1, hk.1.2, hLast⟩)

/-! The literal pointwise supremum used in Definition 24.13.  It is a closed
product because a supremum of values below a coordinate ordinal may equal
that ordinal. -/
noncomputable def cardinalProductClosedPointwiseSup
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {lambda : Cardinal.{u}}
    (f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J))
    (X : Set (Set.Iio lambda.ord)) :
    CardinalProductClosedElement A := by
  classical
  exact fun k =>
    ⟨iSup fun i : Set.Iio lambda.ord =>
        if i ∈ X then cardinalProductOrdinalValue (f i) k else 0,
      Ordinal.iSup_le fun i => by
        split_ifs
        · exact (cardinalProductOrdinalValue_lt (f i) k).le
        · exact bot_le⟩

theorem cardinalProductOrdinalValue_le_closedPointwiseSup
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {lambda : Cardinal.{u}}
    (f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J))
    (X : Set (Set.Iio lambda.ord))
    {i : Set.Iio lambda.ord}
    (hi : i ∈ X)
    (k : CardinalIndex A) :
    cardinalProductOrdinalValue (f i) k <=
      (cardinalProductClosedPointwiseSup f X k).1 := by
  classical
  change cardinalProductOrdinalValue (f i) k <=
    iSup fun j : Set.Iio lambda.ord =>
      if j ∈ X then cardinalProductOrdinalValue (f j) k else 0
  have hLe := Ordinal.le_iSup
    (fun j : Set.Iio lambda.ord =>
      if j ∈ X then cardinalProductOrdinalValue (f j) k else 0) i
  rw [if_pos hi] at hLe
  exact hLe

/-! A pointwise supremum supported by fewer than `k` many family members
stays strictly below the top of a regular coordinate `k`.  The support lives
one universe above the ordinal values, so the lifted form of the cofinality
bound is essential here. -/
theorem cardinalProductClosedPointwiseSup_lt_of_mk_support_lt
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {lambda : Cardinal.{u}}
    (hRegulars : SetOfRegulars A)
    (f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J))
    (X : Set (Set.Iio lambda.ord))
    (k : CardinalIndex A)
    (hXSmall : Cardinal.mk X < Cardinal.lift.{u + 1} k.1) :
    (cardinalProductClosedPointwiseSup f X k).1 < k.1.ord := by
  classical
  let restrictedSup : Ordinal.{u} :=
    iSup fun i : X => cardinalProductOrdinalValue (f i.1) k
  have hRestrictedLt : restrictedSup < k.1.ord := by
    have hLiftSmall :
        Cardinal.lift.{u, u + 1} (Cardinal.mk X) <
          (Ordinal.lift.{u + 1, u} k.1.ord).cof := by
      rw [Cardinal.lift_id'.{u, u + 1}, ← Ordinal.lift_cof,
        (hRegulars k.1 k.2).cof_ord]
      exact hXSmall
    apply Ordinal.lift_iSup_lt_of_lt_cof
      (f := fun i : X => cardinalProductOrdinalValue (f i.1) k)
      (a := k.1.ord) hLiftSmall
    intro i
    exact cardinalProductOrdinalValue_lt (f i.1) k
  apply lt_of_le_of_lt (b := restrictedSup) ?_ hRestrictedLt
  apply Ordinal.iSup_le
  intro i
  by_cases hi : i ∈ X
  · rw [if_pos hi]
    exact Ordinal.le_iSup
      (fun j : X => cardinalProductOrdinalValue (f j.1) k) ⟨i, hi⟩
  · rw [if_neg hi]
    exact bot_le

/-! Arbitrary-type version of the small pointwise-supremum bound.  Unlike
`cardinalProductClosedPointwiseSup`, the family index need not already be an
ordinal initial segment.  This form is used when the family is indexed by a
canonical PCF subtype in the Fubini flattening argument. -/
theorem cardinalProduct_iSup_ordinalValue_lt_of_mk_lt
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    {ι : Type (u + 1)}
    (hSmall : forall k : CardinalIndex A,
      Cardinal.mk ι < Cardinal.lift.{u + 1} k.1)
    (d : ι -> ProductElement (cardinalProductFrame A J))
    (k : CardinalIndex A) :
    (iSup fun i : ι => cardinalProductOrdinalValue (d i) k) < k.1.ord := by
  have hLiftSmall :
      Cardinal.lift.{u, u + 1} (Cardinal.mk ι) <
        (Ordinal.lift.{u + 1, u} k.1.ord).cof := by
    rw [Cardinal.lift_id'.{u, u + 1}, ← Ordinal.lift_cof,
      (hRegulars k.1 k.2).cof_ord]
    exact hSmall k
  apply Ordinal.lift_iSup_lt_of_lt_cof
    (f := fun i : ι => cardinalProductOrdinalValue (d i) k)
    (a := k.1.ord) hLiftSmall
  intro i
  exact cardinalProductOrdinalValue_lt (d i) k

/-! The pointwise supremum of a family smaller than every regular coordinate,
encoded back into the genuine canonical product. -/
noncomputable def cardinalProductPointwiseSupOfSmallFamily
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    {ι : Type (u + 1)}
    (hSmall : forall k : CardinalIndex A,
      Cardinal.mk ι < Cardinal.lift.{u + 1} k.1)
    (d : ι -> ProductElement (cardinalProductFrame A J)) :
    ProductElement (cardinalProductFrame A J) :=
  fun k => Ordinal.ToType.mk
    ⟨iSup fun i : ι => cardinalProductOrdinalValue (d i) k,
      cardinalProduct_iSup_ordinalValue_lt_of_mk_lt
        hRegulars hSmall d k⟩

@[simp] theorem cardinalProductOrdinalValue_pointwiseSupOfSmallFamily
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    {ι : Type (u + 1)}
    (hSmall : forall k : CardinalIndex A,
      Cardinal.mk ι < Cardinal.lift.{u + 1} k.1)
    (d : ι -> ProductElement (cardinalProductFrame A J))
    (k : CardinalIndex A) :
    cardinalProductOrdinalValue
        (cardinalProductPointwiseSupOfSmallFamily hRegulars hSmall d) k =
      iSup fun i : ι => cardinalProductOrdinalValue (d i) k := by
  exact congrArg Subtype.val
    ((Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm_apply_apply
      ⟨iSup fun i : ι => cardinalProductOrdinalValue (d i) k,
        cardinalProduct_iSup_ordinalValue_lt_of_mk_lt
          hRegulars hSmall d k⟩)

theorem cardinalProduct_le_pointwiseSupOfSmallFamily
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    {ι : Type (u + 1)}
    (hSmall : forall k : CardinalIndex A,
      Cardinal.mk ι < Cardinal.lift.{u + 1} k.1)
    (d : ι -> ProductElement (cardinalProductFrame A J))
    (i : ι)
    (k : CardinalIndex A) :
    (show k.1.ord.ToType from d i k) <=
      (show k.1.ord.ToType from
        cardinalProductPointwiseSupOfSmallFamily hRegulars hSmall d k) := by
  rw [← (Ordinal.ToType.mk : Set.Iio k.1.ord ≃o
    k.1.ord.ToType).apply_symm_apply (d i k)]
  apply (Ordinal.ToType.mk : Set.Iio k.1.ord ≃o
    k.1.ord.ToType).monotone
  change cardinalProductOrdinalValue (d i) k <=
    iSup fun j : ι => cardinalProductOrdinalValue (d j) k
  apply le_ciSup (f := fun j : ι =>
    cardinalProductOrdinalValue (d j) k)
  refine ⟨k.1.ord, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact (cardinalProductOrdinalValue_lt (d j) k).le

/-! If the support of a closed pointwise supremum is eventually smaller than
the regular coordinate, the closed supremum has a genuine product
representative on that eventual set.  A supplied product member fills the
remaining coordinates. -/
theorem exists_cardinalProduct_eventually_eq_closedPointwiseSup_of_support_small
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {lambda : Cardinal.{u}}
    (hRegulars : SetOfRegulars A)
    (f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J))
    (X : Set (Set.Iio lambda.ord))
    (hSmall : J.Eventually (fun k =>
      Cardinal.mk X < Cardinal.lift.{u + 1} k.1))
    (d0 : ProductElement (cardinalProductFrame A J)) :
    exists p : ProductElement (cardinalProductFrame A J),
      J.Eventually (fun k => cardinalProductOrdinalValue p k =
        (cardinalProductClosedPointwiseSup f X k).1) := by
  let supportSmall : CardinalIndex A -> Prop := fun k =>
    Cardinal.mk X < Cardinal.lift.{u + 1} k.1
  have hBelow : forall k, supportSmall k ->
      (cardinalProductClosedPointwiseSup f X k).1 < k.1.ord := by
    intro k hk
    exact cardinalProductClosedPointwiseSup_lt_of_mk_support_lt
      hRegulars f X k hk
  let p : ProductElement (cardinalProductFrame A J) :=
    cardinalProductClosedToProductOn d0
      (cardinalProductClosedPointwiseSup f X) supportSmall hBelow
  refine ⟨p, J.eventually_mono hSmall ?_⟩
  intro k hk
  exact cardinalProductOrdinalValue_closedToProductOn d0
    (cardinalProductClosedPointwiseSup f X) supportSmall hBelow k hk

/-! Pointwise-strict directedness simultaneously dominates any small family
of closed pointwise suprema whose supports are eventually smaller than the
regular coordinates.  Each closed supremum is first represented in the
genuine product on its eventual support-small set. -/
theorem exists_cardinalProduct_strictUpperBound_of_closedPointwiseSups
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {lambda theta : Cardinal.{u}}
    {iota : Type u}
    (hRegulars : SetOfRegulars A)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta)
    (hIotaSmall : Cardinal.mk iota < theta)
    (f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J))
    (X : iota -> Set (Set.Iio lambda.ord))
    (hSupportSmall : forall i, J.Eventually (fun k =>
      Cardinal.mk (X i) < Cardinal.lift.{u + 1} k.1))
    (d0 : ProductElement (cardinalProductFrame A J)) :
    exists q : ProductElement (cardinalProductFrame A J),
      forall i, CardinalProductClosedEventuallyLtProduct J
        (cardinalProductClosedPointwiseSup f (X i)) q := by
  choose p hp using fun i =>
    exists_cardinalProduct_eventually_eq_closedPointwiseSup_of_support_small
      hRegulars f (X i) (hSupportSmall i) d0
  obtain ⟨q, hq⟩ := hDirected iota hIotaSmall p
  refine ⟨q, ?_⟩
  intro i
  have hpq := (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue
    (p i) q).mp (hq i)
  exact J.eventually_mono (J.eventually_and (hp i) hpq) (by
    intro k hk
    rw [← hk.1]
    exact hk.2)

/-! The canonical support used at global stage `alpha` for a terminal stage
`beta`.  When `alpha < beta`, it is the image in `Iio lambda.ord` of the
small initial piece of the chosen cofinality club of `beta`; otherwise it is
empty. -/
noncomputable def cardinalProductRapidSupport
    (lambda : Cardinal.{u})
    (beta alpha : Set.Iio lambda.ord) :
    Set (Set.Iio lambda.ord) := by
  classical
  exact if h : alpha < beta then
      (fun xi : Set.Iio beta.1 =>
        (⟨xi.1, by
          have hXi : xi.1 < beta.1 := by
            simpa only [Set.mem_Iio] using xi.2
          have hBeta : beta.1 < lambda.ord := by
            simpa only [Set.mem_Iio] using beta.2
          exact hXi.trans hBeta⟩ : Set.Iio lambda.ord)) ''
        (smallInitialClub beta.1 ∩
          (Set.Iio (⟨alpha.1, h⟩ : Set.Iio beta.1) :
            Set (Set.Iio beta.1)))
    else ∅

theorem cardinalProductRapidSupport_eq
    {lambda : Cardinal.{u}}
    {beta alpha : Set.Iio lambda.ord}
    (hAlphaBeta : alpha < beta) :
    cardinalProductRapidSupport lambda beta alpha =
      (fun xi : Set.Iio beta.1 =>
        (⟨xi.1, by
          have hXi : xi.1 < beta.1 := by
            simpa only [Set.mem_Iio] using xi.2
          have hBeta : beta.1 < lambda.ord := by
            simpa only [Set.mem_Iio] using beta.2
          exact hXi.trans hBeta⟩ : Set.Iio lambda.ord)) ''
        (smallInitialClub beta.1 ∩
          (Set.Iio (⟨alpha.1, hAlphaBeta⟩ : Set.Iio beta.1) :
            Set (Set.Iio beta.1))) := by
  classical
  rw [cardinalProductRapidSupport, dif_pos hAlphaBeta]

theorem cardinalProductRapidSupport_mk_lt_cof
    {lambda : Cardinal.{u}}
    {beta alpha : Set.Iio lambda.ord}
    (hBetaLimit : Order.IsSuccLimit beta.1)
    (hAlphaBeta : alpha < beta) :
    Cardinal.mk (cardinalProductRapidSupport lambda beta alpha) <
      Cardinal.lift.{u + 1} beta.1.cof := by
  rw [cardinalProductRapidSupport_eq hAlphaBeta]
  exact Cardinal.mk_image_le.trans_lt
    (smallInitialClub_initial_mk_lt_cof hBetaLimit
      (⟨alpha.1, hAlphaBeta⟩ : Set.Iio beta.1))

/-! Only terminal stages of cofinality below `kappa` are active in the
simultaneous rapid recursion. -/
noncomputable def cardinalProductRapidSupportBelow
    (kappa lambda : Cardinal.{u})
    (beta alpha : Set.Iio lambda.ord) :
    Set (Set.Iio lambda.ord) := by
  classical
  exact if beta.1.cof < kappa then
      cardinalProductRapidSupport lambda beta alpha
    else ∅

theorem cardinalProductRapidSupportBelow_eq
    {kappa lambda : Cardinal.{u}}
    {beta alpha : Set.Iio lambda.ord}
    (hBetaCof : beta.1.cof < kappa) :
    cardinalProductRapidSupportBelow kappa lambda beta alpha =
      cardinalProductRapidSupport lambda beta alpha := by
  classical
  rw [cardinalProductRapidSupportBelow, if_pos hBetaCof]

theorem cardinalProductRapidSupportBelow_mk_lt_cof
    {kappa lambda : Cardinal.{u}}
    {beta alpha : Set.Iio lambda.ord}
    (hBetaCof : beta.1.cof < kappa)
    (hBetaLimit : Order.IsSuccLimit beta.1)
    (hAlphaBeta : alpha < beta) :
    Cardinal.mk
        (cardinalProductRapidSupportBelow kappa lambda beta alpha) <
      Cardinal.lift.{u + 1} beta.1.cof := by
  rw [cardinalProductRapidSupportBelow_eq hBetaCof]
  exact cardinalProductRapidSupport_mk_lt_cof
    hBetaLimit hAlphaBeta

theorem cardinalProductRapidSupportBelow_subset_Iio
    {kappa lambda : Cardinal.{u}}
    {beta alpha : Set.Iio lambda.ord} :
    cardinalProductRapidSupportBelow kappa lambda beta alpha ⊆
      Set.Iio alpha := by
  classical
  intro i hi
  by_cases hBetaCof : beta.1.cof < kappa
  · rw [cardinalProductRapidSupportBelow_eq hBetaCof] at hi
    by_cases hAlphaBeta : alpha < beta
    · rw [cardinalProductRapidSupport_eq hAlphaBeta] at hi
      obtain ⟨xi, hxi, rfl⟩ := hi
      have hXiAlpha : xi.1 < alpha.1 := by
        simpa only [Set.mem_inter_iff, Set.mem_Iio] using hxi.2
      simpa only [Set.mem_Iio] using hXiAlpha
    · rw [cardinalProductRapidSupport,
        dif_neg hAlphaBeta] at hi
      exact hi.elim
  · rw [cardinalProductRapidSupportBelow, if_neg hBetaCof] at hi
    exact hi.elim

theorem cardinalProductClosedPointwiseSup_congr
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {lambda : Cardinal.{u}}
    {f g : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J)}
    {X : Set (Set.Iio lambda.ord)}
    (hfg : Set.EqOn f g X) :
    cardinalProductClosedPointwiseSup f X =
      cardinalProductClosedPointwiseSup g X := by
  classical
  funext k
  apply Subtype.ext
  change (iSup fun i : Set.Iio lambda.ord =>
      if i ∈ X then cardinalProductOrdinalValue (f i) k else 0) =
    iSup fun i : Set.Iio lambda.ord =>
      if i ∈ X then cardinalProductOrdinalValue (g i) k else 0
  congr 1
  funext i
  by_cases hi : i ∈ X
  · rw [if_pos hi, if_pos hi, hfg hi]
  · rw [if_neg hi, if_neg hi]

/-! Source-level Definition 24.13.  At every `gamma`-cofinal terminal
ordinal `beta`, rapidity supplies a club `C` such that each limit-stage
family member eventually dominates the literal pointwise supremum over
`C ∩ alpha`.  The supremum is closed-valued because it may reach a
coordinate top away from the eventual comparison set. -/
def CardinalProductGammaRapid
    {A : CardSet.{u}}
    (J : Ideal (CardinalIndex A))
    (gamma lambda : Cardinal.{u})
    (f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J)) : Prop :=
  forall beta : Set.Iio lambda.ord, beta.1.cof = gamma ->
    exists C : Set (Set.Iio beta.1), IsClub C /\
      forall alpha : Set.Iio beta.1, Order.IsSuccLimit alpha.1 ->
        CardinalProductClosedEventuallyLtProduct J
          (cardinalProductClosedPointwiseSup f
            ((fun xi : Set.Iio beta.1 =>
              (⟨xi.1, by
                have hXi : xi.1 < beta.1 := by
                  simpa only [Set.mem_Iio] using xi.2
                have hBeta : beta.1 < lambda.ord := by
                  simpa only [Set.mem_Iio] using beta.2
                exact hXi.trans hBeta⟩ :
                Set.Iio lambda.ord)) ''
                (C ∩ Set.Iio alpha)))
          (f ⟨alpha.1, by
            have hAlpha : alpha.1 < beta.1 := by
              simpa only [Set.mem_Iio] using alpha.2
            have hBeta : beta.1 < lambda.ord := by
              simpa only [Set.mem_Iio] using beta.2
            exact hAlpha.trans hBeta⟩)

theorem CardinalProductGammaRapid.localize
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {gamma lambda : Cardinal.{u}}
    {f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J)}
    (hRapid : CardinalProductGammaRapid J gamma lambda f)
    (X : CardinalIndex A -> Prop) :
    CardinalProductGammaRapid (J.localize X) gamma lambda f := by
  intro beta hBetaCof
  obtain ⟨C, hCClub, hC⟩ := hRapid beta hBetaCof
  refine ⟨C, hCClub, ?_⟩
  intro alpha hAlphaLimit
  exact J.le_localize X _ (hC alpha hAlphaLimit)


theorem exists_eventualDominatingStage_of_gammaRapid_of_smallSets_of_support
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {gamma lambda : Cardinal.{u}}
    (hGamma : gamma.IsRegular)
    (hGammaUncountable : Cardinal.aleph0 < gamma)
    (hLambda : lambda.IsRegular)
    (hGammaLambda : gamma < lambda)
    (B : CardinalIndex A -> Prop)
    (hIndexSupportSmall : Cardinal.lift.{u, u + 1}
        (Cardinal.mk {k : CardinalIndex A // B k}) <
          Cardinal.lift.{u + 1} gamma)
    (hB : J.Eventually B)
    (S : CardinalIndex A -> Set (Ordinal.{u}))
    (hSSmall : forall k,
      Cardinal.lift.{u, u + 1} (Cardinal.mk (S k)) <
        Cardinal.lift.{u + 1} gamma)
    (f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J))
    (hIncreasing : forall {alpha beta : Set.Iio lambda.ord},
      alpha < beta ->
        (cardinalProductFrame A J).eventuallyPointwiseLt
          (f alpha) (f beta))
    (hRapid : CardinalProductGammaRapid J gamma lambda f) :
    exists alpha : Set.Iio lambda.ord,
      forall h : ProductElement (cardinalProductFrame A J),
        (forall k, cardinalProductOrdinalValue h k ∈ S k) ->
        (cardinalProductFrame A J).eventuallyPointwiseLt (f alpha) h ->
          forall next : Set.Iio lambda.ord, alpha < next ->
            (cardinalProductFrame A J).eventuallyLe (f next) h := by
  classical
  by_contra hNoStage
  push Not at hNoStage
  choose counter hCounterAllowed hCounter next hStageNext hNotNext using hNoStage
  obtain ⟨beta, hBetaLt, stage, hBetaCof, hStageNormal,
    hStageCofinal, hAdvanceStage⟩ :=
    exists_normal_cofinal_advance_sequence_below
      hGamma hLambda hGammaLambda next hStageNext
  let betaAtLambda : Set.Iio lambda.ord := ⟨beta, hBetaLt⟩
  obtain ⟨C, hCClub, hRapidC⟩ := hRapid betaAtLambda hBetaCof
  let I := gamma.ord.ToType
  haveI : Nonempty I :=
    ⟨Ordinal.ToType.mk ⟨0, hGamma.ord_pos⟩⟩
  letI : NoMaxOrder I := Cardinal.noMaxOrder hGamma.aleph0_le
  have hCofI : Order.cof I = gamma := by
    dsimp only [I]
    rw [Ordinal.cof_toType, hGamma.cof_ord]
  have hCofINe : Order.cof I ≠ Cardinal.aleph0 := by
    rw [hCofI]
    exact ne_of_gt hGammaUncountable
  have hCofBetaIioNe : Order.cof (Set.Iio beta) ≠ Cardinal.aleph0 := by
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, hBetaCof]
    have hLift : Cardinal.lift.{u + 1} Cardinal.aleph0 <
        Cardinal.lift.{u + 1} gamma :=
      Cardinal.lift_lt.mpr hGammaUncountable
    exact ne_of_gt (by simpa using hLift)
  let D : Set I := stage ⁻¹' C
  have hDClub : IsClub D :=
    isClub_preimage_of_isNormal_of_isCofinal
      hStageNormal hStageCofinal hCofBetaIioNe hCClub
  let inclusionD : D -> I := fun i => i.1
  have hInclusionDStrict : StrictMono inclusionD := by
    intro i j hij
    exact hij
  have hInclusionDCofinal : IsCofinal (Set.range inclusionD) := by
    simpa only [inclusionD, Subtype.range_coe_subtype] using hDClub.isCofinal
  have hCofD : Order.cof D = gamma := by
    rw [Order.cof_congr_of_strictMono hInclusionDStrict hInclusionDCofinal,
      hCofI]
  have hDNonempty : D.Nonempty := by
    obtain ⟨i, hiD, _⟩ := hDClub.isCofinal (Classical.choice inferInstance)
    exact ⟨i, hiD⟩
  letI : Nonempty D := ⟨⟨hDNonempty.choose, hDNonempty.choose_spec⟩⟩
  letI : NoMaxOrder D := by
    constructor
    intro i
    obtain ⟨j, hij⟩ := exists_gt i.1
    obtain ⟨k, hkD, hjk⟩ := hDClub.isCofinal j
    exact ⟨⟨k, hkD⟩, hij.trans_le hjk⟩
  letI := WellFoundedLT.toOrderBot D
  letI := WellFoundedLT.conditionallyCompleteLinearOrderBot D
  letI : SuccOrder D := SuccOrder.ofLinearWellFoundedLT D
  let Lset : Set D := StrictLimitPoints (Set.univ : Set D)
  have hCofDNe : Order.cof D ≠ Cardinal.aleph0 := by
    rw [hCofD]
    exact ne_of_gt hGammaUncountable
  have hLClub : IsClub Lset :=
    strictLimitPoints_isClub hCofDNe IsCofinal.univ
  let L := Lset
  have hLNonempty : Lset.Nonempty := by
    obtain ⟨i, hiL, _⟩ := hLClub.isCofinal (Classical.choice inferInstance)
    exact ⟨i, hiL⟩
  letI : Nonempty L := ⟨⟨hLNonempty.choose, hLNonempty.choose_spec⟩⟩
  let inclusionL : L -> D := fun i => i.1
  have hInclusionLStrict : StrictMono inclusionL := by
    intro i j hij
    exact hij
  have hInclusionLCofinal : IsCofinal (Set.range inclusionL) := by
    simpa only [inclusionL, Subtype.range_coe_subtype] using hLClub.isCofinal
  have hCofL : Order.cof L = gamma := by
    rw [Order.cof_congr_of_strictMono hInclusionLStrict hInclusionLCofinal,
      hCofD]
  let atStage (i : D) : Set.Iio lambda.ord :=
    ⟨(stage i.1).1, by
      have hiBeta : (stage i.1).1 < beta := by
        simpa only [Set.mem_Iio] using (stage i.1).2
      exact hiBeta.trans hBetaLt⟩
  have hDSubtypeNormal : Order.IsNormal (fun i : D => i.1) :=
    IsClub.isNormal_subtypeVal hDClub
  have hStageDNormal : Order.IsNormal (fun i : D => stage i.1) :=
    hStageNormal.comp hDSubtypeNormal
  have hBetaInclusionNormal :
      Order.IsNormal (fun x : Set.Iio beta => x.1) := by
    simpa only [Set.principalSegIio_apply] using
      (Set.principalSegIio beta).isNormal
  have hStageDValueNormal :
      Order.IsNormal (fun i : D => (stage i.1).1) :=
    hBetaInclusionNormal.comp hStageDNormal
  have hLimitIndex : forall i : L, Order.IsSuccLimit (i.1 : D) := by
    intro i
    have hi := i.2
    refine ⟨not_isMin_iff.mpr hi.1, ?_⟩
    intro b hCov
    obtain ⟨c, _hc, hbc, hci⟩ := hi.2 b hCov.lt
    exact ((not_covBy_iff hCov.lt).mpr ⟨c, hbc, hci⟩) hCov
  let nextD (i : L) : D := Order.succ (i.1 : D)
  have hINextD : forall i : L, (i.1 : D) < nextD i := by
    intro i
    exact Order.lt_succ _
  have hNextDBeforeLater : forall {i j : L}, i < j ->
      nextD i < (j.1 : D) := by
    intro i j hij
    exact (hLimitIndex j).succ_lt hij
  let h : L -> ProductElement (cardinalProductFrame A J) :=
    fun i => counter (atStage i.1)
  let envelope (i : L) : CardinalProductClosedElement A :=
    cardinalProductClosedPointwiseSup f
      ((fun xi : Set.Iio beta =>
        (⟨xi.1, by
          have hXi : xi.1 < beta := by
            simpa only [Set.mem_Iio] using xi.2
          exact hXi.trans hBetaLt⟩ : Set.Iio lambda.ord)) ''
        (C ∩ Set.Iio (stage i.1.1)))
  have hEnvelopeStart : forall i : L,
      CardinalProductClosedEventuallyLtProduct J
        (envelope i) (f (atStage i.1)) := by
    intro i
    have hStageLimit : Order.IsSuccLimit (stage i.1.1).1 :=
      hStageDValueNormal.map_isSuccLimit (hLimitIndex i)
    simpa only [envelope, atStage, betaAtLambda] using
      hRapidC (stage i.1.1) hStageLimit
  have hEndpointNotLe : forall i : L,
      Not ((cardinalProductFrame A J).eventuallyLe
        (f (atStage (nextD i))) (h i)) := by
    intro i hEndpointLe
    have hRawNextLt : next (atStage i.1) < atStage (nextD i) := by
      exact hAdvanceStage i.1.1 (nextD i).1 (hINextD i)
    have hRawNextLe : (cardinalProductFrame A J).eventuallyLe
        (f (next (atStage i.1))) (f (atStage (nextD i))) :=
      J.eventually_mono (hIncreasing hRawNextLt) (by
        intro k hk
        exact hk.1)
    exact hNotNext (atStage i.1)
      ((cardinalProductFrame A J).eventuallyLe_trans hRawNextLe hEndpointLe)
  have hChain : forall i : L, exists k : CardinalIndex A,
      B k /\
      (envelope i k).1 < cardinalProductOrdinalValue (f (atStage i.1)) k /\
        cardinalProductOrdinalValue (f (atStage i.1)) k <
          cardinalProductOrdinalValue (h i) k /\
        cardinalProductOrdinalValue (h i) k <
          cardinalProductOrdinalValue (f (atStage (nextD i))) k := by
    intro i
    exact
      cardinalProduct_exists_closedOrdinalValue_strict_chain_of_not_eventuallyLe_of_eventually
        hB (hEnvelopeStart i) (hCounter (atStage i.1)) (hEndpointNotLe i)
  let coordinate : L -> CardinalIndex A :=
    fun i => Classical.choose (hChain i)
  have hCoordinateSupport : forall i, B (coordinate i) := by
    intro i
    exact (Classical.choose_spec (hChain i)).1
  let supportedCoordinate : L -> {k : CardinalIndex A // B k} :=
    fun i => ⟨coordinate i, hCoordinateSupport i⟩
  let values : CardinalIndex A -> L -> Ordinal.{u} :=
    fun k i => cardinalProductOrdinalValue (h i) k
  have hValueSmall : forall k,
      Cardinal.lift.{u, u + 1} (Cardinal.mk (Set.range (values k))) <
        Cardinal.lift.{u + 1, u} (Order.cof L) := by
    intro k
    rw [hCofL]
    let embed : Set.range (values k) -> S k := fun x =>
      ⟨x.1, by
        obtain ⟨i, hi⟩ := x.2
        rw [← hi]
        exact hCounterAllowed (atStage i.1) k⟩
    have hEmbed : Function.Injective embed := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : S k => z.1) hxy
    have hRangeLe : Cardinal.mk (Set.range (values k)) <=
        Cardinal.mk (S k) := Cardinal.mk_le_of_injective hEmbed
    exact (Cardinal.lift_le.mpr hRangeLe).trans_lt (hSSmall k)
  let supportedValues : {k : CardinalIndex A // B k} -> L -> Ordinal.{u} :=
    fun k => values k.1
  apply no_repeated_coordinate_strict_pattern_on_club_of_lift_small
    (alpha := L) (D := Set.univ)
    (by rw [hCofL]; exact ne_of_gt hGammaUncountable)
    (by simpa only [hCofL] using hIndexSupportSmall)
    IsClub.univ supportedCoordinate supportedValues (fun k => hValueSmall k.1)
  intro i j _hi _hj hij hSupportedCoordinateEq
  have hCoordinateEq : coordinate i = coordinate j :=
    congrArg Subtype.val hSupportedCoordinateEq
  have hNextStageC : stage (nextD i).1 ∈ C := (nextD i).2
  have hNextStageBefore : stage (nextD i).1 < stage j.1.1 := by
    exact hStageNormal.strictMono (hNextDBeforeLater hij)
  have hSupport : atStage (nextD i) ∈
      (fun xi : Set.Iio beta =>
        (⟨xi.1, by
          have hXi : xi.1 < beta := by
            simpa only [Set.mem_Iio] using xi.2
          exact hXi.trans hBetaLt⟩ : Set.Iio lambda.ord)) ''
        (C ∩ Set.Iio (stage j.1.1)) := by
    exact ⟨stage (nextD i).1,
      ⟨hNextStageC, hNextStageBefore⟩, rfl⟩
  have hMiddle := cardinalProductOrdinalValue_le_closedPointwiseSup
    f _ hSupport (coordinate i)
  have hFirst := (Classical.choose_spec (hChain i)).2.2.2
  have hLast := (Classical.choose_spec (hChain j)).2.1.trans
    (Classical.choose_spec (hChain j)).2.2.1
  change cardinalProductOrdinalValue (h i) (coordinate i) <
    cardinalProductOrdinalValue (f (atStage (nextD i))) (coordinate i)
      at hFirst
  change (envelope j (coordinate j)).1 <
    cardinalProductOrdinalValue (h j) (coordinate j) at hLast
  dsimp only [supportedValues, supportedCoordinate, values]
  have hMiddle' :
      cardinalProductOrdinalValue (f (atStage (nextD i))) (coordinate j) <=
        (envelope j (coordinate j)).1 := by
    rw [hCoordinateEq] at hMiddle
    simpa only [envelope] using hMiddle
  rw [hCoordinateEq] at hFirst ⊢
  exact (hFirst.trans_le hMiddle').trans hLast

theorem CardinalProductEventuallyLtClosed.trans_of_eventuallyPointwiseLt
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {x y : ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hxy : (cardinalProductFrame A J).eventuallyPointwiseLt x y)
    (hyf : CardinalProductEventuallyLtClosed J y f) :
    CardinalProductEventuallyLtClosed J x f := by
  have hxy' :=
    (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue x y).mp hxy
  exact J.eventually_mono (J.eventually_and hxy' hyf) (by
    intro k hk
    exact hk.1.trans hk.2)

theorem CardinalProductEventuallyLtClosed.trans_of_eventuallyLe
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {x y : ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hxy : (cardinalProductFrame A J).eventuallyLe x y)
    (hyf : CardinalProductEventuallyLtClosed J y f) :
    CardinalProductEventuallyLtClosed J x f := by
  exact J.eventually_mono (J.eventually_and hxy hyf) (by
    intro k hk
    have hValueLe : cardinalProductOrdinalValue x k <=
        cardinalProductOrdinalValue y k := by
      exact ((Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm
        |>.monotone hk.1)
    exact hValueLe.trans_lt hk.2)

/-! A closed exact upper bound: every family member is strictly below `f`,
and every genuine product member below `f` is eventually dominated by the
family.  Allowing `f` to be closed, rather than a product member, is the
distinction needed for the top-function argument in Corollary 24.12. -/
def CardinalProductClosedExactUpperBound
    {A : CardSet.{u}}
    (J : Ideal (CardinalIndex A))
    {iota : Type w}
    (d : iota -> ProductElement (cardinalProductFrame A J))
    (f : CardinalProductClosedElement A) : Prop :=
  (forall i, CardinalProductEventuallyLtClosed J (d i) f) /\
  forall h : ProductElement (cardinalProductFrame A J),
    CardinalProductEventuallyLtClosed J h f ->
      exists i, (cardinalProductFrame A J).eventuallyLe h (d i)

/-! Exact upper bounds are invariant under a bijective reindexing of the
family.  This bridges the literal ordinal initial segment used in the source
rapid recursion with the `ToType` index used by canonical scale lengths. -/
theorem CardinalProductClosedExactUpperBound.reindex
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {iota : Type v} {kappa : Type w}
    {d : iota -> ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hExact : CardinalProductClosedExactUpperBound J d f)
    (e : iota ≃ kappa) :
    CardinalProductClosedExactUpperBound J (fun k => d (e.symm k)) f := by
  constructor
  · intro k
    exact hExact.1 (e.symm k)
  · intro h hh
    obtain ⟨i, hi⟩ := hExact.2 h hh
    exact ⟨e i, by simpa using hi⟩

/-! If a closed exact upper bound reaches the coordinate top almost
everywhere, the original family is cofinal in the genuine product.  This is
the final implication used in Theorem 24.16 after Corollary 24.15 forces the
coordinate cofinalities, and it uses the closedness of `f` to turn the
eventual lower bound into equality with the top. -/
theorem CardinalProductClosedExactUpperBound.isCofinalFamily_of_eventually_top
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {iota : Type w}
    {d : iota -> ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hExact : CardinalProductClosedExactUpperBound J d f)
    (hTop : J.Eventually (fun k => k.1.ord <= (f k).1)) :
    (cardinalProductFrame A J).IsCofinalFamily d := by
  intro h
  apply hExact.2 h
  exact J.eventually_mono hTop (by
    intro k hk
    rw [show (f k).1 = k.1.ord from le_antisymm (f k).2 hk]
    exact cardinalProductOrdinalValue_lt h k)

/-! Closed exactness survives localization.  A local test is spliced with
one fixed family member off the localizing predicate before global exactness
is applied. -/
theorem CardinalProductClosedExactUpperBound.localize
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {iota : Type w}
    {d : iota -> ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hExact : CardinalProductClosedExactUpperBound J d f)
    (i0 : iota)
    (X : CardinalIndex A -> Prop) :
    CardinalProductClosedExactUpperBound (J.localize X) d f := by
  classical
  constructor
  · intro i
    exact J.le_localize X _ (hExact.1 i)
  · intro h hh
    let h' : ProductElement (cardinalProductFrame A J) := fun k =>
      if X k then h k else d i0 k
    have hh' : CardinalProductEventuallyLtClosed J h' f := by
      have hhX : J.Small (fun k =>
          Not (cardinalProductOrdinalValue h k < (f k).1) /\ X k) := hh
      have hd0 : J.Small (fun k =>
          Not (cardinalProductOrdinalValue (d i0) k < (f k).1)) :=
        hExact.1 i0
      exact J.subset_small (J.union_small hhX hd0) (by
        intro k hk
        by_cases hkX : X k
        · left
          refine ⟨?_, hkX⟩
          simpa only [h', cardinalProductOrdinalValue, if_pos hkX] using hk
        · right
          simpa only [h', cardinalProductOrdinalValue, if_neg hkX] using hk)
    obtain ⟨i, hi⟩ := hExact.2 h' hh'
    refine ⟨i, ?_⟩
    change J.Small (fun k => Not
      ((cardinalProductFrame A J).le k (h k) (d i k)) /\ X k)
    exact J.subset_small hi (by
      intro k hk
      have : Not ((cardinalProductFrame A J).le k (h' k) (d i k)) := by
        simpa only [h', if_pos hk.2] using hk.1
      exact this)

/-! Corollary 24.15.  A gamma-rapid increasing sequence cannot have a closed
exact upper bound whose coordinate cofinality is below gamma on a positive
set.  On that set, fundamental sequences in the coordinates of the upper
bound form the small sets to which Lemma 24.14 applies.  A later family member
selects points from those sequences; exactness and rapid domination then give
opposite eventual inequalities over the localized proper ideal. -/
theorem CardinalProductClosedExactUpperBound.eventually_cof_ge_of_gammaRapid_of_support
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {gamma lambda : Cardinal.{u}}
    (hGamma : gamma.IsRegular)
    (hGammaUncountable : Cardinal.aleph0 < gamma)
    (hLambda : lambda.IsRegular)
    (hGammaLambda : gamma < lambda)
    (R : CardinalIndex A -> Prop)
    (hIndexSupportSmall : Cardinal.lift.{u, u + 1}
        (Cardinal.mk {k : CardinalIndex A // R k}) <
          Cardinal.lift.{u + 1} gamma)
    (hR : J.Eventually R)
    (f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J))
    (hIncreasing : forall {alpha beta : Set.Iio lambda.ord},
      alpha < beta ->
        (cardinalProductFrame A J).eventuallyPointwiseLt
          (f alpha) (f beta))
    (hRapid : CardinalProductGammaRapid J gamma lambda f)
    (g : CardinalProductClosedElement A)
    (hExact : CardinalProductClosedExactUpperBound J f g) :
    J.Eventually (fun k => gamma <= (g k).1.cof) := by
  classical
  let B : CardinalIndex A -> Prop := fun k => (g k).1.cof < gamma
  by_contra hNotSmall
  change Not (J.Small (fun k => Not (gamma <= (g k).1.cof))) at hNotSmall
  have hBNotSmall : Not (J.Small B) := by
    simpa only [B, not_le] using hNotSmall
  have hBProper : (J.localize B).IsProper :=
    (J.localize_isProper_iff B).mpr hBNotSmall
  let i0 : Set.Iio lambda.ord := ⟨0, hLambda.ord_pos⟩
  choose q hq using fun k : CardinalIndex A =>
    Ordinal.exists_isFundamentalSeq
      (o := (g k).1) (a := (g k).1.cof.ord) rfl
  let base (k : CardinalIndex A) : Set (Ordinal.{u}) :=
    Set.range (fun i : Set.Iio (g k).1.cof.ord => (q k i).1)
  let fallback (k : CardinalIndex A) : Ordinal.{u} :=
    cardinalProductOrdinalValue (f i0) k
  let S (k : CardinalIndex A) : Set (Ordinal.{u}) :=
    if B k then Set.insert (fallback k) (base k) else {fallback k}
  have hSSmall : forall k,
      Cardinal.lift.{u, u + 1} (Cardinal.mk (S k)) <
        Cardinal.lift.{u + 1} gamma := by
    intro k
    rw [Cardinal.lift_id'.{u, u + 1}]
    by_cases hk : B k
    · rw [show S k = Set.insert (fallback k) (base k) by
        simp only [S, if_pos hk]]
      have hRangeLe : Cardinal.mk (base k) <=
          Cardinal.lift.{u + 1} (g k).1.cof := by
        calc
          Cardinal.mk (base k) <=
              Cardinal.mk (Set.Iio (g k).1.cof.ord) := by
            exact Cardinal.mk_range_le
          _ = Cardinal.lift.{u + 1} (g k).1.cof := by
            rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
      have hRangeLt : Cardinal.mk (base k) <
          Cardinal.lift.{u + 1} gamma :=
        hRangeLe.trans_lt (Cardinal.lift_lt.mpr hk)
      exact (Cardinal.mk_insert_le).trans_lt
        (Cardinal.add_lt_of_lt
          (by
            have hAlephLift : Cardinal.aleph0.{u + 1} <=
                Cardinal.lift.{u + 1} gamma := by
              calc
                Cardinal.aleph0.{u + 1} =
                    Cardinal.lift.{u + 1, u} Cardinal.aleph0.{u} :=
                  (Cardinal.lift_aleph0.{u + 1, u}).symm
                _ <= Cardinal.lift.{u + 1, u} gamma :=
                  Cardinal.lift_le.{u + 1, u}.2 hGamma.aleph0_le
            exact hAlephLift)
          hRangeLt
          (by
            have hOne : (1 : Cardinal.{u}) < gamma :=
              Cardinal.one_lt_aleph0.trans hGammaUncountable
            have hOneLift : Cardinal.lift.{u + 1} (1 : Cardinal.{u}) <
                Cardinal.lift.{u + 1} gamma :=
              Cardinal.lift_lt.{u, u + 1}.mpr hOne
            calc
              (1 : Cardinal.{u + 1}) =
                  Cardinal.lift.{u + 1, u} (1 : Cardinal.{u}) :=
                (Cardinal.lift_one.{u, u + 1}).symm
              _ < Cardinal.lift.{u + 1, u} gamma := hOneLift))
    · rw [show S k = ({fallback k} : Set (Ordinal.{u})) by
        simp only [S, if_neg hk]]
      rw [Cardinal.mk_singleton]
      have hOne : (1 : Cardinal.{u}) < gamma :=
        Cardinal.one_lt_aleph0.trans hGammaUncountable
      have hOneLift : Cardinal.lift.{u + 1} (1 : Cardinal.{u}) <
          Cardinal.lift.{u + 1} gamma :=
        Cardinal.lift_lt.{u, u + 1}.mpr hOne
      calc
        (1 : Cardinal.{u + 1}) =
            Cardinal.lift.{u + 1, u} (1 : Cardinal.{u}) :=
          (Cardinal.lift_one.{u, u + 1}).symm
        _ < Cardinal.lift.{u + 1, u} gamma := hOneLift
  have hIncreasingB : forall {alpha beta : Set.Iio lambda.ord},
      alpha < beta ->
        (cardinalProductFrame A (J.localize B)).eventuallyPointwiseLt
          (f alpha) (f beta) := by
    intro alpha beta hab
    exact (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
      (J.localize B) (J.le_localize B) (hIncreasing hab)
  obtain ⟨alpha, hAlpha⟩ :=
    exists_eventualDominatingStage_of_gammaRapid_of_smallSets_of_support
      (J := J.localize B)
      hGamma hGammaUncountable hLambda hGammaLambda R
        hIndexSupportSmall (J.le_localize B _ hR)
        S hSSmall f hIncreasingB (hRapid.localize B)
  letI : NoMaxOrder (Set.Iio lambda.ord) :=
    (Cardinal.isSuccLimit_ord hLambda.aleph0_le).isSuccPrelimit.noMaxOrder_Iio
  obtain ⟨beta, hAlphaBeta⟩ := exists_gt alpha
  have hExistsCofinalValue : forall k : CardinalIndex A,
      cardinalProductOrdinalValue (f beta) k < (g k).1 ->
        exists x : Ordinal.{u},
          x ∈ base k /\
          cardinalProductOrdinalValue (f beta) k <= x /\
          x < (g k).1 := by
    intro k hkBeta
    obtain ⟨y, hyRange, hBetaY⟩ :=
      (hq k).isCofinal_range
        ⟨cardinalProductOrdinalValue (f beta) k, hkBeta⟩
    refine ⟨y.1, ?_, hBetaY, y.2⟩
    obtain ⟨idx, hIdx⟩ := hyRange
    exact ⟨idx, congrArg Subtype.val hIdx⟩
  let cofinalValue (k : CardinalIndex A) : Ordinal.{u} :=
    Classical.epsilon (fun x : Ordinal.{u} =>
      x ∈ base k /\
      cardinalProductOrdinalValue (f beta) k <= x /\
      x < (g k).1)
  have hCofinalValueSpec (k : CardinalIndex A)
      (hkBeta : cardinalProductOrdinalValue (f beta) k < (g k).1) :
      cofinalValue k ∈ base k /\
      cardinalProductOrdinalValue (f beta) k <= cofinalValue k /\
      cofinalValue k < (g k).1 := by
    exact Classical.epsilon_spec (hExistsCofinalValue k hkBeta)
  let selected (k : CardinalIndex A) : Ordinal.{u} :=
    if B k /\ cardinalProductOrdinalValue (f beta) k < (g k).1 then
      cofinalValue k
    else fallback k
  have hSelectedBound : forall k, selected k < k.1.ord := by
    intro k
    by_cases hk : B k /\ cardinalProductOrdinalValue (f beta) k < (g k).1
    · rw [show selected k = cofinalValue k by simp only [selected, if_pos hk]]
      exact (hCofinalValueSpec k hk.2).2.2.trans_le (g k).2
    · rw [show selected k = fallback k by simp only [selected, if_neg hk]]
      simp only [fallback]
      exact cardinalProductOrdinalValue_lt (f i0) k
  let h : ProductElement (cardinalProductFrame A (J.localize B)) :=
    fun k => Ordinal.ToType.mk ⟨selected k, hSelectedBound k⟩
  have hOrdinalValue : forall k,
      cardinalProductOrdinalValue h k = selected k := by
    intro k
    dsimp only [h, cardinalProductOrdinalValue]
    exact congrArg Subtype.val
      ((Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm_apply_apply
        ⟨selected k, hSelectedBound k⟩)
  have hAllowed : forall k, cardinalProductOrdinalValue h k ∈ S k := by
    intro k
    rw [hOrdinalValue]
    by_cases hk : B k /\ cardinalProductOrdinalValue (f beta) k < (g k).1
    · rw [show selected k = cofinalValue k by simp only [selected, if_pos hk]]
      rw [show S k = Set.insert (fallback k) (base k) by
        simp only [S, if_pos hk.1]]
      exact Set.mem_insert_of_mem _ (hCofinalValueSpec k hk.2).1
    · rw [show selected k = fallback k by simp only [selected, if_neg hk]]
      by_cases hkB : B k
      · rw [show S k = Set.insert (fallback k) (base k) by
          simp only [S, if_pos hkB]]
        exact Set.mem_insert _ _
      · rw [show S k = ({fallback k} : Set (Ordinal.{u})) by
          simp only [S, if_neg hkB]]
        exact Set.mem_singleton _
  have hAlphaLtH :
      (cardinalProductFrame A (J.localize B)).eventuallyPointwiseLt
        (f alpha) h := by
    apply (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue
      (J := J.localize B) (f alpha) h).mpr
    have hAlphaBetaValues :=
      (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue
        (J := J.localize B) (f alpha) (f beta)).mp
          (hIncreasingB hAlphaBeta)
    have hBetaG : CardinalProductEventuallyLtClosed (J.localize B)
        (f beta) g := J.le_localize B _ (hExact.1 beta)
    have hEventuallyB : (J.localize B).Eventually B := by
      change J.Small (fun k => Not (B k) /\ B k)
      exact J.subset_small J.empty_small (by simp)
    exact (J.localize B).eventually_mono
      ((J.localize B).eventually_and
        ((J.localize B).eventually_and hAlphaBetaValues hBetaG)
        hEventuallyB) (by
        intro k hk
        rw [hOrdinalValue]
        have hkB : B k := hk.2
        have hkGood : B k /\
            cardinalProductOrdinalValue (f beta) k < (g k).1 :=
          ⟨hkB, hk.1.2⟩
        rw [show selected k = cofinalValue k by
          simp only [selected, if_pos hkGood]]
        exact hk.1.1.trans_le
          (hCofinalValueSpec k hk.1.2).2.1)
  have hHLtG : CardinalProductEventuallyLtClosed (J.localize B) h g := by
    have hBetaG : CardinalProductEventuallyLtClosed (J.localize B)
        (f beta) g := J.le_localize B _ (hExact.1 beta)
    have hEventuallyB : (J.localize B).Eventually B := by
      change J.Small (fun k => Not (B k) /\ B k)
      exact J.subset_small J.empty_small (by simp)
    exact (J.localize B).eventually_mono
      ((J.localize B).eventually_and hBetaG hEventuallyB) (by
      intro k hk
      rw [hOrdinalValue]
      have hkB : B k := hk.2
      have hkGood : B k /\
          cardinalProductOrdinalValue (f beta) k < (g k).1 :=
        ⟨hkB, hk.1⟩
      rw [show selected k = cofinalValue k by
        simp only [selected, if_pos hkGood]]
      exact (hCofinalValueSpec k hk.1).2.2)
  have hExactB : CardinalProductClosedExactUpperBound (J.localize B) f g :=
    hExact.localize i0 B
  obtain ⟨delta, hHDelta⟩ := hExactB.2 h hHLtG
  obtain ⟨nextStage, hMaxNext⟩ := exists_gt (max alpha delta)
  have hAlphaNext : alpha < nextStage :=
    (le_max_left alpha delta).trans_lt hMaxNext
  have hDeltaNext : delta < nextStage :=
    (le_max_right alpha delta).trans_lt hMaxNext
  have hNextH := hAlpha h hAllowed hAlphaLtH nextStage hAlphaNext
  have hHNextStrict :=
    (cardinalProductFrame A (J.localize B)).eventuallyLe_eventuallyPointwiseLt_trans
      hHDelta (hIncreasingB hDeltaNext)
  exact (ReducedProductFrame.eventuallyLt_of_eventually_pointwiseStrict
    hBProper hHNextStrict).2 hNextH

theorem cardinalProductClosedExactUpperBound_top_decomposition
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {iota : Type w}
    {d : iota -> ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (i0 : iota)
    (hExact : CardinalProductClosedExactUpperBound J d f) :
    (exists p : ProductElement (cardinalProductFrame A J),
        (cardinalProductFrame A J).IsPointwiseStrictUpperBound d p) \/
      (cardinalProductFrame A J).IsCofinalFamily d \/
      exists X : CardinalIndex A -> Prop,
        (J.localize X).IsProper /\
        (J.localize (fun k => Not (X k))).IsProper /\
        (exists p : ProductElement (cardinalProductFrame A J),
          (cardinalProductFrame A (J.localize X)).IsPointwiseStrictUpperBound d p) /\
        (cardinalProductFrame A (J.localize (fun k => Not (X k)))).IsCofinalFamily d := by
  classical
  let X : CardinalIndex A -> Prop := fun k => (f k).1 < k.1.ord
  let p : ProductElement (cardinalProductFrame A J) :=
    cardinalProductClosedToProductOn (d i0) f X (fun k hk => hk)
  have hUpperOnX : forall i,
      (cardinalProductFrame A (J.localize X)).eventuallyPointwiseLt (d i) p := by
    intro i
    change J.Small (fun k => Not
      (((show k.1.ord.ToType from d i k) <=
          (show k.1.ord.ToType from p k)) /\
        Not ((show k.1.ord.ToType from p k) <=
          (show k.1.ord.ToType from d i k))) /\ X k)
    have hi := hExact.1 i
    exact J.subset_small hi (by
      intro k hk hGood
      have hVal : cardinalProductOrdinalValue (d i) k <
          cardinalProductOrdinalValue p k := by
        rw [cardinalProductOrdinalValue_closedToProductOn
          (d i0) f X (fun k hk => hk) k hk.2]
        exact hGood
      have hLt : (show k.1.ord.ToType from d i k) <
          (show k.1.ord.ToType from p k) :=
        (cardinalProductOrdinalValue_lt_iff (d i) p k).mp hVal
      exact hk.1 ⟨hLt.le, not_le_of_gt hLt⟩)
  have hCofinalOffX :
      (cardinalProductFrame A (J.localize (fun k => Not (X k)))).IsCofinalFamily d := by
    intro h
    have hh : CardinalProductEventuallyLtClosed
        (J.localize (fun k => Not (X k))) h f := by
      change J.Small (fun k =>
        Not (cardinalProductOrdinalValue h k < (f k).1) /\ Not (X k))
      exact J.subset_small J.empty_small (by
        intro k hk
        have hfTop : (f k).1 = k.1.ord := by
          apply le_antisymm (f k).2
          exact le_of_not_gt hk.2
        exact hk.1 (hfTop.symm ▸ cardinalProductOrdinalValue_lt h k))
    exact (hExact.localize i0 (fun k => Not (X k))).2 h hh
  by_cases hXSmall : J.Small X
  · right
    left
    intro h
    obtain ⟨i, hi⟩ := hCofinalOffX h
    refine ⟨i, J.subset_small (J.union_small hi hXSmall) ?_⟩
    intro k hk
    by_cases hkX : X k
    · exact Or.inr hkX
    · exact Or.inl ⟨hk, hkX⟩
  · by_cases hOffSmall : J.Small (fun k => Not (X k))
    · left
      refine ⟨p, ?_⟩
      intro i
      exact J.subset_small (J.union_small (hUpperOnX i) hOffSmall) (by
        intro k hk
        by_cases hkX : X k
        · exact Or.inl ⟨hk, hkX⟩
        · exact Or.inr hkX)
    · right
      right
      exact ⟨X, (J.localize_isProper_iff X).mpr hXSmall,
        (J.localize_isProper_iff (fun k => Not (X k))).mpr hOffSmall,
        ⟨p, hUpperOnX⟩, hCofinalOffX⟩

/-! An ultrafilter-dual ideal decides the eventual comparison of every two
canonical product elements. This is totality of the reduced-product preorder,
not antisymmetry of raw product functions and not a scale construction. -/
theorem cardinalProductFrame_eventuallyLe_total_of_isUltrafilterDual
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual)
    (x y : ProductElement (cardinalProductFrame A J)) :
    (cardinalProductFrame A J).eventuallyLe x y \/
      (cardinalProductFrame A J).eventuallyLe y x := by
  classical
  change J.Eventually (fun i =>
    (show i.1.ord.ToType from x i) <= (show i.1.ord.ToType from y i)) \/
    J.Eventually (fun i =>
      (show i.1.ord.ToType from y i) <= (show i.1.ord.ToType from x i))
  cases hUltra.eventually_or_eventually_not (fun i =>
    (show i.1.ord.ToType from x i) <= (show i.1.ord.ToType from y i)) with
  | inl hxy => exact Or.inl hxy
  | inr hNotLe =>
      right
      apply J.eventually_mono hNotLe
      intro i hi
      exact (not_le.mp hi).le

/-! Every pair of canonical product elements has a common eventual upper
bound, formed coordinatewise. This directedness holds for every ideal and is
kept separate from the ultrafilter totality result above. -/
theorem cardinalProductFrame_exists_common_eventual_upper_bound
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (x y : ProductElement (cardinalProductFrame A J)) :
    exists z : ProductElement (cardinalProductFrame A J),
      (cardinalProductFrame A J).eventuallyLe x z /\
        (cardinalProductFrame A J).eventuallyLe y z := by
  let z : ProductElement (cardinalProductFrame A J) := fun i =>
    (if (show i.1.ord.ToType from x i) <=
        (show i.1.ord.ToType from y i)
      then (show i.1.ord.ToType from y i)
      else (show i.1.ord.ToType from x i) : i.1.ord.ToType)
  refine ⟨z, ?_, ?_⟩
  · apply ReducedProductFrame.eventuallyLe_of_forallLe
    intro i
    change (show i.1.ord.ToType from x i) <=
      (show i.1.ord.ToType from z i)
    by_cases hxy : (show i.1.ord.ToType from x i) <=
        (show i.1.ord.ToType from y i)
    · simpa only [z, if_pos hxy] using hxy
    · simpa only [z, if_neg hxy] using
        (cardinalProductFrame A J).le_refl i (x i)
  · apply ReducedProductFrame.eventuallyLe_of_forallLe
    intro i
    change (show i.1.ord.ToType from y i) <=
      (show i.1.ord.ToType from z i)
    by_cases hxy : (show i.1.ord.ToType from x i) <=
        (show i.1.ord.ToType from y i)
    · simpa only [z, if_pos hxy] using
        (cardinalProductFrame A J).le_refl i (y i)
    · have hyx : (show i.1.ord.ToType from y i) <=
        (show i.1.ord.ToType from x i) :=
        (not_le.mp hxy).le
      simpa only [z, if_neg hxy] using hyx

/-! The quotient of canonical product elements by mutual eventual domination.
The raw product function type is only a preorder modulo an ideal; this
quotient is the corresponding antisymmetric order carrier. -/
def cardinalProductFrameEventualSetoid
    (A : CardSet.{u})
    (J : Ideal (CardinalIndex A)) :
    Setoid (ProductElement (cardinalProductFrame A J)) where
  r x y :=
    (cardinalProductFrame A J).eventuallyLe x y /\
      (cardinalProductFrame A J).eventuallyLe y x
  iseqv := by
    constructor
    · intro x
      exact ⟨(cardinalProductFrame A J).eventuallyLe_refl x,
        (cardinalProductFrame A J).eventuallyLe_refl x⟩
    · intro x y hxy
      exact ⟨hxy.2, hxy.1⟩
    · intro x y z hxy hyz
      exact ⟨(cardinalProductFrame A J).eventuallyLe_trans hxy.1 hyz.1,
        (cardinalProductFrame A J).eventuallyLe_trans hyz.2 hxy.2⟩

/-! The order quotient of a canonical product by eventual equality. -/
abbrev CardinalProductQuotient
    (A : CardSet.{u})
    (J : Ideal (CardinalIndex A)) : Type (u + 1) :=
  Quotient (cardinalProductFrameEventualSetoid A J)

def cardinalProductQuotientLe
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)} :
    CardinalProductQuotient A J -> CardinalProductQuotient A J -> Prop := by
  intro x y
  exact Quotient.liftOn₂' x y
    (fun a b => (cardinalProductFrame A J).eventuallyLe a b)
    (by
      intro a1 a2 b1 b2 ha hb
      apply propext
      constructor
      · intro h
        exact (cardinalProductFrame A J).eventuallyLe_trans
          ((cardinalProductFrame A J).eventuallyLe_trans ha.2 h) hb.1
      · intro h
        exact (cardinalProductFrame A J).eventuallyLe_trans
          ((cardinalProductFrame A J).eventuallyLe_trans ha.1 h) hb.2)

instance cardinalProductQuotientLE
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)} :
    LE (CardinalProductQuotient A J) :=
  ⟨cardinalProductQuotientLe⟩

@[simp] theorem cardinalProductQuotient_mk_le_mk
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (x y : ProductElement (cardinalProductFrame A J)) :
    (Quotient.mk (cardinalProductFrameEventualSetoid A J) x :
      CardinalProductQuotient A J) <=
      Quotient.mk (cardinalProductFrameEventualSetoid A J) y <->
        (cardinalProductFrame A J).eventuallyLe x y :=
  Iff.rfl

/-! The quotient relation is a genuine partial order for every ideal. -/
instance cardinalProductQuotientPartialOrder
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)} :
    PartialOrder (CardinalProductQuotient A J) where
  le_refl := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => exact (cardinalProductFrame A J).eventuallyLe_refl x
  le_trans := by
    intro q r s hqr hrs
    induction q using Quotient.inductionOn with
    | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
        induction s using Quotient.inductionOn with
        | h z => exact (cardinalProductFrame A J).eventuallyLe_trans hqr hrs
  le_antisymm := by
    intro q r hqr hrq
    induction q using Quotient.inductionOn with
    | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
        exact Quotient.sound ⟨hqr, hrq⟩

/-! If the canonical coordinate index is small in the cardinal universe, then
the raw dependent product is small there as well. The coordinate types already
live in that universe, so this is a direct dependent-product smallness fact. -/
theorem cardinalProductFrame_productElement_small_of_small_cardinalIndex
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    [Small.{u} (CardinalIndex A)] :
    Small.{u} (ProductElement (cardinalProductFrame A J)) := by
  letI : Small.{u} (cardinalProductFrame A J).Index := by
    change Small.{u} (CardinalIndex A)
    infer_instance
  letI : forall i : (cardinalProductFrame A J).Index,
      Small.{u} ((cardinalProductFrame A J).Coord i) :=
    fun _ => small_self _
  exact small_Pi _

/-! Under the same small-index hypothesis, the eventual-equality quotient is
small in the cardinal universe. This is only universe bookkeeping; it does
not select a cofinal chain or produce a scale. -/
theorem cardinalProductQuotient_small_of_small_cardinalIndex
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    [Small.{u} (CardinalIndex A)] :
    Small.{u} (CardinalProductQuotient A J) := by
  letI : Small.{u} (cardinalProductFrame A J).Index := by
    change Small.{u} (CardinalIndex A)
    infer_instance
  letI : forall i : (cardinalProductFrame A J).Index,
      Small.{u} ((cardinalProductFrame A J).Coord i) :=
    fun _ => small_self _
  exact small_quotient _

/-! The order cofinality of a small preorder in `Type (u + 1)` is the lift of
some cardinal in `Type u`. This identifies the universe level of the least
cofinal set, but it does not assert that the resulting cardinal is regular. -/
theorem exists_cof_eq_lift_of_small
    {Q : Type (u + 1)}
    [Preorder Q]
    [Small.{u} Q] :
    exists theta : Cardinal.{u},
      Order.cof Q = Cardinal.lift.{u + 1} theta := by
  have hCofLe : Order.cof Q <= Cardinal.mk Q :=
    Order.cof_le_cardinalMk Q
  have hSmall : Order.cof Q <=
      Cardinal.lift.{u + 1} (Cardinal.mk (Shrink.{u} Q)) := by
    rw [Cardinal.lift_mk_shrink'']
    exact hCofLe
  obtain ⟨theta, hTheta⟩ := Cardinal.mem_range_lift_of_le hSmall
  exact ⟨theta, hTheta.symm⟩

/-! A small canonical index therefore removes the quotient's universe gap at
the level of cardinal representation. Regularity of this represented
cofinality remains a separate theorem before it can yield canonical PCF
membership. -/
theorem cardinalProductQuotient_exists_cof_eq_lift_of_small_cardinalIndex
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    [Small.{u} (CardinalIndex A)] :
    exists theta : Cardinal.{u},
      Order.cof (CardinalProductQuotient A J) =
        Cardinal.lift.{u + 1} theta := by
  letI : Small.{u} (CardinalProductQuotient A J) :=
    cardinalProductQuotient_small_of_small_cardinalIndex
  exact exists_cof_eq_lift_of_small

/-! Strict order between quotient representatives is precisely strict
eventual comparison of the underlying product functions. -/
@[simp] theorem cardinalProductQuotient_mk_lt_mk_iff
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (x y : ProductElement (cardinalProductFrame A J)) :
    (Quotient.mk (cardinalProductFrameEventualSetoid A J) x :
      CardinalProductQuotient A J) <
      Quotient.mk (cardinalProductFrameEventualSetoid A J) y <->
        (cardinalProductFrame A J).eventuallyLt x y :=
  Iff.rfl

/-! The quotient product is directed for every ideal. The upper bound is the
class of the coordinatewise upper bound already constructed on raw functions. -/
theorem cardinalProductQuotient_exists_common_upper_bound
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (q r : CardinalProductQuotient A J) :
    exists s : CardinalProductQuotient A J, q <= s /\ r <= s := by
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      obtain ⟨z, hxz, hyz⟩ :=
        cardinalProductFrame_exists_common_eventual_upper_bound x y
      exact ⟨Quotient.mk (cardinalProductFrameEventualSetoid A J) z, hxz, hyz⟩

/-! An ultrafilter-dual ideal linearly orders the quotient product. This
does not supply a well-ordered cofinal subset of that linear order. -/
theorem cardinalProductQuotient_le_total_of_isUltrafilterDual
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual)
    (q r : CardinalProductQuotient A J) :
    q <= r \/ r <= q := by
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      exact cardinalProductFrame_eventuallyLe_total_of_isUltrafilterDual
        hUltra x y

theorem cardinalProductQuotient_isLinearOrder_of_isUltrafilterDual
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual) :
    IsLinearOrder (CardinalProductQuotient A J) (fun q r => q <= r) where
  toTotal := ⟨cardinalProductQuotient_le_total_of_isUltrafilterDual hUltra⟩

/-! A family is cofinal in the eventual-equality quotient when it eventually
bounds every quotient class. This definition is paired below with its exact
raw-product characterization. -/
def cardinalProductQuotientIsCofinalFamily
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {ι : Type v}
    (d : ι -> CardinalProductQuotient A J) : Prop :=
  forall q, exists i, q <= d i

/-! A quotient scale is a well-ordered strictly increasing cofinal chain in
the antisymmetric eventual-equality quotient. It is deliberately distinct from
`Order.cof`: the latter only supplies a least-size cofinal set, while this
structure contains the increasing well-ordered chain needed for a scale. -/
structure CardinalProductQuotientScale
    (A : CardSet.{u})
    (J : Ideal (CardinalIndex A))
    (L : ScaleLength.{v}) where
  seq : L.Level -> CardinalProductQuotient A J
  increasing : forall {alpha beta}, L.lt alpha beta -> seq alpha < seq beta
  cofinal : cardinalProductQuotientIsCofinalFamily seq

/-! Passing a raw cofinal family to eventual-equivalence classes neither adds
nor loses cofinality. -/
theorem cardinalProductQuotient_mk_isCofinalFamily_iff
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {ι : Type v}
    (d : ι -> ProductElement (cardinalProductFrame A J)) :
    (cardinalProductFrame A J).IsCofinalFamily d <->
      cardinalProductQuotientIsCofinalFamily
        (fun i => Quotient.mk (cardinalProductFrameEventualSetoid A J) (d i)) := by
  constructor
  · intro hCofinal q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨i, hgi⟩ := hCofinal g
      exact ⟨i, hgi⟩
  · intro hCofinal g
    obtain ⟨i, hgi⟩ :=
      hCofinal (Quotient.mk (cardinalProductFrameEventualSetoid A J) g)
    exact ⟨i, hgi⟩

/-! A cofinal family in the quotient can be represented pointwise by raw
product functions without losing cofinality. The index universe is arbitrary;
this remains a family conversion, not a scale construction. -/
theorem cardinalProductFrame_exists_cofinalFamily_of_quotient
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {ι : Type v}
    (d : ι -> CardinalProductQuotient A J)
    (hCofinal : cardinalProductQuotientIsCofinalFamily d) :
    exists e : ι -> ProductElement (cardinalProductFrame A J),
      (cardinalProductFrame A J).IsCofinalFamily e := by
  classical
  choose e he using fun i => Quotient.exists_rep (d i)
  refine ⟨e, ?_⟩
  intro g
  obtain ⟨i, hgi⟩ :=
    hCofinal (Quotient.mk (cardinalProductFrameEventualSetoid A J) g)
  refine ⟨i, ?_⟩
  change (Quotient.mk (cardinalProductFrameEventualSetoid A J) g :
    CardinalProductQuotient A J) <=
      Quotient.mk (cardinalProductFrameEventualSetoid A J) (e i)
  rw [he i]
  exact hgi

/-! In the universe of the quotient itself, the least quotient cofinality is
realized by a raw-product cofinal family of exactly that cardinality. This does
not furnish a well-ordered or strictly increasing family. -/
theorem cardinalProductFrame_exists_cofinalFamily_of_mk_eq_quotient_cof
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)} :
    exists (ι : Type (u + 1))
      (d : ι -> ProductElement (cardinalProductFrame A J)),
        (cardinalProductFrame A J).IsCofinalFamily d /\
          Cardinal.mk ι = Order.cof (CardinalProductQuotient A J) := by
  obtain ⟨s, hSetCofinal, hCard⟩ :=
    Order.exists_cof_eq (CardinalProductQuotient A J)
  let dQuotient : s -> CardinalProductQuotient A J := fun q => q
  have hQuotientCofinal :
      cardinalProductQuotientIsCofinalFamily dQuotient := by
    intro q
    obtain ⟨r, hr, hqr⟩ := hSetCofinal q
    exact ⟨⟨r, hr⟩, hqr⟩
  obtain ⟨d, hRawCofinal⟩ :=
    cardinalProductFrame_exists_cofinalFamily_of_quotient
      dQuotient hQuotientCofinal
  exact ⟨s, d, hRawCofinal, hCard⟩

/-! An already supplied scale becomes a strictly increasing, cofinal chain in
the antisymmetric quotient order. This transports a scale witness; it does
not construct one for a nonprincipal product. -/
theorem cardinalProductQuotient_mk_strictly_increasing_and_cofinal_of_scale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{v}}
    (s : Scale (cardinalProductFrame A J) L) :
    (forall {alpha beta}, L.lt alpha beta ->
      (Quotient.mk (cardinalProductFrameEventualSetoid A J) (s.seq alpha) :
        CardinalProductQuotient A J) <
        Quotient.mk (cardinalProductFrameEventualSetoid A J) (s.seq beta)) /\
      cardinalProductQuotientIsCofinalFamily
        (fun alpha =>
          Quotient.mk (cardinalProductFrameEventualSetoid A J) (s.seq alpha)) := by
  constructor
  · intro alpha beta hlt
    exact s.increasing hlt
  · exact cardinalProductQuotient_mk_isCofinalFamily_iff s.seq |>.mp
      s.isCofinalFamily_seq

/-! Every raw product scale determines a quotient scale with exactly the same
well-ordered index. This merely transports a supplied scale to the quotient. -/
def CardinalProductQuotientScale.ofScale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{v}}
    (s : Scale (cardinalProductFrame A J) L) :
    CardinalProductQuotientScale A J L := by
  obtain ⟨hIncreasing, hCofinal⟩ :=
    cardinalProductQuotient_mk_strictly_increasing_and_cofinal_of_scale s
  exact
    { seq := fun alpha =>
        Quotient.mk (cardinalProductFrameEventualSetoid A J) (s.seq alpha)
      increasing := hIncreasing
      cofinal := hCofinal }

theorem CardinalProductQuotientScale.nonempty_of_scale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{v}}
    (s : Scale (cardinalProductFrame A J) L) :
    Nonempty (CardinalProductQuotientScale A J L) :=
  ⟨CardinalProductQuotientScale.ofScale s⟩

/-! A quotient scale can be represented pointwise by raw product functions
while preserving strict growth and cofinality. Representative choice is used
only to lift the already supplied quotient scale; it does not obtain such a
chain from `Order.cof`. -/
theorem CardinalProductQuotientScale.exists_scale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{v}}
    (s : CardinalProductQuotientScale A J L) :
    Nonempty (Scale (cardinalProductFrame A J) L) := by
  classical
  choose e he using fun alpha => Quotient.exists_rep (s.seq alpha)
  refine ⟨{
    seq := e
    increasing := ?_
    cofinal := ?_ }⟩
  · intro alpha beta hlt
    apply (cardinalProductQuotient_mk_lt_mk_iff (e alpha) (e beta)).mp
    rw [he alpha, he beta]
    exact s.increasing hlt
  · apply cardinalProductQuotient_mk_isCofinalFamily_iff e |>.mpr
    intro q
    obtain ⟨alpha, hAlpha⟩ := s.cofinal q
    refine ⟨alpha, ?_⟩
    change q <= Quotient.mk (cardinalProductFrameEventualSetoid A J) (e alpha)
    rw [he alpha]
    exact hAlpha

/-! Scale existence is equivalent before and after passing to the
eventual-equality quotient, for any fixed well-ordered index. This is an
existence equivalence for a specified index, not a theorem deriving such an
index from quotient cofinality. -/
theorem hasScaleWitness_iff_nonempty_cardinalProductQuotientScale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{v}} :
    HasScaleWitness (cardinalProductFrame A J) L <->
      Nonempty (CardinalProductQuotientScale A J L) := by
  constructor
  · rintro ⟨s⟩
    exact CardinalProductQuotientScale.nonempty_of_scale s
  · rintro ⟨s⟩
    exact s.exists_scale

theorem mk_cardinalProductFrame_productElement
    {A : CardSet.{u}}
    (J : Ideal (CardinalIndex A)) :
    Cardinal.mk (ProductElement (cardinalProductFrame A J)) =
      Cardinal.prod (fun i : CardinalIndex A => i.1) := by
  rw [Cardinal.mk_pi]
  congr 1
  funext i
  exact mk_cardinalProductFrame_coord J i

/-! A family shorter than a regular cardinal has a strict upper bound in
the canonical coordinate order. This is the coordinatewise diagonal step
used below for reduced products. -/
theorem exists_strict_upper_bound_of_mk_lt_regular
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    {ι : Type u}
    (hSmall : Cardinal.mk ι < theta)
    (d : ι -> theta.ord.ToType) :
    exists b, forall i, d i < b := by
  classical
  let f : ι -> Ordinal.{u} :=
    fun i => Ordinal.typein
      (fun a b : theta.ord.ToType => a < b)
      (d i)
  have hf : forall i, f i < theta.ord := by
    intro i
    simpa only [f] using Ordinal.typein_lt_self (d i)
  have hBound : (iSup fun i => f i + 1) < theta.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof
      (by rwa [hRegular.cof_ord]) hf
  let b : theta.ord.ToType :=
    Ordinal.ToType.mk ⟨iSup fun i => f i + 1, hBound⟩
  refine ⟨b, ?_⟩
  intro i
  change d i < Ordinal.ToType.mk ⟨iSup fun i => f i + 1, hBound⟩
  rw [← (Ordinal.ToType.mk).apply_symm_apply (d i)]
  apply (Ordinal.ToType.mk).strictMono
  change f i < iSup fun i => f i + 1
  exact Ordinal.lt_iSup_add_one f i

/-! If the candidate family is smaller than every regular coordinate, its
    members have a common pointwise strict upper bound.  Keeping this
    pointwise form, rather than immediately passing to an ideal, is what makes
    every reverse-comparison set empty in the compactness argument below. -/
theorem cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {ι : Type u}
    (hSmall : forall theta, A theta -> Cardinal.mk ι < theta)
    (d : ι -> ((k : CardinalIndex A) -> k.1.ord.ToType)) :
    exists g : (k : CardinalIndex A) -> k.1.ord.ToType,
      forall i k, d i k < g k := by
  classical
  have hCoordinate : forall k : CardinalIndex A,
      exists b : k.1.ord.ToType,
        forall i, d i k < b := by
    intro k
    exact exists_strict_upper_bound_of_mk_lt_regular
      (hRegulars k.1 k.2) (hSmall k.1 k.2) (fun i => d i k)
  choose g hg using hCoordinate
  exact ⟨g, fun i k => hg k i⟩

/-! The same pointwise construction may be restricted to a chosen set of
    coordinates.  Outside that set an arbitrary zero coordinate is used; no
    smallness claim is made there. -/
theorem cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt_on
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {ι : Type u}
    {B : CardinalIndex A -> Prop}
    (hSmall : forall k : CardinalIndex A,
      B k -> Cardinal.mk ι < k.1)
    (d : ι -> ((k : CardinalIndex A) -> k.1.ord.ToType)) :
    exists g : (k : CardinalIndex A) -> k.1.ord.ToType,
      forall i k, B k -> d i k < g k := by
  classical
  have hCoordinate : forall k : CardinalIndex A, B k ->
      exists b : k.1.ord.ToType,
        forall i, d i k < b := by
    intro k hk
    exact exists_strict_upper_bound_of_mk_lt_regular
      (hRegulars k.1 k.2) (hSmall k hk) (fun i => d i k)
  choose b hb using hCoordinate
  let g : (k : CardinalIndex A) -> k.1.ord.ToType := fun k =>
    if hk : B k then b k hk else
      Ordinal.ToType.mk ⟨0, (hRegulars k.1 k.2).ord_pos⟩
  refine ⟨g, ?_⟩
  intro i k hk
  simpa only [g, dif_pos hk] using hb k hk i

/-! If every small index type is eventually smaller than the coordinate
cardinals, coordinatewise regularity upgrades this tail condition to genuine
eventual pointwise-strict directedness.  This isolates the ideal-theoretic
part of the diagonal argument from its cardinal-coordinate construction. -/
theorem cardinalProductFrame_pointwiseStrictDirectedBelow_of_eventually_coordinate
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hEventually : forall (ι : Type u), Cardinal.mk ι < theta ->
      J.Eventually (fun k : CardinalIndex A => Cardinal.mk ι < k.1)) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta := by
  intro ι hSmall d
  obtain ⟨g, hg⟩ :=
    cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt_on
      hRegulars (B := fun k : CardinalIndex A => Cardinal.mk ι < k.1)
        (fun _ hk => hk) d
  refine ⟨g, ?_⟩
  intro i
  exact J.eventually_mono (hEventually ι hSmall) (by
    intro k hk
    exact ⟨(hg i k hk).le, not_le_of_gt (hg i k hk)⟩)

/-! Layered diagonalization.  The whole family may be as large as the limit
of the coordinate cardinals: coordinate `k` only has to dominate the local
subfamily selected by `B k`, provided that local subfamily is smaller than
`k.1` and every original member belongs to `B k` eventually. -/
theorem cardinalProductFrame_exists_eventuallyPointwiseLt_of_layered
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {J : Ideal (CardinalIndex A)}
    {ι : Type u}
    (B : CardinalIndex A -> ι -> Prop)
    (hLayerSmall : forall k : CardinalIndex A,
      Cardinal.mk {i : ι // B k i} < k.1)
    (hEventually : forall i : ι, J.Eventually (fun k => B k i))
    (d : ι -> ProductElement (cardinalProductFrame A J)) :
    exists g : ProductElement (cardinalProductFrame A J),
      forall i,
        (cardinalProductFrame A J).eventuallyPointwiseLt (d i) g := by
  classical
  have hCoordinate : forall k : CardinalIndex A,
      exists b : k.1.ord.ToType,
        forall i : {i : ι // B k i},
          (show k.1.ord.ToType from d i.1 k) < b := by
    intro k
    exact exists_strict_upper_bound_of_mk_lt_regular
      (hRegulars k.1 k.2) (hLayerSmall k) (fun i => d i.1 k)
  choose g hg using hCoordinate
  refine ⟨g, ?_⟩
  intro i
  exact J.eventually_mono (hEventually i) (by
    intro k hik
    have hlt : (show k.1.ord.ToType from d i k) < g k :=
      hg k ⟨i, hik⟩
    exact ⟨hlt.le, not_le_of_gt hlt⟩)

/-! Every family whose index cardinal is below every coordinate cardinal has
a common strict upper bound in the reduced product over a proper ideal. This
is a genuine diagonalization theorem and does not assume a scale. -/
theorem cardinalProductFrame_exists_strict_upper_bound_of_mk_lt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {ι : Type u}
    (hSmall : forall theta, A theta -> Cardinal.mk ι < theta)
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper)
    (d : ι -> ProductElement (cardinalProductFrame A J)) :
    exists g : ProductElement (cardinalProductFrame A J),
      forall i,
        (cardinalProductFrame A J).eventuallyLt (d i) g := by
  classical
  have hCoordinate : forall k : CardinalIndex A,
      exists b : k.1.ord.ToType,
        forall i, (show k.1.ord.ToType from d i k) < b := by
    intro k
    exact exists_strict_upper_bound_of_mk_lt_regular
      (hRegulars k.1 k.2) (hSmall k.1 k.2) (fun i => d i k)
  choose g hg using hCoordinate
  refine ⟨g, ?_⟩
  intro i
  constructor
  · apply ReducedProductFrame.eventuallyLe_of_forallLe
    intro k
    exact (hg k i).le
  · apply hProper.not_eventually_of_forall_not
    intro k hki
    exact (not_le_of_gt (hg k i)) hki

theorem cardinalProductFrame_not_isCofinalFamily_of_mk_lt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {ι : Type u}
    (hSmall : forall theta, A theta -> Cardinal.mk ι < theta)
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper)
    (d : ι -> ProductElement (cardinalProductFrame A J)) :
    Not ((cardinalProductFrame A J).IsCofinalFamily d) := by
  intro hCofinal
  obtain ⟨g, hStrict⟩ :=
    cardinalProductFrame_exists_strict_upper_bound_of_mk_lt
      hRegulars hSmall hProper d
  obtain ⟨i, hgi⟩ := hCofinal g
  exact (hStrict i).right hgi

/-! A family smaller than every coordinate can be defeated by one
    nonprincipal ultrafilter-dual ideal.  The pointwise diagonal bound makes
    each reverse-comparison predicate empty, so every finite subfamily is
    compatible with the finite-set ideal before the Zorn extension is taken. -/
theorem
    cardinalProductFrame_exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily_of_mk_lt
    {A : CardSet.{u}}
    [Infinite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    {ι : Type u}
    (hSmall : forall theta, A theta -> Cardinal.mk ι < theta)
    (d : ι -> ProductElement
      (cardinalProductFrame A (Ideal.finiteSet (CardinalIndex A)))) :
    exists J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual /\
        (forall i, Not (J = Ideal.excludePoint i)) /\
        Not ((cardinalProductFrame A J).IsCofinalFamily d) := by
  letI : Infinite
      (cardinalProductFrame A
        (Ideal.finiteSet (CardinalIndex A))).Index := by
    change Infinite (CardinalIndex A)
    infer_instance
  obtain ⟨g, hg⟩ :=
    cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt
      hRegulars hSmall d
  obtain ⟨J, hUltra, hNonprincipal, hNotCofinal⟩ :=
    ReducedProductFrame.exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily
      (F := cardinalProductFrame A (Ideal.finiteSet (CardinalIndex A)))
      d g (by
        intro s hUniv
        obtain ⟨T, hT, hCover⟩ := hUniv
        apply Ideal.finiteSet_isProper (I := CardinalIndex A)
        apply (Ideal.finiteSet (CardinalIndex A)).subset_small hT
        intro i _
        rcases hCover i True.intro with hTi | hComparison
        · exact hTi
        · obtain ⟨k, _hks, hgLe⟩ := hComparison
          exact False.elim ((not_le_of_gt (hg k i)) hgLe))
  refine ⟨J, hUltra, hNonprincipal, ?_⟩
  simpa only [ReducedProductFrame.withIdeal, cardinalProductFrame] using
    hNotCofinal

/-! It is enough that the candidate family be smaller than the coordinates
    off a finite exceptional set.  The exceptional coordinates are already
    small in the finite-set ideal, while every reverse comparison is
    impossible on the remaining coordinates. -/
theorem
    cardinalProductFrame_exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily_of_mk_lt_off_finite
    {A : CardSet.{u}}
    [Infinite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    {ι : Type u}
    {B : CardinalIndex A -> Prop}
    (hSmall : forall k : CardinalIndex A,
      B k -> Cardinal.mk ι < k.1)
    (hFiniteException : Set.Finite {k : CardinalIndex A | Not (B k)})
    (d : ι -> ProductElement
      (cardinalProductFrame A (Ideal.finiteSet (CardinalIndex A)))) :
    exists J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual /\
        (forall i, Not (J = Ideal.excludePoint i)) /\
        Not ((cardinalProductFrame A J).IsCofinalFamily d) := by
  letI : Infinite
      (cardinalProductFrame A
        (Ideal.finiteSet (CardinalIndex A))).Index := by
    change Infinite (CardinalIndex A)
    infer_instance
  obtain ⟨g, hg⟩ :=
    cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt_on
      hRegulars hSmall d
  have hExceptionSmall :
      (Ideal.finiteSet (CardinalIndex A)).Small (fun k => Not (B k)) := by
    rw [Ideal.finiteSet_small_iff]
    exact hFiniteException
  obtain ⟨J, hUltra, hNonprincipal, hNotCofinal⟩ :=
    ReducedProductFrame.exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily
      (F := cardinalProductFrame A (Ideal.finiteSet (CardinalIndex A)))
      d g (by
        intro s hUniv
        obtain ⟨T, hT, hCover⟩ := hUniv
        apply Ideal.finiteSet_isProper (I := CardinalIndex A)
        apply (Ideal.finiteSet (CardinalIndex A)).subset_small
          ((Ideal.finiteSet (CardinalIndex A)).union_small hT hExceptionSmall)
        intro i _
        rcases hCover i True.intro with hTi | hComparison
        · exact Or.inl hTi
        · obtain ⟨k, _hks, hgLe⟩ := hComparison
          right
          intro hBi
          exact (not_le_of_gt (hg k i hBi)) hgLe)
  refine ⟨J, hUltra, hNonprincipal, ?_⟩
  simpa only [ReducedProductFrame.withIdeal, cardinalProductFrame] using
    hNotCofinal

/-! With regular coordinates and a proper ideal, the eventual-equality
quotient has no maximal element. This is an order-theoretic consequence of
the one-element diagonal bound, not a construction of a cofinal scale. -/
theorem cardinalProductQuotient_exists_lt_of_regulars
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hProper : J.IsProper)
    (q : CardinalProductQuotient A J) :
    exists r : CardinalProductQuotient A J, q < r := by
  induction q using Quotient.inductionOn with
  | h x =>
    let d : ULift.{u} Unit -> ProductElement (cardinalProductFrame A J) :=
      fun _ => x
    have hSmall : forall theta, A theta -> Cardinal.mk (ULift.{u} Unit) < theta := by
      intro theta hTheta
      simpa only [Cardinal.mk_uLift, Cardinal.mk_unit, Cardinal.lift_one] using
        Cardinal.one_lt_aleph0.trans_le (hRegulars theta hTheta).aleph0_le
    obtain ⟨g, hg⟩ :=
      cardinalProductFrame_exists_strict_upper_bound_of_mk_lt
        hRegulars hSmall hProper d
    refine ⟨Quotient.mk (cardinalProductFrameEventualSetoid A J) g, ?_⟩
    simpa only [d] using hg (ULift.up Unit.unit)

/-! A coordinatewise diagonal bound only needs to hold on an eventual set of
    coordinates. This is the form used for nonprincipal countable-index
    witnesses: the small family is bounded on a strict tail, while arbitrary
    values may be used on the discarded initial segment. -/
 theorem cardinalProductFrame_exists_strict_upper_bound_of_mk_lt_of_eventually
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {ι : Type u}
    {B : CardinalIndex A -> Prop}
    (hSmall : forall k : CardinalIndex A, B k -> Cardinal.mk ι < k.1)
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper)
    (hEventually : J.Eventually B)
    (d : ι -> ProductElement (cardinalProductFrame A J)) :
    exists g : ProductElement (cardinalProductFrame A J),
      forall i,
        (cardinalProductFrame A J).eventuallyLt (d i) g := by
  classical
  have hCoordinate : forall k : CardinalIndex A, B k ->
      exists b : k.1.ord.ToType,
        forall i, (show k.1.ord.ToType from d i k) < b := by
    intro k hk
    exact exists_strict_upper_bound_of_mk_lt_regular
      (hRegulars k.1 k.2) (hSmall k hk) (fun i => d i k)
  choose b hb using hCoordinate
  let g : ProductElement (cardinalProductFrame A J) := fun k =>
    if hk : B k then b k hk else
      Ordinal.ToType.mk ⟨0, (hRegulars k.1 k.2).ord_pos⟩
  have hStrictAt : forall (k : CardinalIndex A), B k -> forall i,
      (show k.1.ord.ToType from d i k) <
        (show k.1.ord.ToType from g k) := by
    intro k hk i
    simpa only [g, dif_pos hk] using hb k hk i
  have hUpper : forall i,
      (cardinalProductFrame A J).eventuallyLt (d i) g := by
    intro i
    refine ⟨?_, ?_⟩
    · exact J.eventually_mono hEventually (by
        intro k hk
        exact (hStrictAt k hk i).le)
    · intro hReverse
      apply hProper.not_eventually_false
      exact J.eventually_mono (J.eventually_and hEventually hReverse)
        (by
          intro k hk
          exact (not_le_of_gt (hStrictAt k hk.1 i)) hk.2)
  exact ⟨g, hUpper⟩

theorem cardinalProductFrame_not_isCofinalFamily_of_mk_lt_of_eventually
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {ι : Type u}
    {B : CardinalIndex A -> Prop}
    (hSmall : forall k : CardinalIndex A, B k -> Cardinal.mk ι < k.1)
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper)
    (hEventually : J.Eventually B)
    (d : ι -> ProductElement (cardinalProductFrame A J)) :
    Not ((cardinalProductFrame A J).IsCofinalFamily d) := by
  obtain ⟨g, hUpper⟩ :=
    cardinalProductFrame_exists_strict_upper_bound_of_mk_lt_of_eventually
      hRegulars hSmall hProper hEventually d
  intro hCofinal
  obtain ⟨i, hgi⟩ := hCofinal g
  exact (hUpper i).right hgi

theorem cardinalProductFrame_not_isCofinalFamily_nat_of_aleph0_lt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper)
    (d : Nat -> ProductElement (cardinalProductFrame A J)) :
    Not ((cardinalProductFrame A J).IsCofinalFamily d) := by
  intro hCofinal
  let dLift : ULift.{u} Nat ->
      ProductElement (cardinalProductFrame A J) :=
    fun i => d i.down
  have hLiftCofinal :
      (cardinalProductFrame A J).IsCofinalFamily dLift := by
    intro g
    obtain ⟨n, hn⟩ := hCofinal g
    exact ⟨ULift.up n, hn⟩
  exact (cardinalProductFrame_not_isCofinalFamily_of_mk_lt
    hRegulars (J := J) (by
      intro theta hTheta
      simpa only [Cardinal.mk_uLift, Cardinal.mk_nat,
        Cardinal.lift_aleph0] using hAleph0 theta hTheta)
    hProper dLift) hLiftCofinal

/-! The order cofinality of the eventual-equality quotient is uncountable
when all regular coordinates are above `aleph0`. A hypothetical countable
cofinal quotient set can be enumerated by `Nat`, lifted to raw representatives,
and is then ruled out by the established diagonal argument. This does not
construct a cofinal scale. -/
theorem cardinalProductQuotient_lift_lt_cof_of_regulars
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {kappa : Cardinal.{u}}
    (hCoordinate : forall theta, A theta -> kappa < theta)
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper) :
    Cardinal.lift.{u + 1} kappa <
      Order.cof (CardinalProductQuotient A J) := by
  classical
  by_contra hNot
  have hCofLe : Order.cof (CardinalProductQuotient A J) <=
      Cardinal.lift.{u + 1} kappa :=
    le_of_not_gt hNot
  obtain ⟨s, hSetCofinal, hCard⟩ :=
    Order.exists_cof_eq (CardinalProductQuotient A J)
  have hSmall : Cardinal.mk s <= Cardinal.lift.{u + 1} kappa := by
    rw [hCard]
    exact hCofLe
  have hEmbed : Nonempty (s ↪ ULift.{u + 1} kappa.out) := by
    apply (Cardinal.le_def _ _).mp
    simpa only [Cardinal.mk_uLift, Cardinal.mk_out] using hSmall
  letI : Small.{u} s :=
    small_of_injective (Classical.choice hEmbed).injective
  let dQuotient : Shrink.{u} s -> CardinalProductQuotient A J :=
    fun i => ((equivShrink s).symm i).1
  have hQuotientCofinal :
      cardinalProductQuotientIsCofinalFamily dQuotient := by
    intro q
    obtain ⟨r, hr, hqr⟩ := hSetCofinal q
    refine ⟨equivShrink s ⟨r, hr⟩, ?_⟩
    simpa only [dQuotient, Equiv.symm_apply_apply] using hqr
  obtain ⟨d, hRawCofinal⟩ :=
    cardinalProductFrame_exists_cofinalFamily_of_quotient
      dQuotient hQuotientCofinal
  have hShrinkLe : Cardinal.mk (Shrink.{u} s) <= kappa := by
    apply Cardinal.lift_le.mp
    calc
      Cardinal.lift.{u + 1} (Cardinal.mk (Shrink.{u} s)) =
          Cardinal.lift.{u} (Cardinal.mk s) :=
        Cardinal.lift_mk_shrink' s
      _ = Cardinal.mk s := Cardinal.lift_id'.{u, u + 1} _
      _ <= Cardinal.lift.{u + 1} kappa := hSmall
  exact (cardinalProductFrame_not_isCofinalFamily_of_mk_lt
    hRegulars
    (fun theta hTheta => hShrinkLe.trans_lt (hCoordinate theta hTheta))
    hProper d) hRawCofinal

/-! The same quotient-cofinality lower bound only needs the coordinate
inequality on an eventual set. A small cofinal quotient family is represented
by raw functions and contradicted by the eventual diagonal theorem; no
well-ordered cofinal chain is constructed. -/
theorem cardinalProductQuotient_aleph0_lt_cof_of_regulars
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper) :
    Cardinal.aleph0 < Order.cof (CardinalProductQuotient A J) := by
  simpa only [Cardinal.lift_aleph0] using
    cardinalProductQuotient_lift_lt_cof_of_regulars
      hRegulars hAleph0 hProper

def IsCardinalProductOver
    (A : CardSet.{u})
    (F : ReducedProductFrame.{u + 1, u}) : Prop :=
  exists J : Ideal (CardinalIndex A),
    J.IsUltrafilterDual /\ F = cardinalProductFrame A J

theorem isCardinalProductOver_cardinalProductFrame
    {A : CardSet.{u}}
    (J : Ideal (CardinalIndex A))
    (hUltra : J.IsUltrafilterDual) :
    IsCardinalProductOver A (cardinalProductFrame A J) :=
  ⟨J, hUltra, rfl⟩

noncomputable def cardinalScaleLength
    (theta : Cardinal.{u}) : ScaleLength.{u} where
  Level := theta.ord.ToType
  lt := (· < ·)
  isWellOrder := by infer_instance

@[simp] theorem mk_cardinalScaleLength_level
    (theta : Cardinal.{u}) :
    Cardinal.mk (cardinalScaleLength theta).Level = theta := by
  exact Cardinal.mk_ord_toType theta

/-! Two cofinal scales on predicates covering every coordinate give a
cofinal family in the original product.  At a common later stage, take the
coordinatewise maximum of the two local scale values.  No completeness of
the ideal is used: the two local exceptional sets are joined by the ordinary
finite-union closure of the ideal. -/
theorem exists_cardinalProduct_cofinalFamily_of_localizedScales_cover
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    {X Y : CardinalIndex A -> Prop}
    (hCover : forall k, X k \/ Y k)
    (sX : PointwiseStrictScale
      (cardinalProductFrame A (J.localize X))
      (cardinalScaleLength theta))
    (sY : PointwiseStrictScale
      (cardinalProductFrame A (J.localize Y))
      (cardinalScaleLength theta)) :
    exists d : (cardinalScaleLength theta).Level ->
        ProductElement (cardinalProductFrame A J),
      (cardinalProductFrame A J).IsCofinalFamily d := by
  classical
  letI : LinearOrder (cardinalScaleLength theta).Level := by
    dsimp only [cardinalScaleLength]
    infer_instance
  letI coordLinearOrder (k : CardinalIndex A) :
      LinearOrder ((cardinalProductFrame A J).Coord k) := by
    dsimp only [cardinalProductFrame]
    infer_instance
  let d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J) := fun alpha k =>
    max (sX.seq alpha k) (sY.seq alpha k)
  refine ⟨d, ?_⟩
  intro h
  obtain ⟨alpha, hAlpha⟩ := sX.cofinal h
  obtain ⟨beta, hBeta⟩ := sY.cofinal h
  let gamma := max alpha beta
  have hXInc : (cardinalProductFrame A (J.localize X)).eventuallyLe
      (sX.seq alpha) (sX.seq gamma) := by
    rcases (le_max_left alpha beta).eq_or_lt with hEq | hLt
    · rw [hEq]
      exact (cardinalProductFrame A (J.localize X)).eventuallyLe_refl _
    · exact (J.localize X).eventually_mono (sX.increasing hLt) (by
        intro k hk
        exact hk.1)
  have hYInc : (cardinalProductFrame A (J.localize Y)).eventuallyLe
      (sY.seq beta) (sY.seq gamma) := by
    rcases (le_max_right alpha beta).eq_or_lt with hEq | hLt
    · rw [hEq]
      exact (cardinalProductFrame A (J.localize Y)).eventuallyLe_refl _
    · exact (J.localize Y).eventually_mono (sY.increasing hLt) (by
        intro k hk
        exact hk.1)
  have hXDom : (cardinalProductFrame A (J.localize X)).eventuallyLe
      h (sX.seq gamma) :=
    (cardinalProductFrame A (J.localize X)).eventuallyLe_trans
      hAlpha hXInc
  have hYDom : (cardinalProductFrame A (J.localize Y)).eventuallyLe
      h (sY.seq gamma) :=
    (cardinalProductFrame A (J.localize Y)).eventuallyLe_trans
      hBeta hYInc
  refine ⟨gamma, ?_⟩
  change J.Small (fun k => Not (h k <= d gamma k))
  exact J.subset_small (J.union_small hXDom hYDom) (by
    intro k hk
    rcases hCover k with hkX | hkY
    · left
      refine ⟨?_, hkX⟩
      intro hLe
      exact hk (hLe.trans (le_max_left _ _))
    · right
      refine ⟨?_, hkY⟩
      intro hLe
      exact hk (hLe.trans (le_max_right _ _)))

theorem exists_cardinalProduct_strictIncreasing_rapidBelow_of_directed
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {kappa lambda : Cardinal.{u}}
    (hRegulars : SetOfRegulars A)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      (Order.succ lambda))
    (hSupportSmall : forall beta alpha : Set.Iio lambda.ord,
      J.Eventually (fun k =>
        Cardinal.mk
            (cardinalProductRapidSupportBelow kappa lambda beta alpha) <
          Cardinal.lift.{u + 1} k.1)) :
    exists f : Set.Iio lambda.ord ->
        ProductElement (cardinalProductFrame A J),
      (forall {alpha beta}, alpha < beta ->
        (cardinalProductFrame A J).eventuallyPointwiseLt
          (f alpha) (f beta)) /\
      forall gamma : Cardinal.{u}, Cardinal.aleph0 < gamma ->
        gamma < kappa -> CardinalProductGammaRapid J gamma lambda f := by
  classical
  let L := (cardinalScaleLength lambda).Level
  letI : LinearOrder L := by
    dsimp only [L, cardinalScaleLength]
    infer_instance
  letI : WellFoundedLT L := by
    refine ⟨?_⟩
    change WellFounded (cardinalScaleLength lambda).lt
    exact (cardinalScaleLength lambda).isWellOrder.wf
  let toIio : L -> Set.Iio lambda.ord := fun alpha =>
    (Ordinal.ToType.mk : Set.Iio lambda.ord ≃o lambda.ord.ToType).symm alpha
  let toLevel : Set.Iio lambda.ord -> L := fun alpha =>
    Ordinal.ToType.mk alpha
  have hLevelSmall : Cardinal.mk L < Order.succ lambda := by
    simpa only [L, mk_cardinalScaleLength_level] using Order.lt_succ lambda
  obtain ⟨d0, _hd0⟩ :=
    hDirected PEmpty (by simp) (fun z => nomatch z)
  let partialAt (alpha : L)
      (previous : forall beta, beta < alpha ->
        ProductElement (cardinalProductFrame A J)) :
      Set.Iio lambda.ord -> ProductElement (cardinalProductFrame A J) :=
    fun i => if hi : toLevel i < alpha then
      previous (toLevel i) hi else d0
  let supportAt (alpha beta : L) : Set (Set.Iio lambda.ord) :=
    cardinalProductRapidSupportBelow kappa lambda
      (toIio beta) (toIio alpha)
  have hStep : forall (alpha : L)
      (previous : forall beta, beta < alpha ->
        ProductElement (cardinalProductFrame A J)),
      exists r : ProductElement (cardinalProductFrame A J),
        (forall beta : L,
          CardinalProductClosedEventuallyLtProduct J
            (cardinalProductClosedPointwiseSup
              (partialAt alpha previous) (supportAt alpha beta)) r) /\
        forall beta hbeta,
          (cardinalProductFrame A J).eventuallyPointwiseLt
            (previous beta hbeta) r := by
    intro alpha previous
    obtain ⟨q, hq⟩ :=
      exists_cardinalProduct_strictUpperBound_of_closedPointwiseSups
        hRegulars hDirected hLevelSmall
          (partialAt alpha previous) (supportAt alpha)
          (fun beta => hSupportSmall (toIio beta) (toIio alpha)) d0
    let family : L -> ProductElement (cardinalProductFrame A J) :=
      fun beta => if hbeta : beta < alpha then
        previous beta hbeta else q
    obtain ⟨r, hr⟩ := hDirected L hLevelSmall family
    have hqr : (cardinalProductFrame A J).eventuallyPointwiseLt q r := by
      simpa only [family, dif_neg (lt_irrefl alpha)] using hr alpha
    refine ⟨r, ?_, ?_⟩
    · intro beta
      have hqrOrd :=
        (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue q r).mp hqr
      exact J.eventually_mono (J.eventually_and (hq beta) hqrOrd) (by
        intro k hk
        exact hk.1.trans hk.2)
    · intro beta hbeta
      simpa only [family, dif_pos hbeta] using hr beta
  let seq : L -> ProductElement (cardinalProductFrame A J) :=
    WellFounded.fix wellFounded_lt
      (fun alpha previous => Classical.choose (hStep alpha previous))
  have hSeqEq : forall alpha,
      seq alpha = Classical.choose
        (hStep alpha (fun beta hbeta => seq beta)) := by
    intro alpha
    exact WellFounded.fix_eq _ _ alpha
  let f : Set.Iio lambda.ord ->
      ProductElement (cardinalProductFrame A J) :=
    fun alpha => seq (toLevel alpha)
  refine ⟨f, ?_, ?_⟩
  · intro alpha beta hAlphaBeta
    have hLevel : toLevel alpha < toLevel beta := by
      simpa only [toLevel, L, cardinalScaleLength] using
        (Ordinal.ToType.mk :
          Set.Iio lambda.ord ≃o lambda.ord.ToType).lt_iff_lt.mpr hAlphaBeta
    rw [show f beta = seq (toLevel beta) from rfl, hSeqEq]
    exact (Classical.choose_spec
      (hStep (toLevel beta) (fun z hz => seq z))).2
        (toLevel alpha) hLevel
  · intro gamma hGammaUncountable hGammaKappa beta hBetaCof
    have hBetaLimit : Order.IsSuccLimit beta.1 := by
      rw [← Ordinal.one_lt_cof_iff]
      rw [hBetaCof]
      exact Cardinal.one_lt_aleph0.trans hGammaUncountable
    refine ⟨smallInitialClub beta.1,
      smallInitialClub_isClub hBetaLimit, ?_⟩
    intro alpha hAlphaLimit
    let alphaGlobal : Set.Iio lambda.ord :=
      ⟨alpha.1, by
        have hAlphaBeta : alpha.1 < beta.1 := by
          simpa only [Set.mem_Iio] using alpha.2
        have hBeta : beta.1 < lambda.ord := by
          simpa only [Set.mem_Iio] using beta.2
        exact hAlphaBeta.trans hBeta⟩
    let alphaLevel : L := toLevel alphaGlobal
    let betaLevel : L := toLevel beta
    have hAlphaBeta : alphaGlobal < beta := by
      exact alpha.2
    have hSupportEq : supportAt alphaLevel betaLevel =
        (fun xi : Set.Iio beta.1 =>
          (⟨xi.1, by
            have hXi : xi.1 < beta.1 := by
              simpa only [Set.mem_Iio] using xi.2
            have hBeta : beta.1 < lambda.ord := by
              simpa only [Set.mem_Iio] using beta.2
            exact hXi.trans hBeta⟩ : Set.Iio lambda.ord)) ''
            (smallInitialClub beta.1 ∩ Set.Iio alpha) := by
      dsimp only [supportAt, alphaLevel, betaLevel, toIio, toLevel]
      rw [(Ordinal.ToType.mk :
          Set.Iio lambda.ord ≃o lambda.ord.ToType).symm_apply_apply,
        (Ordinal.ToType.mk :
          Set.Iio lambda.ord ≃o lambda.ord.ToType).symm_apply_apply,
        cardinalProductRapidSupportBelow_eq (hBetaCof.symm ▸ hGammaKappa),
        cardinalProductRapidSupport_eq hAlphaBeta]
    have hPartialEq : Set.EqOn
        (partialAt alphaLevel
          (fun z hz => seq z)) f (supportAt alphaLevel betaLevel) := by
      intro i hi
      have hiRaw : i < toIio alphaLevel := by
        exact cardinalProductRapidSupportBelow_subset_Iio
          (by simpa only [supportAt] using hi)
      have hiAlpha : i < alphaGlobal := by
        simpa only [alphaLevel, toIio, toLevel,
          (Ordinal.ToType.mk :
            Set.Iio lambda.ord ≃o lambda.ord.ToType).symm_apply_apply]
          using hiRaw
      have hiLevel : toLevel i < alphaLevel := by
        simpa only [toLevel, alphaLevel, L, cardinalScaleLength] using
          (Ordinal.ToType.mk :
            Set.Iio lambda.ord ≃o lambda.ord.ToType).lt_iff_lt.mpr hiAlpha
      simp only [partialAt, dif_pos hiLevel, f]
    have hSupEq := cardinalProductClosedPointwiseSup_congr hPartialEq
    have hChosen := (Classical.choose_spec
      (hStep alphaLevel (fun z hz => seq z))).1 betaLevel
    rw [← hSeqEq alphaLevel] at hChosen
    change CardinalProductClosedEventuallyLtProduct J _ (f alphaGlobal)
    rw [← hSupportEq]
    rw [← hSupEq]
    exact hChosen

/-! A coloring of a regular uncountable canonical scale length by fewer
colors is constant on a stationary, hence cofinal, set of stages.  This is
the pigeonhole step in Jech Lemma 24.10 after functions have been rounded
into a small elementary hull. -/
theorem exists_cofinal_eqOn_const_cardinalScaleLength
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hThetaUncountable : Cardinal.aleph0 < theta)
    {beta : Type v}
    (hSmall : Cardinal.lift.{u, v} (Cardinal.mk beta) <
      Cardinal.lift.{v, u} theta)
    (color : theta.ord.ToType -> beta) :
    exists b : beta, exists T : Set theta.ord.ToType,
      Stationary T /\ IsCofinal T /\
        Set.EqOn color (fun _ => b) T := by
  letI : Nonempty theta.ord.ToType :=
    ⟨Ordinal.ToType.mk ⟨0, hThetaRegular.ord_pos⟩⟩
  have hCofEq : Order.cof theta.ord.ToType = theta := by
    rw [Ordinal.cof_toType, hThetaRegular.cof_ord]
  have hCofNe : Not
      (Order.cof theta.ord.ToType = Cardinal.aleph0) := by
    rw [hCofEq]
    exact ne_of_gt hThetaUncountable
  have hSmall' : Cardinal.lift.{u, v} (Cardinal.mk beta) <
      Cardinal.lift.{v, u} (Order.cof theta.ord.ToType) := by
    rw [hCofEq]
    exact hSmall
  obtain ⟨b, T, _hTSub, hTStationary, hColor⟩ :=
    exists_stationary_eqOn_const_of_small_codomain
      hCofNe hSmall' color
      (univ_stationary hCofNe)
  exact ⟨b, T, hTStationary, stationary_isCofinal hTStationary, hColor⟩

/-! Abstract elementary-hull core of Jech Lemma 24.10.  The hypotheses
separate the three facts supplied by the hull construction: each stage has a
rounded upper bound coded in a small type; minimality of that rounding holds
for functions in the hull; and elementarity reflects the resulting
cofinal-below assertion from hull members to all product members.  The small
coloring theorem above then makes one rounded bound repeat cofinally. -/
theorem exists_cardinalProductClosedExactUpperBound_of_small_roundingHull
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    {Code : Type v}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hThetaUncountable : Cardinal.aleph0 < theta)
    (hCodeSmall : Cardinal.lift.{u, v} (Cardinal.mk Code) <
      Cardinal.lift.{v, u} theta)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A J))
    (hIncreasing : forall {alpha beta : theta.ord.ToType}, alpha < beta ->
      (cardinalProductFrame A J).eventuallyPointwiseLt
        (d alpha) (d beta))
    (code : theta.ord.ToType -> Code)
    (rounded : Code -> CardinalProductClosedElement A)
    (InHull : ProductElement (cardinalProductFrame A J) -> Prop)
    (hRoundedUpper : forall alpha,
      CardinalProductEventuallyLtClosed J (d alpha) (rounded (code alpha)))
    (hRoundingMinimal : forall h,
      InHull h -> forall alpha,
        CardinalProductEventuallyLtClosed J h (rounded (code alpha)) ->
          (cardinalProductFrame A J).eventuallyLe h (d alpha))
    (hReflect : forall c,
      (forall h, InHull h ->
        CardinalProductEventuallyLtClosed J h (rounded c) ->
          exists alpha, (cardinalProductFrame A J).eventuallyLe h (d alpha)) ->
      forall h, CardinalProductEventuallyLtClosed J h (rounded c) ->
        exists alpha, (cardinalProductFrame A J).eventuallyLe h (d alpha)) :
    exists f : CardinalProductClosedElement A,
      CardinalProductClosedExactUpperBound J d f := by
  obtain ⟨c, T, _hTStationary, hTCofinal, hCode⟩ :=
    exists_cofinal_eqOn_const_cardinalScaleLength
      hThetaRegular hThetaUncountable hCodeSmall code
  refine ⟨rounded c, ?_, hReflect c ?_⟩
  · intro alpha
    obtain ⟨beta, hBetaT, hAlphaBeta⟩ := hTCofinal alpha
    have hBetaUpper := hRoundedUpper beta
    rw [hCode hBetaT] at hBetaUpper
    rcases hAlphaBeta.eq_or_lt with hEq | hLt
    · subst beta
      exact hBetaUpper
    · exact hBetaUpper.trans_of_eventuallyPointwiseLt
        (hIncreasing hLt)
  · intro h hHull hh
    obtain ⟨alpha, hAlphaT, _⟩ := hTCofinal
      (Ordinal.ToType.mk ⟨0, hThetaRegular.ord_pos⟩)
    refine ⟨alpha, hRoundingMinimal h hHull alpha ?_⟩
    rwa [hCode hAlphaT]

/-! The exact-upper-bound principle isolated from Jech Lemma 24.10.  It is
stated for a fixed canonical product and cardinal length: every
pointwise-strict increasing sequence of that length has a closed exact upper
bound.  The closed codomain is essential because the bound may attain a
coordinate top. -/
def CardinalProductClosedExactUpperBoundPrinciple
    (A : CardSet.{u})
    (J : Ideal (CardinalIndex A))
    (theta : Cardinal.{u}) : Prop :=
  forall d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J),
    (forall {alpha beta}, (cardinalScaleLength theta).lt alpha beta ->
      (cardinalProductFrame A J).eventuallyPointwiseLt
        (d alpha) (d beta)) ->
    exists f : CardinalProductClosedElement A,
      CardinalProductClosedExactUpperBound
        (iota := (cardinalScaleLength theta).Level) J d f
def CardinalProductHullCounterexample
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A J))
    (c : CardinalProductClosedElement A)
    (h : ProductElement (cardinalProductFrame A J)) : Prop :=
  CardinalProductEventuallyLtClosed J h c /\
    forall alpha, Not ((cardinalProductFrame A J).eventuallyLe h (d alpha))

noncomputable def cardinalProductHullChosenCounterexample
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A J))
    (d0 : ProductElement (cardinalProductFrame A J))
    (c : CardinalProductClosedElement A) :
    ProductElement (cardinalProductFrame A J) := by
  classical
  exact if h : exists x, CardinalProductHullCounterexample d c x then
      Classical.choose h
    else d0
theorem cardinalProductHullChosenCounterexample_spec
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A J))
    (d0 : ProductElement (cardinalProductFrame A J))
    (c : CardinalProductClosedElement A)
    (hExists : exists x, CardinalProductHullCounterexample d c x) :
    CardinalProductHullCounterexample d c
      (cardinalProductHullChosenCounterexample d d0 c) := by
  classical
  rw [cardinalProductHullChosenCounterexample, dif_pos hExists]
  exact Classical.choose_spec hExists

/-! Source-sized W-tree hull for a pushed-forward ideal.  Only coordinates
seen by the source map occur as branches, so its code size is controlled by
`2 ^ #I`, not by the potentially much larger ambient cardinal set. -/
abbrev PushforwardCardinalProductHullLabel
    (I : Type (u + 1)) : Type (u + 1) := I ⊕ I

def pushforwardCardinalProductHullArity
    (I : Type (u + 1)) :
    PushforwardCardinalProductHullLabel I -> Type (u + 1)
  | Sum.inl _ => PEmpty
  | Sum.inr _ => I

abbrev PushforwardCardinalProductHullCode
    (I : Type (u + 1)) : Type (u + 1) :=
  WType (pushforwardCardinalProductHullArity I)

def pushforwardCardinalProductHullTopCode
    {I : Type (u + 1)} (i : I) :
    PushforwardCardinalProductHullCode I :=
  WType.mk (Sum.inl i) (fun z => nomatch z)

def pushforwardCardinalProductHullWitnessCode
    {I : Type (u + 1)}
    (i : I)
    (children : I -> PushforwardCardinalProductHullCode I) :
    PushforwardCardinalProductHullCode I :=
  WType.mk (Sum.inr i) children

noncomputable def pushforwardCardinalProductHullClosedOfValues
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    (c : I -> CardinalIndex A)
    (values : I -> Ordinal.{u}) :
    CardinalProductClosedElement A := by
  classical
  exact fun k => if hk : exists i, c i = k then
      ⟨min (values (Classical.choose hk)) k.1.ord, by
        simpa only [Set.mem_Iic] using
          min_le_right (values (Classical.choose hk)) k.1.ord⟩
    else cardinalProductClosedTop A k

noncomputable def pushforwardCardinalProductHullAlgebra
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c))) :
    (Σ a, pushforwardCardinalProductHullArity I a -> Ordinal.{u}) ->
      Ordinal.{u}
  | ⟨Sum.inl i, _⟩ => (c i).1.ord
  | ⟨Sum.inr i, values⟩ =>
      cardinalProductOrdinalValue
        (cardinalProductHullChosenCounterexample d d0
          (pushforwardCardinalProductHullClosedOfValues c values)) (c i)

noncomputable def pushforwardCardinalProductHullValue
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c))) :
    PushforwardCardinalProductHullCode I -> Ordinal.{u} :=
  WType.elim _ (pushforwardCardinalProductHullAlgebra c d d0)

theorem pushforwardCardinalProductHullValue_top
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (i : I) :
    pushforwardCardinalProductHullValue c d d0
        (pushforwardCardinalProductHullTopCode i) = (c i).1.ord := by
  rfl

theorem pushforwardCardinalProductHullValue_witness
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (i : I)
    (children : I -> PushforwardCardinalProductHullCode I) :
    pushforwardCardinalProductHullValue c d d0
        (pushforwardCardinalProductHullWitnessCode i children) =
      cardinalProductOrdinalValue
        (cardinalProductHullChosenCounterexample d d0
          (pushforwardCardinalProductHullClosedOfValues c
            (fun j => pushforwardCardinalProductHullValue c d d0
              (children j)))) (c i) := by
  rfl

noncomputable def pushforwardCardinalProductHullClosed
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (code : I -> PushforwardCardinalProductHullCode I) :
    CardinalProductClosedElement A :=
  pushforwardCardinalProductHullClosedOfValues c
    (fun i => pushforwardCardinalProductHullValue c d d0 (code i))

def PushforwardCardinalProductInHull
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (h : ProductElement (cardinalProductFrame A (J.pushforward c))) : Prop :=
  forall i, cardinalProductOrdinalValue h (c i) ∈
    Set.range (pushforwardCardinalProductHullValue c d d0)

theorem pushforwardCardinalProductHull_reflect
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (code : I -> PushforwardCardinalProductHullCode I)
    (hHull : forall h, PushforwardCardinalProductInHull c d d0 h ->
      CardinalProductEventuallyLtClosed (J.pushforward c) h
        (pushforwardCardinalProductHullClosed c d d0 code) ->
      exists alpha,
        (cardinalProductFrame A (J.pushforward c)).eventuallyLe h (d alpha)) :
    forall h, CardinalProductEventuallyLtClosed (J.pushforward c) h
        (pushforwardCardinalProductHullClosed c d d0 code) ->
      exists alpha,
        (cardinalProductFrame A (J.pushforward c)).eventuallyLe h (d alpha) := by
  classical
  intro h hh
  by_contra hNo
  push Not at hNo
  have hExists : exists x, CardinalProductHullCounterexample d
      (pushforwardCardinalProductHullClosed c d d0 code) x :=
    ⟨h, hh, hNo⟩
  let witness := cardinalProductHullChosenCounterexample d d0
    (pushforwardCardinalProductHullClosed c d d0 code)
  have hWitness := cardinalProductHullChosenCounterexample_spec d d0
    (pushforwardCardinalProductHullClosed c d d0 code) hExists
  have hWitnessHull :
      PushforwardCardinalProductInHull c d d0 witness := by
    intro i
    refine ⟨pushforwardCardinalProductHullWitnessCode i code, ?_⟩
    rw [pushforwardCardinalProductHullValue_witness]
    rfl
  obtain ⟨alpha, hAlpha⟩ := hHull witness hWitnessHull hWitness.1
  exact hWitness.2 alpha hAlpha

def pushforwardCardinalProductHullRoundingSet
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) : Set (Ordinal.{u}) :=
  { beta | beta ∈ Set.range
        (pushforwardCardinalProductHullValue c d d0) /\
      cardinalProductOrdinalValue (d alpha) (c i) < beta }

theorem pushforwardCardinalProductHullRoundingSet_nonempty
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) :
    (pushforwardCardinalProductHullRoundingSet c d d0 alpha i).Nonempty := by
  refine ⟨(c i).1.ord, ?_, cardinalProductOrdinalValue_lt (d alpha) (c i)⟩
  exact ⟨pushforwardCardinalProductHullTopCode i,
    (pushforwardCardinalProductHullValue_top c d d0 i).symm⟩

noncomputable def pushforwardCardinalProductHullRoundedValue
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) : Ordinal.{u} :=
  sInf (pushforwardCardinalProductHullRoundingSet c d d0 alpha i)

theorem pushforwardCardinalProductHullRoundedValue_mem
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) :
    pushforwardCardinalProductHullRoundedValue c d d0 alpha i ∈
      pushforwardCardinalProductHullRoundingSet c d d0 alpha i := by
  exact csInf_mem
    (pushforwardCardinalProductHullRoundingSet_nonempty c d d0 alpha i)

theorem pushforwardCardinalProductHullRoundedValue_lt
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) :
    cardinalProductOrdinalValue (d alpha) (c i) <
      pushforwardCardinalProductHullRoundedValue c d d0 alpha i :=
  (pushforwardCardinalProductHullRoundedValue_mem c d d0 alpha i).2

theorem pushforwardCardinalProductHullRoundedValue_le_top
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) :
    pushforwardCardinalProductHullRoundedValue c d d0 alpha i <=
      (c i).1.ord := by
  exact (isLeast_csInf
    (pushforwardCardinalProductHullRoundingSet_nonempty c d d0 alpha i)).2
      ⟨⟨pushforwardCardinalProductHullTopCode i,
        (pushforwardCardinalProductHullValue_top c d d0 i).symm⟩,
        cardinalProductOrdinalValue_lt (d alpha) (c i)⟩

theorem pushforwardCardinalProductHullRoundingSet_eq_of_map_eq
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    {i j : I}
    (hij : c i = c j) :
    pushforwardCardinalProductHullRoundingSet c d d0 alpha i =
      pushforwardCardinalProductHullRoundingSet c d d0 alpha j := by
  simp only [pushforwardCardinalProductHullRoundingSet]
  rw [hij]

theorem pushforwardCardinalProductHullRoundedValue_eq_of_map_eq
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    {i j : I}
    (hij : c i = c j) :
    pushforwardCardinalProductHullRoundedValue c d d0 alpha i =
      pushforwardCardinalProductHullRoundedValue c d d0 alpha j := by
  exact congrArg sInf
    (pushforwardCardinalProductHullRoundingSet_eq_of_map_eq
      c d d0 alpha hij)

noncomputable def pushforwardCardinalProductHullRoundingCode
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) : PushforwardCardinalProductHullCode I :=
  Classical.choose
    (pushforwardCardinalProductHullRoundedValue_mem c d d0 alpha i).1

theorem pushforwardCardinalProductHullRoundingCode_spec
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) :
    pushforwardCardinalProductHullValue c d d0
        (pushforwardCardinalProductHullRoundingCode c d d0 alpha i) =
      pushforwardCardinalProductHullRoundedValue c d d0 alpha i :=
  Classical.choose_spec
    (pushforwardCardinalProductHullRoundedValue_mem c d d0 alpha i).1

theorem pushforwardCardinalProductHullClosed_roundingCode_value
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType)
    (i : I) :
    ((pushforwardCardinalProductHullClosed c d d0
      (pushforwardCardinalProductHullRoundingCode c d d0 alpha)) (c i)).1 =
        pushforwardCardinalProductHullRoundedValue c d d0 alpha i := by
  classical
  simp only [pushforwardCardinalProductHullClosed,
    pushforwardCardinalProductHullClosedOfValues]
  rw [dif_pos (show exists j, c j = c i from ⟨i, rfl⟩)]
  let j := Classical.choose (show exists j, c j = c i from ⟨i, rfl⟩)
  have hj : c j = c i :=
    Classical.choose_spec (show exists j, c j = c i from ⟨i, rfl⟩)
  change min (pushforwardCardinalProductHullValue c d d0
      (pushforwardCardinalProductHullRoundingCode c d d0 alpha j))
      (c i).1.ord = _
  rw [pushforwardCardinalProductHullRoundingCode_spec,
    pushforwardCardinalProductHullRoundedValue_eq_of_map_eq c d d0 alpha hj,
    min_eq_left (pushforwardCardinalProductHullRoundedValue_le_top
      c d d0 alpha i)]

theorem pushforwardCardinalProductHull_roundedUpper
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (alpha : theta.ord.ToType) :
    CardinalProductEventuallyLtClosed (J.pushforward c) (d alpha)
      (pushforwardCardinalProductHullClosed c d d0
        (pushforwardCardinalProductHullRoundingCode c d d0 alpha)) := by
  change (J.pushforward c).Eventually (fun k =>
    cardinalProductOrdinalValue (d alpha) k <
      ((pushforwardCardinalProductHullClosed c d d0
        (pushforwardCardinalProductHullRoundingCode c d d0 alpha)) k).1)
  rw [Ideal.pushforward_eventually_iff]
  apply J.eventually_of_forall
  intro i
  rw [pushforwardCardinalProductHullClosed_roundingCode_value]
  exact pushforwardCardinalProductHullRoundedValue_lt c d d0 alpha i

theorem pushforwardCardinalProductHull_roundingMinimal
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (h : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (hInHull : PushforwardCardinalProductInHull c d d0 h)
    (alpha : theta.ord.ToType)
    (hh : CardinalProductEventuallyLtClosed (J.pushforward c) h
      (pushforwardCardinalProductHullClosed c d d0
        (pushforwardCardinalProductHullRoundingCode c d d0 alpha))) :
    (cardinalProductFrame A (J.pushforward c)).eventuallyLe h (d alpha) := by
  change (J.pushforward c).Eventually (fun k =>
    cardinalProductOrdinalValue h k <
      ((pushforwardCardinalProductHullClosed c d d0
        (pushforwardCardinalProductHullRoundingCode c d d0 alpha)) k).1) at hh
  rw [Ideal.pushforward_eventually_iff] at hh
  change (J.pushforward c).Eventually (fun k =>
    (cardinalProductFrame A (J.pushforward c)).le k (h k) (d alpha k))
  rw [Ideal.pushforward_eventually_iff]
  apply J.eventually_mono hh
  intro i hi
  rw [pushforwardCardinalProductHullClosed_roundingCode_value] at hi
  have hValueMem := hInHull i
  have hNotLt : Not (cardinalProductOrdinalValue (d alpha) (c i) <
      cardinalProductOrdinalValue h (c i)) := by
    intro hLt
    have hCandidate : cardinalProductOrdinalValue h (c i) ∈
        pushforwardCardinalProductHullRoundingSet c d d0 alpha i :=
      ⟨hValueMem, hLt⟩
    have hRoundLe :
        pushforwardCardinalProductHullRoundedValue c d d0 alpha i <=
          cardinalProductOrdinalValue h (c i) :=
      (isLeast_csInf
        (pushforwardCardinalProductHullRoundingSet_nonempty
          c d d0 alpha i)).2 hCandidate
    exact (not_lt_of_ge hRoundLe) hi
  have hValueLe : cardinalProductOrdinalValue h (c i) <=
      cardinalProductOrdinalValue (d alpha) (c i) := not_lt.mp hNotLt
  exact ((Ordinal.ToType.mk :
      Set.Iio (c i).1.ord ≃o (c i).1.ord.ToType).symm
    |>.le_iff_le).mp hValueLe

theorem exists_pushforwardCardinalProductClosedExactUpperBound_of_hullCodeSmall
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (hThetaRegular : Cardinal.IsRegular theta)
    (hThetaUncountable : Cardinal.aleph0 < theta)
    (hCodeSmall : Cardinal.lift.{u, u + 1}
        (Cardinal.mk (I -> PushforwardCardinalProductHullCode I)) <
      Cardinal.lift.{u + 1, u} theta)
    (d : theta.ord.ToType ->
      ProductElement (cardinalProductFrame A (J.pushforward c)))
    (hIncreasing : forall {alpha beta : theta.ord.ToType}, alpha < beta ->
      (cardinalProductFrame A (J.pushforward c)).eventuallyPointwiseLt
        (d alpha) (d beta)) :
    exists f : CardinalProductClosedElement A,
      CardinalProductClosedExactUpperBound (J.pushforward c) d f := by
  let alpha0 : theta.ord.ToType :=
    Ordinal.ToType.mk ⟨0, hThetaRegular.ord_pos⟩
  let d0 := d alpha0
  apply exists_cardinalProductClosedExactUpperBound_of_small_roundingHull
    hThetaRegular hThetaUncountable hCodeSmall d hIncreasing
      (pushforwardCardinalProductHullRoundingCode c d d0)
      (pushforwardCardinalProductHullClosed c d d0)
      (PushforwardCardinalProductInHull c d d0)
  · exact pushforwardCardinalProductHull_roundedUpper c d d0
  · exact pushforwardCardinalProductHull_roundingMinimal c d d0
  · exact pushforwardCardinalProductHull_reflect c d d0

theorem mk_pushforwardCardinalProductHullCode_le_two_power
    {I : Type (u + 1)}
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk I) :
    Cardinal.mk (PushforwardCardinalProductHullCode I) <=
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk I := by
  let kappa : Cardinal.{u + 1} := Cardinal.mk I
  let mu : Cardinal.{u + 1} := 2 ^ kappa
  have hKappaNe : kappa ≠ 0 := by
    exact ne_of_gt (Cardinal.aleph0_pos.trans_le hIndexInfinite)
  have hKappaMu : kappa <= mu := (Cardinal.cantor kappa).le
  have hMuInfinite : Cardinal.aleph0 <= mu :=
    hIndexInfinite.trans hKappaMu
  have hMuNe : mu ≠ 0 := ne_of_gt
    (Cardinal.aleph0_pos.trans_le hMuInfinite)
  have hMuPower : mu ^ kappa = mu := by
    dsimp only [mu]
    rw [← Cardinal.power_mul,
      Cardinal.mul_eq_left hIndexInfinite le_rfl hKappaNe]
  have hLabelLe : Cardinal.mk (PushforwardCardinalProductHullLabel I) <=
      mu := by
    change Cardinal.mk (I ⊕ I) <= mu
    rw [Cardinal.mk_sum]
    rw [Cardinal.lift_id (Cardinal.mk I)]
    rw [Cardinal.add_eq_left hIndexInfinite le_rfl]
    exact hKappaMu
  have hArityPower : forall label : PushforwardCardinalProductHullLabel I,
      mu ^ Cardinal.mk (pushforwardCardinalProductHullArity I label) <= mu := by
    intro label
    rcases label with i | i
    · simp only [pushforwardCardinalProductHullArity, Cardinal.mk_pempty]
      simpa using Cardinal.one_le_iff_ne_zero.mpr hMuNe
    · change mu ^ kappa <= mu
      rw [hMuPower]
  apply WType.cardinalMk_le_of_le
  calc
    (Cardinal.sum fun label : PushforwardCardinalProductHullLabel I =>
        mu ^ Cardinal.mk (pushforwardCardinalProductHullArity I label)) <=
        Cardinal.mk (PushforwardCardinalProductHullLabel I) *
          ⨆ label : PushforwardCardinalProductHullLabel I,
            mu ^ Cardinal.mk
              (pushforwardCardinalProductHullArity I label) :=
      Cardinal.sum_le_mk_mul_iSup _
    _ <= mu * mu := mul_le_mul' hLabelLe (ciSup_le' hArityPower)
    _ = mu := Cardinal.mul_eq_left hMuInfinite le_rfl hMuNe

theorem mk_pushforwardCardinalProductHullColorCode_le_two_power
    {I : Type (u + 1)}
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk I) :
    Cardinal.mk (I -> PushforwardCardinalProductHullCode I) <=
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk I := by
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id]
  have hHull :=
    mk_pushforwardCardinalProductHullCode_le_two_power hIndexInfinite
  have hKappaNe : Cardinal.mk I ≠ 0 := by
    exact ne_of_gt (Cardinal.aleph0_pos.trans_le hIndexInfinite)
  calc
    Cardinal.mk (PushforwardCardinalProductHullCode I) ^ Cardinal.mk I <=
      ((2 : Cardinal.{u + 1}) ^ Cardinal.mk I) ^ Cardinal.mk I :=
      Cardinal.power_le_power_right hHull
    _ = (2 : Cardinal.{u + 1}) ^ Cardinal.mk I := by
      rw [← Cardinal.power_mul,
        Cardinal.mul_eq_left hIndexInfinite le_rfl hKappaNe]

theorem pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk I)
    (hThetaRegular : Cardinal.IsRegular theta)
    (hThetaUncountable : Cardinal.aleph0 < theta)
    (hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk I <
      Cardinal.lift.{u + 1} theta) :
    CardinalProductClosedExactUpperBoundPrinciple
      A (J.pushforward c) theta := by
  intro d hIncreasing
  apply exists_pushforwardCardinalProductClosedExactUpperBound_of_hullCodeSmall
    c hThetaRegular hThetaUncountable
  calc
    Cardinal.lift.{u, u + 1}
        (Cardinal.mk (I -> PushforwardCardinalProductHullCode I)) =
        Cardinal.mk (I -> PushforwardCardinalProductHullCode I) :=
      Cardinal.lift_id'.{u, u + 1} _
    _ <= (2 : Cardinal.{u + 1}) ^ Cardinal.mk I :=
      mk_pushforwardCardinalProductHullColorCode_le_two_power hIndexInfinite
    _ < Cardinal.lift.{u + 1} theta := hPower
  exact hIncreasing

theorem localizedPushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
    {I : Type (u + 1)}
    {A : CardSet.{u}}
    {J : Ideal I}
    {theta : Cardinal.{u}}
    (c : I -> CardinalIndex A)
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk I)
    (hThetaRegular : Cardinal.IsRegular theta)
    (hThetaUncountable : Cardinal.aleph0 < theta)
    (hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk I <
      Cardinal.lift.{u + 1} theta)
    (X : CardinalIndex A -> Prop) :
    CardinalProductClosedExactUpperBoundPrinciple
      A ((J.pushforward c).localize X) theta := by
  rw [Ideal.pushforward_localize]
  exact pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
    c hIndexInfinite hThetaRegular hThetaUncountable hPower

/-! Canonical-size strict directedness is the boundary case immediately
above `PointwiseStrictDirectedBelow theta`: it asks for a strict upper bound
for every family indexed by the canonical type of cardinality `theta`. -/
def CardinalProductPointwiseStrictDirectedAt
    (A : CardSet.{u})
    (J : Ideal (CardinalIndex A))
    (theta : Cardinal.{u}) : Prop :=
  forall d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J),
    exists p : ProductElement (cardinalProductFrame A J),
      (cardinalProductFrame A J).IsPointwiseStrictUpperBound d p

/-! Bounding canonical `theta`-families upgrades directedness below `theta`
to directedness below the cardinal successor.  An arbitrary family of size
at most `theta` embeds into the canonical index type and is padded by one of
its members; the empty case is already covered by directedness below
`theta`. -/
theorem pointwiseStrictDirectedBelow_succ_of_directedAt
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaPos : 0 < theta)
    (hBelow : (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta)
    (hAt : CardinalProductPointwiseStrictDirectedAt A J theta) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      (Order.succ theta) := by
  classical
  intro iota hSmall d
  have hLe : Cardinal.mk iota <= theta :=
    Order.lt_succ_iff.mp hSmall
  by_cases hIota : Nonempty iota
  · let i0 : iota := Classical.choice hIota
    have hEmbedding :
        Nonempty (iota ↪ (cardinalScaleLength theta).Level) := by
      apply Cardinal.lift_mk_le.{0}.mp
      simpa using hLe
    let e : iota ↪ (cardinalScaleLength theta).Level :=
      Classical.choice hEmbedding
    let dCanonical : (cardinalScaleLength theta).Level ->
        ProductElement (cardinalProductFrame A J) := fun alpha =>
      if h : alpha ∈ Set.range e then d (Classical.choose h) else d i0
    obtain ⟨p, hp⟩ := hAt dCanonical
    refine ⟨p, ?_⟩
    intro i
    have hEq : dCanonical (e i) = d i := by
      dsimp only [dCanonical]
      rw [dif_pos ⟨i, rfl⟩]
      congr 1
      apply e.injective
      exact Classical.choose_spec
        (⟨i, rfl⟩ : e i ∈ Set.range e)
    simpa only [hEq] using hp (e i)
  · have hZero : Cardinal.mk iota = 0 :=
      Cardinal.mk_eq_zero_iff.mpr (not_nonempty_iff.mp hIota)
    have hEmptySmall : Cardinal.mk iota < theta := by
      rw [hZero]
      exact hThetaPos
    exact hBelow iota hEmptySmall d

/-! A regular-length family can be recursively dominated by a
pointwise-strict increasing sequence whenever the product is strictly
directed below that length.  Cofinality of the original family is not used. -/
theorem pointwiseStrictDominatingSequence_of_directedBelow
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      theta)
    (d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)) :
    Nonempty (PointwiseStrictDominatingSequence
      (cardinalProductFrame A J) (cardinalScaleLength theta) d) := by
  classical
  let L := cardinalScaleLength theta
  let F := cardinalProductFrame A J
  letI : LinearOrder L.Level := by
    change LinearOrder theta.ord.ToType
    infer_instance
  letI : WellFoundedLT L.Level := ⟨L.isWellOrder.wf⟩
  have hStep : forall (alpha : L.Level)
      (previous : forall beta, beta < alpha -> ProductElement F),
      exists q : ProductElement F,
        F.eventuallyPointwiseLt (d alpha) q /\
        forall beta hbeta,
          F.eventuallyPointwiseLt (previous beta hbeta) q := by
    intro alpha previous
    let predFamily : {beta : L.Level // beta < alpha} ->
        ProductElement F := fun beta => previous beta.1 beta.2
    have hPredSmall : Cardinal.mk {beta : L.Level // beta < alpha} <
        theta := by
      have hOrderType :
          (Cardinal.mk L.Level).ord =
            Ordinal.type (fun x y : L.Level => x < y) := by
        rw [show Cardinal.mk L.Level = theta by
          exact mk_cardinalScaleLength_level theta]
        exact (Ordinal.type_toType theta.ord).symm
      calc
        Cardinal.mk {beta : L.Level // beta < alpha} <
            Cardinal.mk L.Level := Cardinal.mk_Iio_lt alpha hOrderType
        _ = theta := mk_cardinalScaleLength_level theta
    obtain ⟨p, hp⟩ := hDirected _ hPredSmall predFamily
    let pair : ULift.{u} (Fin 2) -> ProductElement F := fun i =>
      if i.down = 0 then d alpha else p
    have hTwoSmall : Cardinal.mk (ULift.{u} (Fin 2)) < theta := by
      calc
        Cardinal.mk (ULift.{u} (Fin 2)) = 2 := by simp
        _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
        _ <= theta := hThetaRegular.aleph0_le
    obtain ⟨q, hq⟩ := hDirected (ULift.{u} (Fin 2)) hTwoSmall pair
    have hDq : F.eventuallyPointwiseLt (d alpha) q := by
      simpa only [pair, if_pos] using hq (ULift.up (0 : Fin 2))
    have hPq : F.eventuallyPointwiseLt p q := by
      have hOneNe : (1 : Fin 2) ≠ 0 := by decide
      simpa only [pair, if_neg hOneNe] using hq (ULift.up (1 : Fin 2))
    refine ⟨q, hDq, ?_⟩
    intro beta hbeta
    exact F.eventuallyPointwiseLt_trans
      (hp ⟨beta, hbeta⟩) hPq
  let seq : L.Level -> ProductElement F :=
    WellFounded.fix L.isWellOrder.wf
      (fun alpha previous => Classical.choose (hStep alpha previous))
  have hSeqEq : forall alpha,
      seq alpha = Classical.choose
        (hStep alpha (fun beta hbeta => seq beta)) := by
    intro alpha
    exact WellFounded.fix_eq _ _ alpha
  refine ⟨{
    seq := seq
    increasing := ?_
    dominates := ?_ }⟩
  · intro alpha beta hlt
    rw [hSeqEq beta]
    exact (Classical.choose_spec
      (hStep beta (fun gamma hgamma => seq gamma))).2 alpha hlt
  · intro alpha
    rw [hSeqEq alpha]
    exact (Classical.choose_spec
      (hStep alpha (fun beta hbeta => seq beta))).1

/-! Corollary 24.12 core.  Starting from an unbounded family of regular
length, strict directedness recursively produces an increasing sequence
which is still unbounded.  Lemma 24.10 supplies its closed exact upper bound,
and the top decomposition above forces either a global scale or a scale on a
positive localization. -/
theorem pointwiseStrictScale_or_localizedScale_of_unboundedFamily
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      theta)
    (hExact : CardinalProductClosedExactUpperBoundPrinciple A J theta)
    (d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J))
    (hUnbounded : Not (exists p : ProductElement
        (cardinalProductFrame A J),
      (cardinalProductFrame A J).IsPointwiseStrictUpperBound d p)) :
    Nonempty (PointwiseStrictScale
      (cardinalProductFrame A J) (cardinalScaleLength theta)) \/
      exists X : CardinalIndex A -> Prop,
        (J.localize X).IsProper /\
        Nonempty (PointwiseStrictScale
          (cardinalProductFrame A (J.localize X))
          (cardinalScaleLength theta)) := by
  obtain ⟨s⟩ := pointwiseStrictDominatingSequence_of_directedBelow
    hThetaRegular hDirected d
  obtain ⟨f, hf⟩ := hExact s.seq s.increasing
  let alpha0 : (cardinalScaleLength theta).Level :=
    Ordinal.ToType.mk ⟨0, hThetaRegular.ord_pos⟩
  rcases cardinalProductClosedExactUpperBound_top_decomposition
      alpha0 hf with hBound | hCofinal | hSplit
  · exfalso
    apply hUnbounded
    obtain ⟨p, hp⟩ := hBound
    refine ⟨p, ?_⟩
    intro alpha
    exact (cardinalProductFrame A J).eventuallyPointwiseLt_trans
      (s.dominates alpha) (hp alpha)
  · left
    exact ⟨{
      seq := s.seq
      increasing := s.increasing
      cofinal := hCofinal }⟩
  · obtain ⟨X, hXProper, hOffProper, _hBoundOnX, hCofinalOffX⟩ :=
      hSplit
    right
    refine ⟨fun k => Not (X k), hOffProper, ⟨{
      seq := s.seq
      increasing := ?_
      cofinal := hCofinalOffX }⟩⟩
    intro alpha beta hab
    exact (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
      (J.localize (fun k => Not (X k)))
      (J.le_localize (fun k => Not (X k)))
      (s.increasing hab)

/-! Canonical Corollary 24.12 trichotomy: exact upper bounds and strict
directedness below a regular `theta` imply strict directedness at `theta`, a
global `theta`-scale, or a `theta`-scale on a positive localization. -/
theorem pointwiseStrictDirectedAt_or_scale_or_localizedScale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      theta)
    (hExact : CardinalProductClosedExactUpperBoundPrinciple A J theta) :
    CardinalProductPointwiseStrictDirectedAt A J theta \/
      Nonempty (PointwiseStrictScale
        (cardinalProductFrame A J) (cardinalScaleLength theta)) \/
      exists X : CardinalIndex A -> Prop,
        (J.localize X).IsProper /\
        Nonempty (PointwiseStrictScale
          (cardinalProductFrame A (J.localize X))
          (cardinalScaleLength theta)) := by
  classical
  by_cases hAt : CardinalProductPointwiseStrictDirectedAt A J theta
  · exact Or.inl hAt
  · right
    simp only [CardinalProductPointwiseStrictDirectedAt, not_forall] at hAt
    obtain ⟨d, hd⟩ := hAt
    exact pointwiseStrictScale_or_localizedScale_of_unboundedFamily
      hThetaRegular hDirected hExact d hd

/-! Successor-directed form of the canonical trichotomy.  This is the
cardinal-successor conclusion appearing in Corollary 24.12; the other two
branches exhibit a global or positive-localized scale. -/
theorem pointwiseStrictDirectedBelow_succ_or_scale_or_localizedScale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      theta)
    (hExact : CardinalProductClosedExactUpperBoundPrinciple A J theta) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow
        (Order.succ theta) \/
      Nonempty (PointwiseStrictScale
        (cardinalProductFrame A J) (cardinalScaleLength theta)) \/
      exists X : CardinalIndex A -> Prop,
        (J.localize X).IsProper /\
        Nonempty (PointwiseStrictScale
          (cardinalProductFrame A (J.localize X))
          (cardinalScaleLength theta)) := by
  rcases pointwiseStrictDirectedAt_or_scale_or_localizedScale
      hThetaRegular hDirected hExact with hAt | hScale | hLocalized
  · exact Or.inl (pointwiseStrictDirectedBelow_succ_of_directedAt
      hThetaRegular.pos hDirected hAt)
  · exact Or.inr (Or.inl hScale)
  · exact Or.inr (Or.inr hLocalized)

/-! A target-size family absorbs the scales on every positive localization
when each member of each such scale is eventually below some member of the
family. Under the cardinal bound in Corollary 24.12, the family is obtained
by enumerating all positive predicates and their scales. -/
def CardinalProductLocalizedScaleAbsorbingFamily
    (A : CardSet.{u})
    (J : Ideal (CardinalIndex A))
    (theta : Cardinal.{u})
    (d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)) : Prop :=
  forall X : CardinalIndex A -> Prop, (J.localize X).IsProper ->
    forall s : PointwiseStrictScale
      (cardinalProductFrame A (J.localize X)) (cardinalScaleLength theta),
    forall alpha, exists beta,
      (cardinalProductFrame A (J.localize X)).eventuallyLe
        (s.seq alpha) (d beta)

/-! The supports on which a positive localization carries a scale.  Only the
predicate is retained in the subtype; properness and scale existence are
propositions, so one chosen scale per predicate suffices for the enumeration
argument in Corollary 24.12. -/
def CardinalProductLocalizedScaleSupport
    (A : CardSet.{u})
    (J : Ideal (CardinalIndex A))
    (theta : Cardinal.{u}) :=
  {X : CardinalIndex A -> Prop //
    (J.localize X).IsProper /\
      Nonempty (PointwiseStrictScale
        (cardinalProductFrame A (J.localize X))
        (cardinalScaleLength theta))}

noncomputable def CardinalProductLocalizedScaleSupport.chosenScale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (z : CardinalProductLocalizedScaleSupport A J theta) :
    PointwiseStrictScale
      (cardinalProductFrame A (J.localize z.1))
      (cardinalScaleLength theta) :=
  Classical.choice z.2.2

/-! An injection enumerating every scale support and every position on its
chosen scale gives the absorbing family required in Corollary 24.12.  Values
outside the range are padded by an arbitrary product member. -/
theorem exists_localizedScaleAbsorbingFamily_of_supportEmbedding
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (d0 : ProductElement (cardinalProductFrame A J))
    (e : CardinalProductLocalizedScaleSupport A J theta ×
        (cardinalScaleLength theta).Level ↪
      (cardinalScaleLength theta).Level) :
    exists d : (cardinalScaleLength theta).Level ->
        ProductElement (cardinalProductFrame A J),
      CardinalProductLocalizedScaleAbsorbingFamily A J theta d := by
  classical
  let raw : CardinalProductLocalizedScaleSupport A J theta ×
        (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J) := fun z =>
    z.1.chosenScale.seq z.2
  let d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J) := fun beta =>
    if h : beta ∈ Set.range e then raw (Classical.choose h) else d0
  refine ⟨d, ?_⟩
  intro X hXProper s alpha
  let z : CardinalProductLocalizedScaleSupport A J theta :=
    ⟨X, hXProper, ⟨s⟩⟩
  obtain ⟨beta, hbeta⟩ := z.chosenScale.cofinal (s.seq alpha)
  refine ⟨e (z, beta), ?_⟩
  have hd : d (e (z, beta)) = z.chosenScale.seq beta := by
    dsimp only [d]
    rw [dif_pos ⟨(z, beta), rfl⟩]
    have hPair : Classical.choose
        (⟨(z, beta), rfl⟩ : e (z, beta) ∈ Set.range e) = (z, beta) := by
      apply e.injective
      exact Classical.choose_spec
        (⟨(z, beta), rfl⟩ : e (z, beta) ∈ Set.range e)
    rw [hPair]
  simpa only [hd] using hbeta

/-! The powerset-size bound supplies the preceding injection.  The subtype
of supports has no more elements than the full predicate type, and multiplying
that bound by the infinite cardinal `theta` does not enlarge it. -/
theorem localizedScaleSupport_product_embedding_of_mk_predicates_le
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaInfinite : Cardinal.aleph0 <= theta)
    (hPower : Cardinal.mk (CardinalIndex A -> Prop) <=
      Cardinal.lift.{u + 1} theta) :
    Nonempty (CardinalProductLocalizedScaleSupport A J theta ×
        (cardinalScaleLength theta).Level ↪
      (cardinalScaleLength theta).Level) := by
  have hSupport :
      Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta) <=
        Cardinal.lift.{u + 1} theta :=
    (Cardinal.mk_subtype_le _).trans hPower
  apply Cardinal.lift_mk_le'.mp
  have hLiftSupport : Cardinal.lift.{u}
      (Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta)) =
      Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta) :=
    Cardinal.lift_id'.{u, u + 1} _
  have hIndex :
      Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta ×
        (cardinalScaleLength theta).Level) <=
        Cardinal.lift.{u + 1}
          (Cardinal.mk (cardinalScaleLength theta).Level) := by
    calc
      Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta ×
          (cardinalScaleLength theta).Level) =
          Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta) *
            Cardinal.lift.{u + 1} theta := by
              rw [Cardinal.mk_prod, mk_cardinalScaleLength_level]
              rw [hLiftSupport]
      _ <= max (Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta))
          (Cardinal.lift.{u + 1} theta) :=
        Cardinal.mul_le_max_of_aleph0_le_right
          (Cardinal.aleph0_le_lift.mpr hThetaInfinite)
      _ = Cardinal.lift.{u + 1} theta := max_eq_right hSupport
      _ = Cardinal.lift.{u + 1}
          (Cardinal.mk (cardinalScaleLength theta).Level) := by
        rw [mk_cardinalScaleLength_level]
  have hLiftProduct : Cardinal.lift.{u}
      (Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta ×
        (cardinalScaleLength theta).Level)) =
      Cardinal.mk (CardinalProductLocalizedScaleSupport A J theta ×
        (cardinalScaleLength theta).Level) :=
    Cardinal.lift_id'.{u, u + 1} _
  rw [hLiftProduct]
  exact hIndex

/-! Hence the cardinality bound on the set of predicates constructs the
absorbing family itself.  This is the enumeration step of Jech 24.12, with
one chosen cofinal scale for each positive support. -/
theorem exists_localizedScaleAbsorbingFamily_of_mk_predicates_le
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaInfinite : Cardinal.aleph0 <= theta)
    (hPower : Cardinal.mk (CardinalIndex A -> Prop) <=
      Cardinal.lift.{u + 1} theta)
    (d0 : ProductElement (cardinalProductFrame A J)) :
    exists d : (cardinalScaleLength theta).Level ->
        ProductElement (cardinalProductFrame A J),
      CardinalProductLocalizedScaleAbsorbingFamily A J theta d := by
  obtain ⟨e⟩ := localizedScaleSupport_product_embedding_of_mk_predicates_le
    hThetaInfinite hPower
  exact exists_localizedScaleAbsorbingFamily_of_supportEmbedding d0 e

/-! For a product ideal obtained by pushforward, positive localizations are
controlled by predicates on the source type.  This is the cardinal estimate
used in Theorem 24.16, where the ambient coordinate set is larger than the
range of a cofinal fundamental sequence. -/
def CardinalProductPushforwardLocalizedScaleSupport
    (I : Type (u + 1))
    (A : CardSet.{u})
    (J : Ideal I)
    (c : I -> CardinalIndex A)
    (theta : Cardinal.{u}) :=
  {P : I -> Prop //
    ((J.localize P).pushforward c).IsProper /\
      Nonempty (PointwiseStrictScale
        (cardinalProductFrame A ((J.localize P).pushforward c))
        (cardinalScaleLength theta))}

noncomputable def CardinalProductPushforwardLocalizedScaleSupport.chosenScale
    {I : Type (u + 1)} {A : CardSet.{u}} {J : Ideal I}
    {c : I -> CardinalIndex A} {theta : Cardinal.{u}}
    (z : CardinalProductPushforwardLocalizedScaleSupport I A J c theta) :
    PointwiseStrictScale
      (cardinalProductFrame A ((J.localize z.1).pushforward c))
      (cardinalScaleLength theta) :=
  Classical.choice z.2.2

theorem pushforwardLocalizedScaleSupport_product_embedding_of_mk_predicates_le
    {I : Type (u + 1)} {A : CardSet.{u}} {J : Ideal I}
    {c : I -> CardinalIndex A} {theta : Cardinal.{u}}
    (hThetaInfinite : Cardinal.aleph0 <= theta)
    (hPower : Cardinal.mk (I -> Prop) <= Cardinal.lift.{u + 1} theta) :
    Nonempty (CardinalProductPushforwardLocalizedScaleSupport I A J c theta ×
        (cardinalScaleLength theta).Level ↪
      (cardinalScaleLength theta).Level) := by
  have hSupport :
      Cardinal.mk
          (CardinalProductPushforwardLocalizedScaleSupport I A J c theta) <=
        Cardinal.lift.{u + 1} theta :=
    (Cardinal.mk_subtype_le _).trans hPower
  apply Cardinal.lift_mk_le'.mp
  have hLiftSupport : Cardinal.lift.{u}
      (Cardinal.mk
        (CardinalProductPushforwardLocalizedScaleSupport I A J c theta)) =
      Cardinal.mk
        (CardinalProductPushforwardLocalizedScaleSupport I A J c theta) :=
    Cardinal.lift_id'.{u, u + 1} _
  have hIndex :
      Cardinal.mk
          (CardinalProductPushforwardLocalizedScaleSupport I A J c theta ×
            (cardinalScaleLength theta).Level) <=
        Cardinal.lift.{u + 1}
          (Cardinal.mk (cardinalScaleLength theta).Level) := by
    calc
      Cardinal.mk
          (CardinalProductPushforwardLocalizedScaleSupport I A J c theta ×
            (cardinalScaleLength theta).Level) =
          Cardinal.mk
              (CardinalProductPushforwardLocalizedScaleSupport I A J c theta) *
            Cardinal.lift.{u + 1} theta := by
              rw [Cardinal.mk_prod, mk_cardinalScaleLength_level]
              rw [hLiftSupport]
      _ <= max
          (Cardinal.mk
            (CardinalProductPushforwardLocalizedScaleSupport I A J c theta))
          (Cardinal.lift.{u + 1} theta) :=
        Cardinal.mul_le_max_of_aleph0_le_right
          (Cardinal.aleph0_le_lift.mpr hThetaInfinite)
      _ = Cardinal.lift.{u + 1} theta := max_eq_right hSupport
      _ = Cardinal.lift.{u + 1}
          (Cardinal.mk (cardinalScaleLength theta).Level) := by
        rw [mk_cardinalScaleLength_level]
  have hLiftProduct : Cardinal.lift.{u}
      (Cardinal.mk
        (CardinalProductPushforwardLocalizedScaleSupport I A J c theta ×
          (cardinalScaleLength theta).Level)) =
      Cardinal.mk
        (CardinalProductPushforwardLocalizedScaleSupport I A J c theta ×
          (cardinalScaleLength theta).Level) :=
    Cardinal.lift_id'.{u, u + 1} _
  rw [hLiftProduct]
  exact hIndex

theorem exists_pushforwardLocalizedScaleAbsorbingFamily_of_supportEmbedding
    {I : Type (u + 1)} {A : CardSet.{u}} {J : Ideal I}
    {c : I -> CardinalIndex A} {theta : Cardinal.{u}}
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c)))
    (e : CardinalProductPushforwardLocalizedScaleSupport I A J c theta ×
        (cardinalScaleLength theta).Level ↪
      (cardinalScaleLength theta).Level) :
    exists d : (cardinalScaleLength theta).Level ->
        ProductElement (cardinalProductFrame A (J.pushforward c)),
      CardinalProductLocalizedScaleAbsorbingFamily
        A (J.pushforward c) theta d := by
  classical
  let raw : CardinalProductPushforwardLocalizedScaleSupport I A J c theta ×
        (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A (J.pushforward c)) := fun z =>
    z.1.chosenScale.seq z.2
  let d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A (J.pushforward c)) := fun beta =>
    if h : beta ∈ Set.range e then raw (Classical.choose h) else d0
  refine ⟨d, ?_⟩
  intro X hXProper s alpha
  let P : I -> Prop := fun i => X (c i)
  have hEq : (J.pushforward c).localize X =
      (J.localize P).pushforward c := J.pushforward_localize c X
  have hPProper : ((J.localize P).pushforward c).IsProper := by
    rw [← hEq]
    exact hXProper
  let sP : PointwiseStrictScale
      (cardinalProductFrame A ((J.localize P).pushforward c))
      (cardinalScaleLength theta) := {
    seq := s.seq
    increasing := by
      intro a b hab
      rw [← hEq]
      exact s.increasing hab
    cofinal := by
      intro g
      obtain ⟨a, ha⟩ := s.cofinal g
      refine ⟨a, ?_⟩
      rw [← hEq]
      exact ha }
  let z : CardinalProductPushforwardLocalizedScaleSupport I A J c theta :=
    ⟨P, hPProper, ⟨sP⟩⟩
  obtain ⟨beta, hbeta⟩ := z.chosenScale.cofinal (s.seq alpha)
  refine ⟨e (z, beta), ?_⟩
  have hd : d (e (z, beta)) = z.chosenScale.seq beta := by
    dsimp only [d]
    rw [dif_pos ⟨(z, beta), rfl⟩]
    have hPair : Classical.choose
        (⟨(z, beta), rfl⟩ : e (z, beta) ∈ Set.range e) = (z, beta) := by
      apply e.injective
      exact Classical.choose_spec
        (⟨(z, beta), rfl⟩ : e (z, beta) ∈ Set.range e)
    rw [hPair]
  have hout :
      (cardinalProductFrame A ((J.pushforward c).localize X)).eventuallyLe
        (s.seq alpha) (z.chosenScale.seq beta) := by
    let Q : CardinalIndex A -> Prop := fun i =>
      (cardinalProductFrame A (J.pushforward c)).le i
        (s.seq alpha i) (z.chosenScale.seq beta i)
    change ((J.pushforward c).localize X).Eventually Q
    change ((J.localize P).pushforward c).Eventually Q at hbeta
    rw [hEq]
    exact hbeta
  simpa only [hd] using hout

theorem exists_pushforwardLocalizedScaleAbsorbingFamily_of_mk_predicates_le
    {I : Type (u + 1)} {A : CardSet.{u}} {J : Ideal I}
    {c : I -> CardinalIndex A} {theta : Cardinal.{u}}
    (hThetaInfinite : Cardinal.aleph0 <= theta)
    (hPower : Cardinal.mk (I -> Prop) <= Cardinal.lift.{u + 1} theta)
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c))) :
    exists d : (cardinalScaleLength theta).Level ->
        ProductElement (cardinalProductFrame A (J.pushforward c)),
      CardinalProductLocalizedScaleAbsorbingFamily
        A (J.pushforward c) theta d := by
  obtain ⟨e⟩ :=
    pushforwardLocalizedScaleSupport_product_embedding_of_mk_predicates_le
      hThetaInfinite hPower
  exact exists_pushforwardLocalizedScaleAbsorbingFamily_of_supportEmbedding
    d0 e

/-! Full order-theoretic Corollary 24.12 from its exact-upper-bound and
enumeration ingredients.  The output is successor directedness, a global
scale, or a partition into a scale side and a successor-directed side. -/
theorem pointwiseStrictCorollary2412_of_exactUpperBounds_of_absorbingFamily
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta)
    (hExact : CardinalProductClosedExactUpperBoundPrinciple A J theta)
    (hExactLocalized : forall X : CardinalIndex A -> Prop,
      (J.localize X).IsProper ->
      CardinalProductClosedExactUpperBoundPrinciple A (J.localize X) theta)
    (d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J))
    (hAbsorb : CardinalProductLocalizedScaleAbsorbingFamily A J theta d) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta) \/
      Nonempty (PointwiseStrictScale
        (cardinalProductFrame A J) (cardinalScaleLength theta)) \/
      exists X Y : CardinalIndex A -> Prop,
        (forall k, X k \/ Y k) /\
        (J.localize X).IsProper /\
        (J.localize Y).IsProper /\
        Nonempty (PointwiseStrictScale
          (cardinalProductFrame A (J.localize X))
          (cardinalScaleLength theta)) /\
        (cardinalProductFrame A (J.localize Y)).PointwiseStrictDirectedBelow
          (Order.succ theta) := by
  classical
  rcases pointwiseStrictDirectedBelow_succ_or_scale_or_localizedScale
      hThetaRegular hDirected hExact with hSucc | hGlobal | hInitialLocal
  · exact Or.inl hSucc
  · exact Or.inr (Or.inl hGlobal)
  · obtain ⟨Z, hZProper, ⟨tZ⟩⟩ := hInitialLocal
    obtain ⟨s⟩ := pointwiseStrictDominatingSequence_of_directedBelow
      hThetaRegular hDirected d
    obtain ⟨f, hf⟩ := hExact s.seq s.increasing
    let alpha0 : (cardinalScaleLength theta).Level :=
      Ordinal.ToType.mk ⟨0, hThetaRegular.ord_pos⟩
    have contradictScale
        (Z : CardinalIndex A -> Prop)
        (hZProper : (J.localize Z).IsProper)
        (p : ProductElement (cardinalProductFrame A (J.localize Z)))
        (hUpper : (cardinalProductFrame A (J.localize Z)).IsPointwiseStrictUpperBound
          s.seq p)
        (t : PointwiseStrictScale
          (cardinalProductFrame A (J.localize Z))
          (cardinalScaleLength theta)) : False := by
      apply t.not_exists_pointwiseStrictUpperBound hZProper
      refine ⟨p, ?_⟩
      intro alpha
      obtain ⟨beta, htb⟩ := hAbsorb Z hZProper t alpha
      have hds : (cardinalProductFrame A (J.localize Z)).eventuallyPointwiseLt
          (d beta) (s.seq beta) :=
        (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
          (J.localize Z) (J.le_localize Z) (s.dominates beta)
      exact (cardinalProductFrame A (J.localize Z)).eventuallyPointwiseLt_trans
        ((cardinalProductFrame A (J.localize Z)).eventuallyLe_eventuallyPointwiseLt_trans
          htb hds)
        (hUpper beta)
    rcases cardinalProductClosedExactUpperBound_top_decomposition
        alpha0 hf with hBound | hCofinal | hSplit
    · obtain ⟨p, hp⟩ := hBound
      have hJZ : Ideal.Le J (J.localize Z) := J.le_localize Z
      have hpZ :
          (cardinalProductFrame A (J.localize Z)).IsPointwiseStrictUpperBound
            s.seq p := fun beta =>
        (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
          (J.localize Z) hJZ (hp beta)
      exact False.elim
        (contradictScale Z hZProper p hpZ tZ)
    · exact Or.inr (Or.inl ⟨{
        seq := s.seq
        increasing := s.increasing
        cofinal := hCofinal }⟩)
    · obtain ⟨Y, hYProper, hXProper, ⟨p, hpY⟩, hCofinalX⟩ := hSplit
      let X : CardinalIndex A -> Prop := fun k => Not (Y k)
      have hJX : Ideal.Le J (J.localize X) := J.le_localize X
      have hJY : Ideal.Le J (J.localize Y) := J.le_localize Y
      have hDirectedY :
          (cardinalProductFrame A (J.localize Y)).PointwiseStrictDirectedBelow
            theta := by
        have hRaw :=
          ReducedProductFrame.PointwiseStrictDirectedBelow.withLargerIdeal
            hDirected (J.localize Y) hJY
        simpa only [ReducedProductFrame.withIdeal, cardinalProductFrame] using hRaw
      have hExactY := hExactLocalized Y hYProper
      rcases pointwiseStrictDirectedBelow_succ_or_scale_or_localizedScale
          hThetaRegular hDirectedY hExactY with hSuccY | hScaleY | hNested
      · right
        right
        refine ⟨X, Y, ?_, hXProper, hYProper, ?_, hSuccY⟩
        · intro k
          by_cases hk : Y k
          · exact Or.inr hk
          · exact Or.inl hk
        · exact ⟨{
            seq := s.seq
            increasing := by
              intro alpha beta hab
              have hRaw :=
                (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
                  (J.localize X) hJX (s.increasing hab)
              simpa only [ReducedProductFrame.withIdeal, cardinalProductFrame] using hRaw
            cofinal := hCofinalX }⟩
      · obtain ⟨tY⟩ := hScaleY
        exact False.elim
          (contradictScale Y hYProper p hpY tY)
      · obtain ⟨W, hWProper, ⟨tW⟩⟩ := hNested
        let ZW : CardinalIndex A -> Prop := fun k => Y k /\ W k
        have hEq : (J.localize Y).localize W = J.localize ZW := by
          exact J.localize_localize Y W
        rw [hEq] at hWProper tW
        have hYK : Ideal.Le (J.localize Y) (J.localize ZW) := by
          have hRaw := (J.localize Y).le_localize W
          rwa [hEq] at hRaw
        have hpK :
            (cardinalProductFrame A (J.localize ZW)).IsPointwiseStrictUpperBound
            s.seq p := fun beta =>
          (cardinalProductFrame A (J.localize Y)).eventuallyPointwiseLt_withLargerIdeal
            (J.localize ZW) hYK (hpY beta)
        exact False.elim
          (contradictScale ZW hWProper p hpK tW)

/-! Pushforward/source-cardinality form of Corollary 24.12.  This is the
version suited to Theorem 24.16: the powerset bound is imposed on the source
of the coordinate map, even when the ambient cardinal set is larger. -/
theorem pointwiseStrictCorollary2412_of_pushforward_exactUpperBounds
    {I : Type (u + 1)} {A : CardSet.{u}} {J : Ideal I}
    {c : I -> CardinalIndex A} {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hPower : Cardinal.mk (I -> Prop) <= Cardinal.lift.{u + 1} theta)
    (hDirected :
      (cardinalProductFrame A (J.pushforward c)).PointwiseStrictDirectedBelow
        theta)
    (hExact :
      CardinalProductClosedExactUpperBoundPrinciple A (J.pushforward c) theta)
    (hExactLocalized : forall X : CardinalIndex A -> Prop,
      ((J.pushforward c).localize X).IsProper ->
      CardinalProductClosedExactUpperBoundPrinciple
        A ((J.pushforward c).localize X) theta)
    (d0 : ProductElement (cardinalProductFrame A (J.pushforward c))) :
    (cardinalProductFrame A (J.pushforward c)).PointwiseStrictDirectedBelow
        (Order.succ theta) \/
      Nonempty (PointwiseStrictScale
        (cardinalProductFrame A (J.pushforward c))
        (cardinalScaleLength theta)) \/
      exists X Y : CardinalIndex A -> Prop,
        (forall k, X k \/ Y k) /\
        ((J.pushforward c).localize X).IsProper /\
        ((J.pushforward c).localize Y).IsProper /\
        Nonempty (PointwiseStrictScale
          (cardinalProductFrame A ((J.pushforward c).localize X))
          (cardinalScaleLength theta)) /\
        ReducedProductFrame.PointwiseStrictDirectedBelow
          (cardinalProductFrame A ((J.pushforward c).localize Y))
          (Order.succ theta) := by
  obtain ⟨d, hd⟩ :=
    exists_pushforwardLocalizedScaleAbsorbingFamily_of_mk_predicates_le
      hThetaRegular.aleph0_le hPower d0
  exact pointwiseStrictCorollary2412_of_exactUpperBounds_of_absorbingFamily
    hThetaRegular hDirected hExact hExactLocalized d hd

/-! Cardinal-bound form of Corollary 24.12.  Its enumeration hypothesis is
the cardinality of the full predicate type, i.e. the powerset of the product
index.  The previous theorem constructs the absorbing family internally. -/
theorem pointwiseStrictCorollary2412_of_exactUpperBounds_of_mk_predicates_le
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hPower : Cardinal.mk (CardinalIndex A -> Prop) <=
      Cardinal.lift.{u + 1} theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta)
    (hExact : CardinalProductClosedExactUpperBoundPrinciple A J theta)
    (hExactLocalized : forall X : CardinalIndex A -> Prop,
      (J.localize X).IsProper ->
      CardinalProductClosedExactUpperBoundPrinciple A (J.localize X) theta)
    (d0 : ProductElement (cardinalProductFrame A J)) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta) \/
      Nonempty (PointwiseStrictScale
        (cardinalProductFrame A J) (cardinalScaleLength theta)) \/
      exists X Y : CardinalIndex A -> Prop,
        (forall k, X k \/ Y k) /\
        (J.localize X).IsProper /\
        (J.localize Y).IsProper /\
        Nonempty (PointwiseStrictScale
          (cardinalProductFrame A (J.localize X))
          (cardinalScaleLength theta)) /\
        (cardinalProductFrame A (J.localize Y)).PointwiseStrictDirectedBelow
          (Order.succ theta) := by
  obtain ⟨d, hd⟩ := exists_localizedScaleAbsorbingFamily_of_mk_predicates_le
    hThetaRegular.aleph0_le hPower d0
  exact pointwiseStrictCorollary2412_of_exactUpperBounds_of_absorbingFamily
    hThetaRegular hDirected hExact hExactLocalized d hd

/-! If both global and positive-localized scales are excluded, the preceding
trichotomy leaves canonical-size directedness.  This is the form used when
Corollary 24.12 is applied contrapositively. -/
theorem pointwiseStrictDirectedAt_of_no_scale
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      theta)
    (hExact : CardinalProductClosedExactUpperBoundPrinciple A J theta)
    (hNoScale : Not (Nonempty (PointwiseStrictScale
      (cardinalProductFrame A J) (cardinalScaleLength theta))))
    (hNoLocalizedScale : forall X : CardinalIndex A -> Prop,
      (J.localize X).IsProper ->
      Not (Nonempty (PointwiseStrictScale
        (cardinalProductFrame A (J.localize X))
        (cardinalScaleLength theta)))) :
    CardinalProductPointwiseStrictDirectedAt A J theta := by
  rcases pointwiseStrictDirectedAt_or_scale_or_localizedScale
      hThetaRegular hDirected hExact with hAt | hScale | hLocalized
  · exact hAt
  · exact False.elim (hNoScale hScale)
  · obtain ⟨X, hProper, hScale⟩ := hLocalized
    exact False.elim (hNoLocalizedScale X hProper hScale)

/-! A cofinal family of regular cardinal length can be strictified whenever
the reduced product has pointwise-strict upper bounds for every shorter
family.  At stage `alpha`, first bound all earlier recursive values, then
bound that result together with the `alpha`-th member of the given cofinal
family.  Well-founded recursion supplies the resulting source-level strict
scale. -/
theorem pointwiseStrictScale_of_directedBelow_of_cofinalFamily
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      theta)
    (d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J))
    (hCofinal : (cardinalProductFrame A J).IsCofinalFamily d) :
    Nonempty (PointwiseStrictScale
      (cardinalProductFrame A J) (cardinalScaleLength theta)) := by
  obtain ⟨s⟩ := pointwiseStrictDominatingSequence_of_directedBelow
    hThetaRegular hDirected d
  refine ⟨{
    seq := s.seq
    increasing := s.increasing
    cofinal := ?_ }⟩
  intro g
  obtain ⟨alpha, hga⟩ := hCofinal g
  refine ⟨alpha,
    (cardinalProductFrame A J).eventuallyLe_trans hga ?_⟩
  exact J.eventually_mono (s.dominates alpha) (fun _ hi => hi.1)

theorem cardinalScaleLength_le_mk_of_cofinalFamily
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegular : Cardinal.IsRegular theta)
    (s : Scale
      (cardinalProductFrame A J)
      (cardinalScaleLength theta))
    {ι : Type u}
    (d : ι -> ProductElement (cardinalProductFrame A J))
    (hCofinal :
      (cardinalProductFrame A J).IsCofinalFamily d) :
    theta <= Cardinal.mk ι := by
  classical
  by_contra hNotLe
  have hShort : Cardinal.mk ι < theta := lt_of_not_ge hNotLe
  let alpha : ι -> theta.ord.ToType :=
    fun i => Classical.choose (s.cofinal (d i))
  have hAlpha : forall i,
      (cardinalProductFrame A J).eventuallyLe
        (d i) (s.seq (alpha i)) :=
    fun i => Classical.choose_spec (s.cofinal (d i))
  let f : ι -> Ordinal.{u} :=
    fun i => Ordinal.typein
      (fun a b : theta.ord.ToType => a < b)
      (alpha i)
  have hf : forall i, f i < theta.ord := by
    intro i
    simpa only [f] using Ordinal.typein_lt_self (alpha i)
  have hBound : (iSup fun i => f i + 1) < theta.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof
      (by rwa [hRegular.cof_ord]) hf
  let beta : theta.ord.ToType :=
    Ordinal.ToType.mk ⟨iSup fun i => f i + 1, hBound⟩
  have hAlphaBeta : forall i, alpha i < beta := by
    intro i
    change alpha i < Ordinal.ToType.mk ⟨iSup fun i => f i + 1, hBound⟩
    rw [← (Ordinal.ToType.mk).apply_symm_apply (alpha i)]
    apply (Ordinal.ToType.mk).strictMono
    change f i < iSup fun i => f i + 1
    exact Ordinal.lt_iSup_add_one f i
  obtain ⟨i, hBetaLe⟩ := hCofinal (s.seq beta)
  exact (s.not_eventuallyLe_of_lt (by
    simpa only [cardinalScaleLength] using hAlphaBeta i))
    ((cardinalProductFrame A J).eventuallyLe_trans hBetaLe (hAlpha i))

/-! A regular pointwise-strict family remains cardinal-minimal below any of
its closed exact upper bounds.  This is the counting obstruction used in
Jech 24.19: a purported shorter family cofinal below the exact bound assigns
one stage to each of its members; regularity puts all assigned stages below a
single later stage, contradicting strict increase. -/
theorem cardinalScaleLength_hasTrueCofinality
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegular : Cardinal.IsRegular theta)
    (s : Scale
      (cardinalProductFrame A J)
      (cardinalScaleLength theta)) :
    HasTrueCofinality
      (cardinalProductFrame A J)
      (cardinalScaleLength theta) := by
  constructor
  · exact s.hasScaleWitness
  · intro ι d hCofinal
    simpa only [mk_cardinalScaleLength_level] using
       cardinalScaleLength_le_mk_of_cofinalFamily
         hRegular s d hCofinal

/-! A quotient scale at a regular canonical cardinal length has true
cofinality for the raw canonical product. The proof first selects raw
representatives, then invokes the existing regularity proof of minimality;
it does not infer a quotient scale from `Order.cof`. -/
theorem cardinalScaleLength_hasTrueCofinality_of_quotientScale
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegular : Cardinal.IsRegular theta)
    (s : CardinalProductQuotientScale A J (cardinalScaleLength theta)) :
    HasTrueCofinality
      (cardinalProductFrame A J)
      (cardinalScaleLength theta) := by
  obtain ⟨t⟩ := s.exists_scale
  exact cardinalScaleLength_hasTrueCofinality hRegular t

/-! A supplied quotient scale of regular canonical length computes the order
cofinality of the quotient exactly. The chain is already part of the input;
this theorem does not extract a well-ordered chain from an arbitrary
cofinal subset. -/
theorem cardinalProductQuotient_cof_eq_lift_of_regular_quotientScale
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegular : Cardinal.IsRegular theta)
    (hUltra : J.IsUltrafilterDual)
    (s : CardinalProductQuotientScale A J (cardinalScaleLength theta)) :
    Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta := by
  classical
  letI : LinearOrder (CardinalProductQuotient A J) :=
    { cardinalProductQuotientPartialOrder with
      le_total := cardinalProductQuotient_le_total_of_isUltrafilterDual hUltra
      toDecidableLE := Classical.decRel _ }
  letI : LinearOrder (cardinalScaleLength theta).Level := by
    change LinearOrder theta.ord.ToType
    infer_instance
  have hCof := Order.lift_cof_congr_of_strictMono
    (f := s.seq)
    (fun _ _ hlt => s.increasing hlt)
    (by
      intro q
      obtain ⟨alpha, hAlpha⟩ := s.cofinal q
      refine ⟨s.seq alpha, ?_, hAlpha⟩
      exact ⟨alpha, rfl⟩)
  calc
    Order.cof (CardinalProductQuotient A J) =
        Cardinal.lift.{u} (Order.cof (CardinalProductQuotient A J)) :=
      (Cardinal.lift_id'.{u, u + 1} _).symm
    _ = Cardinal.lift.{u + 1}
        (Order.cof (cardinalScaleLength theta).Level) := hCof.symm
    _ = Cardinal.lift.{u + 1} theta := by
      change Cardinal.lift.{u + 1} (Order.cof theta.ord.ToType) =
        Cardinal.lift.{u + 1} theta
      rw [Ordinal.cof_toType, hRegular.cof_ord]

/-! In a quotient ordered by an ultrafilter-dual ideal, every family whose
index cardinal is strictly below the order cofinality has a common strict
upper bound. This is an order-theoretic consequence of smallness; it does not
well-order or monotonize a cofinal family. -/
theorem cardinalProductQuotient_exists_strict_upper_bound_of_mk_lt_cof
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual)
    {ι : Type (u + 1)}
    (d : ι -> CardinalProductQuotient A J)
    (hSmall : Cardinal.mk ι < Order.cof (CardinalProductQuotient A J)) :
    exists q : CardinalProductQuotient A J, forall i, d i < q := by
  classical
  letI : LinearOrder (CardinalProductQuotient A J) :=
    { cardinalProductQuotientPartialOrder with
      le_total := cardinalProductQuotient_le_total_of_isUltrafilterDual hUltra
      toDecidableLE := Classical.decRel _ }
  have hNotCofinal : Not (IsCofinal (Set.range d)) := by
    intro hCofinal
    have hCofLe : Order.cof (CardinalProductQuotient A J) <=
        Cardinal.mk (Set.range d) :=
      Order.cof_le hCofinal
    exact (not_le_of_gt hSmall) (hCofLe.trans Cardinal.mk_range_le)
  obtain ⟨q, hq⟩ := not_isCofinal_iff.mp hNotCofinal
  refine ⟨q, ?_⟩
  intro i
  exact hq (d i) ⟨i, rfl⟩

/-! A cofinal quotient family indexed by the canonical lower-universe length
provides the upper half of the quotient-cofinality equality. Hence an explicit
lower bound by the same lifted cardinal determines the cofinality exactly.
This is still a statement about a supplied low-universe family. -/
theorem cardinalProductQuotient_cof_eq_lift_of_cofinalFamily_of_lift_le
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (d : (cardinalScaleLength theta).Level -> CardinalProductQuotient A J)
    (hCofinal : cardinalProductQuotientIsCofinalFamily d)
    (hCofLower : Cardinal.lift.{u + 1} theta <=
      Order.cof (CardinalProductQuotient A J)) :
    Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta := by
  apply le_antisymm
  · have hSetCofinal : IsCofinal (Set.range d) := by
      intro q
      obtain ⟨alpha, hAlpha⟩ := hCofinal q
      exact ⟨d alpha, ⟨alpha, rfl⟩, hAlpha⟩
    calc
      Order.cof (CardinalProductQuotient A J) <= Cardinal.mk (Set.range d) :=
        Order.cof_le hSetCofinal
      _ <= Cardinal.lift.{u + 1}
          (Cardinal.mk (cardinalScaleLength theta).Level) := by
        calc
          Cardinal.mk (Set.range d) =
              Cardinal.lift.{u, u + 1} (Cardinal.mk (Set.range d)) :=
            (Cardinal.lift_id'.{u, u + 1} _).symm
          _ <= Cardinal.lift.{u + 1}
              (Cardinal.mk (cardinalScaleLength theta).Level) :=
            Cardinal.mk_range_le_lift (f := d)
      _ = Cardinal.lift.{u + 1} theta := by
        rw [mk_cardinalScaleLength_level]
  · exact hCofLower

/-! An explicit cofinal family indexed by the literal lower-universe canonical
length can be recursively strictified into a quotient scale when the quotient
cofinality is exactly the lifted represented cardinal. The family and equality
are both genuine inputs: this theorem does not lower `Order.cof` from the
quotient universe or obtain either datum from the Zorn ideal. -/
theorem cardinalProductQuotientScale_of_cofinalFamily_of_cof_eq_lift
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    {theta : Cardinal.{u}}
    (d : (cardinalScaleLength theta).Level -> CardinalProductQuotient A J)
    (hCofinal : cardinalProductQuotientIsCofinalFamily d)
    (hCofEq : Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta) :
    Nonempty (CardinalProductQuotientScale A J (cardinalScaleLength theta)) := by
  classical
  letI : LinearOrder (cardinalScaleLength theta).Level := by
    change LinearOrder theta.ord.ToType
    infer_instance
  letI : WellFoundedLT (cardinalScaleLength theta).Level :=
    ⟨(cardinalScaleLength theta).isWellOrder.wf⟩
  let Q := CardinalProductQuotient A J
  letI : LinearOrder Q :=
    { cardinalProductQuotientPartialOrder with
      le_total := cardinalProductQuotient_le_total_of_isUltrafilterDual hUltra
      toDecidableLE := Classical.decRel _ }
  have hStep : forall (alpha : (cardinalScaleLength theta).Level)
      (previous : forall beta, beta < alpha -> Q),
      exists q : Q, d alpha < q /\
        forall beta hbeta, previous beta hbeta < q := by
    intro alpha previous
    let e : ULift.{u + 1} {beta : (cardinalScaleLength theta).Level // beta < alpha} -> Q :=
      fun beta => previous beta.down.1 beta.down.2
    have hSmall : Cardinal.mk
        (ULift.{u + 1} {beta : (cardinalScaleLength theta).Level // beta < alpha}) <
        Order.cof Q := by
      calc
        Cardinal.mk
            (ULift.{u + 1} {beta : (cardinalScaleLength theta).Level // beta < alpha}) =
            Cardinal.lift.{u + 1}
              (Cardinal.mk {beta : (cardinalScaleLength theta).Level // beta < alpha}) := by
          simp
        _ < Cardinal.lift.{u + 1} theta := by
          apply Cardinal.lift_lt.mpr
          change Cardinal.mk {beta : theta.ord.ToType // beta < alpha} < theta
          have hOrderType :
              (Cardinal.mk (cardinalScaleLength theta).Level).ord =
                Ordinal.type (fun x y : (cardinalScaleLength theta).Level => x < y) := by
            rw [mk_cardinalScaleLength_level]
            exact (Ordinal.type_toType theta.ord).symm
          simpa using Cardinal.mk_Iio_lt alpha hOrderType
        _ = Order.cof Q := hCofEq.symm
    obtain ⟨b, hb⟩ :=
      cardinalProductQuotient_exists_strict_upper_bound_of_mk_lt_cof
        hUltra e hSmall
    obtain ⟨c, hbc, hdc⟩ :=
      cardinalProductQuotient_exists_common_upper_bound b (d alpha)
    obtain ⟨q, hcq⟩ := cardinalProductQuotient_exists_lt_of_regulars
      hRegulars hUltra.isProper c
    refine ⟨q, lt_of_le_of_lt hdc hcq, ?_⟩
    intro beta hbeta
    exact (lt_of_lt_of_le (hb (ULift.up ⟨beta, hbeta⟩)) hbc).trans hcq
  let seq : (cardinalScaleLength theta).Level -> Q :=
    WellFounded.fix (cardinalScaleLength theta).isWellOrder.wf
      (fun alpha previous => Classical.choose (hStep alpha previous))
  have hSeqEq : forall alpha,
      seq alpha = Classical.choose (hStep alpha (fun beta hbeta => seq beta)) := by
    intro alpha
    exact WellFounded.fix_eq _ _ alpha
  refine ⟨{
    seq := seq
    increasing := ?_
    cofinal := ?_ }⟩
  · intro alpha beta hlt
    rw [hSeqEq beta]
    exact (Classical.choose_spec (hStep beta (fun gamma hgamma => seq gamma))).2
      alpha hlt
  · intro q
    obtain ⟨alpha, hqa⟩ := hCofinal q
    refine ⟨alpha, hqa.trans ?_⟩
    rw [hSeqEq alpha]
    exact (Classical.choose_spec (hStep alpha (fun beta hbeta => seq beta))).1.le

/-! If the quotient cofinality is exactly the lift of a lower-universe
cardinal, a cofinal family can be reindexed by the literal canonical length.
This uses a least cofinal subset and a cardinal equivalence; it does not show
that an arbitrary quotient cofinality has this lifted form. -/
theorem cardinalProductQuotient_exists_cofinalFamily_of_cof_eq_lift
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hCofEq : Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta) :
    exists d : (cardinalScaleLength theta).Level -> CardinalProductQuotient A J,
      cardinalProductQuotientIsCofinalFamily d := by
  classical
  let Q := CardinalProductQuotient A J
  obtain ⟨s, hSetCofinal, hCard⟩ := Order.exists_cof_eq Q
  have hEquiv : Nonempty (s ≃ (cardinalScaleLength theta).Level) := by
    apply Cardinal.lift_mk_eq'.mp
    calc
      Cardinal.lift.{u} (Cardinal.mk s) = Cardinal.mk s :=
        Cardinal.lift_id'.{u, u + 1} _
      _ = Cardinal.lift.{u + 1} theta := hCard.trans hCofEq
      _ = Cardinal.lift.{u + 1}
          (Cardinal.mk (cardinalScaleLength theta).Level) := by
        rw [mk_cardinalScaleLength_level]
  let e : s ≃ (cardinalScaleLength theta).Level := hEquiv.some
  refine ⟨fun alpha => (e.symm alpha).1, ?_⟩
  intro q
  obtain ⟨r, hr, hqr⟩ := hSetCofinal q
  refine ⟨e ⟨r, hr⟩, ?_⟩
  simpa [e] using hqr

/-! Exact lifted quotient cofinality supplies the low-universe cofinal family
needed by the recursive scale construction. The equality is an explicit input;
this theorem does not prove it for a nonprincipal ideal. -/
theorem cardinalProductQuotientScale_of_cof_eq_lift
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    {theta : Cardinal.{u}}
    (hCofEq : Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta) :
    Nonempty (CardinalProductQuotientScale A J (cardinalScaleLength theta)) := by
  obtain ⟨d, hCofinal⟩ :=
    cardinalProductQuotient_exists_cofinalFamily_of_cof_eq_lift hCofEq
  exact cardinalProductQuotientScale_of_cofinalFamily_of_cof_eq_lift
    hRegulars hUltra d hCofinal hCofEq

/-! Exact lifted cofinality of an ultrafilter quotient is represented by a
regular cardinal once it is infinite. The proof strictifies a cofinal family,
then restricts the resulting chain to a least cofinal subset of the ordinal
length. A singular represented cardinal would give a strictly smaller quotient
cofinal family, contradicting the exact equality. -/
theorem cardinalProductQuotient_isRegular_of_cof_eq_lift
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    {theta : Cardinal.{u}}
    (hAleph0 : Cardinal.aleph0 <= theta)
    (hCofEq : Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta) :
    Cardinal.IsRegular theta := by
  apply Cardinal.IsRegular.of_not_isSingular hAleph0
  intro hSingular
  obtain ⟨qScale⟩ := cardinalProductQuotientScale_of_cof_eq_lift
    hRegulars hUltra hCofEq
  let Q := CardinalProductQuotient A J
  obtain ⟨s, hSetCofinal, hCard⟩ := Order.exists_cof_eq theta.ord.ToType
  let d : s -> Q := fun alpha => qScale.seq alpha.1
  have hDCofinal : cardinalProductQuotientIsCofinalFamily d := by
    intro q
    obtain ⟨alpha, hAlpha⟩ := qScale.cofinal q
    obtain ⟨beta, hBeta, hAlphaBeta⟩ := hSetCofinal alpha
    refine ⟨⟨beta, hBeta⟩, hAlpha.trans ?_⟩
    by_cases hEq : alpha = beta
    · subst beta
      exact le_rfl
    · exact (qScale.increasing (lt_of_le_of_ne hAlphaBeta hEq)).le
  have hSetDCofinal : IsCofinal (Set.range d) := by
    intro q
    obtain ⟨alpha, hAlpha⟩ := hDCofinal q
    exact ⟨d alpha, ⟨alpha, rfl⟩, hAlpha⟩
  have hStrict : Order.cof Q < Cardinal.lift.{u + 1} theta := by
    calc
      Order.cof Q <= Cardinal.mk (Set.range d) :=
        Order.cof_le hSetDCofinal
      _ = Cardinal.lift.{u, u + 1} (Cardinal.mk (Set.range d)) :=
        (Cardinal.lift_id'.{u, u + 1} _).symm
      _ <= Cardinal.lift.{u + 1} (Cardinal.mk s) :=
        Cardinal.mk_range_le_lift (f := d)
      _ = Cardinal.lift.{u + 1} (theta.ord.cof) := by
        rw [hCard, Ordinal.cof_toType]
      _ < Cardinal.lift.{u + 1} theta :=
        Cardinal.lift_lt.mpr hSingular.cof_ord_lt
  simp only [Q, hCofEq] at hStrict
  exact (lt_irrefl _) hStrict

/-! A small canonical index removes the remaining universe obstruction in a
concrete quotient-cofinality lower bound.  If that lower-bound cardinal is
singular, the represented quotient cofinality is a strictly larger regular
cardinal and gives a genuine canonical true-cofinality scale. -/
theorem cardinalProductFrame_exists_trueCofinality_gt_of_small_cardinalIndex
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    {lambda : Cardinal.{u}}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    (hSmall : Small.{u} (CardinalIndex A))
    (hLambdaAleph0 : Cardinal.aleph0 <= lambda)
    (hLambdaNotRegular : Not (Cardinal.IsRegular lambda))
    (hCofLower : Cardinal.lift.{u + 1} lambda <=
      Order.cof (CardinalProductQuotient A J)) :
    exists theta : Cardinal.{u},
      Cardinal.IsRegular theta /\
        HasTrueCofinality
          (cardinalProductFrame A J)
          (cardinalScaleLength theta) /\
        lambda < theta := by
  letI : Small.{u} (CardinalIndex A) := hSmall
  obtain ⟨theta, hCofEq⟩ :=
    cardinalProductQuotient_exists_cof_eq_lift_of_small_cardinalIndex
      (A := A) (J := J)
  have hThetaLower : lambda <= theta := by
    apply Cardinal.lift_le.mp
    calc
      Cardinal.lift.{u + 1} lambda <=
          Order.cof (CardinalProductQuotient A J) := hCofLower
      _ = Cardinal.lift.{u + 1} theta := hCofEq
  have hThetaAleph0 : Cardinal.aleph0 <= theta :=
    hLambdaAleph0.trans hThetaLower
  have hRegular : Cardinal.IsRegular theta :=
    cardinalProductQuotient_isRegular_of_cof_eq_lift
      hRegulars hUltra hThetaAleph0 hCofEq
  have hTcf : HasTrueCofinality
      (cardinalProductFrame A J)
      (cardinalScaleLength theta) :=
    cardinalScaleLength_hasTrueCofinality_of_quotientScale hRegular
      (cardinalProductQuotientScale_of_cof_eq_lift
        hRegulars hUltra hCofEq).some
  have hThetaGt : lambda < theta := by
    have hNe : Not (lambda = theta) := by
      intro hEq
      apply hLambdaNotRegular
      rw [hEq]
      exact hRegular
    exact lt_of_le_of_ne hThetaLower hNe
  exact ⟨theta, hRegular, hTcf, hThetaGt⟩

/-! For a small canonical index, any ultrafilter quotient whose order
cofinality is uncountable has a genuine represented regular true cofinality.
Smallness gives an exact lifted cardinal for the quotient cofinality, and the
strict lower bound makes that represented cardinal infinite. -/
theorem cardinalProductFrame_exists_trueCofinality_of_small_cardinalIndex_of_aleph0_lt_cof
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    (hSmall : Small.{u} (CardinalIndex A))
    (hCofAleph0 : Cardinal.aleph0 <
      Order.cof (CardinalProductQuotient A J)) :
    exists theta : Cardinal.{u},
      Cardinal.IsRegular theta /\
        HasTrueCofinality
          (cardinalProductFrame A J)
          (cardinalScaleLength theta) /\
        Cardinal.aleph0 < theta := by
  letI : Small.{u} (CardinalIndex A) := hSmall
  obtain ⟨theta, hCofEq⟩ :=
    cardinalProductQuotient_exists_cof_eq_lift_of_small_cardinalIndex
      (A := A) (J := J)
  have hThetaAleph0 : Cardinal.aleph0 <= theta := by
    apply Cardinal.lift_le.mp
    calc
      Cardinal.lift.{u + 1} Cardinal.aleph0 = Cardinal.aleph0 := by
        rw [Cardinal.lift_aleph0]
      _ <= Order.cof (CardinalProductQuotient A J) := hCofAleph0.le
      _ = Cardinal.lift.{u + 1} theta := hCofEq
  have hRegular : Cardinal.IsRegular theta :=
    cardinalProductQuotient_isRegular_of_cof_eq_lift
      hRegulars hUltra hThetaAleph0 hCofEq
  obtain ⟨s⟩ := cardinalProductQuotientScale_of_cof_eq_lift
    hRegulars hUltra hCofEq
  exact ⟨theta, hRegular,
    cardinalScaleLength_hasTrueCofinality_of_quotientScale hRegular s,
    Cardinal.lift_lt.mp (by
      calc
        Cardinal.lift.{u + 1} Cardinal.aleph0 = Cardinal.aleph0 := by
          rw [Cardinal.lift_aleph0]
        _ < Order.cof (CardinalProductQuotient A J) := hCofAleph0
        _ = Cardinal.lift.{u + 1} theta := hCofEq)⟩

/-! If every regular coordinate is uncountable, the diagonal quotient
obstruction supplies the uncountable quotient cofinality needed above. Thus
on a small canonical index every ultrafilter-dual product has a genuine true
cofinality scale. -/
theorem cardinalProductFrame_exists_trueCofinality_of_small_cardinalIndex_of_aleph0_lt
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta) :
    exists theta : Cardinal.{u},
      Cardinal.IsRegular theta /\
        HasTrueCofinality
          (cardinalProductFrame A J)
          (cardinalScaleLength theta) /\
        Cardinal.aleph0 < theta := by
  apply cardinalProductFrame_exists_trueCofinality_of_small_cardinalIndex_of_aleph0_lt_cof
    hRegulars hUltra hSmall
  exact cardinalProductQuotient_aleph0_lt_cof_of_regulars
    hRegulars hAleph0 hUltra.isProper

/-! The recursive quotient-scale construction with its exact-cofinality input
derived from a same-length lower bound. The low-universe cofinal family and
the lower bound remain explicit; this theorem does not obtain either from the
abstract quotient cofinality. -/
theorem cardinalProductQuotientScale_of_cofinalFamily_of_lift_le
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    {theta : Cardinal.{u}}
    (d : (cardinalScaleLength theta).Level -> CardinalProductQuotient A J)
    (hCofinal : cardinalProductQuotientIsCofinalFamily d)
    (hCofLower : Cardinal.lift.{u + 1} theta <=
      Order.cof (CardinalProductQuotient A J)) :
    Nonempty (CardinalProductQuotientScale A J (cardinalScaleLength theta)) := by
  exact cardinalProductQuotientScale_of_cofinalFamily_of_cof_eq_lift
    hRegulars hUltra d hCofinal
    (cardinalProductQuotient_cof_eq_lift_of_cofinalFamily_of_lift_le
      d hCofinal hCofLower)

/-! The preceding low-universe quotient-chain construction immediately gives
a raw scale witness after choosing representatives. It remains conditional on
the displayed cofinal family and quotient-cofinality equality. -/
theorem hasScaleWitness_of_quotientCofinalFamily_of_cof_eq_lift
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    {theta : Cardinal.{u}}
    (d : (cardinalScaleLength theta).Level -> CardinalProductQuotient A J)
    (hCofinal : cardinalProductQuotientIsCofinalFamily d)
    (hCofEq : Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta) :
    HasScaleWitness
      (cardinalProductFrame A J)
      (cardinalScaleLength theta) := by
  obtain ⟨s⟩ :=
    cardinalProductQuotientScale_of_cofinalFamily_of_cof_eq_lift
      hRegulars hUltra d hCofinal hCofEq
  exact s.exists_scale

/-! The lower-bound form of the preceding raw-scale witness constructor. -/
theorem hasScaleWitness_of_quotientCofinalFamily_of_lift_le
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    {theta : Cardinal.{u}}
    (d : (cardinalScaleLength theta).Level -> CardinalProductQuotient A J)
    (hCofinal : cardinalProductQuotientIsCofinalFamily d)
    (hCofLower : Cardinal.lift.{u + 1} theta <=
      Order.cof (CardinalProductQuotient A J)) :
    HasScaleWitness
      (cardinalProductFrame A J)
      (cardinalScaleLength theta) := by
  obtain ⟨s⟩ := cardinalProductQuotientScale_of_cofinalFamily_of_lift_le
    hRegulars hUltra d hCofinal hCofLower
  exact s.exists_scale

/-! Exact lifted quotient cofinality also yields a raw scale witness after
selecting representatives. The equality remains an explicit quotient-order
hypothesis rather than a consequence of the Zorn ideal. -/
theorem hasScaleWitness_of_quotientCof_eq_lift
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    {theta : Cardinal.{u}}
    (hCofEq : Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta) :
    HasScaleWitness
      (cardinalProductFrame A J)
      (cardinalScaleLength theta) := by
  obtain ⟨s⟩ := cardinalProductQuotientScale_of_cof_eq_lift
    hRegulars hUltra hCofEq
  exact s.exists_scale

/-! At a regular canonical length, true cofinality is exactly equivalent to
the existence of a lower-universe quotient cofinal family of that length with
the matching quotient-cofinality lower bound. The reverse implication invokes
the proved recursive construction; neither direction derives the family from
an arbitrary high-universe `Order.cof` witness. -/
theorem cardinalScaleLength_hasTrueCofinality_iff_exists_quotientCofinalFamily_of_lift_le
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    (hRegular : Cardinal.IsRegular theta) :
    HasTrueCofinality
      (cardinalProductFrame A J)
      (cardinalScaleLength theta) <->
      exists d : (cardinalScaleLength theta).Level -> CardinalProductQuotient A J,
        cardinalProductQuotientIsCofinalFamily d /\
          Cardinal.lift.{u + 1} theta <=
            Order.cof (CardinalProductQuotient A J) := by
  constructor
  · intro hTcf
    obtain ⟨s⟩ := hTcf.hasScaleWitness
    let qScale := CardinalProductQuotientScale.ofScale s
    refine ⟨qScale.seq, qScale.cofinal, ?_⟩
    exact (cardinalProductQuotient_cof_eq_lift_of_regular_quotientScale
      hRegular hUltra qScale).symm.le
  · rintro ⟨d, hCofinal, hCofLower⟩
    obtain ⟨s⟩ := cardinalProductQuotientScale_of_cofinalFamily_of_lift_le
      hRegulars hUltra d hCofinal hCofLower
    exact cardinalScaleLength_hasTrueCofinality_of_quotientScale hRegular s

/-! For a regular represented cardinal, true cofinality is exactly the
statement that the quotient order cofinality is its lifted cardinal. The
reverse implication uses a least quotient cofinal subset and the recursive
strictification theorem; it does not prove this equality for arbitrary
ultrafilter-dual ideals. -/
theorem cardinalScaleLength_hasTrueCofinality_iff_quotient_cof_eq_lift
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hUltra : J.IsUltrafilterDual)
    (hRegular : Cardinal.IsRegular theta) :
    HasTrueCofinality
      (cardinalProductFrame A J)
      (cardinalScaleLength theta) <->
      Order.cof (CardinalProductQuotient A J) =
        Cardinal.lift.{u + 1} theta := by
  constructor
  · intro hTcf
    obtain ⟨s⟩ := hTcf.hasScaleWitness
    exact cardinalProductQuotient_cof_eq_lift_of_regular_quotientScale
      hRegular hUltra (CardinalProductQuotientScale.ofScale s)
  · intro hCofEq
    obtain ⟨s⟩ := cardinalProductQuotientScale_of_cof_eq_lift
      hRegulars hUltra hCofEq
    exact cardinalScaleLength_hasTrueCofinality_of_quotientScale hRegular s

/-! A lower bound on the order cofinality of a quotient transfers directly
to the length of an already supplied regular quotient scale. This consumes the
scale; it does not create one from the order-cofinality bound. -/
theorem cardinalProductQuotient_cardinal_le_of_regular_quotientScale
    {A : CardSet.{u}}
    {kappa theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hCofLower : Cardinal.lift.{u + 1} kappa <=
      Order.cof (CardinalProductQuotient A J))
    (hRegular : Cardinal.IsRegular theta)
    (hUltra : J.IsUltrafilterDual)
    (s : CardinalProductQuotientScale A J (cardinalScaleLength theta)) :
    kappa <= theta := by
  apply Cardinal.lift_le.mp
  calc
    Cardinal.lift.{u + 1} kappa <=
        Order.cof (CardinalProductQuotient A J) := hCofLower
    _ = Cardinal.lift.{u + 1} theta :=
      cardinalProductQuotient_cof_eq_lift_of_regular_quotientScale
        hRegular hUltra s

noncomputable def singletonCardinalScaleSeq
    (theta : Cardinal.{u})
    (J : Ideal (CardinalIndex (singletonCardSet theta)))
    (alpha : theta.ord.ToType) :
    ProductElement
      (cardinalProductFrame (singletonCardSet theta) J) :=
  fun i =>
    cast
      (congrArg
        (fun c : Cardinal.{u} => c.ord.ToType)
        i.property.symm)
      alpha

@[simp] theorem singletonCardinalScaleSeq_at_index
    (theta : Cardinal.{u})
    (J : Ideal (CardinalIndex (singletonCardSet theta)))
    (alpha : theta.ord.ToType) :
    singletonCardinalScaleSeq theta J alpha
        (singletonCardinalIndex theta) = alpha :=
  rfl

/-- A proper reduced product over the singleton set `{theta}` has the
coordinatewise enumeration of `theta` as a scale of length `theta`. -/
noncomputable def singletonCardinalScale
    (theta : Cardinal.{u})
    (J : Ideal (CardinalIndex (singletonCardSet theta)))
    (hProper : J.IsProper) :
    Scale
      (cardinalProductFrame (singletonCardSet theta) J)
      (cardinalScaleLength theta) where
  seq := singletonCardinalScaleSeq theta J
  increasing := by
    intro alpha beta hAlphaBeta
    constructor
    · apply ReducedProductFrame.eventuallyLe_of_forallLe
      intro i
      rw [i.eq_singletonCardinalIndex]
      exact hAlphaBeta.le
    · apply hProper.not_eventually_of_forall_not
      intro i hBetaAlpha
      rw [i.eq_singletonCardinalIndex] at hBetaAlpha
      exact (not_le_of_gt hAlphaBeta) hBetaAlpha
  cofinal := by
    intro g
    refine ⟨g (singletonCardinalIndex theta), ?_⟩
    apply ReducedProductFrame.eventuallyLe_of_forallLe
    intro i
    rw [i.eq_singletonCardinalIndex]
    exact le_rfl

theorem singletonCardinalScale_hasTrueCofinality
    {theta : Cardinal.{u}}
    (J : Ideal (CardinalIndex (singletonCardSet theta)))
    (hProper : J.IsProper)
    (hRegular : Cardinal.IsRegular theta) :
    HasTrueCofinality
      (cardinalProductFrame (singletonCardSet theta) J)
      (cardinalScaleLength theta) :=
  cardinalScaleLength_hasTrueCofinality
    hRegular (singletonCardinalScale theta J hProper)

def cardinalIndexOfMem
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hTheta : A theta) : CardinalIndex A :=
  ⟨theta, hTheta⟩

def cardinalIndexMap
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B) :
    CardinalIndex A -> CardinalIndex B :=
  fun i => ⟨i.1, hAB i.1 i.2⟩

theorem cardinalIndexMap_injective
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B) :
    Function.Injective (cardinalIndexMap hAB) := by
  intro i j hij
  apply Subtype.ext
  have hval := congrArg (fun k : CardinalIndex B => k.1) hij
  simpa only [cardinalIndexMap] using hval

theorem cardinalIndexMap_mem_range_iff
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (k : CardinalIndex B) :
    (exists i, cardinalIndexMap hAB i = k) <-> A k.1 := by
  constructor
  · rintro ⟨i, hi⟩
    have hValue : i.1 = k.1 :=
      congrArg (fun j : CardinalIndex B => j.1) hi
    exact hValue ▸ i.2
  · intro hAk
    exact ⟨⟨k.1, hAk⟩, Subtype.ext rfl⟩

def restrictCardinalProductElement
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    {J : Ideal (CardinalIndex A)}
    (x : ProductElement
      (cardinalProductFrame B (J.pushforward (cardinalIndexMap hAB)))) :
    ProductElement (cardinalProductFrame A J) :=
  fun i => x (cardinalIndexMap hAB i)

noncomputable def extendCardinalProductElement
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    (x : ProductElement (cardinalProductFrame A J)) :
    ProductElement
      (cardinalProductFrame B (J.pushforward (cardinalIndexMap hAB))) := by
  classical
  intro i
  by_cases hAi : A i.1
  · exact x ⟨i.1, hAi⟩
  · exact Ordinal.ToType.mk ⟨0, (hRegulars i.1 i.2).ord_pos⟩

@[simp] theorem extendCardinalProductElement_at_indexMap
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    (x : ProductElement (cardinalProductFrame A J))
    (i : CardinalIndex A) :
    extendCardinalProductElement hAB hRegulars x
        (cardinalIndexMap hAB i) = x i := by
  classical
  change (if hAi : A i.1 then x ⟨i.1, hAi⟩ else
      Ordinal.ToType.mk ⟨0, (hRegulars i.1 (hAB i.1 i.2)).ord_pos⟩) = x i
  rw [dif_pos i.2]

@[simp] theorem restrict_extendCardinalProductElement
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    (x : ProductElement (cardinalProductFrame A J)) :
    restrictCardinalProductElement hAB
        (extendCardinalProductElement hAB hRegulars x) = x := by
  funext i
  exact extendCardinalProductElement_at_indexMap hAB hRegulars x i

theorem eventuallyLe_restrictCardinalProductElement_iff
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    {J : Ideal (CardinalIndex A)}
    (x y : ProductElement
      (cardinalProductFrame B (J.pushforward (cardinalIndexMap hAB)))) :
    (cardinalProductFrame B
        (J.pushforward (cardinalIndexMap hAB))).eventuallyLe x y <->
      (cardinalProductFrame A J).eventuallyLe
        (restrictCardinalProductElement hAB x)
        (restrictCardinalProductElement hAB y) :=
  Iff.rfl

theorem eventuallyLe_extendCardinalProductElement_iff
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    (x y : ProductElement (cardinalProductFrame A J)) :
    (cardinalProductFrame B
        (J.pushforward (cardinalIndexMap hAB))).eventuallyLe
          (extendCardinalProductElement hAB hRegulars x)
          (extendCardinalProductElement hAB hRegulars y) <->
      (cardinalProductFrame A J).eventuallyLe x y := by
  rw [eventuallyLe_restrictCardinalProductElement_iff]
  simp only [restrict_extendCardinalProductElement]

theorem eventuallyLt_extendCardinalProductElement_iff
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    (x y : ProductElement (cardinalProductFrame A J)) :
    (cardinalProductFrame B
        (J.pushforward (cardinalIndexMap hAB))).eventuallyLt
          (extendCardinalProductElement hAB hRegulars x)
          (extendCardinalProductElement hAB hRegulars y) <->
      (cardinalProductFrame A J).eventuallyLt x y := by
  unfold ReducedProductFrame.eventuallyLt
  rw [eventuallyLe_extendCardinalProductElement_iff,
    eventuallyLe_extendCardinalProductElement_iff]

noncomputable def extendCardinalScale
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{u}}
    (s : Scale (cardinalProductFrame A J) L) :
    Scale
      (cardinalProductFrame B (J.pushforward (cardinalIndexMap hAB))) L where
  seq := fun alpha =>
    extendCardinalProductElement hAB hRegulars (s.seq alpha)
  increasing := by
    intro alpha beta hAlphaBeta
    exact (eventuallyLt_extendCardinalProductElement_iff
      hAB hRegulars (s.seq alpha) (s.seq beta)).mpr
        (s.increasing hAlphaBeta)
  cofinal := by
    intro g
    obtain ⟨alpha, hAlpha⟩ :=
      s.cofinal (restrictCardinalProductElement hAB g)
    refine ⟨alpha, ?_⟩
    rw [eventuallyLe_restrictCardinalProductElement_iff]
    simpa only [restrict_extendCardinalProductElement] using hAlpha

theorem extendCardinalScale_hasTrueCofinality
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    (s : Scale
      (cardinalProductFrame A J)
      (cardinalScaleLength theta)) :
    HasTrueCofinality
      (cardinalProductFrame B (J.pushforward (cardinalIndexMap hAB)))
      (cardinalScaleLength theta) :=
  cardinalScaleLength_hasTrueCofinality hRegular
    (extendCardinalScale hAB hRegulars s)

noncomputable def restrictCardinalScale
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{u}}
    (s : Scale
      (cardinalProductFrame B (J.pushforward (cardinalIndexMap hAB))) L) :
    Scale (cardinalProductFrame A J) L where
  seq := fun alpha =>
    restrictCardinalProductElement hAB (s.seq alpha)
  increasing := by
    intro alpha beta hAlphaBeta
    unfold ReducedProductFrame.eventuallyLt
    constructor
    · exact (eventuallyLe_restrictCardinalProductElement_iff
        hAB (s.seq alpha) (s.seq beta)).mp
        (s.increasing hAlphaBeta).left
    · intro hBetaAlpha
      exact (s.increasing hAlphaBeta).right
        ((eventuallyLe_restrictCardinalProductElement_iff
          hAB (s.seq beta) (s.seq alpha)).mpr hBetaAlpha)
  cofinal := by
    intro g
    obtain ⟨alpha, hAlpha⟩ := s.cofinal
      (extendCardinalProductElement hAB hRegulars g)
    refine ⟨alpha, ?_⟩
    have hRestricted :=
      (eventuallyLe_restrictCardinalProductElement_iff
        hAB (extendCardinalProductElement hAB hRegulars g) (s.seq alpha)).mp
        hAlpha
    simpa only [restrict_extendCardinalProductElement] using hRestricted

theorem restrictCardinalScale_hasTrueCofinality
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{u}}
    (hTcf : HasTrueCofinality
      (cardinalProductFrame B (J.pushforward (cardinalIndexMap hAB))) L) :
    HasTrueCofinality (cardinalProductFrame A J) L := by
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  constructor
  · exact ⟨restrictCardinalScale hAB hRegulars s⟩
  · intro gamma d hCofinal
    apply hTcf.cardinal_le_of_cofinalFamily
      (fun i => extendCardinalProductElement hAB hRegulars (d i))
    intro g
    obtain ⟨alpha, hAlpha⟩ := hCofinal
      (restrictCardinalProductElement hAB g)
    refine ⟨alpha, ?_⟩
    have hRange :
        (J.pushforward (cardinalIndexMap hAB)).Eventually
          (fun k => exists i, cardinalIndexMap hAB i = k) := by
      change J.Small
        (fun i => Not (exists j, cardinalIndexMap hAB j =
          cardinalIndexMap hAB i))
      exact J.subset_small J.empty_small (by
      intro i
      exact fun hNot => hNot ⟨i, rfl⟩)
    have hGE :
        (cardinalProductFrame B
          (J.pushforward (cardinalIndexMap hAB))).eventuallyLe
          g
          (extendCardinalProductElement hAB hRegulars
            (restrictCardinalProductElement hAB g)) := by
      exact (J.pushforward (cardinalIndexMap hAB)).eventually_mono hRange (by
      intro k hk
      obtain ⟨i, rfl⟩ := hk
      simpa only [restrictCardinalProductElement,
        extendCardinalProductElement_at_indexMap]
        using (cardinalProductFrame B
          (J.pushforward (cardinalIndexMap hAB))).le_refl
          (cardinalIndexMap hAB i)
          (g (cardinalIndexMap hAB i)))
    exact (cardinalProductFrame B
      (J.pushforward (cardinalIndexMap hAB))).eventuallyLe_trans hGE
      ((eventuallyLe_extendCardinalProductElement_iff
        hAB hRegulars (restrictCardinalProductElement hAB g) (d alpha)).mpr
        hAlpha)

/-- The scale sequence that varies only at one selected coordinate. All other
coordinates are set to their least ordinal. -/
noncomputable def focusedCardinalScaleSeq
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hTheta : A theta)
    (alpha : theta.ord.ToType) :
    ProductElement
      (cardinalProductFrame A
        (Ideal.excludePoint (cardinalIndexOfMem hTheta))) := by
  classical
  intro i
  by_cases h : i = cardinalIndexOfMem hTheta
  · subst i
    exact alpha
  · exact Ordinal.ToType.mk ⟨0, (hRegulars i.1 i.2).ord_pos⟩

@[simp] theorem focusedCardinalScaleSeq_at_index
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hTheta : A theta)
    (alpha : theta.ord.ToType) :
    focusedCardinalScaleSeq hRegulars hTheta alpha
        (cardinalIndexOfMem hTheta) = alpha := by
  classical
  simp only [focusedCardinalScaleSeq, dite_true]

/-- A principal ideal focused at `theta ∈ A` realizes the coordinate order as
a scale of length `theta`. -/
noncomputable def focusedCardinalScale
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hTheta : A theta) :
    Scale
      (cardinalProductFrame A
        (Ideal.excludePoint (cardinalIndexOfMem hTheta)))
      (cardinalScaleLength theta) where
  seq := focusedCardinalScaleSeq hRegulars hTheta
  increasing := by
    intro alpha beta hAlphaBeta
    constructor
    · apply (Ideal.excludePoint_eventually_iff
        (cardinalIndexOfMem hTheta) _).mpr
      simpa only [focusedCardinalScaleSeq_at_index] using hAlphaBeta.le
    · intro hBetaAlpha
      have hAtTheta := (Ideal.excludePoint_eventually_iff
        (cardinalIndexOfMem hTheta) _).mp hBetaAlpha
      exact (not_le_of_gt hAlphaBeta) (by
        simpa only [focusedCardinalScaleSeq_at_index] using hAtTheta)
  cofinal := by
    intro g
    refine ⟨g (cardinalIndexOfMem hTheta), ?_⟩
    apply (Ideal.excludePoint_eventually_iff
      (cardinalIndexOfMem hTheta) _).mpr
    simpa only [focusedCardinalScaleSeq_at_index] using
      (cardinalProductFrame A
        (Ideal.excludePoint (cardinalIndexOfMem hTheta))).le_refl
          (cardinalIndexOfMem hTheta)
          (g (cardinalIndexOfMem hTheta))

theorem focusedCardinalScale_hasTrueCofinality
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hTheta : A theta) :
    HasTrueCofinality
      (cardinalProductFrame A
        (Ideal.excludePoint (cardinalIndexOfMem hTheta)))
      (cardinalScaleLength theta) :=
  cardinalScaleLength_hasTrueCofinality
    (hRegulars theta hTheta)
    (focusedCardinalScale hRegulars hTheta)

/-- A product modulo the principal ideal focused at `i0` has true cofinality
`theta` exactly when `theta` is the cardinal at the focused coordinate. -/
theorem cardinalProductFrame_excludePoint_hasTrueCofinality_iff
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (i0 : CardinalIndex A)
    {theta : Cardinal.{u}} :
    HasTrueCofinality
        (cardinalProductFrame A (Ideal.excludePoint i0))
        (cardinalScaleLength theta) <->
      theta = i0.1 := by
  constructor
  · intro hThetaTcf
    have hFocusedTcf :
        HasTrueCofinality
          (cardinalProductFrame A (Ideal.excludePoint i0))
          (cardinalScaleLength i0.1) :=
      focusedCardinalScale_hasTrueCofinality hRegulars i0.2
    simpa only [mk_cardinalScaleLength_level] using
      cardinal_mk_level_eq_of_hasTrueCofinality hThetaTcf hFocusedTcf
  · intro hTheta
    subst theta
    exact focusedCardinalScale_hasTrueCofinality hRegulars i0.2

noncomputable def cardinalProductRepresentation :
    PcfRepresentation.{u, u + 1, u, u} where
  IsProductOver := IsCardinalProductOver
  LengthRepresents L theta :=
    L = cardinalScaleLength theta /\ Cardinal.IsRegular theta
  length_cardinal := by
    intro L theta hLength
    rcases hLength with ⟨rfl, _⟩
    simp only [mk_cardinalScaleLength_level, Cardinal.lift_id]
  length_regular := by
    intro L theta hLength
    exact hLength.2

theorem cardinalProductRepresentation_mem_pcf_of_scale
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (J : Ideal (CardinalIndex A))
    (hUltra : J.IsUltrafilterDual)
    (hRegular : Cardinal.IsRegular theta)
    (s : Scale
      (cardinalProductFrame A J)
      (cardinalScaleLength theta)) :
  cardinalProductRepresentation.pcf A theta :=
  cardinalProductRepresentation.mem_pcf_of_witness
    (isCardinalProductOver_cardinalProductFrame J hUltra)
    ⟨rfl, hRegular⟩
    (cardinalScaleLength_hasTrueCofinality hRegular s)

/-! The quotient-scale form of the concrete canonical membership constructor.
It is usable once a quotient chain of the exact lower-universe canonical
length has been constructed; it does not obtain that chain from quotient
cofinality alone. -/
theorem cardinalProductRepresentation_mem_pcf_of_quotientScale
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (J : Ideal (CardinalIndex A))
    (hUltra : J.IsUltrafilterDual)
    (hRegular : Cardinal.IsRegular theta)
    (s : CardinalProductQuotientScale A J (cardinalScaleLength theta)) :
    cardinalProductRepresentation.pcf A theta :=
  cardinalProductRepresentation.mem_pcf_of_witness
    (isCardinalProductOver_cardinalProductFrame J hUltra)
    ⟨rfl, hRegular⟩
    (cardinalScaleLength_hasTrueCofinality_of_quotientScale hRegular s)



/-! Exact lifted quotient cofinality for a regular cardinal gives canonical
PCF membership by constructing the corresponding quotient scale. It does not
establish the displayed cofinality equality for any Zorn-produced ideal. -/
theorem cardinalProductRepresentation_mem_pcf_of_quotient_cof_eq_lift
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hRegulars : SetOfRegulars A)
    (J : Ideal (CardinalIndex A))
    (hUltra : J.IsUltrafilterDual)
    (hRegular : Cardinal.IsRegular theta)
    (hCofEq : Order.cof (CardinalProductQuotient A J) =
      Cardinal.lift.{u + 1} theta) :
    cardinalProductRepresentation.pcf A theta := by
  obtain ⟨s⟩ := cardinalProductQuotientScale_of_cof_eq_lift
    hRegulars hUltra hCofEq
  exact cardinalProductRepresentation_mem_pcf_of_quotientScale
    J hUltra hRegular s

/-- Every regular cardinal belongs to the canonical `pcf` of its singleton
set. Unlike the general membership theorem, this result constructs the scale. -/
theorem cardinalProductRepresentation_mem_pcf_singleton
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta) :
    cardinalProductRepresentation.pcf
      (singletonCardSet theta) theta := by
  let J : Ideal (CardinalIndex (singletonCardSet theta)) :=
    Ideal.excludePoint (singletonCardinalIndex theta)
  have hUltra : J.IsUltrafilterDual :=
    Ideal.excludePoint_isUltrafilterDual (singletonCardinalIndex theta)
  exact cardinalProductRepresentation_mem_pcf_of_scale
    J hUltra hRegular (singletonCardinalScale theta J hUltra.isProper)

/-- Every member of a set of regular cardinals belongs to its canonical PCF
set, witnessed by the principal ideal focused at that member. -/
theorem cardinalProductRepresentation_mem_pcf_of_mem
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hTheta : A theta) :
    cardinalProductRepresentation.pcf A theta := by
  let iTheta : CardinalIndex A := cardinalIndexOfMem hTheta
  let J : Ideal (CardinalIndex A) := Ideal.excludePoint iTheta
  have hUltra : J.IsUltrafilterDual :=
    Ideal.excludePoint_isUltrafilterDual iTheta
  exact cardinalProductRepresentation.mem_pcf_of_witness
    (isCardinalProductOver_cardinalProductFrame J hUltra)
    ⟨rfl, hRegulars theta hTheta⟩
    (focusedCardinalScale_hasTrueCofinality hRegulars hTheta)

theorem cardinalProductRepresentation_subset_pcf
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A) :
    SubsetOf A (cardinalProductRepresentation.pcf A) := by
  intro theta hTheta
  exact cardinalProductRepresentation_mem_pcf_of_mem hRegulars hTheta

theorem cardinalProductRepresentation_mem_pcf_iff
    {A : CardSet.{u}}
    {theta : Cardinal.{u}} :
    cardinalProductRepresentation.pcf A theta <->
      Cardinal.IsRegular theta /\
        exists J : Ideal (CardinalIndex A),
          J.IsUltrafilterDual /\
            HasTrueCofinality
              (cardinalProductFrame A J)
              (cardinalScaleLength theta) := by
  constructor
  · rintro ⟨F, L, ⟨J, hUltra, rfl⟩, ⟨rfl, hRegular⟩, hTcf⟩
    exact ⟨hRegular, J, hUltra, hTcf⟩
  · rintro ⟨hRegular, J, hUltra, hTcf⟩
    exact ⟨cardinalProductFrame A J, cardinalScaleLength theta,
      ⟨J, hUltra, rfl⟩, ⟨rfl, hRegular⟩, hTcf⟩

/-! A canonical PCF value outside its generating set must be represented by
a nonprincipal ultrafilter-dual ideal.  A principal representation has true
cofinality exactly equal to its focused coordinate. -/
theorem cardinalProductRepresentation_mem_pcf_not_mem_has_nonprincipal_ideal
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta)
    (hNotMem : Not (A theta)) :
    exists J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual /\
        HasTrueCofinality
          (cardinalProductFrame A J)
          (cardinalScaleLength theta) /\
        forall i, Not (J = Ideal.excludePoint i) := by
  obtain ⟨_hRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff (A := A) (theta := theta)).mp hPcf
  refine ⟨J, hUltra, hTcf, ?_⟩
  intro i hPrincipal
  apply hNotMem
  have hFocusedTcf : HasTrueCofinality
      (cardinalProductFrame A (Ideal.excludePoint i))
      (cardinalScaleLength theta) := by
    rw [← hPrincipal]
    exact hTcf
  have hThetaEq : theta = i.1 :=
    (cardinalProductFrame_excludePoint_hasTrueCofinality_iff
      hRegulars i).mp hFocusedTcf
  rw [hThetaEq]
  exact i.2




theorem cardinalProductRepresentation_mem_pcf_iff_hasScaleWitness
    {A : CardSet.{u}}
    {theta : Cardinal.{u}} :
    cardinalProductRepresentation.pcf A theta <->
      Cardinal.IsRegular theta /\
        exists J : Ideal (CardinalIndex A),
          J.IsUltrafilterDual /\
            HasScaleWitness
              (cardinalProductFrame A J)
              (cardinalScaleLength theta) := by
  constructor
  · intro hPcf
    obtain ⟨hRegular, J, hUltra, hTcf⟩ :=
      (cardinalProductRepresentation_mem_pcf_iff (A := A) (theta := theta)).mp hPcf
    exact ⟨hRegular, J, hUltra, hTcf.hasScaleWitness⟩
  · rintro ⟨hRegular, J, hUltra, hScale⟩
    obtain ⟨s⟩ := hScale
    exact cardinalProductRepresentation_mem_pcf_of_scale
      J hUltra hRegular s



/-! The canonical scale sequence is injective: strict eventual growth rules
    out equality at two distinct ordinal indices. This gives the correct
    cross-universe cardinal bound for a canonical PCF witness. -/
theorem cardinalProductRepresentation_pcf_theta_le_productCardinal
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta) :
    exists J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual /\
      Cardinal.lift.{u + 1} theta <= Cardinal.mk
        (ProductElement (cardinalProductFrame A J)) := by
  obtain ⟨_hRegular, J, hUltra, hScale⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff_hasScaleWitness
      (A := A) (theta := theta)).mp hPcf
  obtain ⟨s⟩ := hScale
  letI : LinearOrder (cardinalScaleLength theta).Level := by
    change LinearOrder theta.ord.ToType
    infer_instance
  have hInjective : Function.Injective s.seq := by
    intro alpha beta hEq
    by_contra hNe
    have hCases : alpha < beta \/ beta < alpha := lt_or_gt_of_ne hNe
    rcases hCases with hlt | hgt
    · have hLt := s.increasing hlt
      apply hLt.right
      rw [hEq]
      exact (cardinalProductFrame A J).eventuallyLe_refl _
    · have hLt := s.increasing hgt
      apply hLt.right
      rw [hEq]
      exact (cardinalProductFrame A J).eventuallyLe_refl _
  exact ⟨J, hUltra, by
    convert (Cardinal.lift_mk_le_lift_mk_of_injective
      (α := (cardinalScaleLength theta).Level)
      (β := ProductElement (cardinalProductFrame A J)) hInjective) using 1
    · simp only [mk_cardinalScaleLength_level]
    · exact (Cardinal.lift_id'.{u, u + 1} _).symm⟩

theorem cardinalProductRepresentation_pcf_theta_le_coordinateProduct
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta) :
    exists J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual /\
      Cardinal.lift.{u + 1} theta <=
        Cardinal.prod (fun i : CardinalIndex A => i.1) := by
  obtain ⟨J, hUltra, hBound⟩ :=
    cardinalProductRepresentation_pcf_theta_le_productCardinal hPcf
  refine ⟨J, hUltra, ?_⟩
  rw [← mk_cardinalProductFrame_productElement J]
  exact hBound


/-! A coordinatewise bound on the ambient product gives a power bound for
    every canonical PCF value. The bound is stated with `Cardinal.lift`
    because the coordinate index type lives one universe above `A`. -/
theorem cardinalProductRepresentation_pcf_theta_le_power_of_coordinate_bound
    {A : CardSet.{u}}
    {theta K : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta)
    (hCoordinate : forall i : CardinalIndex A,
      Cardinal.lift.{u + 1} i.1 <= Cardinal.lift.{u + 1} K) :
    exists J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual /\
      Cardinal.lift.{u + 1} theta <=
        (Cardinal.lift.{u + 1} K) ^
          Cardinal.lift.{u} (Cardinal.mk (CardinalIndex A)) := by
  obtain ⟨J, hUltra, hProduct⟩ :=
    cardinalProductRepresentation_pcf_theta_le_coordinateProduct hPcf
  have hCoordinateRaw : forall i : CardinalIndex A, i.1 <= K := by
    intro i
    exact Cardinal.lift_le.mp (hCoordinate i)
  have hProductBound :
      Cardinal.prod (fun i : CardinalIndex A => i.1) <=
        Cardinal.prod (fun _ : CardinalIndex A => K) := by
    apply Cardinal.prod_le_prod
    intro i
    exact hCoordinateRaw i
  have hProductPower :
      Cardinal.prod (fun _ : CardinalIndex A => K) =
        (Cardinal.lift.{u + 1} K) ^
          Cardinal.lift.{u} (Cardinal.mk (CardinalIndex A)) := by
    rw [Cardinal.prod_const]
  refine ⟨J, hUltra, ?_⟩
  have hProductLift :
      Cardinal.prod (fun i : CardinalIndex A => i.1) <=
        (Cardinal.lift.{u + 1} K) ^
          Cardinal.lift.{u} (Cardinal.mk (CardinalIndex A)) := by
    exact hProductBound.trans_eq hProductPower
  exact hProduct.trans hProductLift

/-! Every canonical PCF value dominates at least one member of the underlying
regular-cardinal set. Otherwise its scale would be shorter than every
coordinate, so the coordinatewise diagonal theorem would give a strict upper
bound for the entire cofinal scale. -/
theorem cardinalProductRepresentation_mem_pcf_exists_member_le
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta) :
    exists beta, A beta /\ beta <= theta := by
  obtain ⟨_hRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := A) (theta := theta)).mp hPcf
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  by_contra hNoMember
  have hSmall : forall beta, A beta ->
      Cardinal.mk (cardinalScaleLength theta).Level < beta := by
    intro beta hBeta
    rw [mk_cardinalScaleLength_level]
    exact lt_of_not_ge (fun hBetaTheta =>
      hNoMember ⟨beta, hBeta, hBetaTheta⟩)
  obtain ⟨g, hStrict⟩ :=
    cardinalProductFrame_exists_strict_upper_bound_of_mk_lt
      hRegulars hSmall hUltra.isProper s.seq
  obtain ⟨alpha, hAlpha⟩ := s.cofinal g
  exact (hStrict alpha).right hAlpha


/-! A general cofinality obstruction: if every proper canonical product has
no cofinal family indexed by a type of cardinality at most `kappa`, then a
canonical PCF value must be strictly above `kappa`. The scale occurring in a
PCF witness is itself the forbidden cofinal family. -/
theorem cardinalProductRepresentation_mem_pcf_gt_of_no_small_cofinal_family
    {A : CardSet.{u}}
    {kappa theta : Cardinal.{u}}
    (hNoSmall : forall (J : Ideal (CardinalIndex A)), J.IsProper ->
      forall (ι : Type u) (d : ι -> ProductElement (cardinalProductFrame A J)),
        Cardinal.mk ι <= kappa ->
        Not ((cardinalProductFrame A J).IsCofinalFamily d))
    (hPcf : cardinalProductRepresentation.pcf A theta) :
    kappa < theta := by
  obtain ⟨_hRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff (A := A) (theta := theta)).mp hPcf
  by_contra hNot
  have hThetaLe : theta <= kappa := le_of_not_gt hNot
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  have hLevelLe : Cardinal.mk (cardinalScaleLength theta).Level <= kappa := by
    simpa only [mk_cardinalScaleLength_level] using hThetaLe
  exact hNoSmall J hUltra.isProper
    (cardinalScaleLength theta).Level s.seq hLevelLe s.isCofinalFamily_seq


/-! Eventual coordinate bounds constrain the cardinality of any supplied
cofinal scale. The predicate `B` may discard a small initial part of the
coordinates, provided it is eventual for the fixed proper product ideal. -/
theorem cardinalProductFrame_mk_scaleLength_gt_of_eventual_coordinate_bound
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {kappa : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    {B : CardinalIndex A -> Prop}
    {L : ScaleLength.{u}}
    (hProper : J.IsProper)
    (hScale : HasScaleWitness
      (cardinalProductFrame A J) L)
    (hEventual : J.Eventually B)
    (hCoordinate : forall i : CardinalIndex A, B i -> kappa < i.1) :
    kappa < Cardinal.mk L.Level := by
  by_contra hNot
  have hLengthLe : Cardinal.mk L.Level <= kappa := le_of_not_gt hNot
  obtain ⟨s⟩ := hScale
  have hNoCofinal : Not
      ((cardinalProductFrame A J).IsCofinalFamily s.seq) := by
    apply cardinalProductFrame_not_isCofinalFamily_of_mk_lt_of_eventually
      (A := A) (B := B) (ι := L.Level)
      hRegulars
    · intro i hi
      calc
        Cardinal.mk L.Level <= kappa := hLengthLe
        _ < i.1 := hCoordinate i hi
    · exact hProper
    · exact hEventual
  exact hNoCofinal s.isCofinalFamily_seq

/-! Eventual coordinate unboundedness already constrains every cofinal
family, without assuming that the product has a scale. -/
theorem cardinalProductFrame_cardinal_le_of_cofinalFamily_of_eventually_unbounded
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {lambda : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper)
    (hUnbounded : forall kappa : Cardinal.{u}, kappa < lambda ->
      exists B : CardinalIndex A -> Prop,
        J.Eventually B /\
          forall i : CardinalIndex A, B i -> kappa < i.1)
    {ι : Type u}
    (d : ι -> ProductElement (cardinalProductFrame A J))
    (hCofinal : (cardinalProductFrame A J).IsCofinalFamily d) :
    lambda <= Cardinal.mk ι := by
  by_contra hNot
  have hSmall : Cardinal.mk ι < lambda := lt_of_not_ge hNot
  obtain ⟨B, hEventual, hCoordinate⟩ :=
    hUnbounded (Cardinal.mk ι) hSmall
  exact (cardinalProductFrame_not_isCofinalFamily_of_mk_lt_of_eventually
    hRegulars hCoordinate hProper hEventual d) hCofinal


/-! If the coordinates are eventually unbounded below a cardinal `lambda`,
then a supplied cofinal scale has cardinality at least `lambda`. This fixes one
concrete product ideal, so it applies directly to the nonprincipal branch of a
given witness. -/
theorem cardinalProductFrame_mk_scaleLength_ge_of_eventually_unbounded
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {lambda : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    {L : ScaleLength.{u}}
    (hProper : J.IsProper)
    (hScale : HasScaleWitness
      (cardinalProductFrame A J) L)
    (hUnbounded : forall kappa : Cardinal.{u}, kappa < lambda ->
      exists B : CardinalIndex A -> Prop,
        J.Eventually B /\
          forall i : CardinalIndex A, B i -> kappa < i.1) :
    lambda <= Cardinal.mk L.Level := by
  obtain ⟨s⟩ := hScale
  exact cardinalProductFrame_cardinal_le_of_cofinalFamily_of_eventually_unbounded
    hRegulars hProper hUnbounded s.seq s.isCofinalFamily_seq

/-! The canonical cardinal-length specialization of the preceding generic
scale-cardinality bound. -/
theorem cardinalProductFrame_cardinalScaleLength_gt_of_eventual_coordinate_bound
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {kappa theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    {B : CardinalIndex A -> Prop}
    (hProper : J.IsProper)
    (hScale : HasScaleWitness
      (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hEventual : J.Eventually B)
    (hCoordinate : forall i : CardinalIndex A, B i -> kappa < i.1) :
    kappa < theta := by
  simpa only [mk_cardinalScaleLength_level] using
    cardinalProductFrame_mk_scaleLength_gt_of_eventual_coordinate_bound
      hRegulars hProper hScale hEventual hCoordinate

/-! The canonical cardinal-length specialization of eventual scale-length
unboundedness. -/
theorem cardinalProductFrame_cardinalScaleLength_ge_of_eventually_unbounded
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {lambda theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper)
    (hScale : HasScaleWitness
      (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hUnbounded : forall kappa : Cardinal.{u}, kappa < lambda ->
      exists B : CardinalIndex A -> Prop,
        J.Eventually B /\
          forall i : CardinalIndex A, B i -> kappa < i.1) :
    lambda <= theta := by
  simpa only [mk_cardinalScaleLength_level] using
    cardinalProductFrame_mk_scaleLength_ge_of_eventually_unbounded
      hRegulars hProper hScale hUnbounded

/-! If eventual coordinate unboundedness is measured below a nonregular
cardinal, then a canonical scale of regular represented length must be
strictly longer.  This is the order-theoretic upgrade of the preceding weak
scale bound; it does not construct a scale. -/
theorem cardinalProductFrame_cardinalScaleLength_gt_of_eventually_unbounded_of_not_isRegular
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {lambda theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper)
    (hScale : HasScaleWitness
      (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hUnbounded : forall kappa : Cardinal.{u}, kappa < lambda ->
      exists B : CardinalIndex A -> Prop,
        J.Eventually B /\
          forall i : CardinalIndex A, B i -> kappa < i.1)
    (hLambdaNotRegular : Not (Cardinal.IsRegular lambda))
    (hThetaRegular : Cardinal.IsRegular theta) :
    lambda < theta := by
  have hGe := cardinalProductFrame_cardinalScaleLength_ge_of_eventually_unbounded
    hRegulars hProper hScale hUnbounded
  have hNe : Not (lambda = theta) := by
    intro hEq
    apply hLambdaNotRegular
    rw [hEq]
    exact hThetaRegular
  exact lt_of_le_of_ne hGe hNe


/-! A canonical PCF value cannot be `aleph0` when every proper product ideal
admits no Nat-indexed cofinal family. The proof reindexes a hypothetical
`aleph0`-length scale by an equivalence with `Nat`, so the obstruction is a
semantic consequence of the scale interface rather than a cardinal shortcut. -/
theorem cardinalProductRepresentation_mem_pcf_gt_aleph0_of_no_nat_cofinal_family
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hNoNat : forall (J : Ideal (CardinalIndex A)), J.IsProper ->
      forall d : Nat -> ProductElement (cardinalProductFrame A J),
        Not ((cardinalProductFrame A J).IsCofinalFamily d))
    (hPcf : cardinalProductRepresentation.pcf A theta) :
    Cardinal.aleph0 < theta := by
  obtain ⟨hRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff (A := A) (theta := theta)).mp hPcf
  by_contra hNot
  have hThetaLe : theta <= Cardinal.aleph0 := le_of_not_gt hNot
  have hThetaEq : theta = Cardinal.aleph0 :=
    le_antisymm hThetaLe hRegular.aleph0_le
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  have hLevelNat :
      Cardinal.mk (cardinalScaleLength theta).Level =
        Cardinal.mk (ULift.{u} Nat) := by
    rw [mk_cardinalScaleLength_level, hThetaEq, Cardinal.mk_uLift,
      Cardinal.mk_nat, Cardinal.lift_aleph0]
  obtain ⟨e⟩ := Cardinal.eq.mp hLevelNat
  let d : Nat -> ProductElement (cardinalProductFrame A J) :=
    fun n => s.seq (e.symm (ULift.up n))
  have hCofinal :
      (cardinalProductFrame A J).IsCofinalFamily d := by
    intro g
    obtain ⟨alpha, hAlpha⟩ := s.cofinal g
    refine ⟨(e alpha).down, ?_⟩
    change (cardinalProductFrame A J).eventuallyLe g
      (s.seq (e.symm (ULift.up (e alpha).down)))
    have hAlphaIndex : e.symm (ULift.up (e alpha).down) = alpha := by
      apply e.injective
      simp
    rw [hAlphaIndex]
    exact hAlpha
  exact hNoNat J hUltra.isProper d hCofinal

theorem cardinalProductRepresentation_mem_pcf_of_concentrated_witness
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual)
    (hTcf : HasTrueCofinality
      (cardinalProductFrame B (J.pushforward (cardinalIndexMap hAB)))
      (cardinalScaleLength theta)) :
    cardinalProductRepresentation.pcf A theta := by
  have hRestrictedTcf := restrictCardinalScale_hasTrueCofinality
    hAB hRegulars hTcf
  exact (cardinalProductRepresentation_mem_pcf_iff
    (A := A) (theta := theta)).mpr
      ⟨hRegular, J, hUltra, hRestrictedTcf⟩

/-- For a regular `theta`, the only possible true cofinality of a canonical
product over `{theta}` is `theta`. -/
theorem cardinalProductRepresentation_mem_pcf_singleton_iff
    {theta beta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta) :
    cardinalProductRepresentation.pcf
        (singletonCardSet theta) beta <->
      beta = theta := by
  constructor
  · intro hBeta
    obtain ⟨_hBetaRegular, J, hUltra, hBetaTcf⟩ :=
      (cardinalProductRepresentation_mem_pcf_iff
        (A := singletonCardSet theta) (theta := beta)).mp hBeta
    have hThetaTcf :
        HasTrueCofinality
          (cardinalProductFrame (singletonCardSet theta) J)
          (cardinalScaleLength theta) :=
      singletonCardinalScale_hasTrueCofinality J hUltra.isProper hRegular
    simpa only [mk_cardinalScaleLength_level] using
      cardinal_mk_level_eq_of_hasTrueCofinality hBetaTcf hThetaTcf
  · intro hBeta
    subst beta
    exact cardinalProductRepresentation_mem_pcf_singleton hRegular

end PcfProject
