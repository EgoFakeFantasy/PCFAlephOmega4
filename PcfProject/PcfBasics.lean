import PcfProject.CardinalArithmetic
import PcfProject.TcfScale

/-!
# Stage 5: Mathlib-cardinal PCF membership interface

This file replaces the former `CardinalArithmeticFrame`-based skeleton with a
small Mathlib-level interface for membership in `pcf A`.

It is still abstract: `PcfRepresentation` records what it means for a reduced
product to be over a set of cardinals and what it means for a scale length to
represent a cardinal. Membership requires `HasTrueCofinality`, including its
minimality among all cofinal families. A represented length is required to
have cardinality equal to the represented cardinal, with universe lifts made
explicit. The separate `length_regular` field is still the source of
regularity for an arbitrary representation; that fact is not derived here
merely from the existence of a scale. No generator, no-holes, max-pcf,
countable PCF bound, or final continuum bound is proved here.
-/

namespace PcfProject

universe u v w x

abbrev CardSet : Type (u + 1) :=
  Cardinal.{u} -> Prop

def SubsetOf (B A : CardSet.{u}) : Prop :=
  forall theta, B theta -> A theta

def SetOfRegulars (A : CardSet.{u}) : Prop :=
  forall theta, A theta -> Cardinal.IsRegular theta

theorem setOfRegulars_of_subset
    {A B : CardSet.{u}}
    (hBA : SubsetOf B A)
    (hRegulars : SetOfRegulars A) :
    SetOfRegulars B := by
  intro theta hTheta
  exact hRegulars theta (hBA theta hTheta)

/-- `A` is progressive when its cardinality is below each member. The member
cardinal is lifted because the subtype of `Cardinal.{u}` lives in `Type (u+1)`. -/
def ProgressiveCardSet (A : CardSet.{u}) : Prop :=
  forall theta, A theta ->
    Cardinal.mk { beta : Cardinal.{u} // A beta } <
      Cardinal.lift.{u + 1} theta

theorem progressiveCardSet_of_subset
    {A B : CardSet.{u}}
    (hBA : SubsetOf B A)
    (hProgressive : ProgressiveCardSet A) :
    ProgressiveCardSet B := by
  intro theta hTheta
  exact (Cardinal.mk_subtype_mono hBA).trans_lt
    (hProgressive theta (hBA theta hTheta))

structure PcfRepresentation where
  IsProductOver :
    CardSet.{u} -> ReducedProductFrame.{v, w} -> Prop
  LengthRepresents :
    ScaleLength.{x} -> Cardinal.{u} -> Prop
  length_cardinal :
    forall {L : ScaleLength.{x}} {theta : Cardinal.{u}},
      LengthRepresents L theta ->
        Cardinal.lift.{u} (Cardinal.mk L.Level) =
          Cardinal.lift.{x} theta
  length_regular :
    forall {L : ScaleLength.{x}} {theta : Cardinal.{u}},
      LengthRepresents L theta -> Cardinal.IsRegular theta

namespace PcfRepresentation

variable (R : PcfRepresentation.{u, v, w, x})

def pcf (A : CardSet.{u}) : CardSet.{u} :=
  fun theta =>
    exists F : ReducedProductFrame.{v, w},
      exists L : ScaleLength.{x},
        R.IsProductOver A F /\
          R.LengthRepresents L theta /\
          HasTrueCofinality F L

theorem mem_pcf_of_witness
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    {F : ReducedProductFrame.{v, w}}
    {L : ScaleLength.{x}}
    (hProduct : R.IsProductOver A F)
    (hLength : R.LengthRepresents L theta)
    (hTcf : HasTrueCofinality F L) :
    R.pcf A theta := by
  exact Exists.intro F
    (Exists.intro L
      (And.intro hProduct (And.intro hLength hTcf)))

theorem mem_pcf_hasTrueCofinality
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    exists F : ReducedProductFrame.{v, w},
      exists L : ScaleLength.{x},
        R.IsProductOver A F /\
          R.LengthRepresents L theta /\
          HasTrueCofinality F L :=
  hTheta

theorem represented_length_cardinality
    {L : ScaleLength.{x}}
    {theta : Cardinal.{u}}
    (hLength : R.LengthRepresents L theta) :
    Cardinal.lift.{u} (Cardinal.mk L.Level) =
      Cardinal.lift.{x} theta :=
  R.length_cardinal hLength

theorem mem_pcf_has_represented_length
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    exists F : ReducedProductFrame.{v, w},
      exists L : ScaleLength.{x},
        R.IsProductOver A F /\
          HasTrueCofinality F L /\
          Cardinal.lift.{u} (Cardinal.mk L.Level) =
            Cardinal.lift.{x} theta := by
  obtain ⟨F, L, hProduct, hLength, hTcf⟩ := hTheta
  exact ⟨F, L, hProduct, hTcf, R.length_cardinal hLength⟩

theorem mem_pcf_regular
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    Cardinal.IsRegular theta := by
  rcases hTheta with ⟨_F, _L, _hProduct, hLength, _hTcf⟩
  exact R.length_regular hLength

theorem pcf_is_setOfRegulars
    (A : CardSet.{u}) :
    SetOfRegulars (R.pcf A) := by
  intro theta hTheta
  exact mem_pcf_regular R hTheta

theorem progressiveCardSet_pcf_of_subset
    {A : CardSet.{u}}
    (hBA : SubsetOf (R.pcf A) A)
    (hProgressive : ProgressiveCardSet A) :
    ProgressiveCardSet (R.pcf A) :=
  progressiveCardSet_of_subset hBA hProgressive

/-! These are order-theoretic closure consequences. They do not assert the
hard PCF reverse inclusion `pcf A subset A`; callers must supply it. -/

theorem pcf_eq_of_subset_of_subset
    {A : CardSet.{u}}
    (hExpand : SubsetOf A (R.pcf A))
    (hContract : SubsetOf (R.pcf A) A) :
    R.pcf A = A := by
  funext theta
  apply propext
  constructor
  · exact hContract theta
  · exact hExpand theta

theorem pcf_eq_iff_of_subset
    {A : CardSet.{u}}
    (hExpand : SubsetOf A (R.pcf A)) :
    R.pcf A = A <-> SubsetOf (R.pcf A) A := by
  constructor
  · intro hEq theta hTheta
    rw [hEq] at hTheta
    exact hTheta
  · intro hContract
    exact R.pcf_eq_of_subset_of_subset hExpand hContract

theorem pcf_pcf_eq_of_pcf_eq
    {A : CardSet.{u}}
    (hEq : R.pcf A = A) :
    R.pcf (R.pcf A) = R.pcf A :=
  congrArg R.pcf hEq

end PcfRepresentation

end PcfProject
