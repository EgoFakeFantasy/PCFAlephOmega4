import PcfProject.CardinalArithmetic
import PcfProject.TcfScale

/-!
# PCF membership

`PcfRepresentation` records what it means for a reduced
product to be over a set of cardinals and what it means for a scale length to
represent a cardinal. Membership requires `HasTrueCofinality`, including its
minimality among all cofinal families. A represented length is required to
have cardinality equal to the represented cardinal, with universe lifts made
explicit. The separate `length_regular` field is the source of
regularity for an arbitrary representation; that fact is not derived here
merely from the existence of a scale. No generator, no-holes, max-pcf,
countable PCF bound, or continuum bound is proved here.
-/

namespace PcfProject

universe u v w x

/-- A cardinal set, represented extensionally by its membership predicate. -/
abbrev CardSet : Type (u + 1) :=
  Cardinal.{u} -> Prop

/-- Pointwise inclusion of cardinal sets: every member of `B` belongs to `A`. -/
def SubsetOf (B A : CardSet.{u}) : Prop :=
  forall theta, B theta -> A theta

/-- Every cardinal selected by `A` is regular. -/
def SetOfRegulars (A : CardSet.{u}) : Prop :=
  forall theta, A theta -> Cardinal.IsRegular theta

theorem setOfRegulars_of_subset
    {A B : CardSet.{u}}
    (hBA : SubsetOf B A)
    (hRegulars : SetOfRegulars A) :
    SetOfRegulars B := by
  intro theta hTheta
  exact hRegulars theta (hBA theta hTheta)

/-- Abstract semantics connecting cardinal sets, reduced products, scale lengths,
and the regular cardinals represented by those scales. -/
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

/-- The PCF spectrum witnessed by a represented reduced product with true cofinality. -/
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

end PcfRepresentation

end PcfProject
