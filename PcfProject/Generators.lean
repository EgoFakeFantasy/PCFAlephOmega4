import PcfProject.PcfBasics

/-!
# Generator systems and maximum PCF witnesses

This file defines the interfaces used to state generator systems and
maximum-PCF witnesses,
but it does not prove the structural PCF theorems.

`GeneratorSystem` requires its two ideals to have the standard PCF semantics
through `pcf (A inter B)`, rather than accepting arbitrarily named ideals. The
maximum-PCF witness separately records membership and the universal upper
bound property, so callers expose exactly the hard mathematical input they use.
-/

namespace PcfProject

universe u v w x

/-- Intersection of cardinal sets, expressed by conjunction of membership predicates. -/
def interCardSet (A B : CardSet.{u}) : CardSet.{u} :=
  fun theta => A theta /\ B theta

/-- A PCF generator system whose ideals have the canonical below/at-most
semantics and whose generator converts one ideal into the other. -/
structure GeneratorSystem
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) where
  belowIdeal : Cardinal.{u} -> Ideal Cardinal.{u}
  atMostIdeal : Cardinal.{u} -> Ideal Cardinal.{u}
  generator : Cardinal.{u} -> CardSet.{u}
  belowIdeal_spec :
    forall theta B,
      (belowIdeal theta).Small B <->
        forall beta, R.pcf (interCardSet A B) beta -> beta < theta
  atMostIdeal_spec :
    forall theta B,
      (atMostIdeal theta).Small B <->
        forall beta, R.pcf (interCardSet A B) beta -> beta <= theta
  generator_subset :
    forall {theta}, R.pcf A theta -> SubsetOf (generator theta) A
  generator_ideal_equiv :
    forall {theta}, R.pcf A theta ->
      Ideal.Equivalent
        (atMostIdeal theta)
        ((belowIdeal theta).extendBy (generator theta))

namespace GeneratorSystem

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}

theorem subset_of_mem_pcf
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    SubsetOf (G.generator theta) A :=
  G.generator_subset hTheta

theorem belowIdeal_small_iff
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u})
    (B : CardSet.{u}) :
    (G.belowIdeal theta).Small B <->
      forall beta, R.pcf (interCardSet A B) beta -> beta < theta :=
  G.belowIdeal_spec theta B

theorem atMostIdeal_small_iff
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u})
    (B : CardSet.{u}) :
    (G.atMostIdeal theta).Small B <->
      forall beta, R.pcf (interCardSet A B) beta -> beta <= theta :=
  G.atMostIdeal_spec theta B

theorem ideal_equiv_of_mem_pcf
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    Ideal.Equivalent
      (G.atMostIdeal theta)
      ((G.belowIdeal theta).extendBy (G.generator theta)) :=
  G.generator_ideal_equiv hTheta

theorem atMost_le_generated
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    Ideal.Le
      (G.atMostIdeal theta)
      ((G.belowIdeal theta).extendBy (G.generator theta)) :=
  Ideal.le_of_equivalent_left (G.ideal_equiv_of_mem_pcf hTheta)

theorem generated_le_atMost
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    Ideal.Le
      ((G.belowIdeal theta).extendBy (G.generator theta))
      (G.atMostIdeal theta) :=
  Ideal.le_of_equivalent_right (G.ideal_equiv_of_mem_pcf hTheta)

theorem belowIdeal_le_atMost
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u}) :
    Ideal.Le (G.belowIdeal theta) (G.atMostIdeal theta) :=
  by
    intro B hB
    apply (G.atMostIdeal_small_iff theta B).mpr
    intro beta hBeta
    exact ((G.belowIdeal_small_iff theta B).mp hB beta hBeta).le

theorem generator_small_atMost
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    (G.atMostIdeal theta).Small (G.generator theta) :=
  G.generated_le_atMost hTheta
    (G.generator theta)
    ((G.belowIdeal theta).generator_small_in_extendBy (G.generator theta))

theorem generator_pcf_le
    (G : GeneratorSystem R A)
    {theta beta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hBeta : R.pcf (interCardSet A (G.generator theta)) beta) :
    beta <= theta :=
  (G.atMostIdeal_small_iff theta (G.generator theta)).mp
    (G.generator_small_atMost hTheta) beta hBeta

end GeneratorSystem

/-- `theta` belongs to `pcf(A)` and bounds every other member of that spectrum. -/
def IsMaxPcf
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u})
    (theta : Cardinal.{u}) : Prop :=
  R.pcf A theta /\ forall beta, R.pcf A beta -> beta <= theta

/-- The represented PCF spectrum of `A` has a maximum. -/
def HasMaxPcf
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) : Prop :=
  exists theta, IsMaxPcf R A theta

/-- Bundled data of a maximum PCF cardinal together with its maximality proof. -/
structure MaxPcfWitness
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) where
  theta : Cardinal.{u}
  isMax : IsMaxPcf R A theta

theorem maxPcf_mem
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf R A theta) :
    R.pcf A theta :=
  hMax.left

theorem maxPcf_bounds
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    {theta beta : Cardinal.{u}}
    (hMax : IsMaxPcf R A theta)
    (hBeta : R.pcf A beta) :
    beta <= theta :=
  hMax.right beta hBeta

namespace MaxPcfWitness

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}

theorem mem_pcf
    (M : MaxPcfWitness R A) :
    R.pcf A M.theta :=
  maxPcf_mem M.isMax

theorem isRegular
    (M : MaxPcfWitness R A) :
    Cardinal.IsRegular M.theta :=
  R.mem_pcf_regular M.mem_pcf

theorem bounds
    (M : MaxPcfWitness R A)
    {beta : Cardinal.{u}}
    (hBeta : R.pcf A beta) :
    beta <= M.theta :=
  maxPcf_bounds M.isMax hBeta

theorem hasMaxPcf
    (M : MaxPcfWitness R A) :
    HasMaxPcf R A :=
  Exists.intro M.theta M.isMax

/-- Maximal PCF values are monotone under inclusion of the represented PCF
sets. This is independent of generators and no-holes. -/
theorem theta_le_of_pcf_subset
    {B : CardSet.{u}}
    (M : MaxPcfWitness R A)
    (N : MaxPcfWitness R B)
    (hSubset : SubsetOf (R.pcf A) (R.pcf B)) :
    M.theta <= N.theta :=
  N.bounds (hSubset M.theta M.mem_pcf)

end MaxPcfWitness

end PcfProject
