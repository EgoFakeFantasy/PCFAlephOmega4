import PcfProject.CanonicalPcf
import PcfProject.CountableBound

/-!
# 主超滤情形的核心接口

若一个基数集上的每个超滤对偶理想都集中在单个坐标，则其规范 pcf 谱仍落在原集合中。
因此，只要原集合低于 `aleph_omega`，整个 pcf 谱就严格低于目标 `aleph_{omega+4}`。
-/

namespace PcfProject

universe u

/-- 每个超滤对偶理想都是排除某个单点所得的主理想。 -/
def PrincipalUltrafiltersOn (A : CardSet.{u}) : Prop :=
  forall J : Ideal (CardinalIndex A),
    J.IsUltrafilterDual ->
      exists i0, J = Ideal.excludePoint i0

/-- 主理想假设使规范 pcf 谱包含于原集合，从而把 `aleph_omega` 下界传递为目标上界。 -/
theorem cardinalProductRepresentation_pcf_below_alephOmega4_of_principalUltrafilters
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hPrincipal : PrincipalUltrafiltersOn A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 cardinalProductRepresentation A := by
  intro theta hTheta
  exact (hBelow theta
    (cardinalProductRepresentation_pcf_subset_of_principal_ultrafilters
      hRegulars hPrincipal theta hTheta)).trans
    targetAlephOmega_lt_targetAlephOmega4

#print axioms cardinalProductRepresentation_pcf_below_alephOmega4_of_principalUltrafilters

end PcfProject
