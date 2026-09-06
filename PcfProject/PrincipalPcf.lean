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
def AllUltrafiltersPrincipal (A : CardSet.{u}) : Prop :=
  forall J : Ideal (CardinalIndex A),
    J.IsUltrafilterDual ->
      exists i0, J = Ideal.excludePoint i0

namespace AllUltrafiltersPrincipal

/-- 若所有超滤对偶理想都为主理想，则规范 PCF 谱不产生新基数。
因此，一个由正则基数组成且位于 `aleph_omega` 以下的集合，其 PCF 谱也严格低于
`aleph_(omega_4)`。此定理只处理主理想情形，不声称所有超滤自动为主的。 -/
theorem pcf_below_alephOmega4
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hPrincipal : AllUltrafiltersPrincipal A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 cardinalProductRepresentation A := by
  intro theta hTheta
  exact (hBelow theta
    (cardinalProductRepresentation_pcf_subset_of_principal_ultrafilters
      hRegulars hPrincipal theta hTheta)).trans
    targetAlephOmega_lt_targetAlephOmega4

#print axioms AllUltrafiltersPrincipal.pcf_below_alephOmega4

end AllUltrafiltersPrincipal

end PcfProject
