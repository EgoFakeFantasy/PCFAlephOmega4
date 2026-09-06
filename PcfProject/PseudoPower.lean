import PcfProject.ContinuumControl

/-!
# 核心连续统上界接口

核心证明在本层只使用一个明确的序关系：给定最大 pcf 见证 `M`，若
`ContinuumAtAlephOmega ≤ M.theta`，并且 `M.theta < targetAlephOmega4`，
则连续统严格小于目标基数。本文件保留该假设的原名与终端引理，避免
用未参与核心证明的替代包装遮蔽这两项数学输入。
-/

namespace PcfProject

universe u v w x

/-- 最大 pcf 见证 `M` 足够大，能够控制 `aleph_omega` 处的连续统。 -/
def ContinuumLeMaxPcfWitness
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (M : MaxPcfWitness R A) : Prop :=
  ContinuumAtAlephOmega <= M.theta

/--
连续统先由最大 pcf 见证从上方控制，而该见证又严格低于 `aleph_{omega+4}`；
传递性因此给出核心证明所需的严格连续统上界。
-/
theorem continuum_bound_of_maxPcfWitness_lt
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (M : MaxPcfWitness R A)
    (hContinuum : ContinuumLeMaxPcfWitness M)
    (hMaxLt : M.theta < targetAlephOmega4) :
    targetUpperBoundStatement.{u} := by
  change ContinuumAtAlephOmega < targetAlephOmega4
  exact lt_of_le_of_lt hContinuum hMaxLt

#print axioms continuum_bound_of_maxPcfWitness_lt

end PcfProject
