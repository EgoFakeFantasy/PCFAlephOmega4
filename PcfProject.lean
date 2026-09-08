import PcfProject.AxiomAudit

/-!
# PCF 证明库入口

本文件只负责公开已经核验完成的证明链，不再重复导入中间模块，也不保存
逐日开发记录。全部数学定义、引理和证明仍位于 `PcfProject/` 下的分层模块中；
最后一层 `PcfTransitiveApplications` 会沿依赖关系传递性地导入它们。

## 核心定理的语义

`PcfProject.two_power_alephOmega_lt_alephOmega4` 表示：若
`targetAlephOmega` 是强极限基数，则

`2 ^ targetAlephOmega < targetAlephOmega4`。

这里 `targetAlephOmega` 是 `aleph_omega` 的项目记号，
`targetAlephOmega4` 是 `aleph_(omega_4)` 的项目记号。

## 可复核的证明路线

1. `PcfGeneratorConstruction` 构造满足所需有向性的语义生成元。
2. `PcfTransitiveGenerators` 将局部生成元整理成传递生成元系统。
3. `PcfNoHoles` 与 `RankClosureConstruction` 给出核心 PCF 区间和
   `omega_4` 截断所需的秩闭包结论。
4. `PcfContinuumBridge` 把 PCF 最大值估计转换成
   `aleph_omega` 的幂集估计。
5. `PcfTransitiveApplications.targetConditionalStatement_of_strongLimit` 汇总上述
   构造；最终定理只是把强极限假设代入该已证明的条件结论。

`PcfProject.AxiomAudit` 集中检查本入口公开的里程碑。当前输出仅包含
Mathlib/Lean 通常使用的 `propext`、`Classical.choice` 与 `Quot.sound`；证明
不含占位项、项目自定义公理，也没有把目标结论藏入结构字段。
-/
