# Proof trophies

本页只列入已经位于默认构建链中的稳定数学成果。每一项都直接指向真实 Lean
声明；项目不会为了展示而增加同义包装定理。条件性结果必须列出其实际前提，
基础设施与最终结论分开记录。

## Lean 入口

```lean
import PcfProject

#check PcfProject.two_power_alephOmega_lt_alephOmega4
#check PcfProject.targetConditionalStatement_of_strongLimit
#check PcfProject.alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit
#check PcfProject.exists_pcf_transitive_successorDirected_generators_of_successorDoublePower
#check PcfProject.successorAlephLocalLemma2410ExactUpperBounds
#check PcfProject.exists_omegaOneClubGuessingAtAlephThree
#check PcfProject.targetAlephOmega_power_aleph0_le_maxPcf_of_strongLimit_of_lt_alephOmega4
```

## 最终结果

| ID | Lean 声明 | 数学内容 | 实际前提 | 源码 |
| --- | --- | --- | --- | --- |
| PCF-001 | `two_power_alephOmega_lt_alephOmega4` | `2 ^ aleph_omega < aleph_(omega_4)` | `aleph_omega` 是强极限基数 | [PcfTransitiveApplications.lean](PcfProject/PcfTransitiveApplications.lean#L795) |
| PCF-002 | `targetConditionalStatement_of_strongLimit` | 构造完整的条件目标：强极限性蕴含 PCF 上界 | 无额外参数；强极限性是目标命题的前件 | [PcfTransitiveApplications.lean](PcfProject/PcfTransitiveApplications.lean#L750) |

## 可复用基础设施

| ID | Lean 声明 | 数学内容 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| PCF-101 | `exists_pcf_transitive_successorDirected_generators_of_successorDoublePower` | 在 PCF 谱上构造传递且后继有向的生成元系统 | 需要正则性、小指标、指标无限及逐坐标双幂集间隙 | [PcfTransitiveGenerators.lean](PcfProject/PcfTransitiveGenerators.lean#L2091) |
| PCF-102 | `alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit` | 对完整后继 aleph 核心证明 Localization 24.32 所需输出 | 需要 `aleph_omega` 强极限；尾部生成元在证明内构造 | [PcfTransitiveApplications.lean](PcfProject/PcfTransitiveApplications.lean#L713) |
| PCF-103 | `successorAlephLocalLemma2410ExactUpperBounds` | 对推前非稳理想及其局部化给出 Lemma 24.10 的闭精确上界 | 保留源共尾度与幂集间隙前提 | [RankClosureConstruction.lean](PcfProject/RankClosureConstruction.lean#L1405) |
| PCF-104 | `exists_omegaOneClubGuessingAtAlephThree` | 在 `omega_3` 以下构造同时猜测俱乐部的 `omega_1` 梯系统 | 结论在项目基础理论中直接证明，不把猜测系统作为假设 | [LocalRank.lean](PcfProject/LocalRank.lean#L1235) |
| PCF-105 | `targetAlephOmega_power_aleph0_le_maxPcf_of_strongLimit_of_lt_alephOmega4` | 将特征模型计数转化为 `aleph_omega ^ aleph_0` 的 PCF 最大值上界 | 需要强极限性及一个低于 `aleph_(omega_4)` 的核心最大 PCF 见证 | [PcfContinuumBridge.lean](PcfProject/PcfContinuumBridge.lean#L687) |
| PCF-106 | `canonicalGeneratorSystemOfTwoPowerBelowCoordinates` | 从逐坐标幂集间隙构造语义生成元系统 | 需要正则、小而无限的指标及显式幂集间隙；不声称适用于任意渐进集 | [PcfGeneratorConstruction.lean](PcfProject/PcfGeneratorConstruction.lean#L775) |

## 依赖主线

```text
基数与约化积
  -> PCF 谱和真共尾度
  -> 语义生成元与传递生成元
  -> Corollary 24.30 + Localization 24.32
  -> 局部秩闭包和 omega_4 截断
  -> 特征模型连续统桥
  -> two_power_alephOmega_lt_alephOmega4
```

## 信任与核验

- 最近核验日期：2026-09-06。
- 默认 `lake build`：1017/1017 个任务通过。
- 核心定理公理：`propext`、`Classical.choice`、`Quot.sound`。
- 禁止项扫描：无 `sorry`、`admit`、`native_decide`、`sorryAx`、顶层
  `axiom`。
- 新里程碑必须直接引用公开声明，并同步更新本页日期、构建结果与公理审计。
