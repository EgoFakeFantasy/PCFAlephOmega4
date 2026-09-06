# PCFAlephOmega4

`PCFAlephOmega4` 是一个以 Lean 4 与 Mathlib 编写的 PCF 理论形式化项目。它的
核心结果是 Shelah 的 `aleph_omega` 幂集上界在强极限假设下的直接基数形式：

```text
如果 aleph_omega 是强极限基数，那么
2 ^ aleph_omega < aleph_(omega_4)。
```

对应的公开声明是：

```lean
import PcfProject

#check PcfProject.two_power_alephOmega_lt_alephOmega4
#print axioms PcfProject.two_power_alephOmega_lt_alephOmega4
```

定理的假设没有被隐藏在项目公理或结果型结构中。当前公理审计输出仅包含
`propext`、`Classical.choice` 与 `Quot.sound`，即本项目通过 Mathlib 使用的标准
基础设施；源码中没有 `sorry`、`admit`、`native_decide`、`sorryAx` 或项目级
`axiom`。

## 数学记号

- `targetAlephOmega` 表示 `aleph_omega`。
- `targetIndexOmega4` 表示初始序数 `omega_4`。
- `targetAlephOmega4` 表示 `aleph_(omega_4)`。
- `targetConditionalStatement` 表示“`aleph_omega` 为强极限蕴含目标上界”。

因此，核心定理不是无条件断言强极限性，而是精确保留这一数学前提。

## 证明结构

| 层次 | 主要模块 | 作用 |
| --- | --- | --- |
| 基础 | `CardinalArithmetic`, `IdealProduct`, `TcfScale` | 基数记号、理想约化积与真共尾度 |
| PCF 表示 | `CanonicalProduct`, `CanonicalPcf`, `CofinalCore` | 标准乘积表示、PCF 谱与核心性质 |
| 生成元 | `Generators`, `PcfGeneratorConstruction`, `PcfTransitiveGenerators` | 生成元构造、有向性与传递化 |
| 秩与稳集 | `Stationary`, `StationaryIdeal`, `LocalRank`, `RankClosureConstruction` | 俱乐部猜测、非稳理想与局部秩闭包 |
| 连续统桥 | `PcfCharacteristicModels`, `PcfContinuumBridge` | 特征模型计数与 `aleph_omega ^ aleph_0` 上界 |
| 汇总 | `PcfTransitiveApplications` | 构造强极限尾部并组合出最终不等式 |

更细的稳定里程碑、准确前提与依赖关系见 [TROPHIES.md](TROPHIES.md)。命名
规则见 [ProofNaming.md](ProofNaming.md)，迁移度量见
[ProofNamingBaseline.md](ProofNamingBaseline.md)。

## 本地复核

项目固定使用 Lean `v4.30.0` 与 Mathlib `v4.30.0`：

```text
lake update
lake build
```

完整构建会编译根模块 `PcfProject.lean` 及其传递依赖，并同时执行源码中的
`#print axioms` 审计点。2026-09-07 的默认构建通过了 1017 个构建任务。

## 仓库范围

公开仓库只保存可复核的 Lean 源码、Lake 配置、说明文档和持续集成配置。
构建产物、本地审计日志、工作草稿与逐日开发记录不属于证明接口，也不进入
版本控制。

## 许可

本项目以 [MIT License](LICENSE) 发布。
