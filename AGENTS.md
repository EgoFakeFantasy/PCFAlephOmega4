# AGENTS.md

本文件规定本仓库中任何自动化代理或人工贡献者必须遵守的证明审计规则。

## 不可妥协的规则

1. `PcfProject/` 与根入口中不得出现 `sorry`、`admit`、`native_decide` 或
   `sorryAx`。
2. 不得用顶层 `axiom` 代替应当证明的结论。真正的条件必须显式出现在定理
   参数、命题前件或清楚标注的假设结构中。
3. 不得把假设重新包装成以困难定理命名的循环结论。只做展开或字段投影的声明
   必须在名称和注释中准确说明其性质。
4. 不得把未证明的数学困难藏进结构字段，再把字段投影描述为已证明结果。
5. 每个新的跨模块定理必须就近加入 `#print axioms`。允许的输出只有空集或
   `propext`、`Classical.choice`、`Quot.sound`。
6. README、TROPHIES 与源码必须一致；条件性定理必须列出实际前提。

## 修改流程

- 修改证明或公开名称前，先运行并记录一次 `lake build`。
- 每个独立改动保持足够小，使失败时可以完整回退该步。
- 每一步完成后运行默认 `lake build`；只有通过才可继续。
- 最终运行禁止项扫描，并核对核心定理的 `#print axioms` 输出。
- 不提交 `.lake/`、构建产物、审计日志、工作草稿、备份或逐日开发记录。

## 代码与命名

- 遵守 [ProofNaming.md](ProofNaming.md)。名称表达数学语义，不表达 tactic、
  “已完成”状态或版本历史。
- 对外可复用且语义不直观的声明必须带有人类可读 docstring，说明结论、前提
  与适用边界。
- 不为展示创建包装别名；[TROPHIES.md](TROPHIES.md) 直接引用默认构建中的
  真实声明。

## 核心验收

```text
lake build
```

构建必须包含 `PcfProject.two_power_alephOmega_lt_alephOmega4`，且其公理审计
仅报告 Lean/Mathlib 的标准基础公理。
