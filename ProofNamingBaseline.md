# 证明命名迁移基线

本文档记录源码命名重构前的稳定快照。统计只覆盖 Git 跟踪的 Lean 文件，
排除 `.lake` 和其他构建产物；字节数把换行统一为 LF 后按无 BOM UTF-8 计算，
避免 CRLF 差异掩盖真实的命名变化。命名规则见 [ProofNaming.md](ProofNaming.md)。

## 基线快照

| 项目 | 数值 |
| --- | ---: |
| 测量日期 | 2026-09-07 |
| 基线提交 | `2b83adc` |
| Git 跟踪的 Lean 文件 | 29 |
| LF 归一化 UTF-8 字节 | 1,203,365 |
| LF 归一化源码行 | 28,805 |

## 最大模块

| 文件 | 工作区字节 | 行数 |
| --- | ---: | ---: |
| `PcfProject/CanonicalProduct.lean` | 299,641 | 7,055 |
| `PcfProject/Stationary.lean` | 114,829 | 3,064 |
| `PcfProject/RankClosureConstruction.lean` | 109,002 | 2,335 |
| `PcfProject/PcfTransitiveGenerators.lean` | 103,109 | 2,092 |
| `PcfProject/LocalRank.lean` | 63,077 | 1,537 |

大文件不作为首批迁移目标。命名迁移按依赖自底向上进行，优先选择小型、
完整、调用面可穷尽的公开接口。每批必须同步更新全部调用点，不保留旧名别名，
并在完整 `lake build` 通过后记录新快照。

## 第一批：主超滤接口

目标模块为 `PcfProject/PrincipalPcf.lean`。迁移将“所有超滤为主”改为可作为
命名空间的数学谓词 `AllUltrafiltersPrincipal`，并将其唯一公开定理改为
`AllUltrafiltersPrincipal.pcf_below_alephOmega4`。新名不再重复规范表示的实现名，
而是由命名空间表达前件、定理词根表达结论。

迁移同时覆盖有限指标集给出的标准见证：
`AllUltrafiltersPrincipal.of_finite`。旧谓词名、旧定理名及全部旧调用点均已删除，
没有加入兼容别名。

## 第一批完成快照

| 项目 | 数值 | 相对基线 |
| --- | ---: | ---: |
| Git 跟踪的 Lean 文件 | 29 | 0 |
| LF 归一化 UTF-8 字节 | 1,203,683 | +318 |
| LF 归一化源码行 | 28,816 | +11 |

本批增加的 11 行均为命名空间边界和面向读者的语义注释，不是证明包装层。
默认构建通过 1017/1017 个任务；核心定理的公理集合保持为
`propext`、`Classical.choice`、`Quot.sound`。

## 第二批：模块职责说明

基础接口与关键构造模块的标题改为数学职责，不再沿用开发阶段编号；说明文字
删除“旧骨架”“占位符”等实现历史，只保留结论、前提与未覆盖范围。此批没有
改动任何 Lean 声明或证明项。

| 项目 | 数值 | 相对第一批 |
| --- | ---: | ---: |
| Git 跟踪的 Lean 文件 | 29 | 0 |
| LF 归一化 UTF-8 字节 | 1,203,096 | -587 |
| LF 归一化源码行 | 28,808 | -8 |

默认构建再次通过 1017/1017 个任务。

## 第三批：无警告基础接口

把两处已弃用的 Mathlib API 更新为当前等价接口，并按 Lean 检查器建议精简三处
证明表达。四个受影响模块分别通过检查，全库构建也未再报告这些警告。

| 项目 | 数值 | 相对第二批 |
| --- | ---: | ---: |
| Git 跟踪的 Lean 文件 | 29 | 0 |
| LF 归一化 UTF-8 字节 | 1,202,939 | -157 |
| LF 归一化源码行 | 28,807 | -1 |

所有定理类型保持不变；核心定理的公理集合仍为 `propext`、
`Classical.choice`、`Quot.sound`。

## 第四批：基数集合和值的大小写

将四个返回集合或基数的公开定义统一为函数和值的小驼峰命名：
`InterCardSet` 改为 `interCardSet`，`UnionCardSet` 改为 `unionCardSet`，
`FinsetUnionCardSet` 改为 `finsetUnionCardSet`，`ContinuumAtAlephOmega`
改为 `continuumAtAlephOmega`。这些声明不是类型、结构或主要谓词，因此不应使用
大驼峰；数学含义及全部定理类型均未改变。旧名称和旧调用点已全部删除，未增加
兼容别名。

| 项目 | 数值 | 相对第三批 |
| --- | ---: | ---: |
| Git 跟踪的 Lean 文件 | 29 | 0 |
| LF 归一化 UTF-8 字节 | 1,202,939 | 0 |
| LF 归一化源码行 | 28,807 | 0 |

本批只改变同长度标识符的首字母大小写，所以源码规模不变。默认构建通过
1017/1017 个任务；核心定理的公理集合仍为 `propext`、
`Classical.choice`、`Quot.sound`。
