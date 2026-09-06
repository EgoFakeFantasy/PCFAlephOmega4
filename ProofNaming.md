# Proof naming convention

本项目采用 Mathlib 风格，并针对 PCF 中反复出现的复合术语作少量稳定约定。
命名必须表达数学语义，而不是证明过程或文件历史。

## 1. 所有权放在命名空间中

- 全部公开声明位于 `PcfProject` 或其数学子命名空间中。
- 声明名不重复 `PcfProject`、模块名或完整参数列表。
- 文件采用 `UpperCamelCase.lean`，并按数学职责划分，而非按开发阶段编号。

## 2. 声明名表达数学命题

- 类型、结构和主要谓词使用 `UpperCamelCase`，例如 `MaxPcfWitness`。
- 定理、定义和函数以小写开头；不同语义子句用下划线分隔。
- 项目已稳定使用的领域原子保留驼峰拼写，例如 `alephOmega`、`maxPcf`、
  `cardinalProduct`。它们作为一个数学词处理，不在重构中机械拆分。
- 用 `_of_` 引出充分条件，用 `_iff_` 表示等价，用 `_eq_`、`_lt_`、
  `_le_` 明确关系方向。
- 构造性存在定理以 `exists_` 开头；从已给见证选出的非可计算对象使用与其
  数学角色一致的名，而不是 `chosenThing`。

推荐：

```lean
targetConditionalStatement_of_strongLimit
continuumAtAlephOmega_le_maxPcf_of_strongLimit_of_lt_alephOmega4
exists_pcf_transitive_successorDirected_generators_of_successorDoublePower
```

禁止把以下词作为公开名称的证明历史后缀：`proved`、`final`、`new`、`old`、
`v2`、`helper`、`aux`、`tmp`、`main`。若一个声明确实是辅助事实，应按其真实
数学结论命名，并在最窄作用域内定义。

## 3. 假设与语义边界

- 名称和声明必须保留真正使用的最弱前提。
- 条件性适配器不得命名成无条件大定理。
- 结构字段可以表达调用者必须提供的假设，但文档与定理名不得把字段投影描述
  为项目已经证明的数学结果。
- 不为 README 或 trophy 表格创建仅用于展示的同义定理。

## 4. 局部名称与注释

- 常见基数、序数和集合可使用 `A`、`J`、`theta`、`eta` 等标准数学符号。
- 布尔式证明变量采用 `h` 加短语义，如 `hStrongLimit`、`hRegulars`、
  `hDirected`；避免无含义的 `h1`、`h2`。
- 每个跨模块公开构造或语义不直观的定理应有 docstring，说明“结论是什么、
  需要什么、没有证明什么”。注释不复述 tactic 流程。

## 5. 重命名流程

1. 以一个完整公开接口为单位改名并更新全部调用点。
2. 不保留长期兼容别名，也不创建展示别名。
3. 改名前后分别保证默认构建有效。
4. 改名后检查 `#print axioms`，并同步 README/TROPHIES 中的公开入口。

本项目没有 YesMetaZFC 的宿主层、元理论层和对象理论层三层架构，因此不机械
采用 `_l`、`_m`、`_d` 后缀；命名空间和数学术语已经能够准确表达这里的层次。
