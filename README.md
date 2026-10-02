# Makar–Limanov 猜想的 Lean 形式化

**原主定理已通过 Lean 验证，无 `sorry`、无自定义公理。**

入口是 [Main.lean](MakarLimanov/Main.lean) 中的 `MakarLimanov.makarLimanov`。
原定理陈述保持不变，其传递公理依赖为：

```text
propext, Classical.choice, Quot.sound
```

历史接口 [AuditedAssumptions.lean](MakarLimanov/AuditedAssumptions.lean) 中的
`finite_newton_approximation` 和 `symbol_realization` 现在都是有完整证明的定理。
该文件名和命名空间仅为兼容现有调用保留。

## 证明连接

- [StarOperatorRepresentation.lean](MakarLimanov/StarOperatorRepresentation.lean)
  将具体星符号与已证明非零的微分算子求值连接。插值多项式使用下降阶乘基展开，
  得到正确的系数符号 `Σ cⱼ τʲ uʲ`。
- [InitialSlopeData.lean](MakarLimanov/InitialSlopeData.lean)
  选择初始支撑斜率和固定的输入支撑界 `A`；`A` 在目标精度之前选定。
- [NewtonSlopeData.lean](MakarLimanov/NewtonSlopeData.lean)
  证明每次修正后的下一斜率、格点细化、活动次数整除性及重数预算，
  并通过有限迭代达到任意给定精度。
- [FiniteNewtonTheorem.lean](MakarLimanov/FiniteNewtonTheorem.lean)
  组合具体分离、初始化与迭代，证明完整的有限 Newton 逼近结论。
- [SymbolRealization.lean](MakarLimanov/SymbolRealization.lean)
  给出保单位、保基域常数及精确支撑界的矩阵实现。
  [ConditionalMain.lean](MakarLimanov/ConditionalMain.lean) 和
  [TwoGenerator.lean](MakarLimanov/TwoGenerator.lean)
  完成矩阵压缩、扩域秩下降及两生成元约化，得到原主定理。

这些步骤沿用 [proof.tex](proof.tex) 中的证明路线。有限逼近接口只要求某个统一的 `A`，
因此形式化在初始斜率确定后选择 `A`，无需使用文章中更强的显式初始常数估计。

## 验证

Lean：`leanprover/lean4:v4.30.0-rc1`。
mathlib 提交：`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`。

```sh
lake build
lake env lean FullAxiomAudit.lean
lake env lean MainAxiomAudit.lean
lake env lean VerifyComplete.lean
lake env lean VerifyConditional.lean
```

- `lake build` 检查辅助库和原主定理。
- `FullAxiomAudit.lean` 遍历辅助库全部项目声明，包括私有和生成声明。
- `MainAxiomAudit.lean` 打印主定理的实际传递公理依赖。
- `VerifyComplete.lean` 严格检查原主定理只依赖三条标准公理。
- 历史入口 `VerifyConditional.lean` 现在同样只允许三条标准公理，并遍历
  辅助库和主定理导入的全部项目声明。

以上检查均已通过。实际输出、声明计数和源文件哈希见 [verification.json](verification.json)。

## 来源与复核

- 原证明：[proof.tex](proof.tex)。
- 历史数学复核：[informal-audit-2026-09-30.md](review/informal-audit-2026-09-30.md)。
- 网站题目：`0e7dcc7f-6d6b-47e5-b157-1427684fbfab`。
- 原证明 SHA-256：`c0c6e2b60a71767774b1d51e9984d96fc64f6b10dbd60ecaef25b9b5fd7a47f4`。

`review/` 中旧日志保留了当时尚未完成的状态，当前状态以验证入口和
`verification.json` 为准。

依赖使用本机 `SunMatrix/.lake/packages/mathlib` 的绝对路径。迁移机器时需改为对应
提交的 Git 依赖并获取缓存。
