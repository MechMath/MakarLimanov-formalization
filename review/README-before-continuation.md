# tsuki 解答的 Lean 形式化核验

**状态：部分引理通过；原命题的完整形式化证明尚未完成。**

本工程针对已上传的 `proof.pdf` 对应 LaTeX 源码。现有 506 行数学 Lean 源码、31 个公开定理
通过编译及传递公理检查。这些定理包括若干辅助结论和带有明确前提的推论，**不能据此声称
13 页证明整体通过形式化验证**。`OriginalConjecture` 目前只有命题定义，没有证明项。

## 实际完成的内容

| 文件 | 核验范围 |
|---|---|
| [Statement.lean](MakarLimanov/Statement.lean) | 自由多项式的有序矩阵求值；最小秩的存在与取到；正整数阶数上的实数下确界；与任意 epsilon 小秩矩阵的等价性；标量零点分支；给定矩阵见证后的极限步骤 |
| [ScalarReduction.lean](MakarLimanov/ScalarReduction.lean) | 存在标量零点，或交换化为非零常数的分类；原文 Lemma 2.1 的第一部分 |
| [Descent.lean](MakarLimanov/Descent.lean) | 有限变量多项式方程组从任意扩域下降到代数闭基域 |
| [MatrixDescent.lean](MakarLimanov/MatrixDescent.lean) | 原文基域下降引理的完整形式化；使用秩分解编码方程，代替原文的子式方法；不要求扩域有限或代数 |
| [BoundaryRank.lean](MakarLimanov/BoundaryRank.lean) | 支撑在指定行集合或列集合中的矩阵，秩不超过两个集合的基数之和 |
| [Numerics.lean](MakarLimanov/Numerics.lean) | Newton 分母/重数预算、条件性有限步数估计、下一斜率的次数比较、压缩后的秩比计算 |
| [Assembly.lean](MakarLimanov/Assembly.lean) | **假定**存在扩域上的定量矩阵见证时，完成基域下降并推出原题的下确界结论 |

原命题定义保留原题所有条件：代数闭、特征零、有限个自由非交换变量、非标量自由多项式、
所有正整数矩阵阶数、各阶数上实际取到的最小秩，以及实数意义的下确界。
`eval_mul`、`eval_generator`、`eval_constant` 明确检查求值使用矩阵乘法、保持字母顺序，
并将常数送到标量矩阵。

## 仍然缺失的证明

| 原文位置 / 标签 | 状态与具体缺项 |
|---|---|
| 第 2 节 `lem:reduction` | 两生成元编码的单射性、归一化后的支撑和次数界尚未形式化；标量分类已完成 |
| 第 3 节 `lem:algebra`、`lem:twist` | 上有界分数指数级数、双导子星乘法及结合律、中心扭曲尚未构造 |
| 第 3 节 `lem:separation`、`lem:variation` | 泛型分离与精确斜率协变尚未形式化 |
| 第 4 节 `lem:branch` | 满足方程与不等式的兼容交换微分域扩张尚未形式化 |
| 第 5 节 `lem:step`、`lem:orbit`、`prop:finite` | Newton 修正存在性、因子轨道估计、有限精度符号的实际构造尚未形式化；仅完成其部分数值推论 |
| 第 6 节 `lem:realization` | 无限矩阵代数及局部有限性、Taylor/正规排序实现的同态性质尚未形式化 |
| 第 6 节 `prop:compression` | 路径压缩、边界支撑和格点计数尚未形式化；给定边界支撑后的线性代数秩估计已完成 |
| 第 7 节最终证明 | 尚无满足 `Assembly.lean` 中 `hZ` 的实际矩阵见证族，因而无法消去最终组合定理的这一前提 |

这些缺项没有被写成公理或偷偷作为“已证明事实”引入。条件性定理的前提在 Lean 类型中显式可见。
源码中没有 `sorry` 仅表示**已经写出的这些证明**没有占位符；由于完整目标还没有证明项，
这不表示全篇证明完成。这次结果也没有给出原命题的反例或判定其为假。

## 验证与复现

- Lean：`leanprover/lean4:v4.30.0-rc1`。
- mathlib：`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`。
- `lake build` 成功（3312 jobs，包含依赖任务；不是 3312 个本地定理）。
- 31 个公开定理的 `#print axioms` 结果仅含 `propext`、`Classical.choice`、`Quot.sound`
  中的部分或全部；没有 `sorryAx` 或自定义公理。
- 对 7 个数学模块的 sorry 扫描结果为 0。

在本机进入此目录执行：

```sh
lake build
lake env lean AxiomAudit.lean
```

本机配置通过 `lakefile.toml` 及 `lake-manifest.json` 使用已有 mathlib 和其依赖的本地路径；
没有复制或链接其他工程的构建目录。迁移机器时需把 mathlib 的 path 依赖换成上述提交的 Git
依赖，重新生成 manifest 并取得对应缓存。当前配置可在本机直接复现，不是无依赖的可移植包。

公理检查原始输出：[logs/axioms.log](logs/axioms.log)。机器可读状态：
[verification.json](verification.json)。完整原命题是否通过的字段明确为 `false`。

## 来源与修改范围

- 对应网站题目：`0e7dcc7f-6d6b-47e5-b157-1427684fbfab`。
- 原证明源文件 SHA-256：`c0c6e2b60a71767774b1d51e9984d96fc64f6b10dbd60ecaef25b9b5fd7a47f4`。
- 已上传 PDF SHA-256：`e4c0739722de2706c7092895b4c3d547346a285472a7ddfc919e22f4dec74a7c`。
- 新增文件均在 `formalization/`；未修改原证明、原运行状态或网站提交。
- 本次曾创建诊断文件 `/tmp/makar-check.lean`，完成后已清理。

继续工作的核心交付条件是构造 `Assembly.lean` 要求的矩阵见证族，证明它满足 `hZ`，
并在不增加数学公理或修改原题的前提下，给出 `OriginalConjecture K d` 的证明项。
