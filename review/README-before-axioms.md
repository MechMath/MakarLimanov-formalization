# Makar–Limanov 猜想的 Lean 形式化

**状态：辅助库通过；原命题的完整形式化仍未完成。**

工程已从 `mmat-website-mcp-v0.1.0/formalization/` 移至本桌面目录。
原证明源码保存在 [proof.tex](proof.tex)。主定理是
[Main.lean](MakarLimanov/Main.lean) 中的 `MakarLimanov.makarLimanov`，
第 18 行仍有一个 `sorry`；其传递公理包含 `sorryAx`。

## 本次续作

- 新增 [Variations.lean](MakarLimanov/Variations.lean)：通过中心参数多项式定义实际变分，
  证明重构公式、有序卷积、变分阶数上界、同态相容和中心乘法公式 (3.7)。
- 新增 [SymbolVariations.lean](MakarLimanov/SymbolVariations.lean)：将变分接入实际星代数，
  证明非零中心扭曲保持变分非零性，并使 Laurent 阶数精确平移。
- 新增 [GenericJets.lean](MakarLimanov/GenericJets.lean)：在全部混合 jet 变量的分式域上
  构造两个交换导子；证明每个变量确实是同一个元素的混合导数，且非零微分多项式不消失。
- 新增 [JetTransform.lean](MakarLimanov/JetTransform.lean)：构造无限 jet 多项式环上的
  二项式三角自同构及逆，证明公式 (3.8) 和特征向量乘法保持微分代数独立性。
- 新增 [GenericTwist.lean](MakarLimanov/GenericTwist.lean)：把中心扭曲扩域与泛型 jet 扩域
  接起来，实际构造有理特征值的非零特征向量，以及扭曲前后均泛型的元素。
- 新增 [DifferentialCoefficients.lean](MakarLimanov/DifferentialCoefficients.lean)：证明 jet
  多项式系数子代数在两个导子、星项、星乘法和自由多项式求值下封闭。
- 新增 [SymbolSpecialization.lean](MakarLimanov/SymbolSpecialization.lean)：处理可能不单射的
  系数特化，证明共同支撑界下特化与无限星乘法相容。
- 新增 [JetPolynomialCoefficients.lean](MakarLimanov/JetPolynomialCoefficients.lean)：证明
  每个泛型符号和变分系数都有 jet 多项式代表，而无需特化分式域。
- 新增 [JetSpecialization.lean](MakarLimanov/JetSpecialization.lean)：把多项式 jet 代表特化到
  任意兼容微分元，证明非零具体值可反推出泛型值非零，并保持下界支撑。
- 新增 [GenericSeparation.lean](MakarLimanov/GenericSeparation.lean)：在具体混合 jet
  分式域模型中证明多项式评价等于分式域嵌入，因而非零且具有单射性。
- 新增 [NewtonConstruction.lean](MakarLimanov/NewtonConstruction.lean)：形式化论文第 5 节
  的数值 Newton 预算、分母重数界、严格进展和有限终止接口；实际代数 correction 仍作为
  显式输入保留。
- 新增十一个模块均纳入默认构建；全库 1006 个声明通过传递公理检查。
  **这些构造尚未证明完整斜率协变：仍须证明自由多项式符号求值的 jet 系数表示、
  泛型分离和任意符号上的消失变分结论。主定理仍有一个 `sorry`。**

### 上一阶段

- 修复 `BinarySupport.lean` 中列表计数的四处 Lean 检查错误，保持定理陈述不变。
- 将此前未由入口导入的 `BinarySupport` 和 `SymbolSeries` 纳入默认库构建。
- 新增 [CentralTwist.lean](MakarLimanov/CentralTwist.lean)：在具体有理函数域上构造
  两个扩张导子，证明它们交换；构造非零特征向量，并证明相应符号为中心可逆元。
  `exists_extension` 给出实际扩张，`twist_properties` 给出星乘法下的中心性及双侧逆。
- 重新检查全部辅助库声明的传递公理，并单独暴露主定理的未完成状态。

## 现有形式化范围

| 模块 | 已检查的内容 |
|---|---|
| Statement、ScalarReduction、TwoGenerator、BinarySupport | 原题定义、标量分支、两生成元编码及归一化、零交换化的支撑性质 |
| Descent、MatrixDescent、BoundaryRank、Assembly | 基域下降、边界秩估计、给定见证后的最终组合 |
| DifferentialExtension、CommutingDerivations、PolynomialDerivations、LocalizedDerivations | 导子构造、分式域及可分扩张上的相容延拓 |
| CKStrip、AlgebraicBranch、GenericKernel | 交换微分条带、泛型代数根、核与不等式保持 |
| SymbolSeries、CentralTwist | Laurent 模型、无限星乘法及结合律、代数结构、系数扩张、指数格细化、中心扭曲 |
| Variations、SymbolVariations | 实际变分、有序卷积、有限阶数界、中心扭曲公式及其精确阶数平移 |
| GenericJets、JetTransform、GenericTwist、GenericSeparation | 泛型双微分扩域、可逆三角 jet 替换、公式 (3.8)、泛型性、具体模型中的非零性与单射性 |
| DifferentialCoefficients、SymbolSpecialization、JetPolynomialCoefficients、JetSpecialization | jet 多项式系数、非注入特化、星乘法相容、泛型值非零传递及支撑下界 |
| NewtonConstruction | Newton 数值预算、分母界、有限精度终止接口 |
| Numerics、Ramification | 条件性 Newton 数值预算及稀疏多项式因子次数界 |
| ControlledMatrix、Compression、Lattice、ControlledWitness | 受控无限矩阵代数、有限压缩、格点计数及给定受控逼近后的矩阵见证 |
| TaylorSeries、NormalOrdering | Taylor 同态及单射性、正规排序恒等式 |

## 主定理仍缺少的内容

1. 泛型符号分离、初始阶界和精确斜率协变。
2. 从任意相关微分多项式方程到现有条带/泛型根构造的完整接线。
3. 实际 Newton 修正与有限精度符号族；现有数值预算并不构造这些符号。
4. 从符号代数到受控无限矩阵代数的实际同态及支撑界；Taylor 和正规排序引理尚未组成这一实现。
5. 将上述构造连接到 `ControlledWitness`，消去逼近假设，证明 `NormalizedBinaryClaim`，
   最后填入 `Main.lean`。

原题陈述没有修改，未引入自定义公理。以上缺口没有被当成已经证明的事实。

## 验证

Lean：`leanprover/lean4:v4.30.0-rc1`。
mathlib 提交：`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`。

```sh
lake build
lake env lean FullAxiomAudit.lean
lake build MakarLimanov.Main
lake env lean MainAxiomAudit.lean
lake env lean VerifyComplete.lean
```

- 默认入口编译 36 个数学模块，不导入尚未证明的 `Main`。
- 显式构建辅助库和 `Main` 成功，但 `Main` 报告 `declaration uses sorry`。
- `FullAxiomAudit.lean` 检查 1006 个库声明（包括私有辅助声明及生成的声明），
  仅依赖 `propext`、`Classical.choice`、`Quot.sound`；这不是 1006 个公开定理的计数。

公开基建检索结论：mathlib 已有 Hahn/Laurent series、SummableFamily 和 SkewPolynomial；
但其 SkewPolynomial 文档明确将微分 Ore 关系 `X*a = φ(a)*X + δ(a)` 留作 TODO，
也没有现成的局部有限无限矩阵类型或本论文的 Newton 定理。因此当前项目的
`SymbolSeries`、`ControlledMatrix` 和 Newton 构造仍需自行证明，不能直接移植外部 Sage/Python
实现作为 Lean 证明。
- `MainAxiomAudit.lean` 显示主定理依赖 `sorryAx`。
- **`VerifyComplete.lean` 目前会失败**，明确报出 `sorryAx`。只有补全原题证明后才应通过。

机器可读结果见 [verification.json](verification.json)。旧 `AxiomAudit.lean` 和
`logs/axioms.log` 保留为早期核验记录，不代表当前整个工程的状态。

依赖仍采用本机 `SunMatrix/.lake/packages/` 内的绝对路径；本次移动不影响解析。
迁移到另一台机器时需将这些本地依赖改为对应提交的 Git 依赖并获取缓存。

## 来源

- 网站题目：`0e7dcc7f-6d6b-47e5-b157-1427684fbfab`。
- 原证明源码 SHA-256：`c0c6e2b60a71767774b1d51e9984d96fc64f6b10dbd60ecaef25b9b5fd7a47f4`。
- `review/` 中的旧人工审计是数学参考，不是 Lean 完成证书。
