# 论文与当前 Lean 工程的对应

依据两版论文直接替换关键步骤后的正文编号，路径相对 `lean/`。本表是实现定位，不是数学正文全面核查完成的声明。
正文保留 3.1—3.23，表 1 按这些编号重映射；不再保留 3.1'、3.8'、独立贡献 (4) 或重复附录 A。
Lean 源码、配置、版本锁与源码映射保持不变，`GAC/Reformulated/` 只是内部模块名。
历史 review 记录及 Lean 注释中的旧编号保留为原验证快照，当前编号以本表为准。
当前 82 个工程模块加根审计共 83 个源文件；71 个模块改编自上游，来源、许可及旧新路径见
[SOURCE_MAP.md](SOURCE_MAP.md) 和 [source-map.json](source-map.json)。
`GAC.Paper` 的接口为透明缩写或已证明包装，不更改底层定义。

## 主证明对应

下表短名除显式命名空间外相对于 `GAC.Persistence`，文件相对于 `GAC/Persistence/`。

| 论文位置 | 当前声明／接口 | 当前文件 |
| --- | --- | --- |
| 第 2 节 | `ReactionNetwork`、`WeaklyReversible`、`massAction`、`PositiveState`、`IsGlobalForwardSolution` | `Model/Network.lean` |
| 定理 3.1：存在全局解，所有解正且共享对数界 L≥0 | `GAC.Reformulated.wr_trajectory_log_bound`；`bounded_persistent_of_weaklyReversible` | `GAC/Reformulated/Interfaces.lean` 给存在性与共同界；`BoundedPersistence.lean` 给显式正性 |
| 引理 3.2 | `Cuts.cut_flux_nonneg_of_ordered_sources`、`massAction_points_inward_of_order` | `Flux/DirectedCuts.lean`、`Flux/InwardDirections.lean` |
| 引理 3.3 | `monomial_bound_of_exponent_gap` | `Asymptotics/MonomialComparison.lean` |
| 引理 3.4 | `exists_sign_margin_function`、`exists_uniform_sign_gap` | `Asymptotics/SignMargins.lean` |
| 命题 3.5 | `Affine.uniform_data_of_full_certificates`；`GAC.Paper.uniform_affine_approximation` | `Approximation/Uniform/UniformData.lean`；`GAC/Paper.lean` |
| 命题 3.6（B3 只形式化活跃支斜率非负；整盒线段形式由正文应用引理 3.8 得到） | `Barrier.exists_barrier_data`；`GAC.Paper.exists_minBarrierSpec`；旧 `inward_on_box` 与一般可行性判据 | `Barrier/Construction.lean`；`GAC/Paper.lean`；B3 每点 z∈Bₕ 各有 ε(z)>0，所有 0≤s≤ε(z) 的 z+s f(z) 留在 {F≥F(z)}，不是统一步长 |
| 引理 3.7 | `Barrier.BarrierData.plateau_subset_interior_box`、`.isCompact_plateau` | `Barrier/PlateauCompactness.lean` |
| 引理 3.8：任意有限仿射约束的紧约束斜率非负 iff 短线段可行 | `GAC.Reformulated.feasible_direction_iff_tight` | `GAC/Reformulated/FeasibleDirections.lean`；旧 A.3 的直接证明，含空约束 |
| 引理 3.9：F 全局 Lipschitz＋曲线一阶误差→Dini 非负→单调 | `finite_minimum_monotone_of_active_slopes` | `Confinement/MinimumMonotonicity.lean`；原形式化用有限最小值单调性取得相同约束结论，没有新手写 Lipschitz／Dini 链的逐字接口 |
| 引理 3.10：沿上述链作首次退出 | `Confinement.forward_solution_trapped` | `Confinement/SegmentTrapping.lean`、`Confinement/ForwardInvariance.lean`；原形式化陷俘链，不声称逐行验证新手写路径 |
| 引理 3.11 | `global_solution_of_compact_trap`、`global_massAction_of_compact_trap` | `ODE/GlobalExtension.lean`、`ODE/CompactTrapping.lean` |
| 引理 3.12 | `Affine.exists_full_certificate` | `Approximation/Gluing/FullExistence.lean` 及其导入；证书定义在 `Approximation/Layers/Certificates.lean` |
| 推论 3.13 | `Affine.FullCertificate.uniform_activity_bound` | `Approximation/Uniform/FromFullCertificates.lean` |

下表短名相对于 `GAC.Paper`，除另注外位于 `GAC/Paper.lean`，核心证明在 `GAC/DetailedBalance.lean`。

| 论文位置 | 当前声明／接口 | 备注 |
| --- | --- | --- |
| 定义与主定理陈述 | `CRN`、`RxnIdx`、`rateField`、`reactionSpan`、`SolvesForward`、`DBCondition` | 透明接口与细致平衡结构 |
| 引理 2.3 | `strongConn_of_hasReverses` | 可逆推出弱可逆 |
| 引理 3.14 | `trajectory_in_coset` | 相容类 |
| 推论 3.15：K=[exp(−L),exp L]^d ∩ (x₀+S) | `GAC.exists_compact_class_container`；`GAC.Reformulated.wr_trajectory_log_bound` | `GAC/CompactClass.lean`；`GAC/Reformulated/Interfaces.lean`；正文采用对数界构造 K，既有容器接口不声称整个盒子正向不变 |
| 引理 3.16 | `entropyFn_ge_zero`、`entropyFn_deriv`、`entropyRate_continuous` | 熵与导数 |
| 引理 3.17 | `entropyRate_double`、`entropyRate_le_zero` | 耗散恒等式与非正性 |
| 引理 3.18：正平衡点集＝零耗散集＝{x*⊙exp u : u∈S⊥}，参数唯一 | `entropyRate_eq_zero_iff`、`logGap_vanish_of_rate_zero`、`rateField_zero_of_logGap`；`GAC.Reformulated.positive_equilibria_eq_exp_normal`、`.exponential_parameter_unique` | 已有零耗散接口与 `GAC/Reformulated/Equilibria.lean` 合用，三集相等由两组声明合用给出，无单一声明 |
| 引理 3.19：设 a=x*⊙exp u、b=x*⊙exp v 证类内唯一性 | `GAC.Reformulated.equilibria_unique_of_exp_parameterization` | `GAC/Reformulated/Interfaces.lean`；旧 `unique_of_logGap`、`equilibria_coincide` 仍保留 |
| 引理 3.20 | `entropyRate_zero_at_accumulation` | 使用速度有界的下降论证 |
| 定理 1.1／3.21 | `db_unique_equilibrium_attracts` | 底层 `GAC.detailed_balanced_global_convergence` |
| 第 5.1 节 | `GAC.PaperExample.net_detailed_balanced`、`.total_conserved`、`.equilibrium_is_equilibrium`、`.equilibrium_total`、`.tends_to_equilibrium_of_total_eq_three` | `GAC/PaperExample.lean` |
| 图 1 五组初值 | `GAC.PaperExample.figure_initial_states_positive`、`.figure_initial_states_total`、`.figure_initial_states_converge` | 同上；精确有理数，不验证数值求解器 |
| 原有 A ⇌ B 例子 | `GAC.Example.convergence` | `GAC/Example.lean` |

## 正文步骤的直接证明、桥接与历史编号

以下短名均相对于 `GAC.Reformulated`，文件相对于 `GAC/Reformulated/`。
前三份直接证明不调用原全局收敛定理；通量、耗散恒等式和 Mathlib 基础结论正常复用。
`Interfaces.lean` 则明确将它们接回已有网络定理。

| 论文位置 | 当前声明 | 文件及覆盖边界 |
| --- | --- | --- |
| 定理 3.1／推论 3.15（旧 A.1／A.2） | `compact_positive_iff_log_bound`、`solution_family_log_confinement` | `Compactness.lean`；正紧包含与对数界，解族正性与存在性量词显式保留 |
| 引理 3.8（旧 A.3） | `feasible_direction_iff_tight` | `FeasibleDirections.lean`；有限可空仿射约束，不含方向导数公式 |
| 引理 3.18（旧 A.4） | `positive_equilibria_eq_exp_normal`、`exponential_parameter_unique` | `Equilibria.lean`；整个正平衡点集与唯一参数，不独立证明相容类内存在性 |
| 定理 3.1（旧 3.1'） | `wr_trajectory_log_bound` | `Interfaces.lean`；存在性与所有解的共同对数界，显式正性另用原有有界持久性定理 |
| 引理 3.8 的平台特例（旧 3.8' 平台条件） | `plateau_active_iff_tight` | 同上；平台上活跃支恰为紧约束 |
| 引理 3.8 的平台特例（旧 3.8' (i)↔(iv)） | `plateau_feasible_direction_iff_active` | 同上；在已构造屏障的平台上应用一般判据 |
| 命题 3.6 (B3) 的平台特例 | `plateau_massAction_feasible` | 同上；非 whole-box B3 的完整接口，亦非完整 ODE 不变性等价 |
| 引理 3.19（旧 A.4 的应用） | `equilibria_unique_of_exp_parameterization` | 同上；指数参数化推出同相容类正平衡点唯一性 |

当前改写部分 5 模块共 421 行：`Compactness` 85、`FeasibleDirections` 64、`Equilibria` 126、
`Interfaces` 119、`Audit` 27。独立入口审计 16 条直接证明声明和上述 5 条桥接声明，共 21 条。
它们不由 `import GAC` 自动导入，须显式导入相应模块。

## 验证与未覆盖范围

82 个工程模块全量源码编译 95 秒通过，根入口 14 条与独立入口 21 条公理审计约 12 秒通过。
来源映射当前哈希之后作元数据修正，不改变已验证 Lean 证明。

完整方向导数等价、一般 Dini 导数原文陈述、引理 3.18 三集相等的单一声明、推论 3.23 的类内渐近稳定性、
一般 Wegscheider 判据、任意速率例子、边界初值／siphon 讨论、闭正卦限熵扩展、复平衡推广、数值积分均不在已声明的 Lean 覆盖范围内。
不要将部分充分条件、局部可行性或全量编译通过表述成全文数学审查完成。
已有直接证明与桥接已编译核验，但三项正文替换不能一概称为新路径已全部逐行机器验证；
尤其 3.9—3.10 的新手写 Lipschitz／Dini 论证只有原形式化约束结论链可供对应。

## 补充定位符

论文第 4.3 节删去了下列实现层定位，保留在这里：`GAC.Paper.logQuot` 表示 L_y，`entropyFn` 与 `entropyRate` 表示 V 与 D，
`GAC.monomial_ratio` 给出第 3.2 节的单项式恒等式，`GAC.sum_revR` 在引理 3.17 中按逆反应重排求和；
命题 3.6 的比较方向集为 `Barrier.comparisonDirections`，命题 3.5 的仿射逼近接口类型为 `Barrier.UniformAffineApproximation`；
定理 3.21 的紧性步骤使用 Mathlib 的 `IsCompact.exists_mapClusterPt` 与 `IsCompact.tendsto_nhds_of_unique_mapClusterPt`。

## 模块清单

论文第 4 节不再列出逐模块清单，原表 2 移到这里。括号内为含注释与空行的行数；持久性各行目录相对 `GAC/Persistence/`。
71 个持久性模块 7,900 行，6 个主证明模块 956 行，5 个坐标／几何接口模块 421 行，根 `Audit.lean` 另有 31 行。
`Approximation/Layers/ConstantLabels.lean`、`Approximation/Local/PositiveLimitSets.lean` 与 `Approximation/Gluing/IntervalChains.lean` 是主定理依赖闭包之外的替代写法。

| 目录／部分 | 模块（行数） |
| --- | --- |
| `Confinement` | `ActiveBranches` (138), `MinimumAlongCurves` (156), `ForwardInvariance` (85), `SegmentTrapping` (79), `MinimumMonotonicity` (139), `LabelTrapping` (60) |
| `Approximation/Local` | `ActivityLimitSets` (105), `PositiveLimitSets` (144), `MinimumBand` (103), `AsymptoticActivity` (183), `CubeNeighborhood` (112), `CertificateRadius` (45), `OffsetDecay` (88) |
| `Approximation/Uniform` | `ActivityCompactness` (181), `FromFullCertificates` (43), `SequentialBounds` (74), `UniformData` (68) |
| `Approximation/Layers` | `LocalFromLabels` (36), `Certificates` (166), `LayerCertificates` (268), `LocalFromLayers` (53), `LocalFromLowerDimension` (39), `SubcubeEmbedding` (222), `Labels` (167), `ConstantLabels` (168), `RelativeEstimates` (270), `LayerChain` (55), `TypeFamilies` (137), `TypeLayers` (99) |
| `Approximation/Gluing` | `FullFromLocal` (56), `FullExistence` (38), `ShiftedFamilies` (233), `FamilyAssembly` (193), `GlobalGluing` (310), `CutComparison` (170), `FullExistenceAlternative` (24), `LocalToGlobal` (65), `IntervalChains` (233), `OrderedCovers` (222) |
| `Barrier` | `LabelPolytope` (78), `PlateauCompactness` (116), `FiniteLabelData` (50), `Construction` (170), `ConstantBranch` (85), `PlateauTopology` (119), `Polyhedra` (156), `LogBox` (73) |
| `Asymptotics` | `DotSignGap` (65), `VariableExponents` (127), `MonomialComparison` (167), `PowerRatios` (96), `SignMargins` (119), `ParameterChoice` (152) |
| `ODE` | `LipschitzExtension` (75), `PositiveBounds` (47), `CompactTrapping` (60), `InvariantBounds` (40), `FirstBoundaryTime` (69), `PiecewiseDerivative` (72), `LocalSolutions` (63), `Concatenation` (87), `GlobalExtension` (134), `Uniqueness` (72), `TrajectoryUniqueness` (50) |
| `Flux` | `LevelIntegral` (59), `DirectedCuts` (135), `InwardDirections` (68) |
| `Persistence (root)` | `BoundedPersistence` (92) |
| `Model` | `LinearFunctionals` (64), `Smoothness` (35), `Network` (78) |
| Main proof and examples | `GAC/PaperExample` (166), `GAC/CompactClass` (52), `GAC/DetailedBalance` (501), `GAC/Example` (50), `GAC/Paper` (183), `GAC` (4) |
| `GAC/Reformulated/` | `Audit` (27), `Compactness` (85), `Equilibria` (126), `FeasibleDirections` (64), `Interfaces` (119) |
