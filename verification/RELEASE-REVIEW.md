# 发布前复审

> 本报告是 2026-10-11 发布前检查结束时的历史快照，当时尚未创建公开仓库或发送 scope 询问。
> 后续公开版本与线上 CI 入口见 [PUBLICATION.md](PUBLICATION.md)。

公开项目作者与维护者：**wang060919**。日期：2026-10-11（Asia/Shanghai）。
计划仓库：`wang060919/jsp-000936-unit-circle-lean`。

**本地发布准备已完成，正式源码和整套本地验证已通过。** GitHub Actions 配置已就绪，尚未在线执行；按用户要求，未 push，也未提交官方 awards PR。

## 已完成事项

| 项目 | 结果 |
| --- | --- |
| 公开身份 | README、79 个 Lean 文件头、AUTHORS、PROVENANCE 和验证报告统一使用 `wang060919` |
| 新增代码许可 | 根 LICENSE 采用 MIT，版权署名 `wang060919` |
| 第三方归属 | 七个复用模块完整保留原 MIT 文本、Ethan Yang / randyxian08 原版权与固定来源 |
| 数学来源 | 原始单位圆论文、历史作者与复用 generic kernels 单独归属；Codex 的真实协助记录在 AUTHORS |
| 本机工具依赖 | `.tools` 改为可选；正确 Elan/PATH 可运行全部审计；Lean 版本、release commit 和 Lake 版本均校验 |
| CI | 固定官方 Action SHA，执行 build、771 项公理、五项原始陈述、fresh replay 与完整文件清单检查 |
| 文件完整性 | SHA256SUMS 配套 verifier 同时检测内容变化、遗漏文件和新增 Git-tracked 文件 |
| 数学证明 | 每个原 Lean 文件正文逐字节保留，只增加作者和来源注释 |

## 实际验证

- 正式版本编译、公理审计和原始陈述检查退出码 0；77 个模块、771 项公开定理和五项 literal challenge 全部通过。
- 最终模块及导入常量的 fresh kernel replay 退出码 0，耗时 265.32 秒。
- 隔离目录无 `.tools`、无项目编译缓存起步；只复用固定依赖缓存，77 个模块及入口全部新编译，完整审计退出码 0，耗时 89.26 秒。
- 79 个当前 Lean 输入的源码哈希与编译/隔离审计证书一致。完整 Target 只依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 对先前实际问题做临时回归探针：混用 Lake/Lean 被拒绝；内容修改、清单遗漏和新增 Git-tracked 文件遗漏均被拒绝。
- Workflow 语法、固定 Action 的真实参数、只读权限和执行步骤已核查。上述本地结果不冒充 GitHub CI 已绿。

完整证据见 [REPORT.md](REPORT.md) 和 `evidence/`。仍有三项原有 MarkovKernel API 弃用警告，未引入新的证明失败。

## 公开前后边界

本轮未初始化正式 Git 仓库、未创建正式提交、未发布仓库、未 push、未提交官方 awards PR或联系主办方。临时清单回归探针在本任务创建的 `/tmp` 测试目录使用了本地 Git 索引，未创建 commit 或对外发布。

以后公开时，应使用准确的公开身份及仓库名，保存完整 40 位 verified commit SHA，实际运行 GitHub CI，并从该 SHA 的独立 checkout 复现。只有届时的真实记录才能填写 CI URL、公开完成时间与优先权证据。

单位圆变体是否获主办方接受、AI-assisted 贡献的奖项作者认定与获奖资格仍未确定；署名统一不能代替官方审核。
