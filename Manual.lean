/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Intro
import Manual.Elaboration
import Manual.Language
import Manual.Terms
import Manual.Tactics
import Manual.Simp
import Manual.BasicTypes

open Verso.Genre Manual

set_option pp.rawOnError true

/-
#doc (Manual) "The Lean Language Reference" =>
-/
#doc (Manual) "The Lean Language Reference 日本語訳" =>

**注意:** この翻訳は有志による **非公式** 翻訳です。原文の最新版は [こちら](https://lean-lang.org/doc/reference/latest/) です。

_CAUTION:_ This is an **Unofficial** translation by volunteers.
The latest version of original is [here](https://lean-lang.org/doc/reference/latest/).

This is the _Lean Language Reference_, an in-progress reference work on Lean.
It is intended to be a comprehensive, precise description of Lean: a reference work in which Lean users can look up detailed information, rather than a tutorial for new users.
For other documentation, please refer to the [Lean documentation site](https://lean-lang.org/documentation/).

{include Manual.Intro}

{include Manual.Elaboration}

{include Manual.Language}

{include Manual.Terms}

# Monads and `do`-Notation

:::planned 102
This chapter will describe `do`-notation in Lean:
 * Desugaring of `do` and its associated control structures
 * Comprehensive description of the syntax of `do`-notation
 * Definition of being in the "same `do`-block"
:::

# IO
:::planned 102
This chapter will describe features for writing programs that can have side effects on the real world.
:::

{include 0 Manual.Tactics}

{include 0 Manual.Simp}

{include 0 Manual.BasicTypes}

# Standard Library

:::planned 109
Overview of the standard library, including types from the prelude and those that require imports.
:::

## Optional Values
:::planned 110
Describe {name}`Option`, including the default coercions and its API.
:::


# Notations and Macros
%%%
tag := "language-extension"
%%%

## Notations

:::planned 69
A presentation of the `notation` command and how to define infix operators
:::

## Syntax Categories and Extensions

:::planned 70
 * Syntax extension and syntax categories
   * Precedence
:::


## Macros
%%%
tag := "macros"
%%%

:::planned 71
 * Definition of {deftech}_macro_
 * `macro_rules`
   * Syntax patterns
   * Backtracking on expansion failure
 * {deftech}[Hygiene] and quotation
 * The `macro` command
:::


## Elaborators
%%%
tag := "elaborators"
%%%

:::planned 72
For now, a quick overview of elaborators - detailed description to be written in a later revision
:::

# Elan

::: planned 74

This section will describe Elan and how to use it:

 * `lean-toolchain` files
 * `+`-syntax for toolchain selection
 * Specific overrides
 * Using a local development build of Lean with Elan
:::

# Lake and Reservoir

## Lake

::: planned 75
 * Port and organize the information in the Lake README
 * Describe the underlying Lake-specific concepts of traces, artifacts, workspaces, and facets
:::

## Reservoir

::: planned 76
 * Concepts
 * Package and toolchain versions
 * Tags and builds
:::

# Index
%%%
number := false
file := some "the-index"
%%%

{theIndex}

# この翻訳について

この翻訳は有志による **非公式** 翻訳です。翻訳に際して分かりやすさのために表現を大きく変えた箇所があります。また、用語の訳が一般的でない・誤りを含む可能性があります。必要に応じて原文 [Lean Language Reference](https://lean-lang.org/doc/reference/latest/)([GitHub](https://github.com/leanprover/reference-manual))をご覧ください。

原文にはライセンスが無かったため、原著者様より許諾をいただいて翻訳させていただいています。（[Zulip Chat](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.20thread.20for.20Lean.20Language.20Reference/near/478724278)）。

誤字脱字・内容の誤りの指摘・フォークからのPull Request・フォークによる翻訳の改変等歓迎いたします。ご指摘は [当該リポジトリ](https://github.com/lean-ja/reference-manual-ja) にてIssue・Pull Requestで受け付けております。

翻訳に際して、機械翻訳サービス [DeepL翻訳](https://www.deepl.com/ja/translator) を参考にしました。

この翻訳は原文のcommit [2fbf58d9210323e4ebc0a002d9f761074da462cf](https://github.com/leanprover/reference-manual/commit/2fbf58d9210323e4ebc0a002d9f761074da462cf) に基づいています。

::::::draft

:::progress
```namespace
String Char Nat Lean.Elab.Tactic
```
```exceptions
String.revFindAux String.extract.go₂ String.substrEq.loop String.casesOn
String.offsetOfPosAux String.extract.go₁ String.mapAux String.firstDiffPos.loop String.utf8SetAux String.revPosOfAux String.replace.loop
String.rec String.recOn String.posOfAux String.splitAux String.foldrAux
String.splitOnAux String.intercalate.go String.anyAux String.findAux
String.utf8GetAux? String.foldlAux String.utf8GetAux
String.utf8PrevAux String.noConfusionType String.noConfusion
String.utf8ByteSize.go String.validateUTF8.loop
String.crlfToLf.go
String.fromUTF8.loop
String.one_le_csize
```

```exceptions
String.sluggify
```

```exceptions
Nat.anyM.loop
Nat.nextPowerOfTwo.go
Nat.foldRevM.loop
Nat.foldM.loop
Nat.foldTR.loop
Nat.recAux
Nat.allTR.loop
Nat.allM.loop
Nat.anyTR.loop
Nat.anyM.loop
Nat.toSuperDigitsAux
Nat.casesAuxOn
Nat.forM.loop
Nat.repeatTR.loop
Nat.forRevM.loop
Nat.toSubDigitsAux
```

```exceptions
Nat.one_pos
Nat.not_lt_of_lt
Nat.sub_lt_self
Nat.lt_or_gt
Nat.pow_le_pow_left
Nat.not_lt_of_gt
Nat.le_or_le
Nat.le_or_ge
Nat.pred_lt'
Nat.pow_le_pow_right
Nat.lt_iff_le_and_not_ge
Nat.mul_pred_right
Nat.mul_pred_left
Nat.prod_dvd_and_dvd_of_dvd_prod
Nat.lt_iff_le_and_not_ge
Nat.mul_pred_right
```

```exceptions
Nat.binductionOn
Nat.le.rec
Nat.le.recOn
Nat.le.casesOn
Nat.le.below
Nat.le.below.step
Nat.le.below.rec
Nat.le.below.recOn
Nat.le.below.refl
Nat.le.below.casesOn
```

```exceptions
Lean.Elab.Tactic.evalUnfold.go
Lean.Elab.Tactic.dsimpLocation.go
Lean.Elab.Tactic.withCollectingNewGoalsFrom.go
Lean.Elab.Tactic.evalRunTac.unsafe_impl_1
Lean.Elab.Tactic.evalRunTac.unsafe_1
Lean.Elab.Tactic.evalTactic.handleEx
Lean.Elab.Tactic.simpLocation.go
Lean.Elab.Tactic.instToSnapshotTreeTacticParsedSnapshot.go
Lean.Elab.Tactic.dsimpLocation'.go
Lean.Elab.Tactic.withRWRulesSeq.go
Lean.Elab.Tactic.runTermElab.go
Lean.Elab.Tactic.getMainGoal.loop
Lean.Elab.Tactic.elabSimpArgs.isSimproc?
Lean.Elab.Tactic.elabSimpArgs.resolveSimpIdTheorem?
Lean.Elab.Tactic.tactic.dbg_cache
Lean.Elab.Tactic.tactic.simp.trace
Lean.Elab.Tactic.liftMetaTacticAux
```

```exceptions

Lean.Elab.Tactic.elabSetOption
Lean.Elab.Tactic.evalSeq1
Lean.Elab.Tactic.evalSimp
Lean.Elab.Tactic.evalSpecialize
Lean.Elab.Tactic.evalTacticAt
Lean.Elab.Tactic.evalSimpAll
Lean.Elab.Tactic.evalIntro.introStep
Lean.Elab.Tactic.evalDone
Lean.Elab.Tactic.evalRevert
Lean.Elab.Tactic.evalRight
Lean.Elab.Tactic.evalUnfold
Lean.Elab.Tactic.evalConstructor
Lean.Elab.Tactic.evalTacticCDot
Lean.Elab.Tactic.evalTraceMessage
Lean.Elab.Tactic.evalClear
Lean.Elab.Tactic.evalIntroMatch
Lean.Elab.Tactic.evalInduction
Lean.Elab.Tactic.evalApply
Lean.Elab.Tactic.evalUnknown
Lean.Elab.Tactic.evalRefl
Lean.Elab.Tactic.evalTactic.throwExs
Lean.Elab.Tactic.evalDSimp
Lean.Elab.Tactic.evalSepTactics.goEven
Lean.Elab.Tactic.evalAllGoals
Lean.Elab.Tactic.evalSplit
Lean.Elab.Tactic.evalInjection
Lean.Elab.Tactic.evalParen
Lean.Elab.Tactic.evalFocus
Lean.Elab.Tactic.evalLeft
Lean.Elab.Tactic.evalRotateRight
Lean.Elab.Tactic.evalWithReducible
Lean.Elab.Tactic.evalTactic.expandEval
Lean.Elab.Tactic.evalTraceState
Lean.Elab.Tactic.evalCase'
Lean.Elab.Tactic.evalSepTactics.goOdd
Lean.Elab.Tactic.evalWithReducibleAndInstances
Lean.Elab.Tactic.evalTacticSeqBracketed
Lean.Elab.Tactic.evalTactic.eval
Lean.Elab.Tactic.evalAlt
Lean.Elab.Tactic.evalGeneralize
Lean.Elab.Tactic.evalRewriteSeq
Lean.Elab.Tactic.evalSleep
Lean.Elab.Tactic.evalDSimpTrace
Lean.Elab.Tactic.evalReplace
Lean.Elab.Tactic.evalOpen
Lean.Elab.Tactic.evalAssumption
Lean.Elab.Tactic.evalSepTactics
Lean.Elab.Tactic.evalWithUnfoldingAll
Lean.Elab.Tactic.evalMatch
Lean.Elab.Tactic.evalRepeat1'
Lean.Elab.Tactic.evalFailIfSuccess
Lean.Elab.Tactic.evalRename
Lean.Elab.Tactic.evalFirst.loop
Lean.Elab.Tactic.evalSimpTrace
Lean.Elab.Tactic.evalFirst
Lean.Elab.Tactic.evalSubstVars
Lean.Elab.Tactic.evalRunTac
Lean.Elab.Tactic.evalSymmSaturate
Lean.Elab.Tactic.evalWithAnnotateState
Lean.Elab.Tactic.evalTacticAtRaw
Lean.Elab.Tactic.evalDbgTrace
Lean.Elab.Tactic.evalSubst
Lean.Elab.Tactic.evalNativeDecide
Lean.Elab.Tactic.evalCalc
Lean.Elab.Tactic.evalCase
Lean.Elab.Tactic.evalRepeat'
Lean.Elab.Tactic.evalRefine
Lean.Elab.Tactic.evalContradiction
Lean.Elab.Tactic.evalSymm
Lean.Elab.Tactic.evalInjections
Lean.Elab.Tactic.evalExact
Lean.Elab.Tactic.evalRotateLeft
Lean.Elab.Tactic.evalFail
Lean.Elab.Tactic.evalTactic
Lean.Elab.Tactic.evalSimpAllTrace
Lean.Elab.Tactic.evalRefine'
Lean.Elab.Tactic.evalChoice
Lean.Elab.Tactic.evalInduction.checkTargets
Lean.Elab.Tactic.evalIntro
Lean.Elab.Tactic.evalAnyGoals
Lean.Elab.Tactic.evalCases
Lean.Elab.Tactic.evalDelta
Lean.Elab.Tactic.evalDecide
Lean.Elab.Tactic.evalChoiceAux
Lean.Elab.Tactic.evalTacticSeq
Lean.Elab.Tactic.evalCheckpoint
Lean.Elab.Tactic.evalRenameInaccessibles
Lean.Elab.Tactic.evalIntros
Lean.Elab.Tactic.evalApplyLikeTactic
Lean.Elab.Tactic.evalSkip
Lean.Elab.Tactic.evalCalc.throwFailed
Lean.Elab.Tactic.evalSubstEqs
Lean.Elab.Tactic.evalTacticSeq1Indented
```

```exceptions
List.tacticSizeOf_list_dec
Lean.Parser.Tactic.tacticRefine_lift_
Lean.Parser.Tactic.tacticRefine_lift'_
Array.tacticArray_mem_dec
Lean.Parser.Tactic.normCast0
tacticClean_wf
Lean.Parser.Tactic.nestedTactic
Lean.Parser.Tactic.unknown
Lean.Parser.Tactic.paren
tacticDecreasing_trivial_pre_omega
```

:::

::::::
