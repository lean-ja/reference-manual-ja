/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.BasicTypes.Nat
import Manual.BasicTypes.String
import Manual.BasicTypes.Array

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


/-
#doc (Manual) "Basic Types" =>
-/
#doc (Manual) "基本的な型（Basic Types）" =>
%%%
tag := "basic-types"
%%%


:::comment
Lean includes a number of built-in types that are specially supported by the compiler.
Some, such as {lean}`Nat`, additionally have special support in the kernel.
Other types don't have special compiler support _per se_, but rely in important ways on the internal representation of types for performance reasons.

:::

Lean にはコンパイラが特別にサポートする組み込みの型が多数あります。 {lean}`Nat` のように、カーネルで特別にサポートされているものもあります。その他の型はコンパイラからの特別なサポート _自体_ はありませんが、パフォーマンス上の理由から型の内部表現に依存しています。

{include 0 Manual.BasicTypes.Nat}

# Integers
%%%
tag := "Int"
%%%

::: planned 104
 * Compile-time and run-time characteristics, and how they're inherited from {lean}`Nat`
 * API reference
:::

# Fixed-Precision Integer Types
%%%
tag := "fixed-ints"
%%%


::: planned 105
 * Compile-time and run-time characteristics for {lean}`UInt8`, {lean}`UInt16`, {lean}`UInt32`, {lean}`UInt64`
 * API reference
:::

# Bitvectors
%%%
tag := "BitVec"
%%%


:::planned 106
 * Run-time and kernel representations of {name}`BitVec`
 * API reference
 * Cross-reference to TBW chapter on `bv_decide`
:::

# Floating-Point Numbers
%%%
tag := "Float"
%%%


:::planned 107
 * Run-time and kernel representations
 * Precision, and whether it's platform-dependent
 * Relationship between IEEE floats and decidable equality
:::

:::comment
# Characters
:::

# 文字（Characters）
%%%
tag := "Char"
%%%



{docstring Char}

:::comment
## Syntax
:::

## 構文（Syntax）
%%%
tag := "char-syntax"
%%%



:::comment
## Logical Model
:::

## 論理モデル（Logical Model）
%%%
tag := "char-model"
%%%


:::comment
## Run-Time Representation
:::

## ランタイム表現（Run-Time Representation）
%%%
tag := "char-runtime"
%%%


:::comment
In monomorphic contexts, characters are represented as 32-bit immediate values. In other words, a field of a constructor or structure of type `Char` does not require indirection to access. In polymorphic contexts, characters are boxed.


:::

モノ射なコンテキストでは、文字は32ビットの即値として表現されます。言い換えると、`Char` 型のコンストラクタや構造体のフィールドにアクセスする際にインダイレクトは必要ありません。多相なコンテキストでは文字はボックス化されます。

:::comment
## API Reference
:::

## API リファレンス（API Reference）
%%%
tag := "char-api"
%%%



:::comment
### Character Classes
:::

### 文字クラス（Character Classes）
%%%
tag := "char-api-classes"
%%%



{docstring Char.isAlpha}

{docstring Char.isAlphanum}

{docstring Char.isDigit}

{docstring Char.isLower}

{docstring Char.isUpper}

{docstring Char.isWhitespace}


{include 0 Manual.BasicTypes.String}

# Linked Lists
%%%
tag := "List"
%%%


::: planned 108
 * Representation at compile time and run time
 * API reference
 * Literal syntax
 * Constructor/pattern syntax
:::


{include 0 Manual.BasicTypes.Array}


# Lazy Computations
%%%
tag := "Thunk"
%%%


::: planned 92
Description and API reference for {name}`Thunk`:
 * Logical model as wrapper around a function from {lean}`Unit`
 * Run-time realization as a lazy computation
 * API reference
:::

# Tasks and Threads
%%%
tag := "concurrency"
%%%


::: planned 90
Description and API reference for {name}`Task` and runtime threads, including {lean}`IO.Promise`

 * Scheduling model
 * Things to be careful of

This section may be moved to the section on {name}`IO` in particular.
:::
