/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

/-
#doc (Manual) "Functions" =>
-/
#doc (Manual) "関数（Functions）" =>
%%%
tag := "functions"
%%%


:::comment
Function types are a built-in feature of Lean.
{deftech}[Functions] map the values of one type (the {deftech}_domain_) into those of another type (the {deftech}_range_), and {deftech}_function types_ specify the domain and range of functions.
:::

関数型は Lean の組み込み機能です。 {deftech}[関数] （function）とはある型の値（ {deftech}_定義域_ 、domain）から別の型の値（ {deftech}_値域_ 、range）へとマッピングし、 {deftech}_関数型_ （function type） は関数の定義域と値域を指定します。

:::comment
There are two kinds of function type:
:::

関数型には2種類あります：

:::comment
 : {deftech}[Dependent]

   Dependent function types explicitly name the parameter, and the function's range may refer explicitly to this name.
   Because types can be computed from values, a dependent function may return values from any number of different types, depending on its argument.{margin}[Dependent functions are sometimes referred to as {deftech}_dependent products_, because they correspond to an indexed product of sets.]
:::

 : {deftech}[依存的] （dependent）

   依存関数の型はパラメータに明示的に名前を付け、関数の値域はこの名前を明示的に参照することができます。型は値から計算できるため、依存関数はその引数に応じて任意の数の異なる型の値を返すことができます。 {margin}[依存関数は集合の添字付き積に対応するため、 {deftech}_依存積_ （dependent product）と呼ばれることもあります。]

:::comment
 : {deftech}[Non-Dependent]

   Non-dependent function types do not include a name for the parameter, and the range does not vary based on the specific argument provided.
:::

 : {deftech}[非依存的] （non-dependent）

   非依存関数の型はパラメータの名前を含まず、提供される特定の引数によって値域が変わることはありません。

:::comment
::syntax term title:="Function types"
:::
::::syntax term title:="関数型"
:::comment
Dependent function types include an explicit name:
:::

依存関数の型は明示的な名前を含みます：

```grammar
($x:ident : $t) → $t2
```

:::comment
Non-dependent function types do not:
:::

非依存関数の型は含みません：

```grammar
$t1:term → $t2
```
::::

:::::keepEnv
:::comment
::example "Dependent Function Types"
:::
::::example "依存関数型"

:::comment
The function {lean}`two` returns values in different types, depending on which argument it is called with:

:::

関数 {lean}`two` はどの引数で呼び出されるかに応じて異なる型の値を返します：

```lean
def two : (b : Bool) → if b then Unit × Unit else String :=
  fun b =>
    match b with
    | true => ((), ())
    | false => "two"
```

:::comment
The body of the function cannot be written with `if...then...else...` because it does not refine types the same way that {keywordOf Lean.Parser.Term.match}`match` does.
:::

関数の本体は `if...then...else...` と書くことができません。なぜならこの書き方は {keywordOf Lean.Parser.Term.match}`match` と同じように型を絞り込むわけではないからです。

::::
:::::

:::comment
In Lean's core language, all function types are dependent: non-dependent function types are dependent function types in which the parameter name does not occur in the range.
Additionally, two dependent function types that have different parameter names may be definitionally equal if renaming the parameter makes them equal.
However, the Lean elaborator does not introduce a local binding for non-dependent functions' parameters.

:::

Lean のコア言語では、すべての関数型は依存的です：非依存関数型はパラメータ名が値域内に存在しない依存関数型のことです。さらに、パラメータ名が異なる2つの依存関数型について、パラメータ名をリネームしたものが等しい場合、これら2つは定義上等しくなります。しかし、Lean のエラボレータは非依存関数のパラメータにローカル束縛を導入しません。

:::comment
::example "Equivalence of Dependent and Non-Dependent Functions"
:::
::::example "依存・非依存関数の等価性"
:::comment
The types {lean}`(x : Nat) → String` and {lean}`Nat → String` are definitionally equal:
:::

型 {lean}`(x : Nat) → String` と {lean}`Nat → String` は定義上等価です：

```lean
example : ((x : Nat) → String) = (Nat → String) := rfl
```
:::comment
Similarly, the types {lean}`(n : Nat) → n + 1 = 1 + n` and {lean}`(k : Nat) → k + 1 = 1 + k` are definitionally equal:
:::

同様に、型 {lean}`(n : Nat) → n + 1 = 1 + n` と {lean}`(k : Nat) → k + 1 = 1 + k` は定義上等価です：


```lean
example : ((n : Nat) → n + 1 = 1 + n) = ((k : Nat) → k + 1 = 1 + k) := rfl
```
::::

::::::keepEnv
:::comment
::example "Non-Dependent Functions Don't Bind Variables"
:::
:::::example "非依存関数は変数を束縛しない"

::::keepEnv
:::comment
A dependent function is required in the following statement that all elements of an array are non-zero:
:::

以下の文では、配列のすべての要素が0でないことを示す依存関数が必要です：

```lean
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (lt : i < xs.size) → xs[i] ≠ 0
```
::::

::::keepEnv
:::comment
This is because the elaborator for array access requires a proof that the index is in bounds.
The non-dependent version of the statement does not introduce this assumption:
:::

これは配列アクセスのためのエラボレータが、インデックスが範囲内にあることの証明を必要とするためです。非依存バージョンの文では、この仮定は導入されていません：

```lean (error := true) (name := nondepOops)
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (i < xs.size) → xs[i] ≠ 0
```
```leanOutput nondepOops
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array Nat
i : Nat
⊢ i < xs.size
```
::::
:::::
::::::

:::comment
# Functions
:::

# 関数（Functions）
%%%
tag := "function-terms"
%%%



:::comment
Terms with function types can be created via abstractions, introduced with the {keywordOf Lean.Parser.Term.fun}`fun` keyword.

:::

関数型を持つ項は {keywordOf Lean.Parser.Term.fun}`fun` キーワードで導入される抽象によって作成することができます。

:::comment
::syntax term title:="Function Abstraction"
:::
::::syntax term title:="関数抽象"
:::comment
The most basic function abstraction introduces a variable to stand for the function's parameter:

:::

最も基本的な関数抽象では、関数のパラメータを表す変数を導入します：

```grammar
fun $x:ident => $t
```

:::comment
At elaboration time, Lean must be able to determine the function's domain.
A type ascription is one way to provide this information:

:::

エラボレーション時において、Lean は関数の定義域を決定できなければなりません。type ascription はこの情報を提供する1つの方法です：

```grammar
fun $x:ident : term => $t
```
::::

:::comment
Function definitions defined with keywords such as {keywordOf Lean.Parser.Command.declaration parser:=Lean.Parser.Command.definition}`def` desugar to {keywordOf Lean.Parser.Term.fun}`fun`.
However, not all functions originate from abstractions: {tech}[type constructors], {tech}[constructors], and {tech}[recursors] may have function types, but they cannot be defined using function abstractions alone.

:::

{keywordOf Lean.Parser.Command.declaration parser:=Lean.Parser.Command.definition}`def` のようなキーワードで定義された関数定義は {keywordOf Lean.Parser.Term.fun}`fun` に脱糖されます。しかし、すべての関数が抽象されたものではありません： {tech}[型コンストラクタ] ・ {tech}[コンストラクタ] ・ {tech}[再帰子] は関数型を持つ場合がありますが、関数抽象だけでは定義できません。

:::comment
# Currying
:::

# カリー化（Currying）
%%%
tag := "currying"
%%%



:::comment
In Lean's core type theory, every function maps each element of the domain to a single element of the range.
In other words, every function expects exactly one parameter.
Multiple-parameter functions are implemented by defining higher-order functions that, when supplied with the first parameter, return a new function that expects the remaining parameters.
This encoding is called {deftech}_currying_, popularized by and named after Haskell B. Curry.
Lean's syntax for defining functions, specifying their types, and applying them creates the illusion of multiple-parameter functions, but the result of elaboration contains only single-parameter functions.

:::

Lean のコア型理論では、すべての関数は定義域の要素をそれぞれ値域の単一の要素にマッピングします。言い換えれば、すべての関数は正確に1つのパラメータを必要とします。複数のパラメータを持つ関数は、高階関数を定義することで実装されます。これは最初のパラメータを与えると、残りのパラメータを持つ新しい関数を返します。このエンコーディングは {deftech}[カリー化] （currying）と呼ばれ、Haskell B. Curry にちなんで命名されました。関数を定義し、型を指定し、それを適用するための Lean の構文は、複数パラメータの関数のような錯覚を引き起こしますが、エラボレーションの結果は単一パラメータの関数のみが含まれます。

:::comment
::syntax term title:="Curried Functions"
:::
::::syntax term title:="カリー化された関数"

:::comment
Dependent Function types may include multiple parameters that have the same type in a single set of parentheses:
:::

依存関数型は同じ型を持つ複数のパラメータを1つの括弧の中に含めることができます：

```grammar
($x:ident* : $t) → $t
```
:::comment
This is equivalent to repeating the type annotation for each parameter name in a nested function type.

:::

これはネストされた関数型の各パラメータ名に対して、型注釈を繰り返すことと同じです。

:::comment
Multiple parameter names are accepted after after {keywordOf Lean.Parser.Term.fun}`fun`:
:::

{keywordOf Lean.Parser.Term.fun}`fun` の後に複数のパラメータ名を指定することができます：

```grammar
fun $x:ident* => $t
```

```grammar
fun $x:ident* : $t:term => $t
```

:::comment
These are equivalent to writing nested {keywordOf Lean.Parser.Term.fun}`fun` terms.
:::

これらは {keywordOf Lean.Parser.Term.fun}`fun` 項をネストして書くことと同じです。

::::


:::comment
# Implicit Functions
:::

# 暗黙の関数（Implicit Functions）
%%%
tag := "implicit-functions"
%%%



:::comment
Lean supports implicit parameters to functions.
This means that Lean itself can supply arguments to functions, rather than requiring users to supply all needed arguments.
Implicit parameters come in three varieties:

:::

Lean は関数への暗黙のパラメータをサポートしています。これはユーザが必要な引数をすべて与えるのではなく、Lean 自身が関数に引数を与えることができることを意味します。暗黙のパラメータには3種類あります：

:::comment
  : Ordinary implicit parameters

    Ordinary implicit parameters are function parameters that Lean should determine values for via unification.
    In other words, each call site should have exactly one potential argument value that would cause the function call as a whole to be well-typed.
    The Lean elaborator attempts to find values for all implicit arguments at each occurrence of a function.
    Ordinary implicit parameters are written in curly braces (`{` and `}`).

:::

  : 通常の暗黙のパラメータ

    通常の暗黙のパラメータとは、Lean が単一化によって値を決定すべき関数パラメータのことです。言い換えると、各呼び出し部位は、関数呼び出し全体が well-typed であるような潜在的な引数の値を1つだけ持つべきです。Lean のエラボレータは関数の各呼び出しですべての暗黙引数の値を見つけようとします。通常の暗黙の引数は波括弧（`{` と `}`）で囲んで記述します。

:::comment
  : Strict implicit parameters

    Strict implicit parameters are identical to ordinary implicit parameters, except Lean will only attempt to find argument values when subsequent explicit arguments are provided at a call site.
    Strict implicit parameters are written in double curly braces (`⦃` and `⦄`, or `{{` and `}}`).

:::

  : 厳格な暗黙のパラメータ

    厳格な暗黙のパラメータは通常の暗黙のパラメータと同じですが、Lean は呼び出し先で明示的な引数が指定された場合にのみ引数の値を見つけようとします。厳格な暗黙のパラメータは二重波括弧（`⦃` と `⦄` または `{{` と `}}`）で記述します。

:::comment
  : Instance implicit parameters

    Arguments for instance implicit parameters are found via {ref "instance-synth"}[type class synthesis].
    Instance implicit parameters are written in square brackets (`[` and `]`), and in most cases omit the parameter name because instances synthesized as parameters to functions are already available in the functions' bodies, even without being named explicitly.

:::

  : インスタンスの暗黙のパラメータ

    インスタンスの暗黙のパラメータの引数は {ref "instance-synth"}[型クラス合成] を介して見つけられます。インスタンスの暗黙のパラメータは角括弧（`[` と `]`）で囲まれ、ほとんどの場合パラメータ名は省略されます。というのも、パラメータとして関数に渡されるインスタンス合成は名前を明示的にしなくともすでに関数本体で利用可能であるからです。

:::::keepEnv
:::comment
::example "Ordinary vs Strict Implicit Parameters"
:::
::::example "通常と厳格な暗黙のパラメータ"
:::comment
The difference between the functions {lean}`f` and {lean}`g` is that `α` is strictly implicit in {lean}`f`:
:::

{lean}`f` と {lean}`g` の違いは、 {lean}`f` では `α` が厳密に暗黙であることです：

```lean
def f ⦃α : Type⦄ : α → α := fun x => x
def g {α : Type} : α → α := fun x => x
```

:::comment
These functions are elaborated identically when applied to concrete arguments:
:::

これらの関数は具体的な引数に適用された際には同一のものへエラボレートされます：

```lean
example : f 2 = g 2 := rfl
```

:::comment
However, when the explicit argument is not provided, uses of {lean}`f` do not require the implicit `α` to be solved:
:::

しかし、明示的な引数が与えられない場合、 {lean}`f` の使用は `α` を解決する必要はありません：

```lean
example := f
```
:::comment
However, uses of `g` do require it to be solved, and fail to elaborate if there is insufficient information available:
:::

しかし、`g` を使う際はこれを解決することが要求され、利用可能な情報が不十分な場合はエラボレートに失敗します：

```lean (error := true) (name := noAlpha)
example := g
```
```leanOutput noAlpha
don't know how to synthesize implicit argument 'α'
  @g ?m.6
context:
⊢ Type
```
::::
:::::


:::comment
::syntax term title := "Functions with Varying Binders"
:::
::::syntax term title := "束縛子が変化する関数"
:::comment
The most general syntax for {keywordOf Lean.Parser.Term.fun}`fun` accepts a sequence of binders:
:::

{keywordOf Lean.Parser.Term.fun}`fun` の最も一般的な構文は束縛子の列を受け入れます：

```grammar
fun $p:funBinder* => $t
```
::::


:::comment
::syntax Lean.Parser.Term.funBinder title:="Function Binders"
:::
::::syntax Lean.Parser.Term.funBinder title:="関数の束縛子"
:::comment
Function binders may be identifiers:
:::

関数の束縛子は以下のいずれかです。識別子：

```grammar
$x:ident
```
:::comment
sequences of identifiers with a type ascription:
:::

type ascription を持つ識別子の列：

```grammar
($x:ident $y:ident* : $t)
```
:::comment
implicit parameters, with or without a type ascription:
:::

type ascription がある・無い暗黙のパラメータ：

```grammar
{$x:ident*}
```
```grammar
{$x:ident* : $t}
```
:::comment
instance implicits, anonymous or named:
:::

無名・名前付きのインスタンスの暗黙のパラメータ：

```grammar
[$t]
```
```grammar
[$x:ident : $t]
```
:::comment
or strict implicit parameters, with or without a type ascription:
:::

type ascription がある・無い厳格な暗黙のパラメータ：

```grammar
⦃$t⦄
```
```grammar
⦃$x:ident* : $t⦄
```
::::


:::comment
Lean's core language does not distinguish between implicit, instance, and explicit parameters: the various kinds of function and function type are definitionally equal.
The differences can be observed only during elaboration.

:::

Lean のコア言語では暗黙・インスタンス・明示的なパラメータを区別しません：それぞれで書き直された関数とそれらの関数の型は定義上等しいです。これらの違いが観測されるのはエラボレーションの間のみです。

```lean (show := false)
-- Evidence of claims in next paragraph
example : ({x : Nat} → Nat) = (Nat → Nat) := rfl
example : (fun {x} => 2 : {x : Nat} → Nat) = (fun x => 2 : Nat → Nat) := rfl
example : ([x : Repr Nat] → Nat) = (Repr Nat → Nat) := rfl
example : (⦃x : Nat⦄ → Nat) = (Nat → Nat) := rfl
```

:::comment
# Pattern Matching

:::

# パターンマッチ（Pattern Matching）

::::syntax term
:::comment
Functions may be specified via pattern matching by writing a sequence of patterns after {keywordOf Lean.Parser.Term.fun}`fun`, each preceded by a vertical bar (`|`).
:::

関数は {keywordOf Lean.Parser.Term.fun}`fun` の後に、縦棒（`|`）で始まる一連のパターンを書くことでパターンマッチによって指定することができます。

```grammar
fun
  $[| $pat,* => $term]*
```
:::comment
This desugars to a function that immediately pattern-matches on its arguments.
:::

これは引数を即座にパターンマッチする関数に脱糖されます。

::::

:::::keepEnv
:::comment
::example "Pattern-Matching Functions"
:::
::::example "パターンマッチ関数"
:::comment
{lean}`isZero` is defined using a pattern-matching function abstraction, while {lean}`isZero'` is defined using a pattern match expression:
:::

{lean}`isZero` はパターンマッチ関数を抽象化して定義される一方、 {lean}`isZero'` はパターンマッチ式を使って定義されます：

```lean
def isZero : Nat → Bool :=
  fun
    | 0 => true
    | _ => false

def isZero' : Nat → Bool :=
  fun n =>
    match n with
    | 0 => true
    | _ => false
```
:::comment
Because the former is syntactic sugar for the latter, they are definitionally equal:
:::

前者は後者のための構文糖衣であるため、定義上等しいです：

```lean
example : isZero = isZero' := rfl
```
:::comment
The desugaring is visible in the output of {keywordOf Lean.Parser.Command.print}`#print`:
:::

脱糖結果は {keywordOf Lean.Parser.Command.print}`#print` の出力で見ることができます：

```lean (name := isZero)
#print isZero
```
:::comment
outputs
:::

上記は以下を出力し、

```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
:::comment
while
:::

一方で、

```lean (name := isZero')
#print isZero'
```
:::comment
outputs
:::

は以下を出力します。

```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
::::
:::::

:::comment
# Extensionality
:::

# 外延性（Extensionality）
%%%
tag := "function-extensionality"
%%%



:::comment
Definitional equality of functions in Lean is {deftech}_intensional_.
This means that definitional equality is defined _syntactically_, modulo renaming of bound variables and {tech}[reduction].
To a first approximation, this means that two functions are definitionally equal if they implement the same algorithm, rather than the usual mathematical notion of equality that states that two functions are equal if they map equal elements of the domain to equal elements of the range.

:::

Lean における関数の定義上の等価性は {deftech}_内包的_ （intensional）です。つまり、この定義上の等価性は、束縛変数のリネームと {tech}[簡約] によって _構文上_ （syntactically）で定義されます。大まかに言えば、これは2つの関数が同じアルゴリズムを実装していれば定義上等しいということを意味し、定義域の等しい要素を値域の等しい要素にマッピングしていれば等しいという通常の数学的な等値性の概念とは異なります。

:::comment
Intensional equality is mechanically decidable; Lean's type checker can decide whether two functions are intensionally equal.
Extensional equality is not decidable, so it is instead made available as reasoning principle when proving the {tech}[proposition] that two functions are equal.

:::

Lean の型チェッカは2つの関数が内包的に等しいかどうかを判断できます。外延的な等価性は決定できないため、代わりに2つの関数が等しいという {tech}[命題] を証明する時に推論原理として利用できるようにします。

::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : α → Type
axiom f : (x : α) → β x

-- test claims in next para
example : (fun x => f x) = f := by rfl
```

:::comment
In addition to reduction and renaming of bound variables, definitional equality does support one limited form of extensionality, called {deftech}_η-equivalence_, in which functions are equal to abstractions whose bodies apply them to the argument.
Given {lean}`f` with type {lean}`(x : α) → β x`, {lean}`f` is definitionally equal to {lean}`fun x => f x`
:::

束縛変数の簡約とリネームに加えて、 {deftech}[η同値] （η-equivalence）と呼ばれる外延性の1つの限定された形式をサポートします。これは関数はその本体が引数に適用する抽象と等しいことを指します。 {lean}`f` の型が {lean}`(x : α) → β x` であるとすると、 {lean}`f` は {lean}`fun x => f x` と定義上等価です。

::::

:::comment
When reasoning about functions, the theorem {lean}`funext`{margin}[Unlike some intensional type theories, {lean}`funext` is a theorem in Lean. It can be proved using {tech}[quotient] types.] or the corresponding tactics {tactic}`funext` or {tactic}`ext` can be used to prove that two functions are equal if they map equal inputs to equal outputs.

:::

関数について推論するとき、定理 {lean}`funext`{margin}[いくつかの拡張された型理論とは異なり、 {lean}`funext` は Lean における定理です。これは {tech}[quotient] 型を使って証明できます。] または対応するタクティク {tactic}`ext` を使用して、2つの関数が等しい入力を等しい出力にマッピングする場合に等しいことを証明することができます。

{docstring funext}

:::comment
# Totality and Termination
:::

# 全域性と停止（Totality and Termination）
%%%
tag := "totality"
%%%



:::comment
Functions can be defined recursively using {keywordOf Lean.Parser.Command.declaration}`def`.
From the perspective of Lean's logic, all functions are {deftech}_total_, meaning that they map each element of the domain to an element of the range in finite time.{margin}[Some programming language communities use the term _total_ in a more restricted sense, where functions are considered total if they do not crash but non-termination is ignored.]
The values of total functions are defined for all type-correct arguments, and they cannot fail to terminate or crash due to a missing case in a pattern match.

:::

関数は {keywordOf Lean.Parser.Command.declaration}`def` を使って再帰的に定義することができます。Lean の論理の観点から、すべての関数は {deftech}_全域_ （total）です。これは関数が定義域の各要素を値域の要素に有限時間でマッピングすることを意味します。 {margin}[プログラミング言語のコミュニティによっては、より限定的な意味で _全域_ という用語を使用するものもあり、その場合、関数はクラッシュしなければ全域と見なされますが、非停止は無視されます。] 全域関数の値はすべての型が正しい引数に対して定義され、パターンマッチでケースが漏れて停止に失敗したりクラッシュしたりすることはありません。

:::comment
While the logical model of Lean considers all functions to be total, Lean is also a practical programming language that provides certain "escape hatches".
Functions that have not been proven to terminate can still be used in Lean's logic as long as their range is proven nonempty.
These functions are treated as uninterpreted functions by Lean's logic, and their computational behavior is ignored.
In compiled code, these functions are treated just like any others.
Other functions may be marked unsafe; these functions are not available to Lean's logic at all.
The section on {ref "partial-unsafe"}[partial and unsafe function definitions] contains more detail on programming with recursive functions.

:::

Lean の論理モデルはすべての関数を全域関数と見なしますが、Lean は実用的なプログラミング言語でもあり、ある種の「逃げ道」を用意しています。停止することが証明されていない関数は、その値域が空でないことが証明されている限り Lean の論理で使用することができます。これらの関数は Lean の論理では未解釈の関数として扱われ、その計算動作は無視されます。コンパイルされたコードでは、これらの関数は他の関数と同様に扱われます。そうではない関数は unsafe とマークされることがあります；これらの関数は Lean の論理では全く使用することができません。 {ref "partial-unsafe"}[partial と unsafe 関数定義] の節で再帰関数を使ったプログラミングの詳細があります。

:::comment
Similarly, operations that should fail at runtime in compiled code, such as out-of-bounds access to an array, can only be used when the resulting type is known to be inhabited.
These operations result in an arbitrarily chosen inhabitant of the type in Lean's logic (specifically, the one specified in the type's {name}`Inhabited` instance).

:::

同様に、配列への範囲外アクセスなど、コンパイルされたコードではランタイムに失敗するはずの操作は、結果の型が inhabited であることが分かっている場合にのみ使用することができます。これらの操作の結果、Lean のロジックでは型の住人が任意に選ばれます（具体的には、その型の {name}`Inhabited` インスタンスで指定されたもの）。

:::comment
::example "Panic"
:::
::::example "パニック"
:::comment
The function {name}`thirdChar` extracts the third element of an array, or panics if the array has two or fewer elements:
:::

関数 {name}`thirdChar` は配列の3番目の要素を取り出します。配列の要素が2個以下の場合はパニックになります：

```lean
def thirdChar (xs : Array Char) : Char := xs[2]!
```
:::comment
The (nonexistent) third elements of {lean}`#['!']` and {lean}`#['-', 'x']` are equal, because they result in the same arbitrarily-chosen character:
:::

{lean}`#['!']` と {lean}`#['-', 'x']` の（存在しない）3番目の要素は等しいです。なぜなら、どちらも同じ任意に選ばれた文字を返すからです：

```lean
example : thirdChar #['!'] = thirdChar #['-', 'x'] := rfl
```
:::comment
Indeed, both are equal to {lean}`'A'`, which happens to be the default fallback for {lean}`Char`:
:::

実際、どちらも {lean}`'A'` に等しく、これは偶然にも {lean}`Char` のデフォルトのフォールバックです：

```lean
example : thirdChar #['!'] = 'A' := rfl
example : thirdChar #['-', 'x'] = 'A' := rfl
```
::::
