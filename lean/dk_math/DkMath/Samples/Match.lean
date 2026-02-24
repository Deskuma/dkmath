/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- match 式のサンプル。単純な例を示すため、DkMath の他のモジュールはインポートしない。

namespace DkMath.Samples.Match

/- ## Sample 解説

以下の型を定義して、型マッチングの例を示す。

- Unit := Gap, Hole, Ud
- Value := Body, Number, Vd
- NumberUniverse := Big, Universe, Nu

-/

inductive Unit where
  | Gap
  | Hole
  | Ud
deriving Repr

inductive Value where
  | Body
  | Number
  | Vd
deriving Repr

inductive NumberUniverse where
  | Big
  | Universe
  | Nu
deriving Repr

def matchUnit (u : Unit) : String :=
  match u with
  | Unit.Gap => "Matched Gap!"
  | Unit.Hole => "Matched Hole!"
  | Unit.Ud => "Matched Ud!"

def matchValue (v : Value) : String :=
  match v with
  | Value.Body => "Matched Body!"
  | Value.Number => "Matched Number!"
  | Value.Vd => "Matched Vd!"

def matchNumberUniverse (n : NumberUniverse) : String :=
  match n with
  | NumberUniverse.Big => "Matched Big!"
  | NumberUniverse.Universe => "Matched Universe!"
  | NumberUniverse.Nu => "Matched Nu!"

#eval matchUnit Unit.Gap  -- "Matched Gap!"
#eval matchUnit Unit.Hole  -- "Matched Hole!"
#eval matchUnit Unit.Ud  -- "Matched Ud!"

#eval matchValue Value.Body  -- "Matched Body!"
#eval matchValue Value.Number  -- "Matched Number!"
#eval matchValue Value.Vd  -- "Matched Vd!"

#eval matchNumberUniverse NumberUniverse.Big  -- "Matched Big!"
#eval matchNumberUniverse NumberUniverse.Universe  -- "Matched Universe!"
#eval matchNumberUniverse NumberUniverse.Nu  -- "Matched Nu!"

def matchExample (u : Unit) (v : Value) (n : NumberUniverse) : String :=
  match u, v, n with
  | Unit.Gap, Value.Body, NumberUniverse.Big => "Matched Gap, Body, Big!"
  | Unit.Hole, Value.Number, NumberUniverse.Universe => "Matched Hole, Number, Universe!"
  | Unit.Ud, Value.Vd, NumberUniverse.Nu => "Matched Ud, Vd, Nu!"
  | _, _, _ => "No match found."

#eval matchExample Unit.Gap Value.Body NumberUniverse.Big  -- "Matched Gap, Body, Big!"
#eval matchExample Unit.Hole Value.Number NumberUniverse.Universe  -- "Matched Hole, Number, Universe!"
#eval matchExample Unit.Ud Value.Vd NumberUniverse.Nu  -- "Matched Ud, Vd, Nu!"
#eval matchExample Unit.Gap Value.Number NumberUniverse.Big  -- "No match found."

end DkMath.Samples.Match

/- match 式の利用どころ

説明：
match 式は、型の値に対してパターンマッチングを行うための構文です。
これにより、異なるケースに対して異なる処理を記述できます。
上記の例では、Unit、Value、NumberUniverse という3つの異なる型を定義し、
それぞれに対して match 式を使用して特定の文字列を返す関数を作成しました。

利用例：
- データ構造の解析：複雑なデータ構造を持つ場合、match 式を使用して特定のパターンに基づいて処理を分岐させることができます。
- エラー処理：エラーコードや状態を表す型に対して match 式を使用して、異なるエラーや状態に対する処理を記述できます。
- ユーザー入力の処理：ユーザーからの入力を特定のパターンに基づいて処理する場合、match 式を使用して入力の種類に応じた処理を行うことができます。
- 状態遷移の管理：状態遷移を表す型に対して match 式を使用して、異なる状態に対する処理を記述できます。
- パターンマッチングの例：複数の型や値の組み合わせに対して、特定のパターンに基づいて処理を分岐させることができます。
- データの分類：データを特定のカテゴリに分類する場合、match 式を使用して、異なるカテゴリに対する処理を記述できます。
- ロジックの分岐：複数の条件に基づいてロジックを分岐させる場合、match 式を使用して、異なる条件に対する処理を記述できます。
- 可読性・保守性・安全性・効率性・柔軟性・再利用性が向上します。
-/
