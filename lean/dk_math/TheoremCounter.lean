/-
  Lean 定理、命題・補題の総数カウント
-/
-- Author D. and Wise Wolf
-- 2026/06/28  6:10

-- import Lean
-- import Mathlib
import DkMath

-- theorem one_is_one : 1 = 1 := by decide  -- コメントを外せばこの１件もカウントされる（テスト用）

#eval do  -- ここにカーソルを合わせると右に数が出ます
  let env ← Lean.getEnv  -- Lean の環境を取得
  let decls := env.constants.fold (
    fun (acc : List Lean.Name) (name : Lean.Name) (info : Lean.ConstantInfo) =>
    match info with
    | Lean.ConstantInfo.thmInfo _ => name :: acc
    | _ => acc
    ) []
  pure decls.length

#eval do
  let env ← Lean.getEnv
  let ns : Lean.Name := `DkMath
  let decls := env.constants.fold (
    fun (acc : List Lean.Name) (name : Lean.Name) (info : Lean.ConstantInfo) =>
    match info with
    | Lean.ConstantInfo.thmInfo _ =>
      if ns.isPrefixOf name then name :: acc else acc
    | _ => acc
  ) []
  pure decls.length

/-
DkMath Theorems
506113 - 498084 = 8029 件
Lean+Mathlib Theorems
498084 件
-/

set_option linter.style.longLine false
-- ----------------------------------------------------------------------------
/- サマリースクリプトへの追加案件 -/
/-
echo "# Summary counts" > logs/summary_report/__counts.txt

printf "theorem: " >> logs/summary_report/__counts.txt
grep -E '^[0-9]+:theorem\b' logs/summary_report/__theorems-heading.txt | wc -l >> logs/summary_report/__counts.txt

printf "lemma: " >> logs/summary_report/__counts.txt
grep -E '^[0-9]+:lemma\b' logs/summary_report/__theorems-heading.txt | wc -l >> logs/summary_report/__counts.txt

printf "def: " >> logs/summary_report/__counts.txt
grep -E '^[0-9]+:def\b' logs/summary_report/__theorems-heading.txt | wc -l >> logs/summary_report/__counts.txt

printf "theorem+lemma+def: " >> logs/summary_report/__counts.txt
grep -E '^[0-9]+:(theorem|lemma|def)\b' logs/summary_report/__theorems-heading.txt | wc -l >> logs/summary_report/__counts.txt
-/

/-
generated_at: 2026-06-28 06:10 JST
snapshot: <git hash or snapshot name>

Lean thmInfo total:
  DkMath: 7798

Source heading counts:
  theorem:
  lemma:
  def:
  theorem + lemma:
  theorem + lemma + def:
-/

/-
import DkMath

#eval do
  let env ← Lean.getEnv

  let countTheoremsIn (ns : Lean.Name) : Nat :=
    env.constants.fold
      (fun acc name info =>
        match info with
        | Lean.ConstantInfo.thmInfo _ =>
            if ns.isPrefixOf name then acc + 1 else acc
        | _ => acc)
      0

  let targets : List Lean.Name := [
    `DkMath,
    `DkMath.CosmicFormula,
    `DkMath.Petal,
    `DkMath.NumberTheory,
    `DkMath.ABC,
    `DkMath.FLT,
    `DkMath.PowerSwap,
    `DkMath.Collatz,
    `DkMath.KUS,
    `DkMath.RH
  ]

  for ns in targets do
    IO.println s!"{ns}: {countTheoremsIn ns}"
  -/
