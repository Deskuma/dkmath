# GitHub Actions CI 設定

DkMath の Lean プロジェクトは、リポジトリ直下ではなく `lean/dk_math/` に配置されている。

そのため、GitHub Actions の workflow 自体はリポジトリ直下の `.github/workflows/` に置き、各 Action に Lean パッケージの位置を明示する必要がある。

## 1. ディレクトリ構成

```text
dkmath/
├─ .github/
│  ├─ workflows/
│  │  ├─ lean_action_ci.yml
│  │  └─ update.yml
│  └─ disabled-workflows/
│     └─ create-release.yml
└─ lean/
   └─ dk_math/
      ├─ lean-toolchain
      ├─ lakefile.toml
      ├─ lake-manifest.json
      └─ DkMath/
```

GitHub Actions が workflow として認識するのは、リポジトリ直下の `.github/workflows/` にある YAML ファイルだけである。

次のような配置では認識されない。

```text
lean/dk_math/.github/workflows/
```

## 2. Lean CI

ファイル:

```text
.github/workflows/lean_action_ci.yml
```

内容:

```yaml
name: Lean CI

on:
  push:
  pull_request:
  workflow_dispatch:

permissions:
  contents: read

jobs:
  build:
    name: Build DkMath
    runs-on: ubuntu-latest

    steps:
      - name: Checkout repository
        uses: actions/checkout@v5

      - name: Build Lean project
        uses: leanprover/lean-action@v1
        with:
          lake-package-directory: lean/dk_math
          build: true
          test: false
          lint: false
```

### 動作

- 任意ブランチへの `push` で自動実行される。
- Pull Request でも自動実行される。
- `workflow_dispatch` により手動実行できる。
- `lake-package-directory: lean/dk_math` により、サブディレクトリ内の Lake プロジェクトを対象にする。
- `lake build` の終了コードが `0` なら CI 成功、非 `0` なら失敗となる。
- Lean の warning は通常 CI を失敗させない。

### 確認済み実行

初回有効化後、次のブランチで成功を確認した。

```text
develop

dev/petal-collatz-bridge-260630-v6
```

GitHub 上で各コミットに `Lean CI ✓` が表示されれば、そのコミットが GitHub の Ubuntu runner 上でもビルドを通過した公開記録となる。

## 3. 依存関係更新 workflow

ファイル:

```text
.github/workflows/update.yml
```

内容:

```yaml
name: Update Dependencies

on:
  workflow_dispatch:

jobs:
  check-for-updates:
    name: Check for updates
    runs-on: ubuntu-latest

    outputs:
      is-update-available: ${{ steps.check-for-updates.outputs.is-update-available }}
      new-tags: ${{ steps.check-for-updates.outputs.new-tags }}

    steps:
      - name: Check for Mathlib updates
        id: check-for-updates
        uses: leanprover-community/mathlib-update-action@v1
        with:
          intermediate_releases: latest
          lake_package_directory: lean/dk_math

  do-update:
    name: Test update
    runs-on: ubuntu-latest

    permissions:
      contents: write
      issues: write
      pull-requests: write

    needs:
      - check-for-updates

    if: ${{ needs.check-for-updates.outputs.is-update-available == 'true' }}

    strategy:
      max-parallel: 1
      matrix:
        tag: ${{ fromJSON(needs.check-for-updates.outputs.new-tags) }}

    steps:
      - name: Update and build repository
        id: update-the-repo
        uses: leanprover-community/mathlib-update-action/do-update@v1
        with:
          tag: ${{ matrix.tag }}
          lake_package_directory: lean/dk_math
          on_update_succeeds: pr
          on_update_fails: issue
```

この workflow は `workflow_dispatch` のみなので、自動では起動しない。

GitHub Actions から Pull Request を作成させる場合は、必要に応じて次を有効にする。

```text
Settings
→ Actions
→ General
→ Workflow permissions
→ Allow GitHub Actions to create and approve pull requests
```

`lean-action` の入力名は `lake-package-directory`、`mathlib-update-action` の入力名は `lake_package_directory` であり、ハイフンとアンダースコアが異なることに注意する。

## 4. リリース workflow

`leanprover-community/lean-release-tag` は、リポジトリ直下に `lean-toolchain` がある構成を前提としている。

DkMath の `lean-toolchain` は次にある。

```text
lean/dk_math/lean-toolchain
```

このため、現在のリリース workflow は実行対象から外し、次へ退避している。

```text
.github/disabled-workflows/create-release.yml
```

`DkMath.Lib.*` または `DkMathlib.*` のリリース準備段階で、サブディレクトリ構成に対応した独自 workflow を再設計する。

## 5. workflow ファイル更新時の GitHub 認証

`.github/workflows/*.yml` を HTTPS 経由で push するとき、認証トークンに `workflow` scope がない場合、GitHub は push を拒否する。

代表的なエラー:

```text
refusing to allow an OAuth App to create or update workflow
`.github/workflows/lean_action_ci.yml` without `workflow` scope
```

GitHub CLI を使う場合の修正手順:

```bash
gh auth status
gh auth refresh -h github.com -s workflow
gh auth setup-git
git push origin develop
```

このエラーが発生しても、ローカルの commit は失われない。認証 scope を追加した後、同じ push を再実行すればよい。

## 6. 手動実行とブランチ

`push:` に branch 制限を設定していないため、`develop` や作業ブランチへの push でも CI は自動実行される。

`workflow_dispatch` の `Run workflow` ボタンを利用するには、通常 workflow ファイルがデフォルトブランチにも存在する必要がある。デフォルトブランチへ導入後は、実行対象ブランチとして `develop` などを選択できる。

## 7. warning の扱い

標準設定では、CI の成否は `lake build` の終了コードで決まる。

```text
warning あり + exit code 0     → CI 成功
error あり   + exit code 非 0  → CI 失敗
```

warning をすべてエラーとして扱う設定は、実験段階の `DkMath.*` では使用しない。

将来、安定 API である `DkMath.Lib.*` や `DkMathlib.*` に対して、より厳格な warning 方針を導入する余地がある。

## 8. 運用方針

現在の CI は、公開されたコミットについて次を保証するために使用する。

- 指定された Lean toolchain を取得できる。
- Mathlib などの依存関係を解決できる。
- `lean/dk_math` において `lake build` が成功する。
- GitHub のクリーンな Ubuntu runner 上で結果を再現できる。

CI は定理の自然言語上の意味や研究上の解釈を保証するものではない。

保証対象は、指定された形式化コードが Lean によってビルド可能であることまでである。
