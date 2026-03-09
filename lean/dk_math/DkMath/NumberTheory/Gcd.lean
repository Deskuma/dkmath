/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- Gcd 系の API

-- Note: 各種 Gcd 補題の import
-- 実装は ./Gcd/ ディレクトリ配下にて行う。e.g. ./Gcd/Basic.lean, ./Gcd/GN.lean, ./Gcd/Div.lean など。
-- 現在ある既存の Gcd*.lean は、後々リファクタリングを行いながら ./Gcd/ へと移動する。
-- 移動後は、こちらの `import DkMath.NumberTheory.Gcd` から
-- `./Gcd/Basic.lean`, `./Gcd/GN.lean`, `./Gcd/Div.lean` などを import する形にする。
-- 個別に import を行う場合は `DkMath.NumberTheory.Gcd.Basic`,
-- `DkMath.NumberTheory.Gcd.GN` などを import する。

import DkMath.NumberTheory.Gcd.Basic
import DkMath.NumberTheory.Gcd.GN
