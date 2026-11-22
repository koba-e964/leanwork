# 命題論理に対する Glivenko の定理

Lean 4.36.0 による構文的な証明です。外部ライブラリ（Mathlib を含む）は不要です。

```sh
cd glivenko
lake build
```

## 定義

実装は `Glivenko/Basic.lean` にあります。名前空間は `Glivenko` です。

- `Formula`：自然数で識別する命題変数、偽 `bot`、含意 `⇒`、連言 `⋏`、選言 `⋎`。
- `∼A`：`A ⇒ Formula.bot` の略記。Lean 自身の `Not` とは区別します。
- `IntAxiom`：直観主義命題論理の Hilbert 公理スキーマ。K、S、爆発律、連言の導入・除去、選言の導入・除去を含みます。
- `Derives L Γ A`：仮定のリスト `Γ` からの導出。仮定、公理、modus ponens を使い、`L = Logic.classical` の場合だけ排中律を追加できます。
- `IPC Γ A`、`CPC Γ A`：それぞれ直観主義・古典命題論理での導出可能性。

これらは対象論理の構文と導出の帰納的定義です。古典論理の証明可能性を Lean の `Prop` の真偽として定義しているわけではありません。

## 定理

通常の、仮定を持たない形は次です。

```lean
theorem glivenko_closed (A : Formula) : CPC [] A ↔ IPC [] (∼∼A)
```

より一般に、同じ仮定リストを保持する形も証明しています。

```lean
theorem glivenko (h : CPC Γ A) : IPC Γ (∼∼A)
theorem glivenko_iff : CPC Γ A ↔ IPC Γ (∼∼A)
```

## 証明の構成

1. `Derives.weaken` と `Derives.discharge` で弱化と演繹定理を証明します。
2. 直観主義論理で二重否定の導入、二重否定された式についての modus ponens、排中律の二重否定を導きます。
3. 古典論理の導出に関する帰納法で `glivenko` を証明します。仮定と直観主義公理には二重否定を導入し、modus ponens と排中律には手順 2 の補題を使います。
4. 逆向きは直観主義的導出を古典論理に埋め込み、排中律から導いた二重否定除去を使います。

`#print axioms` により主定理の依存公理をビルド時に表示します。3 つの主定理はいずれも公理への依存がないことを確認できます。`sorry`、未証明の公理宣言、`Classical.choice` は使用していません。
