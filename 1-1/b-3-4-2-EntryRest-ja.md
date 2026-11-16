[ステージ 1-1 に戻る](README-ja.md)

# 入口に残るバイト

対象は変更前の `Rest` の 36 バイトです。第 1 矩形波の効果音キューを `Entry` 自体から外し、`Rest` は 35 バイトになりました。ガード、押すときの条件、保つバイトは増やしません。

3 段階は、フレーム 0 で分かること、ガードが添字の書き込みから守ること、フレームの歩きが値を保つことです。最初に分かっても、番地を直接指定する書き込みはガードでは止まりません。変わるバイトは、同じ値を保つ方法では証明できません。

| バイト | 最初に知る状態 | 止まる理由 | 書く処理 |
|---|---|---|---|
| `GameEngineSubroutine+0` | 8/8 | 操作中は別のルーチン。入る種類の指定が残る | `HandlePipeEntry / SetPRout` |
| `EnemyObjectPageSel+0` | 8/8 | 敵の読み込みと位置で変わる | `CheckRightBounds / CheckPageCtrlRow` |
| `AreaMusicBuffer_Alt+0` | 0/8 | フレーム 0 で不明。音の処理も書く | `NoStopSfx` |
| `Block_State+0` | 8/8 | 本物のフレームで変わる。添字の書き込み | `DBlockSte / ChkBrick / UpdSte` |
| `Block_State+1` | 8/8 | 本物のフレームで変わる。添字の書き込み | `DBlockSte / ChkBrick / UpdSte` |
| `Block_RepFlag+0` | 8/8 | 本物のフレームで変わる。添字の書き込み | `BouncingBlockHandler / ReplaceBlockMetatile` |
| `Block_RepFlag+1` | 8/8 | 本物のフレームで変わる。添字の書き込み | `BouncingBlockHandler / ReplaceBlockMetatile` |
| `Misc_State+8` | 8/8 | 本物のフレームで変わる。コインの処理 | `JCoinC / ProcJumpCoin` |
| `FloateyNum_Control+0` | 8/8 | 本物のフレームで変わる。浮かぶ点数の処理 | `SetupFloateyNumber / FloateyNumbersRoutine` |
| `FloateyNum_Control+1` | 8/8 | 本物のフレームで変わる。浮かぶ点数の処理 | `SetupFloateyNumber / FloateyNumbersRoutine` |
| `FloateyNum_Control+2` | 8/8 | 本物のフレームで変わる。浮かぶ点数の処理 | `SetupFloateyNumber / FloateyNumbersRoutine` |
| `FloateyNum_Control+3` | 8/8 | 本物のフレームで変わる。浮かぶ点数の処理 | `SetupFloateyNumber / FloateyNumbersRoutine` |
| `Enemy_State+0` | 8/8 | 本物のフレームで変わる。当たりと物の更新 | `SetDBSte / EraseEnemyObject / HandlePECollisions` |
| `Enemy_State+1` | 8/8 | 本物のフレームで変わる。当たりと物の更新 | `SetDBSte / EraseEnemyObject / HandlePECollisions` |
| `Enemy_State+2` | 8/8 | 本物のフレームで変わる。当たりと物の更新 | `SetDBSte / EraseEnemyObject / HandlePECollisions` |
| `Square1SoundQueue+0` | 8/8 | Entry から削除。ガードと押す条件の追加なし | `sound engine` |
| `Enemy_Flag+4` | 8/8 | 物の処理が書く。地図と物の事実が要る | `EraseEnemyObject / KillELoop / FinishFlame` |
| `Enemy_Flag+5` | 8/8 | 本物のフレームで変わる。パワーアップなどの処理が直接書く | `PwrUpJmp / FlagpoleObject` |
| `Enemy_ID+0` | 8/8 | 敵の読み込みの添字書き込み。ガードを増やすと本物の走りが落ちる | `StrID / StrFre / EraseEnemyObject` |
| `Enemy_ID+1` | 8/8 | 敵の読み込みの添字書き込み。ガードを増やすと本物の走りが落ちる | `StrID / StrFre / EraseEnemyObject` |
| `Enemy_ID+2` | 8/8 | 敵の読み込みの添字書き込み。ガードを増やすと本物の走りが落ちる | `StrID / StrFre / EraseEnemyObject` |
| `Enemy_ID+3` | 8/8 | 敵の読み込みの添字書き込み。ガードを増やすと本物の走りが落ちる | `StrID / StrFre / EraseEnemyObject` |
| `AreaMusicQueue+0` | 8/8 | パワーアップの当たりが書く。地図と当たりの事実が要る | `HandlePowerUpCollision / StoreMusic` |
| `EventMusicQueue+0` | 8/8 | 死亡とタイマーの処理が書く | `HoleDie / RunGameTimer / FlagpoleCollision` |
| `NoiseSoundQueue+0` | 8/8 | 物とレンガの処理が書く | `BrickShatter / InitBowserFlame` |
| `NoiseSoundBuffer+0` | 8/8 | 音の処理にキューの事実が要る | `NoiseSfxHandler / DecrementSfx3Length` |
| `AreaMusicBuffer+0` | 8/8 | 音の処理に曲のキューの事実が要る | `HandleAreaMusicLoopB / NotTRO` |
| `EventMusicBuffer+0` | 8/8 | 音の処理に曲のキューの事実が要る | `LoadEventMusic / HandleAreaMusicLoopB` |
| `VineFlagOffset+0` | 8/8 | つるの処理が書く。地図と物の事実が要る | `NextVO / KillVine` |
| `EnemyFrenzyBuffer+0` | 8/8 | 敵の処理が書く。地図と物の事実が要る | `InitEnemyFrenzy / BowserControl / SetoffF` |
| `EnemyFrenzyQueue+0` | 8/8 | エリアの読み込みが書く | `ExitAFrenzy / ChkEnemyFrenzy` |
| `WarpZoneControl+0` | 8/8 | エリアの読み込みが書く。地図の事実が要る | `WarpNum / WarpZoneObject` |
| `AreaPointer+0` | 8/8 | 敵のデータの命令が書く。位置とデータの事実が要る | `ParseRow0e / GetWNum` |
| `EntrancePage+0` | 8/8 | 敵のデータの命令が書く。位置とデータの事実が要る | `ParseRow0e / GetWNum` |
| `StarInvincibleTimer+0` | 8/8 | パワーアップの当たりが書く。タイマーと当たりの事実が要る | `HandlePowerUpCollision / timer updates` |
| `WorldNumber+0` | 8/8 | ワープの入りが書く。ワープと地図の事実が要る | `GetWNum` |

最初の状態の列は `TitleStart` の近い状態の数です。値が基準と一致するという意味ではありません。ルーチンや敵のページ選択は、操作中に基準と違う値を持ちます。保存した曲だけは、近い状態のどれもそのバイトを知りません。ここを強めるなら押すときの条件も調べる必要があります。この仕事では変更していません。

既存のガードにない候補を保つと、入口のガードに 1 バイト追加します。合併ガードがすでに持つ場合は、合併ガードの追加はありません。正確な内訳は `entry-rest-audit` が出します。ただし、直接の書き込み、実際に変わる値、添字の書き込みが残れば、その追加だけでは証明になりません。

## 効果音キューを外す確認

`Square1SoundQueue` のマスクを外し、`entryDropped` に加えます。出口の一覧から、知っているバイトとして再び加わらないようにします。土管の歩きは入口でこのバイトを知らずに始まります。入力はどれでも許したままです。

前の一覧での `entry-need 15` は、位置の確認、元の歩き、ポーズのクラスを持つ歩きの全部を通りました。クラスを持つ歩きの表は 158,808 と 143,194 状態、約 54 秒でした。仮定は 1 バイト減りますが、土管の確認は重くなります。証明のビルドで `Proof.PipeChangeEnd` は約 270 秒（前は 233 秒）で、`pipe-end-check` のメモリは約 1.6 GB（前は 0.5 GB）です。`entry-keep-check`（221,490 フレーム）で保つバイトを失うフレームはなく、40 の入口はどれも `Rest` と `Entry` を満たします。

## 残ること

保存した曲、地図と物の処理、タイマーや位置に依存するバイトは仮定のままです。番地への書き込みと添字の書き込みの両方を扱う必要があります。`time₁` は変更していません。

現状の入口のガードは 125 バイト、合併ガードは 143 バイトです。残る 35 バイトのうち、ルーチンはすでに両方で守ります。ほかの 34 バイトをそれぞれ追加する候補では、入口のガードと合併ガードの両方に 1 バイトずつ増えます。今回実際に増やしたバイトはありません。
