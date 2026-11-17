import Theorems.EntrySolid
import Theorems.SidePipe

namespace Smbrta.EntryBufferNear
open ScreenPage PipeTransitionAll

/-- A column of the two block buffers, with both pages in order. -/
def column (P : Places) (j : Nat) : Nat := j / (P.bufN / 2) * 16 + j % 16

/-- Each map coin lies at least gap columns to the left of the mouth. -/
def gapCheck (sy : Syms) (nm : Names) (m0 : Machine) (gap : Nat) : Bool :=
  let P := placesR sy nm m0
  let M := RoomMap.mapRef m0
  let cs := RoomBlocks.coinsOf P
  (List.range P.bufN).all fun j => !cs.contains (M.ram.get! (P.bufLo+j)) || decide (column P j + gap ≤ SidePipe.column sy)

theorem gap_of_check {sy : Syms} {nm : Names} {m0 : Machine} {gap j : Nat}
    (h : gapCheck sy nm m0 gap = true) (hj : j < (placesR sy nm m0).bufN)
    (hc : (RoomMap.mapRef m0).ram.get! ((placesR sy nm m0).bufLo+j) ∈ RoomBlocks.coinsOf (placesR sy nm m0)) :
    column (placesR sy nm m0) j + gap ≤ SidePipe.column sy := by
  have h' := List.all_eq_true.1 h j (List.mem_range.2 hj)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h'
  rcases h' with hn | hn
  · have he := List.contains_iff_mem.2 hc
    rw [he] at hn
    cases hn
  · exact hn

/-- A solid non-coin map byte cannot become a coin. -/
theorem map_coin {P : Places} {cs : List UInt8} {M m : Machine} {d : Nat}
    (hS : RoomBlocks.Solid P cs M m) (hlo : P.bufLo ≤ d) (hhi : d < P.bufLo + P.bufN)
    (hc : m.ram.get! d ∈ cs) : M.ram.get! d ∈ cs := by
  by_cases hm : M.ram.get! d ∈ cs
  · exact hm
  · rw [hS d hlo hhi hm] at hc
    exact hc

/-- Separate player positions from two read positions, with offsets shorter than a column. -/
theorem read_separation {coin pipe xc xp ac ap gap : Nat}
    (hg : coin + gap ≤ pipe) (hc : xc + ac < 16 * (coin + 1))
    (hp : 16 * pipe ≤ xp + ap) (ha : ap < 16) (hl : 30 ≤ 16 * gap) :
    xc + (16 * gap - 30) ≤ xp := by omega

/-- The geometric gap is incompatible with a one-frame movement bound smaller than it. -/
theorem not_short_move {coin pipe xc xp ac ap gap speed : Nat}
    (hg : coin + gap ≤ pipe) (hc : xc + ac < 16 * (coin + 1))
    (hp : 16 * pipe ≤ xp + ap) (ha : ap < 16) (hs : speed < 16 * gap - 30)
    (hl : 30 ≤ 16 * gap) (hm : xp ≤ xc + speed) : False := by
  have h := read_separation hg hc hp ha hl
  omega
end Smbrta.EntryBufferNear
