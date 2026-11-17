import Theorems.EntryHeight
import Theorems.RoomBlocks

namespace Smbrta.EntrySolid
open TaintRun ScreenPage PipeTransitionAll

/-- Coin bytes retain the old zero bits; every other map byte is known in full. -/
def masks (P : Places) (cs : List UInt8) (M : Machine) : List (Nat × UInt8) :=
  (List.range P.bufN).map fun j =>
    let d := P.bufLo + j
    (d, if cs.contains (M.ram.get! d) then ~~~ M.ram.get! d else 0xFF)

/-- Strengthen the room condition using the already proved solid map. -/
theorem cond_of_solid {E : Env} {P : Places} {cs : List UInt8} {M r m : Machine} {K L : List (Nat × UInt8)}
    (hm : RoomCond E r (K ++ RoomMap.bufK P.bufLo P.bufN M ++ L) m)
    (hs : RoomBlocks.Solid P cs M m)
    (hr : ∀ d, P.bufLo ≤ d → d < P.bufLo + P.bufN → M.ram.get! d ∉ cs → r.ram.get! d = M.ram.get! d) :
    RoomCond E r (K ++ masks P cs M ++ L) m := by
  refine { hm with bytes := ?_ }
  intro p hp
  simp only [List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · exact hm.bytes p (by simp [hp])
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    have hj' := List.mem_range.1 hj
    by_cases hc : cs.contains (M.ram.get! (P.bufLo + j)) = true
    · simp only [hc, if_true]
      exact hm.bytes (P.bufLo + j, ~~~ M.ram.get! (P.bufLo + j)) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j, hj, rfl⟩)))
    · have hn : M.ram.get! (P.bufLo + j) ∉ cs := fun h => hc (List.contains_iff_mem.2 h)
      simp only [hc, Bool.false_eq_true, if_false]
      rw [hs _ (by omega) (by omega) hn, hr _ (by omega) (by omega) hn]
  · exact hm.bytes p (by simp [hp])

def known (sy : Syms) (nm : Names) (m0 : Machine) : List (Nat × UInt8) :=
  knownOf nm ++ masks (placesR sy nm m0) (RoomBlocks.coinsOf (placesR sy nm m0)) (RoomMap.mapRef m0) ++ RoomMap.scrK sy m0

def refs (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  let P := placesR sy nm m0
  let M := RoomMap.mapRef m0
  let cs := RoomBlocks.coinsOf P
  (List.range P.bufN).all fun j => cs.contains (M.ram.get! (P.bufLo+j)) || (refR m0).ram.get! (P.bufLo+j) == M.ram.get! (P.bufLo+j)

theorem cond {sy : Syms} {nm : Names} {m0 m : Machine}
    (hr : refs sy nm m0 = true)
    (hm : RoomCond (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0) m)
    (hs : RoomBlocks.SolidR sy nm m0 m) : RoomCond (envR sy nm m0) (refR m0) (known sy nm m0) m := by
  apply cond_of_solid hm hs
  intro d hd1 hd2 hn
  have h := List.all_eq_true.1 hr (d - (placesR sy nm m0).bufLo) (List.mem_range.2 (by omega))
  have he : (placesR sy nm m0).bufLo + (d - (placesR sy nm m0).bufLo) = d := by omega
  rw [he] at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact False.elim (hn (List.contains_iff_mem.1 h))
  · exact h
end Smbrta.EntrySolid
