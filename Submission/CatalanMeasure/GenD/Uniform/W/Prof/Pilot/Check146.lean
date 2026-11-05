module
public import Mathlib.Tactic.IntervalCases
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Pilot.Data146
@[expose] public section
set_option Elab.async false

/-! Generated: kernel check of the stored packet, head and each chart as its own declaration. -/
namespace CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
open CatalanMeasure.GenD.Uniform.W.Prof

set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 50

theorem head_ok : packet.checkHead = true := by decide +kernel

theorem ch_ok0 : (chart 0).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok1 : (chart 1).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok2 : (chart 2).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok3 : (chart 3).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok4 : (chart 4).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok5 : (chart 5).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok6 : (chart 6).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok7 : (chart 7).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok8 : (chart 8).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok9 : (chart 9).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok10 : (chart 10).check packet.n packet.d packet.v = true := by decide +kernel

theorem packet_check : packet.check = true :=
  Packet.check_of_parts head_ok (by
    intro c hc
    simp only [packet, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    interval_cases j
    exacts [ch_ok0, ch_ok1, ch_ok2, ch_ok3, ch_ok4, ch_ok5, ch_ok6, ch_ok7, ch_ok8, ch_ok9, ch_ok10])

theorem packet_sound : packet.Sound := Packet.check_sound packet_check

end CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
