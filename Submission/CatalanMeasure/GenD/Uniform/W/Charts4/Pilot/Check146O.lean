module
public import Mathlib.Tactic.IntervalCases
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Data146O
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Pilot.Check146
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146

set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 50

theorem cho_ok0 : (chartO 0).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok1 : (chartO 1).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok2 : (chartO 2).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok3 : (chartO 3).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok4 : (chartO 4).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok5 : (chartO 5).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok6 : (chartO 6).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok7 : (chartO 7).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok8 : (chartO 8).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok9 : (chartO 9).check packet.n packet.d packet.v = true := by decide +kernel
theorem cho_ok10 : (chartO 10).check packet.n packet.d packet.v = true := by decide +kernel

theorem packetO_check : packetO.check = true :=
  Packet.check_of_parts head_ok (by
    intro c hc
    simp only [packetO, packet, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    interval_cases j
    exacts [cho_ok0, cho_ok1, cho_ok2, cho_ok3, cho_ok4, cho_ok5, cho_ok6, cho_ok7, cho_ok8, cho_ok9, cho_ok10])

theorem packetO_sound : packetO.Sound := Packet.check_sound packetO_check

end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
