module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts5.Cover3
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Unique146
@[expose] public section
set_option Elab.async false

/-!
# `PhysHost` for the L0146 packet (`packetO`, window `Win`)

Assembly: `monoData` (R1) with `monoHost2` (hdom = `hdom_pilot`, hinj = `hinj_pilot`, hG = `hG_pilot`,
cover = `cover_pilot`).  `xi = projExtras ∘ emb`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts5
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts Finset
noncomputable section

/-- **The physical host of the L0146 packet.** -/
theorem physHost_pilot : PhysHost design packetO Win cNat wNatO := by
  intro N p hN hp hp2 hH hApp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hpD⟩ := hApp
  have hn : 1 ≤ design.n N := by rw [design_n]; have := hW.1; omega
  have hK' : packetO.n = bN design N p * 4 + 2 + 2 := packetO_n.trans (hKp hW)
  let M : MonoData design N p packetO.n := monoData hp2 hn hK'
  have hM : pd146.Realises M.prof := monoProfile_realises hW hK'
  refine ⟨M.sys, ⟨?_⟩⟩
  exact monoHost2 (width := fun g => wNatO g N p) M (projExtras hK')
    (fun y => sumProf_proj hK' _ (fun j => rfl) y) (fun y => sumProf_proj hK' _ (fun j => rfl) y)
    (low146 p) (design.q N / p) (design.q N % p) (fun g k => jetP N p g.val k.val)
    (fun x hker hproj => hinj_pilot hW hpD x hker hproj)
    (fun x hker => by
      obtain ⟨c, hc⟩ := hdom_pilot hW hp2 hn x hker
      exact ⟨c, hc⟩)
    (fun x hker => hG_pilot hW x hker)
    (cover_pilot hW M hM)

end
end CatalanMeasure.GenD.Uniform.W.Charts5
