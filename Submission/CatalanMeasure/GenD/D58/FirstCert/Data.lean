module
public import Submission.CatalanMeasure.Cert.ShiftedCover
public import Submission.CatalanMeasure.FirstStrongTrial.Data
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert OAI.InternalCatalan
/-! D58 first trial: the frozen 40-mode trial data (design independent) with the D58 weights. -/
def R : RowWeights := ⟨11/29,3/29,49/58,168493357/100000000,5/29⟩
def C : ColumnWeights := ⟨9/58,3/58,0⟩
abbrev Pc : List ℤ := CatalanMeasure.FirstStrongTrial.Pc
abbrev P : List TailQ := CatalanMeasure.FirstStrongTrial.P
abbrev Vc : List ℤ := CatalanMeasure.FirstStrongTrial.Vc
abbrev V : List TailQ := CatalanMeasure.FirstStrongTrial.V
def MX : ℚ := -57927/50000
def MY : ℚ := -132981/100000
end CatalanMeasure.GenD.D58.FirstCert
