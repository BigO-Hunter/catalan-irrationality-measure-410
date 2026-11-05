module
public import Submission.CatalanMeasure.Cert.Norm
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan

deriving instance DecidableEq for LogTerm

/-- A single finite coefficient contribution, checked independently of the sum. -/
def finNormTermQ (cs : List ℤ) (tail : List TailQ) (k : ℕ) : ℚ :=
  let f : ℚ := (cs.getD k 0 : ℚ)/100000000
  (f*f+2*f*tailValQ tail (k+1))/(k+1:ℕ)

theorem finNormQ_of_terms {cs : List ℤ} {tail : List TailQ} {qs : List ℚ}
    (hlen : qs.length=cs.length)
    (h : ∀ k, k<cs.length → finNormTermQ cs tail k=qs.getD k 0) :
    finNormQ cs tail=qs.sum := by
  unfold finNormQ
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro k hk hkq
    simp only [List.getElem_map,List.getElem_range]
    simpa only [finNormTermQ,List.getD_eq_getElem qs 0 hkq] using h k (by simpa using hk)

/-- Only the logarithmic tail is reduced in this check. The potentially large
finite rational sum is supplied by separately checked coefficient equalities. -/
def normTailOK (tail : List TailQ) (f B : ℚ) : Bool :=
  match sumLogs (pairTerms tail) with
  | some ve => decide (ve.1+ve.2+f ≤ B)
  | none => false

theorem normSq_le_of_split {cs : List ℤ} {tail : List TailQ} {f B : ℚ}
    (hd : tailsInDisk tail=true) (hf : finNormQ cs tail=f)
    (hc : normTailOK tail f B=true) :
    barrierTrialNormSq (trialSeq cs tail) ≤ (B:ℝ) := by
  unfold normTailOK at hc
  split at hc
  · rename_i ve he
    have ha : normApprox cs tail=some (ve.1+f,ve.2) := by
      unfold normApprox
      rw [he,hf]
      rfl
    have hb := normApprox_spec hd ha
    have hq : ve.1+ve.2+f ≤ B := of_decide_eq_true hc
    have hr : (ve.1:ℝ)+ve.2+f ≤ B := by exact_mod_cast hq
    push_cast at hb
    linarith only [hb,hr]
  · simp at hc

def logUpperOK (terms : List LogTerm) (B : ℚ) : Bool :=
  match sumLogs terms with
  | some ve => decide (ve.1+ve.2 ≤ B)
  | none => false

theorem logUpper_le {terms : List LogTerm} {B : ℚ}
    (hc : logUpperOK terms B=true) : (terms.map LogTerm.val).sum ≤ (B:ℝ) := by
  unfold logUpperOK at hc
  split at hc
  · rename_i ve he
    have hh := sumLogs_spec he
    have hq : ve.1+ve.2 ≤ B := of_decide_eq_true hc
    have hr : ((ve.1+ve.2:ℚ):ℝ) ≤ (B:ℝ) := by exact_mod_cast hq
    push_cast at hr
    linarith only [(abs_le.mp hh).2,hr]
  · simp at hc

theorem logChunks_le {chunks : List (List LogTerm)} {bs : List ℚ}
    (hc : List.Forall₂ (fun l b => logUpperOK l b=true) chunks bs) :
    (chunks.flatten.map LogTerm.val).sum ≤ (bs.sum:ℝ) := by
  induction hc with
  | nil => simp
  | cons h ht ih =>
    simp only [List.flatten_cons,List.map_append,List.sum_append,List.sum_cons,Rat.cast_add]
    exact add_le_add (logUpper_le h) ih

theorem normSq_le_of_logChunks {cs : List ℤ} {tail : List TailQ} {f B : ℚ}
    {chunks : List (List LogTerm)} {bs : List ℚ}
    (hd : tailsInDisk tail=true) (hf : finNormQ cs tail=f)
    (he : pairTerms tail=chunks.flatten)
    (hc : List.Forall₂ (fun l b => logUpperOK l b=true) chunks bs)
    (hs : f+bs.sum ≤ B) : barrierTrialNormSq (trialSeq cs tail) ≤ (B:ℝ) := by
  rw [trialSeq_normSq hd,←pairTerms_val,he,hf]
  have hh := logChunks_le hc
  have hr : ((f+bs.sum:ℚ):ℝ) ≤ (B:ℝ) := by exact_mod_cast hs
  push_cast at hr
  push_cast at hh
  linarith only [hh,hr]

end CatalanMeasure.Cert
