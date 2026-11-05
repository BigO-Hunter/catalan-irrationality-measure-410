module
public import Submission.CatalanMeasure.Parametric.RawDigitReduction
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan

def sparseDigitZero (v j : ℕ) : ℚ := -(3/2:ℚ)*zetaRat (v+1) j
def sparseDigitOne (sign : ℚ) (v j : ℕ) : ℚ :=
  sign*(momentRatSigned ((v:ℤ)-1) j-momentRatSigned ((v:ℤ)+1) j) -
    (3/2:ℚ)*zetaRat v j
def sparseDigitTwo (sign : ℚ) (v j : ℕ) : ℚ :=
  2*sign*(momentRatSigned ((v:ℤ)-2) j-momentRatSigned (v:ℤ) j) -
    3*zetaRat (v-1) j+(3/2:ℚ)*zetaRat (v+1) j

theorem sparseDigit_identity_pos (j : Fin 2) :
    sparseDigitTwo 1 2 (j.val+1) =
      (292/59:ℚ)*sparseDigitOne 1 2 (j.val+1) -
        (3281/177:ℚ)*sparseDigitZero 2 (j.val+1) := by
  fin_cases j <;> decide +kernel

theorem sparseDigit_identity_neg (j : Fin 2) :
    sparseDigitTwo (-1) 2 (j.val+1) =
      -(604/139:ℚ)*sparseDigitOne (-1) 2 (j.val+1) -
        (7745/417:ℚ)*sparseDigitZero 2 (j.val+1) := by
  fin_cases j <;> decide +kernel

end CatalanMeasure.Parametric
