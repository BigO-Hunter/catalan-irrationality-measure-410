module

public import Mathlib.Tactic.FinCases
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularMinusProductRows40To41
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularPlusProductRows40To41
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularZeroInvRows36To47
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularZeroModRows24To35
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1.P1

@[expose] public section

namespace OAI

section

namespace InternalCatalan


end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralBaseMod (r : Fin 49) (k : Fin 48) : ZMod 101 :=
  match r.val with
  | 0 => fixedLiteralModZeroRow_0 k
  | 1 => fixedLiteralModZeroRow_1 k
  | 2 => fixedLiteralModZeroRow_2 k
  | 3 => fixedLiteralModZeroRow_3 k
  | 4 => fixedLiteralModZeroRow_4 k
  | 5 => fixedLiteralModZeroRow_5 k
  | 6 => fixedLiteralModZeroRow_6 k
  | 7 => fixedLiteralModZeroRow_7 k
  | 8 => fixedLiteralModZeroRow_8 k
  | 9 => fixedLiteralModZeroRow_9 k
  | 10 => fixedLiteralModZeroRow_10 k
  | 11 => fixedLiteralModZeroRow_11 k
  | 12 => fixedLiteralModZeroRow_12 k
  | 13 => fixedLiteralModZeroRow_13 k
  | 14 => fixedLiteralModZeroRow_14 k
  | 15 => fixedLiteralModZeroRow_15 k
  | 16 => fixedLiteralModZeroRow_16 k
  | 17 => fixedLiteralModZeroRow_17 k
  | 18 => fixedLiteralModZeroRow_18 k
  | 19 => fixedLiteralModZeroRow_19 k
  | 20 => fixedLiteralModZeroRow_20 k
  | 21 => fixedLiteralModZeroRow_21 k
  | 22 => fixedLiteralModZeroRow_22 k
  | 23 => fixedLiteralModZeroRow_23 k
  | 24 => fixedLiteralModZeroRow_24 k
  | 25 => fixedLiteralModZeroRow_25 k
  | 26 => fixedLiteralModZeroRow_26 k
  | 27 => fixedLiteralModZeroRow_27 k
  | 28 => fixedLiteralModZeroRow_28 k
  | 29 => fixedLiteralModZeroRow_29 k
  | 30 => fixedLiteralModZeroRow_30 k
  | 31 => fixedLiteralModZeroRow_31 k
  | 32 => fixedLiteralModZeroRow_32 k
  | 33 => fixedLiteralModZeroRow_33 k
  | 34 => fixedLiteralModZeroRow_34 k
  | 35 => fixedLiteralModZeroRow_35 k
  | 36 => fixedLiteralModZeroRow_36 k
  | 37 => fixedLiteralModZeroRow_37 k
  | 38 => fixedLiteralModZeroRow_38 k
  | 39 => fixedLiteralModZeroRow_39 k
  | 40 => fixedLiteralModZeroRow_40 k
  | 41 => fixedLiteralModZeroRow_41 k
  | 42 => fixedLiteralModZeroRow_42 k
  | 43 => fixedLiteralModZeroRow_43 k
  | 44 => fixedLiteralModZeroRow_44 k
  | 45 => fixedLiteralModZeroRow_45 k
  | 46 => fixedLiteralModZeroRow_46 k
  | 47 => fixedLiteralModZeroRow_47 k
  | _ => fixedLiteralModPlusRow_47 k - fixedLiteralModZeroRow_47 k

theorem fixedLiteralBaseMod_zero (r k : Fin 48) :
    fixedLiteralBaseMod r.castSucc k = fixedLiteralModZero r k := by
  fin_cases r <;> rfl

theorem fixedLiteralBaseMod_auxiliary (k : Fin 48) :
    fixedLiteralBaseMod 48 k = fixedLiteralModPlusRow_47 k - fixedLiteralModZeroRow_47 k := by
  rfl

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_0 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 0 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 0 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_1 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 1 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 1 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_10 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 10 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 10 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_11 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 11 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 11 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_12 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 12 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 12 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_13 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 13 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 13 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_14 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 14 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 14 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_15 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 15 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 15 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_16 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 16 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 16 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_17 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 17 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 17 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_18 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 18 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 18 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_19 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 19 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 19 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_20 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 20 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 20 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_21 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 21 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 21 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_22 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 22 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 22 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_23 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 23 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 23 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_24 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 24 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 24 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_25 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 25 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 25 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_26 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 26 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 26 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_27 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 27 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 27 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_28 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 28 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 28 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_29 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 29 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 29 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_2 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 2 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 2 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_3 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 3 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 3 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_30 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 30 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 30 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_31 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 31 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 31 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_32 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 32 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 32 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_33 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 33 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 33 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_34 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 34 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 34 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_35 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 35 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 35 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_36 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 36 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 36 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_37 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 37 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 37 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_38 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 38 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 38 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_39 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 39 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 39 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_0 : ∀ k : Fin 48,
    fixedLiteralBaseMod (0 : Fin 48).castSucc k +
      fixedLiteralBaseMod (0 : Fin 48).succ k = fixedLiteralModPlus 0 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_0 : ∀ k : Fin 48,
    fixedLiteralBaseMod (0 : Fin 48).castSucc k -
      fixedLiteralBaseMod (0 : Fin 48).succ k = fixedLiteralModMinus 0 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_1 : ∀ k : Fin 48,
    fixedLiteralBaseMod (1 : Fin 48).castSucc k +
      fixedLiteralBaseMod (1 : Fin 48).succ k = fixedLiteralModPlus 1 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_1 : ∀ k : Fin 48,
    fixedLiteralBaseMod (1 : Fin 48).castSucc k -
      fixedLiteralBaseMod (1 : Fin 48).succ k = fixedLiteralModMinus 1 k := by
  decide +kernel

end InternalCatalan

end

end OAI
