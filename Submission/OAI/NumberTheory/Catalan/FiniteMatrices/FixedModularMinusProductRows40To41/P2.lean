module

public import Mathlib.Tactic.FinCases
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularMinusInvRows36To47
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularMinusModRows24To35
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularMinusProductRows40To41.P1

@[expose] public section

namespace OAI

section

namespace InternalCatalan


def fixedLiteralInvMinus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralInvMinusRow_0
  | 1 => fixedLiteralInvMinusRow_1
  | 2 => fixedLiteralInvMinusRow_2
  | 3 => fixedLiteralInvMinusRow_3
  | 4 => fixedLiteralInvMinusRow_4
  | 5 => fixedLiteralInvMinusRow_5
  | 6 => fixedLiteralInvMinusRow_6
  | 7 => fixedLiteralInvMinusRow_7
  | 8 => fixedLiteralInvMinusRow_8
  | 9 => fixedLiteralInvMinusRow_9
  | 10 => fixedLiteralInvMinusRow_10
  | 11 => fixedLiteralInvMinusRow_11
  | 12 => fixedLiteralInvMinusRow_12
  | 13 => fixedLiteralInvMinusRow_13
  | 14 => fixedLiteralInvMinusRow_14
  | 15 => fixedLiteralInvMinusRow_15
  | 16 => fixedLiteralInvMinusRow_16
  | 17 => fixedLiteralInvMinusRow_17
  | 18 => fixedLiteralInvMinusRow_18
  | 19 => fixedLiteralInvMinusRow_19
  | 20 => fixedLiteralInvMinusRow_20
  | 21 => fixedLiteralInvMinusRow_21
  | 22 => fixedLiteralInvMinusRow_22
  | 23 => fixedLiteralInvMinusRow_23
  | 24 => fixedLiteralInvMinusRow_24
  | 25 => fixedLiteralInvMinusRow_25
  | 26 => fixedLiteralInvMinusRow_26
  | 27 => fixedLiteralInvMinusRow_27
  | 28 => fixedLiteralInvMinusRow_28
  | 29 => fixedLiteralInvMinusRow_29
  | 30 => fixedLiteralInvMinusRow_30
  | 31 => fixedLiteralInvMinusRow_31
  | 32 => fixedLiteralInvMinusRow_32
  | 33 => fixedLiteralInvMinusRow_33
  | 34 => fixedLiteralInvMinusRow_34
  | 35 => fixedLiteralInvMinusRow_35
  | 36 => fixedLiteralInvMinusRow_36
  | 37 => fixedLiteralInvMinusRow_37
  | 38 => fixedLiteralInvMinusRow_38
  | 39 => fixedLiteralInvMinusRow_39
  | 40 => fixedLiteralInvMinusRow_40
  | 41 => fixedLiteralInvMinusRow_41
  | 42 => fixedLiteralInvMinusRow_42
  | 43 => fixedLiteralInvMinusRow_43
  | 44 => fixedLiteralInvMinusRow_44
  | 45 => fixedLiteralInvMinusRow_45
  | 46 => fixedLiteralInvMinusRow_46
  | 47 => fixedLiteralInvMinusRow_47
  | _ => fun _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_0 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 0 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 0 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_1 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 1 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 1 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_10 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 10 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 10 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_11 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 11 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 11 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_12 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 12 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 12 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_13 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 13 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 13 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_14 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 14 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 14 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_15 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 15 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 15 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_16 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 16 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 16 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_17 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 17 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 17 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_18 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 18 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 18 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_19 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 19 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 19 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_20 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 20 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 20 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_21 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 21 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 21 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_22 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 22 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 22 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_23 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 23 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 23 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_24 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 24 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 24 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_25 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 25 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 25 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_26 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 26 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 26 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_27 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 27 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 27 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_28 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 28 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 28 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_29 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 29 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 29 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_2 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 2 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 2 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_3 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 3 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 3 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_30 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 30 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 30 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_31 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 31 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 31 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_32 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 32 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 32 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_33 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 33 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 33 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_34 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 34 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 34 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_35 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 35 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 35 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_36 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 36 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 36 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_37 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 37 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 37 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_38 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 38 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 38 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_39 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 39 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 39 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_40 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 40 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 40 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_41 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 41 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 41 k := by
  decide +kernel

end InternalCatalan

end

end OAI
