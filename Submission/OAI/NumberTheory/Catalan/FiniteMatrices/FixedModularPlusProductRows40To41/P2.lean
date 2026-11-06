module

public import Mathlib.Tactic.FinCases
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularPlusInvRows36To47
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularPlusModRows24To35
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularPlusProductRows40To41.P1

@[expose] public section

namespace OAI

section

namespace InternalCatalan


def fixedLiteralInvPlus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralInvPlusRow_0
  | 1 => fixedLiteralInvPlusRow_1
  | 2 => fixedLiteralInvPlusRow_2
  | 3 => fixedLiteralInvPlusRow_3
  | 4 => fixedLiteralInvPlusRow_4
  | 5 => fixedLiteralInvPlusRow_5
  | 6 => fixedLiteralInvPlusRow_6
  | 7 => fixedLiteralInvPlusRow_7
  | 8 => fixedLiteralInvPlusRow_8
  | 9 => fixedLiteralInvPlusRow_9
  | 10 => fixedLiteralInvPlusRow_10
  | 11 => fixedLiteralInvPlusRow_11
  | 12 => fixedLiteralInvPlusRow_12
  | 13 => fixedLiteralInvPlusRow_13
  | 14 => fixedLiteralInvPlusRow_14
  | 15 => fixedLiteralInvPlusRow_15
  | 16 => fixedLiteralInvPlusRow_16
  | 17 => fixedLiteralInvPlusRow_17
  | 18 => fixedLiteralInvPlusRow_18
  | 19 => fixedLiteralInvPlusRow_19
  | 20 => fixedLiteralInvPlusRow_20
  | 21 => fixedLiteralInvPlusRow_21
  | 22 => fixedLiteralInvPlusRow_22
  | 23 => fixedLiteralInvPlusRow_23
  | 24 => fixedLiteralInvPlusRow_24
  | 25 => fixedLiteralInvPlusRow_25
  | 26 => fixedLiteralInvPlusRow_26
  | 27 => fixedLiteralInvPlusRow_27
  | 28 => fixedLiteralInvPlusRow_28
  | 29 => fixedLiteralInvPlusRow_29
  | 30 => fixedLiteralInvPlusRow_30
  | 31 => fixedLiteralInvPlusRow_31
  | 32 => fixedLiteralInvPlusRow_32
  | 33 => fixedLiteralInvPlusRow_33
  | 34 => fixedLiteralInvPlusRow_34
  | 35 => fixedLiteralInvPlusRow_35
  | 36 => fixedLiteralInvPlusRow_36
  | 37 => fixedLiteralInvPlusRow_37
  | 38 => fixedLiteralInvPlusRow_38
  | 39 => fixedLiteralInvPlusRow_39
  | 40 => fixedLiteralInvPlusRow_40
  | 41 => fixedLiteralInvPlusRow_41
  | 42 => fixedLiteralInvPlusRow_42
  | 43 => fixedLiteralInvPlusRow_43
  | 44 => fixedLiteralInvPlusRow_44
  | 45 => fixedLiteralInvPlusRow_45
  | 46 => fixedLiteralInvPlusRow_46
  | 47 => fixedLiteralInvPlusRow_47
  | _ => fun _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_0 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 0 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 0 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_1 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 1 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 1 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_10 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 10 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 10 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_11 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 11 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 11 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_12 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 12 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 12 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_13 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 13 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 13 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_14 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 14 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 14 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_15 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 15 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 15 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_16 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 16 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 16 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_17 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 17 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 17 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_18 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 18 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 18 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_19 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 19 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 19 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_20 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 20 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 20 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_21 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 21 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 21 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_22 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 22 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 22 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_23 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 23 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 23 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_24 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 24 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 24 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_25 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 25 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 25 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_26 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 26 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 26 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_27 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 27 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 27 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_28 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 28 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 28 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_29 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 29 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 29 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_2 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 2 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 2 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_3 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 3 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 3 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_30 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 30 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 30 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_31 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 31 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 31 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_32 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 32 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 32 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_33 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 33 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 33 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_34 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 34 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 34 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_35 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 35 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 35 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_36 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 36 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 36 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_37 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 37 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 37 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_38 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 38 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 38 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_39 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 39 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 39 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_40 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 40 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 40 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_41 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 41 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 41 k := by
  decide +kernel

end InternalCatalan

end

end OAI
