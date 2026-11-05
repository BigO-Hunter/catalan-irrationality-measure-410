module
public import Submission.CatalanMeasure.Cert.IntegerPoly
@[expose] public section

namespace CatalanMeasure.Cert

/-- Denominator power and numerator for an affine substitution, using integers only. -/
def ipAffine (a h d : ℤ) : List ℤ → ℤ × List ℤ
  | [] => (1, [])
  | c :: p =>
    let q := ipAffine a h d p
    (d * q.1, ipAdd [c * q.1] (ipLinear a h q.2))

theorem ipAffine_eval (p : List ℤ) (a h d : ℤ) (y : ℝ) (hd : (d : ℝ) ≠ 0) :
    ((ipAffine a h d p).1 : ℝ) = (d : ℝ) ^ p.length ∧
    (d : ℝ) * ipEval (ipAffine a h d p).2 y =
      (d : ℝ) ^ p.length * ipEval p (((a : ℝ) + h * y) / d) := by
  induction p with
  | nil => simp [ipAffine, ipEval]
  | cons c p ih =>
    simp only [ipAffine, Int.cast_mul, ipEval_add, ipEval, ipEval_linear,
      List.length_cons, pow_succ]
    constructor
    · rw [ih.1]; ring
    · rw [ih.1]
      let s : ℝ := a + h * y
      change (d : ℝ) * ((c : ℝ) * d ^ p.length + y * 0 + s * ipEval (ipAffine a h d p).2 y) =
        (d : ℝ) ^ p.length * d * ((c : ℝ) + s / d * ipEval p (s / d))
      have he : (d : ℝ) * (s / d) = s := by field_simp
      calc
        _ = (c : ℝ) * (d ^ p.length * d) + s * (d * ipEval (ipAffine a h d p).2 y) := by ring
        _ = (c : ℝ) * (d ^ p.length * d) + s * (d ^ p.length * ipEval p (s / d)) := by rw [ih.2]
        _ = (d : ℝ) ^ p.length * d * c + (d : ℝ) ^ p.length * (d * (s / d)) * ipEval p (s / d) := by rw [he]; ring
        _ = _ := by ring

def ipAbsSum (p : List ℤ) : ℤ := (p.map (fun c => |c|)).sum

@[simp] theorem ipAbsSum_cons (c : ℤ) (p : List ℤ) :
    ipAbsSum (c :: p) = |c| + ipAbsSum p := by simp [ipAbsSum]

theorem ipAbsSum_nonneg (p : List ℤ) : 0 ≤ ipAbsSum p := by
  unfold ipAbsSum
  exact List.sum_nonneg (by intro x hx; obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg c)

theorem abs_ipEval_le (p : List ℤ) {y : ℝ} (hy : |y| ≤ 1) :
    |ipEval p y| ≤ (ipAbsSum p : ℝ) := by
  induction p with
  | nil => simp [ipEval, ipAbsSum]
  | cons c p ih =>
    rw [ipEval, ipAbsSum_cons]
    push_cast
    calc
      _ ≤ |(c : ℝ)| + |y| * |ipEval p y| := by simpa [abs_mul] using abs_add_le (c : ℝ) (y * ipEval p y)
      _ ≤ |(c : ℝ)| + 1 * (ipAbsSum p : ℝ) := by gcongr
      _ = _ := by ring

theorem abs_ipEval_ge (c : ℤ) (p : List ℤ) {y : ℝ} (hy : |y| ≤ 1) :
    ((|c| - ipAbsSum p : ℤ) : ℝ) ≤ |ipEval (c :: p) y| := by
  have h := abs_ipEval_le p hy
  have hm : |y * ipEval p y| ≤ (ipAbsSum p : ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul hy h (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he := abs_sub_abs_le_abs_sub (c : ℝ) (-(y * ipEval p y))
  rw [sub_neg_eq_add, abs_neg] at he
  simp only [ipEval]
  push_cast
  linarith

end CatalanMeasure.Cert
